// Fuck it we're doing it live!
// Cranelift (and probably any other codegen IR like LLVM or libgccjit) is just
// a bit too abstact for us; specifically, they target multiple ISAs, so try not
// to expose processor flags behavior to the user.
// We *need* processor flag behavior, however, because the assembly we're lifting
// depends on it.
//
// Thus, this IR was born. It's basically just a thin shim over dynasm-rs, but
// with an RSVDG-esque graph structure for data dependencies for instructions.
// This is because the *primary* use for it is register allocation; the assembly
// itself is already reasonably optimized just by LLVM when it is first emitted,
// we just want to elide checks and stop everything from moving back and forth for
// the function ABI for each inlined closure body.
use lineiform::lift::{JitValue, JitTemp};
use lineiform::block::{Function};
use petgraph::prelude::*;
use petgraph::stable_graph::StableGraph;
use petgraph::graph::{NodeIndex};
use petgraph::Direction;
use petgraph::visit::{EdgeRef, Dfs, Reversed, depth_first_search, DfsEvent, ControlFlow, IntoEdgeReferences};
use yaxpeax_x86::long_mode::{Operand, RegSpec, register_class};
use yaxpeax_x86::x86_64;
use dynasmrt::{dynasm, DynasmApi, DynasmLabelApi, AssemblyOffset};
use dynasmrt::x64::Assembler;
use std::collections::{HashMap, HashSet};
use std::cmp::Ordering;

// yaxpeax decoder example
mod decoder {
    use yaxpeax_arch::{Arch, AddressDisplay, Decoder, Reader, ReaderBuilder};

    pub fn decode_stream<
        'data,
        A: yaxpeax_arch::Arch,
        U: ReaderBuilder<A::Address, A::Word>,
    >(data: U) -> Vec<A::Instruction>
        where A::Instruction: std::fmt::Display
    {
        let mut reader = ReaderBuilder::read_from(data);
        let mut address: A::Address = reader.total_offset();

        let decoder = A::Decoder::default();
        let mut decode_res = decoder.decode(&mut reader);
        let mut res = Vec::new();
        loop {
            match decode_res {
                Ok(inst) => {
                    //println!("{}: {}", address.show(), inst);
                    decode_res = decoder.decode(&mut reader);
                    address = reader.total_offset();
                    res.push(inst);
                }
                Err(e) => {
                    //println!("{}: decode error: {}", address.show(), e);
                    break;
                }
            }
        }
        res
    }
}


#[derive(PartialEq, Debug, Copy, Clone)]
pub enum EdgeVariant {
    State,
    Data,
}

pub type NodeIdx = NodeIndex;
#[derive(Clone, Copy, PartialEq, Debug, Eq)]
pub enum Storage {
    Virtual(u16), // todo: width?
    Physical(RegSpec),
}

impl core::fmt::Display for Storage {
    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Storage::Virtual(v) => write!(fmt, "v{}", v),
            Storage::Physical(p) => write!(fmt, "{}", p),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct OptionalStorage(Option<Storage>);
impl core::fmt::Display for OptionalStorage {
    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self.0 {
            None => write!(fmt, "()"),
            Some(r) => write!(fmt, "{}", r),
        }
    }
}

impl Deref for OptionalStorage {
    type Target = Option<Storage>;
    fn deref(&self) -> &<Self as Deref>::Target {
        &self.0
    }
}


#[derive(Clone, Copy, Debug)]
pub struct Port {
    id: u32,
    variant: EdgeVariant,
    storage: OptionalStorage,
    time: Option<usize>,
    done: bool,
    // The node the port is attached to. If none, it isn't attached to any (e.g. a region
    // source/sink)
    node: Option<NodeIdx>,
}
impl Port {
    pub fn new() -> Self {
        let mut guard = PORT_COUNT.lock().unwrap();
        let curr = *guard;
        *guard += 1;
        println!("created port v{:?}", curr);
        Port { id: curr, variant: EdgeVariant::Data, storage: OptionalStorage(None), time: None, done: false, node: None }
    }

    pub fn set_storage(&mut self, store: Storage) {
        assert!(self.variant != EdgeVariant::State, "tried to set storage on a state port");
        self.storage = OptionalStorage(Some(store));
    }

    pub fn set_node(&mut self, n: NodeIdx) {
        self.node = Some(n);
    }
}

pub type PortIdx = NodeIndex;
use std::sync::Mutex;
lazy_static::lazy_static! {
    static ref PORT_COUNT: Mutex<u32> = Mutex::new(0);
}

#[derive(Clone, Debug)]
pub struct Edge {
    variant: EdgeVariant,
}
pub type PortEdge = EdgeIndex;

#[derive(Default)]
pub struct Region {
    nodes: StableGraph<Node, (), petgraph::Directed>,
    /// The list of all ports inside this region, such as those attached to nodes.
    ports: StableGraph<Port, Edge, petgraph::Directed>,
    /// The input ports to this region
    sources: Vec<PortIdx>,
    /// The output ports for this region
    sinks: Vec<PortIdx>,
    live: bool,
    idx: RegionIdx,
    order: Vec<usize>,
}

struct VirtualRegister {
    ports: Vec<PortIdx>, // these are reversed: the 0th element is the last port that uses it
    hints: HashSet<RegSpec>,
    backing: Option<RegSpec>,
    allocated: bool,
}

type VirtualRegisterMap = HashMap<usize, VirtualRegister>;

use lazy_static::lazy_static;
lazy_static! {
    static ref REGMAP: HashMap<RegSpec, RegSpec> = [
        (RegSpec::al(), RegSpec::rax()),
        (RegSpec::ah(), RegSpec::rax()),
        (RegSpec::ax(), RegSpec::rax()),
        (RegSpec::eax(), RegSpec::rax()),
        (RegSpec::rax(), RegSpec::rax()),

        (RegSpec::bl(), RegSpec::rbx()),
        (RegSpec::bh(), RegSpec::rbx()),
        (RegSpec::bx(), RegSpec::rbx()),
        (RegSpec::ebx(), RegSpec::rbx()),
        (RegSpec::rbx(), RegSpec::rbx()),

        (RegSpec::cl(), RegSpec::rcx()), // no cx() in real_mode
        (RegSpec::ch(), RegSpec::rcx()), // no cx() in real_mode
        (RegSpec::cx(), RegSpec::rcx()), // no cx() in real_mode
        (RegSpec::ecx(), RegSpec::rcx()),
        (RegSpec::rcx(), RegSpec::rcx()),

        (RegSpec::dl(), RegSpec::rdx()),
        (RegSpec::dh(), RegSpec::rdx()),
        (RegSpec::dx(), RegSpec::rdx()),
        (RegSpec::edx(), RegSpec::rdx()),
        (RegSpec::rdx(), RegSpec::rdx()),

        (RegSpec::sil(), RegSpec::rsi()), // esi is not public
        (RegSpec::esi(), RegSpec::rsi()), // esi is not public
        (RegSpec::rsi(), RegSpec::rsi()), // esi is not public

        (RegSpec::dil(), RegSpec::rdi()), // edi is not public
        (RegSpec::edi(), RegSpec::rdi()), // edi is not public
        (RegSpec::rdi(), RegSpec::rdi()), // edi is not public

        (RegSpec::bpl(), RegSpec::rbp()), // there's only a bp() helper in real_mode
        (RegSpec::bp(), RegSpec::rbp()), // there's only a bp() helper in real_mode
        (RegSpec::ebp(), RegSpec::rbp()), // no ebp() helper
        (RegSpec::rbp(), RegSpec::rbp()), // no ebp() helper
    ].iter().cloned().collect();
}

lazy_static! {
    // The prefered allocation order for registers
    static ref REGS: Vec<RegSpec> = vec![
        RegSpec::rax(),
        //RegSpec::rbx(),
        RegSpec::rcx(),
        RegSpec::rdx(),
        RegSpec::rsi(),
        RegSpec::rdi(),
        //RegSpec::rbp(), // there's only a bp() helper in real_mode
    ];
}



impl Region {
    pub fn new() -> Self {
        Self {
            live: false,
            ..Default::default()
        }
    }

    pub fn validate(&self) {
        for port in self.ports.node_weights() {
            assert!(port.storage.is_some(), "port v{} with unconstrained storage", port.id);
        }
    }

    pub fn add_node<T, F>(&mut self, mut n: T,
        f: F) -> NodeIdx where F: FnOnce(&mut Node, &mut Region) -> (), T: NodeBehavior + 'static {
        let mut n = Node::new(box n as Box<dyn NodeBehavior>);
        n.containing_region = Some(self.idx);
        n.create_ports(self);
        f(&mut n, self);
        let idx = self.nodes.add_node(n);
        // Now we can attach the ports to the actual node
        for port in self.nodes[idx].ports() {
            self.ports[port].node = Some(idx);
        }
        idx
    }

    pub fn add_port(&mut self) -> PortIdx {
        let p = Port::new();
        self.ports.add_node(p)
    }

    pub fn connect_ports(&mut self, input: PortIdx, output: PortIdx) -> PortEdge {
        let input_kind = self.ports[input].variant;
        let output_kind = self.ports[output].variant;
        assert_eq!(input_kind, output_kind);
        let e = Edge {
            variant: input_kind,
        };
        self.ports.add_edge(output, input, e)
    }

    pub fn add_source(&mut self) -> PortIdx {
        let p = self.add_port();
        self.sources.push(p);
        p
    }

    pub fn add_sink(&mut self) -> PortIdx {
        let p = self.add_port();
        self.sinks.push(p);
        p
    }

    pub fn constrain(&mut self, port: PortIdx, store: Storage) {
        println!("constraining port v{} to storage {}", self.ports[port].id, store);
        self.ports[port].set_storage(store)
    }

    pub fn create_virtual_registers(&mut self) -> VirtualRegisterMap {
        let mut reg = 0;
        let mut virts: VirtualRegisterMap = HashMap::new();
        let mut ports = self.ports.clone();
        // Give all ports that have no incoming edges and no storage a new virtual register
        self.ports.clone().externals(Direction::Incoming).filter(|e| ports[*e].storage.is_none() ).map(|e| {
            self.ports[e].set_storage(Storage::Virtual(reg));
            println!("gave {:?} virtual register {}", e, reg);
            virts.insert(reg.into(), VirtualRegister { ports: vec![], hints: HashSet::new(), backing: None, allocated: false });
            reg += 1;
        }).for_each(drop);

        // Give all ports that have a physical storage a virtual register constrained to the
        // physical
        ports.node_indices().clone().filter(|e| if let Some(Storage::Physical(_)) = *ports[*e].storage { true } else { false } ).map(|e| {
            let phys = if let Some(Storage::Physical(p)) = *self.ports[e].storage { p }
                else { panic!() };
            self.ports[e].set_storage(Storage::Virtual(reg));
            println!("made physical {:?} into virtual {}", e, reg);
            let mut set = HashSet::new();
            set.insert(phys);
            virts.insert(reg.into(), VirtualRegister { ports: vec![], hints: set, backing: Some(phys), allocated: false });
            reg += 1;
        }).for_each(drop);
        ports = self.ports.clone();

        // We have a set of all the ports and edges between them
        let mut ports_edges: Vec<_> = ports.edge_references().collect();
        // And we repeatedly propogate any edges we can. If we do propogate, we
        // can remove it from the working set for next iteration.
        // This is pretty slow, but who cares for now tbh.
        //
        // This should just be a queue that we add all source.incoming() to when
        // we process (backwards moving frontier)
        while ports_edges.len() > 0 {
            println!("propogating edges, {} left", ports_edges.len());
            println!("{:?}", ports_edges);
            ports_edges = ports_edges.drain(..).filter(|e| {
                let mut source = self.ports[e.target()];
                let mut sink = self.ports[e.source()];
                println!("v{} <- v{}", sink.id, source.id);
                println!("storages {} <- {}", sink.storage, source.storage);
                if let None = *sink.storage {
                    // We don't have a target storage to progate upwards, so
                    // have to try against next time
                    return true
                }
                match (*sink.storage.clone(), *source.storage.clone()) {
                    (Some(Storage::Virtual(sink_store)), Some(Storage::Virtual(source_store)))
                    if sink_store == source_store => {
                        // Do nothing, there are no conflicts
                    },
                    (Some(p0), Some(source_store)) if p0 != source_store => {
                        // we emit a move before any instruction that has conflicting
                        // registers: this could be either because there's a physical
                        // storage already allocated, or two virtual registers
                        // use the same previous register
                        self.ports.remove_edge(e.id());
                        let mut n = Node::r#move(p0, source_store);
                        println!("INSERT MOVE");
                        self.add_node(n, |n, r| {
                            n.connect_input(0, e.target(), r);
                            n.connect_output(0, e.source(), r);
                            // TODO: we need a way to say that these values *depend* on eachother
                            // but don't share storage
                            r.connect_ports(n.sources()[0], n.sinks()[0]);
                            r.ports[n.sources()[0]].set_storage(source_store);
                            r.ports[n.sinks()[0]].set_storage(p0);
                        });
                    },
                    (Some(Storage::Virtual(sink_store)), None) if virts[&sink_store.into()].backing.is_some() => {
                        // create a virtual register before the physical one, and give it a hint
                        virts.insert(reg.into(),
                            VirtualRegister { ports: vec![], hints: HashSet::from([virts[&sink_store.into()].backing.unwrap()]), backing: None, allocated: false}
                        );
                        self.ports[e.target()].set_storage(Storage::Virtual(reg));
                        reg += 1;
                        return false;
                    },
                    (Some(Storage::Virtual(sink_store)), _) => {
                        println!("just propogating");
                        // we can't just use source.set_storage because it's
                        // a clone.
                        self.ports[e.target()].set_storage(Storage::Virtual(sink_store));
                    },
                    (x, y) => {
                        unimplemented!("create_virtual_registers unhandled {:?} {:?}", x, y);
                    },
                };
                false
            }).collect();
        };
        // Make sure all ports have storages now
        for p in self.ports.node_indices() {
            assert!(self.ports[p].storage.is_some(), "port {:?} without storage", p);
            let vreg = if let Storage::Virtual(v) = self.ports[p].storage.unwrap() { v } else { panic!("port {:?} has physical storage", p) };
            // and add them to their virtual registers' port list
            virts.get_mut(&vreg.into()).unwrap().ports.push(p);
        }

        virts
    }

    pub fn annotate_port_times_and_hints(&mut self, virts: &mut VirtualRegisterMap) {
        use std::collections::BTreeSet;
        let mut nodes = { self.nodes.externals(Direction::Incoming).collect::<BTreeSet<_>>() };

        {
            // The initial set of nodes with no dependencies can already be marked done
            for n in &nodes {
                println!("root {:?}", self.nodes[*n]);
                self.nodes[*n].done = true;
            }
        }
        println!("all nodes {:#?}", self.nodes.node_weights().collect::<Vec<_>>());

        // Then give process the nodes, adding their dependents to the working set
        // and having their time be the max of their dependencies' time
        'process: while let Some(sink) = &nodes.pop_first() {
            let mut dependencies = self.nodes.neighbors_directed(*sink, Direction::Incoming).detach();
            let mut time = self.nodes[*sink].time;
            while let Some((e, dependency)) = dependencies.next(&self.nodes) {
                // We could have processed a node before we processed all of its dependencies
                let dependency = &self.nodes[dependency];
                if dependency.done == false {
                    // If so, we just remove it from the set and don't process it:
                    // it will be re-added to the set later once we *do* process its
                    // dependencies.
                    println!("node {:?} too soon", self.nodes[*sink]);
                    continue 'process;
                };
                time = core::cmp::max(time, dependency.time + 1); // TODO: latency
            }
            println!("node {:?} has time {:?}", self.nodes[*sink], time);
            self.nodes[*sink].time = time;
            self.nodes[*sink].done = true;

            let mut dependents = self.nodes.neighbors_directed(*sink, Direction::Outgoing).detach();
            while let Some((e, source)) = dependents.next(&self.nodes) {
                // Add all the dependants of the node to the working set
                nodes.insert(source);
            }
        }

        let mut last = 0;
        // validate all nodes were given times
        for n in self.nodes.node_weights().into_iter() {
            assert_eq!(n.done, true, "no time for {:?}", n);
            // and give its ports the correct timings
            use core::cmp::max;
            for p in n.sources() { self.ports[p].time = Some(n.time); last = max(last, n.time); }
            // TODO: latency
            for p in n.sinks() { self.ports[p].time = Some(n.time + 1); last = max(last, n.time); }
        }

        // and our functions entry/exit ports also need a time
        for p in &self.sources {
            self.ports[*p].time = Some(0);
        }
        for p in &self.sinks {
            self.ports[*p].time = Some(last+1);
        }

        // sort the uses for virtual registers by timings for later
        for (i, vreg) in virts {
            vreg.ports.sort_by(|a, b| self.ports[*a].time.unwrap().partial_cmp(&self.ports[*b].time.unwrap()).unwrap());
        }
    }


    pub fn allocate_physical_for_virtual(&mut self, virts: &mut VirtualRegisterMap) {
        // TODO: all of this should just be over virtual register and not ports

        // the nodes that we have to allocate
        let mut ports = self.ports.node_weights().collect::<Vec<_>>();
        println!("allocating ports {:?}", ports);
        let mut working = self.ports.externals(Direction::Outgoing).collect::<Vec<_>>();
        // We also want the first port for each virtual register that has to be
        // a specific physical register
        working.append(
            &mut virts.values()
            .filter(|v| v.backing.is_some()).
            map(|v| *v.ports.first().unwrap()).collect());
        let mut defered: Vec<(usize, PortIdx)> = vec![];
        use rangemap::RangeInclusiveMap;
        // The rangemap is (end..start, portidx). portidx is the first port that
        let mut live: HashMap<RegSpec, RangeInclusiveMap<usize, PortIdx>> = HashMap::new();
        let mut cache = petgraph::algo::DfsSpace::new(&self.nodes);
        'work: while
            let Some(p) = {
                println!("working {:?}", working);
                println!("live {:?}", live.clone());
                working = working.drain(..).filter(|p| {
                    let port = self.ports[*p];
                    if let Some(Storage::Virtual(v)) = *port.storage {
                        // !virts[&v.into()].allocated
                        !port.done
                    } else { true }
                }).collect();
                working.sort_by(|a, b| {
                    let a = self.ports[*a];
                    let b = self.ports[*b];
                    let (v_a, v_b) = if let (Some(Storage::Virtual(v_a)), Some(Storage::Virtual(v_b))) = (*a.storage, *b.storage) { (v_a, v_b) } else { panic!() };
                    // We want to allocate all the physical register ranges first
                    match (virts[&v_a.into()].backing, virts[&v_b.into()].backing) {
                        (None, None) => Ordering::Equal,
                        (Some(_), Some(_)) => Ordering::Equal,
                        (Some(_), None) => Ordering::Greater,
                        (None, Some(_)) => Ordering::Less,
                    }.then(a.time.partial_cmp(&b.time).unwrap()).reverse()
                });
                defered.sort_by_key(|n| n.0 );
                let mut r = None;
                if let Some(deferral) = defered.first() {
                    if working.first().is_none() || deferral.0 > self.ports[working[0]].time.unwrap() {
                        println!("using deferral");
                        let mut deferral = defered.pop().unwrap();
                        // TODO: make sure ports downstream of this also get scheduled after this?
                        self.ports[deferral.1].time = Some(deferral.0);
                        r = Some(deferral.1)
                    }
                }
                r.or_else(|| working.pop())
                } {
            let port = self.ports[p];
            if port.done {
                continue;
            }

            let storage = port.storage.unwrap();
            println!("port {} @ time {:?} has storage {}", port.id, port.time, storage);
            if let Storage::Virtual(vreg) = storage {
                if let Some(backed) = virts[&vreg.into()].backing {
                    let vreg_entry = &virts[&vreg.into()];
                    let range = self.ports[*vreg_entry.ports.first().unwrap()].time.unwrap()..=self.ports[*vreg_entry.ports.last().unwrap()].time.unwrap();
                    println!("trying to allocate physical register for range {:?}", range);
                    let reg_live = live.entry(*REGMAP.get(&backed).unwrap()).or_insert_with(|| {
                        println!("first allocation for {}", backed); RangeInclusiveMap::new()
                    });
                    let already = reg_live.get_key_value(&port.time.unwrap());
                    match already {
                        Some((r, start)) => {
                            // We somehow already have this physical register allocated
                            // at the given time - we have to defer it until after the
                            // use is done.
                            println!("test this");
                            defered.push((*r.end()+1, p));
                            continue 'work;
                        },
                        None | Some(_) => {
                            // block off the timeslice
                            // TODO: latency
                            reg_live.insert(range, p);
                            virts.get_mut(&vreg.into()).unwrap().allocated = true;
                            self.ports[p].done = true;
                        }
                    }
                } else {
                    let uses = &virts[&vreg.into()].ports;
                    let range = self.ports[*uses.first().unwrap()].time.unwrap()..=self.ports[*uses.last().unwrap()].time.unwrap();
                    println!("trying to allocate virtual register for range {:?}", range);
                    let mut ord = REGS.clone();
                    let hints = &virts[&vreg.into()].hints;
                    for hint in hints {
                        println!("hint {}", hint);
                    }
                    // Try to allocate it in one of the hints first
                    ord.sort_by(|a, b| {
                        hints.contains(a)
                            .partial_cmp(&hints.contains(b))
                        .unwrap().reverse()
                    });
                    for reg in ord {
                        println!("trying to allocate virtual reg in {}", reg);
                        let reg_live = live.entry(*REGMAP.get(&reg).unwrap())
                            .or_insert_with(|| {
                                println!("first allocation for {} from virtual", reg); RangeInclusiveMap::new()
                            });
                        self.ports[p].done = true;
                        if let Some(x) = reg_live.gaps(&range).next() {
                            // We can't use the range if the range isn't empty, or
                            // if the next step in the range isn't connected to our
                            // port
                            if x != range
                            {
                                println!("bogos binted {:?}", x);
                                continue;
                            }
                        } else {
                            println!("no gaps?");
                            continue;
                        }
                        println!("allocating virtual reg in {}", reg);
                        reg_live.insert(range.clone(), p);
                        virts.get_mut(&vreg.into()).unwrap().backing = Some(reg);
                        virts.get_mut(&vreg.into()).unwrap().allocated = true;
                        continue 'work;
                    }
                    panic!("allocate virtual here");
                }
            } else {
                panic!();
            }

            let mut neighbors = self.ports.neighbors_directed(p, Direction::Incoming).detach();
            while let Some((e, source)) = neighbors.next(&self.ports) {
                // if sink <- source where sink is virtual and we're physical, add a hint
                if let (Storage::Virtual(vreg), Storage::Physical(reg))
                    = (storage, self.ports[source].storage.unwrap()) {
                    print!("adding hint to {}", vreg);
                    virts.get_mut(&vreg.into()).unwrap().hints.insert(reg);
                }
                println!("adding {:?} to working set", source);
                working.push(source);
            }
        }
    }

    pub fn replace_virtual_with_backing(&mut self, virts: &mut VirtualRegisterMap) {
        for port in self.ports.node_weights_mut() {
            if let Some(Storage::Virtual(vreg)) = *port.storage {
                port.storage = OptionalStorage(Some(Storage::Physical(virts[&vreg.into()].backing.unwrap())));
            }
        }
    }

    // Set the node that each port is attached to
    pub fn attach_ports(&mut self) {
        for n in self.nodes.node_indices() {
            let node = &self.nodes[n];
            for p in node.ports() { self.ports[p].set_node(n) }
        }
    }

    // Using which port is attaached to which node, create edges between nodes
    // denoting dependencies
    pub fn create_dependencies(&mut self) {
        let indices: Vec<_> = self.ports.edge_references().collect();
        for e in indices {
            if let (Some(source), Some(sink)) = (self.ports[e.source()].node, self.ports[e.target()].node) {
                if source == sink { continue }
                self.nodes.add_edge(sink, source, ());
            }
        }
    }

    pub fn codegen(&mut self, ir: &mut IR, ops: &mut Assembler) {
        // TODO: emit all the constant values first?
        let mut nodes_graph = StableGraph::new();
        std::mem::swap(&mut self.nodes, &mut nodes_graph);
        let mut nodes: Vec<_> = nodes_graph.node_weights().collect();
        nodes.sort_by_key(|n| n.time );
        // lol this is wrong. we actually want to thread a State edge through
        // nodes, and just visit the State edge uses in order.
        for n in nodes {
            n.codegen(vec![], vec![], self, ir, ops);
        }
        std::mem::swap(&mut self.nodes, &mut nodes_graph);
    }
}

#[derive(Debug)]
pub enum Operation {
    Nop,
    Constant(JitTemp),
    Apply, // Call a Function node with arguments
    Inc,
    Add,
}

mod NodeVariant {
    use super::{Operation, Region};
    use std::marker::PhantomData;
    use super::*;
    #[derive(Debug)]
    pub struct Move(pub Storage, pub Storage); // A move operation, sink <- source.
    #[derive(Debug)]
    pub struct Simple(pub Operation); // Instructions or constant operands
    #[derive(Debug)]
    pub struct Function<const A: usize, const O: usize> {
        pub args: u8,
        pub outs: u8,
        pub region: RegionIdx,
    } // "Lambda-Nodes"; procedures and functions
    impl<const A: usize, const O: usize> Function<A, O> {
        pub fn new(ir: &mut IR) -> Function<A, O> {
            let r = ir.new_region();
            Self {
                region: r,
                args: 0,
                outs: 0
            }
        }

        pub fn add_body<T, F>(
            &mut self,
            mut n: T,
            ir: &mut IR,
            f: F) -> NodeIdx where F: FnOnce(&mut Node, &mut Region) -> (), T: NodeBehavior + 'static + core::fmt::Debug
        {
            ir.in_region(self.region, |mut r, ir| {
                r.add_node(n, f)
            })
        }

        pub fn add_argument(&mut self, ir: &mut IR) -> PortIdx {
            let arg_map = vec![
                RegSpec::rdi(),
                RegSpec::rsi(),
                RegSpec::rdx(),
            ];
            let port = ir.in_region(self.region, |mut r, ir| {
                let port = r.add_source();
                r.constrain(port, Storage::Physical(arg_map[self.args as usize].clone()));
                port
            });
            self.args += 1;
            port
        }

        pub fn add_return(&mut self, ir: &mut IR) -> PortIdx {
            let out_map = vec![
                RegSpec::rax(),
                RegSpec::rdx(),
            ];
            let port = ir.in_region(self.region, |mut r, ir| {
                let port = r.add_sink();
                r.constrain(port, Storage::Physical(out_map[self.outs as usize].clone()));
                port
            });
            self.outs += 1;
            port
        }
    }
    pub struct Global(pub Region); // "Delta-Nodes"; global variables
    pub struct Loop(pub Region); // "Theta-Nodes"; do-while loops. Only ever tail-controlled.
    pub struct Partition(pub Vec<Region>); // "Gamma-Nodes"; if-then-else statements and case-switch
    // The paper also has "Phi-Nodes" (mutually recursive functions) and
    // "Omega-Nodes" (translation units). We only ever JIT one function at a time.
}
// this is dumb, but rust's type inference chokes on the builder functions without
// an explicit NodeVariant type, so just give it this.
type S = NodeVariant::Simple;

pub trait NodeBehavior: core::fmt::Debug {
    fn set_time(&mut self, time: usize) {
       unimplemented!();
    }
    fn get_time(&self) -> usize {
        unimplemented!();
    }

    fn create_ports(&mut self, r: &mut Region) {
    }

    fn ports_callback(&mut self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region) {
    }

    fn codegen(&self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        unimplemented!();
    }


    fn tag(&self) -> String {
        "<unknown>".to_string()
    }

    fn input_count(&self) -> usize {
        unimplemented!();
    }
    fn output_count(&self) -> usize {
        unimplemented!();
    }
}

impl Node {
    fn set_time(&mut self, time: usize) {
        self.time = time;
    }
    fn get_time(&self) -> usize {
        self.time
    }

    fn sinks(&self) -> Vec<PortIdx> {
        self.outputs.clone()
    }

    fn sources(&self) -> Vec<PortIdx> {
        self.inputs.clone()
    }

    fn ports(&self) -> Vec<PortIdx> {
        let mut p = self.sources();
        p.append(&mut self.sinks());
        p
    }

    fn add_input(&mut self, p: PortIdx, r: &mut Region) {
        self.inputs.push(p)
    }

    fn add_output(&mut self, r: &mut Region) -> PortIdx {
        let p_x = r.add_port();
        self.outputs.push(p_x);
        p_x
    }

    fn connect_input(&mut self, idx: usize, input: PortIdx, r: &mut Region) -> PortEdge {
        let p = self.inputs[idx];
        r.connect_ports(input, p)
    }

    fn connect_output(&mut self, idx: usize, output: PortIdx, r: &mut Region) -> PortEdge {
        let p = self.outputs[idx];
        r.connect_ports(p, output)
    }

    fn connect_operands(&mut self, input: usize, output: usize, r: &mut Region) -> PortEdge {
        let input = self.inputs[input];
        let output = self.outputs[output];
        r.connect_ports(input, output)
    }

    fn create_ports(&mut self, r: &mut Region) {
        println!("create_ports called");
        self.variant.create_ports(r);
        let mut inputs = vec![];
        let mut outputs = vec![];
        for i in 0..self.input_count() {
            let p = r.add_port();
            self.add_input(p, r);
            inputs.push(p);
        }
        for i in 0..self.output_count() {
            outputs.push(self.add_output(r));
        }
        self.variant.ports_callback(inputs, outputs, r);
    }

   fn input_count(&self) -> usize {
        self.variant.input_count()
    }

    fn output_count(&self) -> usize {
        self.variant.output_count()
    }

    fn codegen(&self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        println!("node codegen for {:?}", self.variant);
        self.variant.codegen(self.inputs.clone(), self.outputs.clone(), r, ir, ops)
    }
}

impl NodeBehavior for NodeVariant::Simple {
    fn input_count(&self) -> usize {
        match &self.0 {
            Operation::Inc => 1,
            Operation::Add => 2,
            _ => unimplemented!(),
        }
    }

    fn output_count(&self) -> usize {
        match &self.0 {
            Operation::Inc => 1,
            Operation::Add => 1,
            _ => unimplemented!(),
        }
    }


    fn codegen(&self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        match &self.0 {
            Operation::Inc => {
                let operand = &r.ports[inputs[0]];
                match operand.storage.as_ref().unwrap() {
                    Storage::Physical(r) => match r.class() {
                        register_class::Q => dynasm!(ops
                            ; inc Rq(r.num())
                        ),
                        register_class::D => dynasm!(ops
                            ; inc Rd(r.num())
                        ),
                        x => unimplemented!("unknown class {:?} for inc", x),
                    },
                    _ => unimplemented!(),
                }
            },
            Operation::Add => {
                let operand_0 = &r.ports[inputs[0]];
                let operand_1 = &r.ports[inputs[1]];
                match (operand_0.storage.as_ref().unwrap(), operand_1.storage.as_ref().unwrap()) {
                    (Storage::Physical(r0), Storage::Physical(r1)) => match (r0.class(), r1.class()) {
                        (register_class::Q, register_class::Q) => dynasm!(ops
                            ; add Rq(r0.num()), Rq(r1.num())
                        ),
                        (register_class::D, register_class::D) => dynasm!(ops
                            ; add Rd(r0.num()), Rd(r1.num())
                        ),
                        x => unimplemented!("unknown class {:?} for add", x),
                    },
                    _ => unimplemented!(),
                }
            }
            x => unimplemented!("unimplemented codegen for {:?}", x),
        }
    }

    fn ports_callback(&mut self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region) {
        println!("{:?} <- {:?} ", outputs, inputs);
        match &self.0 {
            Operation::Inc =>
                r.connect_ports(inputs[0], outputs[0]),
            Operation::Add =>
                r.connect_ports(inputs[0], outputs[0]),
            _ => unimplemented!("ports_callback for {:?}", self.tag()),
        };
    }

    fn tag(&self) -> String {
        match &self.0 {
            Operation::Inc => "inc".to_string(),
            Operation::Add => "add".to_string(),
            _ => unimplemented!(),
        }
    }
}

impl NodeBehavior for NodeVariant::Move {
    fn input_count(&self) -> usize {
        1
    }

    fn output_count(&self) -> usize {
        1
    }

    fn ports_callback(&mut self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region) {
        println!("{:?} <- {:?} ", outputs, inputs);
        r.constrain(outputs[0], self.0.clone());
        r.constrain(inputs[0], self.1.clone());
    }

    fn codegen(&self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        let source = &r.ports[inputs[0]];
        let sink = &r.ports[outputs[0]];
        match (sink.storage.as_ref().unwrap(), source.storage.as_ref().unwrap()) {
            (Storage::Physical(r0), Storage::Physical(r1)) => {
                match (r0.class(), r1.class()) {
                    (register_class::Q, register_class::Q) =>
                        dynasm!(ops
                            ; mov Rq(r0.num()), Rq(r1.num())
                        ),
                    (x, y) => unimplemented!("{:?} <- {:?} unimplemented", x, y),
                }
            },
            _ => unimplemented!(),
        }
    }

}


impl<const A: usize, const O: usize> NodeBehavior for NodeVariant::Function<A, O> {
    fn input_count(&self) -> usize {
        0
    }

    fn output_count(&self) -> usize {
        // The output of a function node is always the function itself
        // todo lol
        1
    }

    fn codegen(&self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        // if we're calling codegen on a function, it should be the only one.
        ir.in_region(self.region, |r, ir| { r.codegen(ir, ops); });
        dynasm!(ops
            ; ret
        );
    }
}

#[derive(Debug)]
pub struct Node {
    variant: Box<dyn NodeBehavior>,
    inputs: Vec<PortIdx>,
    outputs: Vec<PortIdx>,
    label: Option<String>,
    containing_region: Option<RegionIdx>,
    time: usize,
    done: bool,
}

use core::ops::Deref;
impl Deref for Node {
    type Target = Box<dyn NodeBehavior>;
    fn deref(&self) -> &<Self as Deref>::Target {
        &self.variant
    }
}
use core::ops::DerefMut;
impl DerefMut for Node {
    fn deref_mut(&mut self) -> &mut <Self as Deref>::Target {
        &mut self.variant
    }
}

impl Node {
    pub fn new(var: Box<dyn NodeBehavior>) -> Node {
        Node {
            variant: var,
            inputs: vec![],
            outputs: vec![],
            label: None,
            containing_region: None,
            time: 1,
            done: false,
        }
    }
    pub fn simple(op: Operation) -> NodeVariant::Simple {
        NodeVariant::Simple(op)
    }

    pub fn r#move(sink: Storage, source: Storage) -> NodeVariant::Move {
        NodeVariant::Move(sink, source)
    }

    pub fn function<const A: usize, const O: usize>(ir: &mut IR) -> NodeVariant::Function<A, O> {
        NodeVariant::Function::new(ir)
    }
}

type RegionEdge = ();
type RegionIdx = NodeIndex;

#[derive(Default)]
pub struct IR {
    body: Option<NodeIdx>,
    /// A directed acyclic graph of regions; if there is an edge r_1 -> r_2, then
    /// r_2 is within r_1.
    regions: StableGraph<Region, RegionEdge, petgraph::Directed>,
    /// The outer-most region that all other regions are under.
    master_region: RegionIdx,
}

impl IR {
    pub fn new() -> Self {
        let mut r = Region::new();
        r.live = true;
        let mut r_map = StableGraph::new();
        let r_x = r_map.add_node(r);
        Self {
            body: None,
            regions: r_map,
            master_region: r_x,
        }
    }

    /// Create a region in this IR instance at the top-most level.
    pub fn new_region(&mut self) -> RegionIdx {
        let mut r = Region::new();
        r.live = true;
        let r_x = self.regions.add_node(r);
        { self.regions.node_weight_mut(r_x).unwrap().idx = r_x; }
        self.regions.add_edge(self.master_region, r_x, ());
        r_x
    }

    pub fn add_function<const A: usize, const O: usize>(&mut self, f: NodeVariant::Function<A, O>) {
        self.in_region(self.master_region, |r, ir| {
            r.add_node(f, |n, r| {
            });
        });
    }

    pub fn set_body<const A: usize, const O: usize>(&mut self, f: NodeVariant::Function<A, O>) {
        println!("setting IR body");
        let body = self.in_region(self.master_region, |r, ir| {
            NodeIndex::new(r.nodes.node_count())
        });
        assert_eq!(f.args as usize, A);
        assert_eq!(f.outs as usize, O);
        self.add_function(f);
        self.body = Some(body); // once told me
    }

    pub fn in_region<F, O>(&mut self, r: RegionIdx, f: F) -> O
        where F: FnOnce(&mut Region, &mut Self) -> O {
        let mut dummy = Region::new();
        std::mem::swap(&mut dummy, &mut self.regions[r]);
        assert_eq!(dummy.live, true, "dead region? {:?}", r);
        //assert!(dummy.idx.is_some(), "region {:?} not connected to graph", r);
        let o = f(&mut dummy, self);
        std::mem::swap(&mut dummy, &mut self.regions[r]);
        o
    }

    pub fn optimize(&mut self) -> &mut Self {
        self
    }

    pub fn regalloc(&mut self) {
        for r in self.regions.node_weights_mut() {
            if r.idx == self.master_region {
                continue;
            }
            r.attach_ports();
            // Create virtual register storages for all nodes and ports
            let mut virt_map = r.create_virtual_registers();
            println!("created virtual registers");
            r.create_dependencies();
            r.annotate_port_times_and_hints(&mut virt_map);
            println!("annoated port times and hints");
            r.allocate_physical_for_virtual(&mut virt_map);
            println!("allocated physical registers for virtual register");
            r.replace_virtual_with_backing(&mut virt_map);
            println!("replacing virtual registers with physical registers");
            // Create a dependency graph for registers
            //let dg = r.create_register_dependencies();
        }
    }

    pub fn validate(&mut self) {
        // This is currently worse than useless
        //for r in self.regions.node_weights_mut() {
        //    if r.idx == self.master_region {
        //        continue;
        //    }
        //    r.validate();
        //}
    }

    pub fn codegen(&mut self) -> (Assembler, AssemblyOffset, usize) {
        let mut ops = Assembler::new().unwrap();
        let start = ops.offset();
        let mut ret = None;
        self.in_region(self.master_region, |r, ir| {
            let mut n = StableGraph::new();
            std::mem::swap(&mut r.nodes, &mut n);
            ret = Some(n[ir.body.unwrap()].codegen(vec![], vec![], r, ir, &mut ops));
            std::mem::swap(&mut r.nodes, &mut n);
        });
        let end = ops.offset();
        (ops, start, end.0 - start.0)
    }

    pub fn compile_fn<A, O>(&mut self) -> Result<extern "C" fn(A) -> O, Box<dyn std::error::Error>> {
        self.regalloc();
        self.validate();
        let (mut ops, off, size) = self.codegen();
        let buf = ops.finalize().unwrap();
        let hello_fn: extern "C" fn(A) -> O = unsafe { std::mem::transmute(buf.ptr(off)) };
        let all = crate::ir::decoder::decode_stream::<yaxpeax_x86::x86_64, _>(unsafe {
            core::slice::from_raw_parts(
                buf.ptr(off) as *const u8,
                size as usize) as &[u8]
        });
        println!("disassembly: \n");
        let mut fmt = String::new();
        for inst in all {
            inst.write_to(&mut fmt)?;
            fmt.push('\n');
        }
        println!("{}", fmt);
        std::mem::forget(buf);
        Ok(hello_fn)
    }

    pub fn print(&self) {
        // XXX: we want to dump a graphviz view or something else pretty here;
        // debugging a graph based IR without that sounds like hell.
    }
}

#[cfg(test)]
mod test {
    use super::{Node, IR, NodeBehavior, NodeVariant, Operation};

    type S = NodeVariant::Simple;
    #[test]
    pub fn simple_function() {
        let mut ir = IR::new();
        let mut f = Node::function::<0, 0>(&mut ir);
    }

    #[test]
    pub fn function_inc() {
        let mut ir = IR::new();
        let mut f = Node::function::<1, 1>(&mut ir);
        let port = f.add_argument(&mut ir);
        let ret_port = f.add_return(&mut ir);
        let mut inc = Node::simple(Operation::Inc);
        f.add_body(inc, &mut ir, |inc, ir| {
            inc.connect_input(0, port, ir);
            inc.connect_output(0, ret_port, ir);
        });
        ir.set_body(f);
    }

    #[test]
    pub fn function_inc_regalloc() {
        let mut ir = IR::new();
        let mut f = Node::function::<1, 1>(&mut ir);
        let port = f.add_argument(&mut ir);
        let ret_port = f.add_return(&mut ir);
        let mut inc = Node::simple(Operation::Inc);
        f.add_body(inc, &mut ir, |inc, r| {
            inc.connect_input(0, port, r);
            inc.connect_output(0, ret_port, r);
        });
        ir.set_body(f);
        ir.regalloc();
        ir.validate();
    }

    #[test]
    pub fn function_inc_codegen() {
        let mut ir = IR::new();
        let mut f = Node::function::<1, 1>(&mut ir);
        let port = f.add_argument(&mut ir);
        let ret_port = f.add_return(&mut ir);
        let mut inc = Node::simple(Operation::Inc);
        f.add_body(inc, &mut ir, |inc, r| {
            inc.connect_input(0, port, r);
            inc.connect_output(0, ret_port, r);
        });
        ir.set_body(f);
        let hello_fn: extern "C" fn(usize) -> usize = ir.compile_fn().unwrap();
        assert_eq!(hello_fn(1), 2);
    }

    #[test]
    pub fn function_add_codegen() {
        let mut ir = IR::new();
        let mut f = Node::function::<2, 1>(&mut ir);
        let port_0 = f.add_argument(&mut ir);
        let port_1 = f.add_argument(&mut ir);
        let ret_port = f.add_return(&mut ir);
        let mut add = Node::simple(Operation::Add);
        f.add_body(add, &mut ir, |add, r| {
            add.connect_input(0, port_0, r);
            add.connect_input(1, port_1, r);
            add.connect_output(0, ret_port, r);
        });
        ir.set_body(f);
        let hello_fn: extern "C" fn((usize, usize)) -> usize = ir.compile_fn().unwrap();
        assert_eq!(hello_fn((1, 2)), 3);
    }

    #[test]
    pub fn function_inc_disjoint() {
        let mut ir = IR::new();
        let mut f = Node::function::<2, 2>(&mut ir);
        let port_0 = f.add_argument(&mut ir);
        let port_1 = f.add_argument(&mut ir);
        let ret_port_0 = f.add_return(&mut ir);
        let ret_port_1 = f.add_return(&mut ir);
        let mut inc_0 = Node::simple(Operation::Inc);
        let mut inc_1 = Node::simple(Operation::Inc);
        f.add_body(inc_0, &mut ir, |inc, r| {
            inc.connect_input(0, port_0, r);
            inc.connect_output(0, ret_port_0, r);
        });
        f.add_body(inc_1, &mut ir, |inc, r| {
            inc.connect_input(0, port_1, r);
            inc.connect_output(0, ret_port_1, r);
        });

        ir.set_body(f);
        let hello_fn: extern "C" fn((usize, usize)) -> (usize, usize) = ir.compile_fn().unwrap();
        assert_eq!(hello_fn((1, 2)), (2, 3));
    }

    #[test]
    pub fn function_inc_then_add() {
        let mut ir = IR::new();
        let mut f = Node::function::<2, 1>(&mut ir);
        let port_0 = f.add_argument(&mut ir);
        let port_1 = f.add_argument(&mut ir);
        let ret_port = f.add_return(&mut ir);
        let mut inc_0 = Node::simple(Operation::Inc);
        let mut inc_1 = Node::simple(Operation::Inc);
        let mut add = Node::simple(Operation::Add);
        let inc_0_i = f.add_body(inc_0, &mut ir, |inc_0, r| {
            inc_0.connect_input(0, port_0, r);
        });
        let inc_1_i = f.add_body(inc_1, &mut ir, |inc_1, r| {
            inc_1.connect_input(0, port_1, r);
        });
        f.add_body(add, &mut ir, |add, r| {
            add.connect_input(0, r.nodes[inc_0_i].sinks()[0], r);
            add.connect_input(1, r.nodes[inc_1_i].sinks()[0], r);
            add.connect_output(0, ret_port, r);
        });
        ir.set_body(f);

        extern "C" fn foo(a: usize, b: usize) -> usize {
            (a + 1) + (b + 1)
        }
        assert_eq!(foo(1, 2), 5);
        let hello_fn: extern "C" fn((usize, usize)) -> usize = ir.compile_fn().unwrap();
        assert_eq!(hello_fn((1, 2)), 5);
    }

    #[test]
    pub fn function_inc_shared() {
        let mut ir = IR::new();
        let mut f = Node::function::<2, 2>(&mut ir);
        let port_0 = f.add_argument(&mut ir);
        let port_1 = f.add_argument(&mut ir);
        let ret_port_0 = f.add_return(&mut ir);
        let ret_port_1 = f.add_return(&mut ir);
        let mut inc_0 = Node::simple(Operation::Inc);
        let mut inc_1 = Node::simple(Operation::Inc);
        f.add_body(inc_0, &mut ir, |inc, r| {
            inc.connect_input(0, port_0, r);
            inc.connect_output(0, ret_port_0, r);
        });
        f.add_body(inc_1, &mut ir, |inc, r| {
            inc.connect_input(0, port_1, r);
            inc.connect_output(0, ret_port_1, r);
        });

        ir.set_body(f);
        let hello_fn: extern "C" fn((usize, usize)) -> (usize, usize) = ir.compile_fn().unwrap();
        assert_eq!(hello_fn((1, 2)), (2, 3));
    }

}
