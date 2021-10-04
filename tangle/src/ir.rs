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
use petgraph::stable_graph::StableGraph;
use petgraph::graph::{NodeIndex};
use petgraph::Direction;
use petgraph::visit::{EdgeRef, Dfs, Reversed, depth_first_search, DfsEvent, ControlFlow};
use yaxpeax_x86::long_mode::{Operand, RegSpec};

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum EdgeVariant {
    State,
    Data,
}

pub type NodeId = u64;
#[derive(Clone, PartialEq, Debug)]
pub enum Storage {
    Virtual(u16), // todo: width?
    Physical(RegSpec),
}

#[derive(Clone, Debug)]
pub struct Port {
    id: u32,
    variant: EdgeVariant,
    storage: Option<Storage>,
}
impl Port {
    pub fn new() -> Self {
        let mut guard = PORT_COUNT.lock().unwrap();
        let curr = *guard;
        *guard += 1;
        println!("created port v{:?}", curr);
        Port { id: curr, variant: EdgeVariant::Data, storage: None }
    }

    pub fn set_storage(&mut self, store: Storage) {
        assert!(self.variant != EdgeVariant::State, "tried to set storage on a state port");
        self.storage = Some(store);
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

#[derive(Default)]
pub struct Region {
    nodes: Vec<Box<dyn NodeBehavior>>,
    /// The list of all ports inside this region, such as those attached to nodes.
    ports: StableGraph<Port, Edge, petgraph::Directed>,
    /// The input ports to this region
    sources: Vec<PortIdx>,
    /// The output ports for this region
    sinks: Vec<PortIdx>,
    live: bool,
    idx: RegionIdx,
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
            assert!(port.storage.is_some(), "port v{:?} with unconstrained storage", port.id);
        }
    }

    pub fn add_node<T: 'static + NodeBehavior, F>(&mut self, mut n: Node<T>,
        f: F) where F: FnOnce(&mut Node<T>, &mut Region) -> () {
        n.containing_region = Some(self.idx);
        n.create_ports(self);
        f(&mut n, self);
        self.nodes.push(box n)
    }

    pub fn add_port(&mut self) -> PortIdx {
        let p = Port::new();
        self.ports.add_node(p)
    }

    pub fn connect_ports(&mut self, input: PortIdx, output: PortIdx) {
        let input_kind = self.ports[input].variant;
        let output_kind = self.ports[output].variant;
        assert_eq!(input_kind, output_kind);
        let e = Edge {
            variant: input_kind,
        };
        self.ports.add_edge(output, input, e);
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
        println!("constraining port v{:?} to storage {:?}", self.ports[port].id, store);
        self.ports[port].set_storage(store)
    }

    pub fn regalloc(&mut self) {
        // Starting at the sinks to the region, we do a DFS visit for all of the
        // ports connected to each sink.
        let mut nodes = self.sinks.clone();

        struct RegMeta {
            // todo: what information should we keep around? minimum width (maybe with a bitmap?)
            width: u8,
            // it was a virtual register, but one of the uses is constrained to
            hint: Storage,
        }
        //let mut regmap = HashMap::<Storage, RegMeta>::new();
        let mut virt_num = 0;

        while let Some(n) = nodes.pop() {
            println!("got root {:?}", n);
            depth_first_search(&self.ports.clone(), Some(n), |event| {
                match event {
                    DfsEvent::TreeEdge(u, v) => {
                        let mut sink = self.ports[u].clone();
                        let mut source = self.ports[v].clone();
                        println!("v{:?} <- v{:?}", sink.id, source.id);
                        println!("storages {:?} <- {:?}", sink.storage, source.storage);
                        let sink_store = sink.storage.clone().unwrap();
                        if let Some(source_store) = &source.storage {
                            match (sink_store.clone(), source_store.clone()) {
                                (sink_store, source_store) if sink_store == source_store => {
                                },
                                (Storage::Physical(p0), Storage::Physical(p1)) => {
                                    // we have two regions each with their own
                                    // physical register constraint. we by
                                    // definition need to emit a move.
                                    // TODO: this can probably do some sort
                                    // of deduplication, if e.g. there are
                                    // two sources of the value with the same
                                    // register constraint to avoid emitting
                                    // a move for each.
                                    let con = self.ports.find_edge(u, v).unwrap();
                                    self.ports.remove_edge(con);
                                    let mut n = Node::<S>::r#move(sink_store.clone(), source_store.clone());
                                    self.add_node(n, |n, r| {
                                        n.connect_input(0, v, r);
                                        n.connect_output(0, u, r);
                                        // and then add the source to the visitation set
                                        nodes.push(v);
                                    });
                                },
                                (x, y) => unimplemented!("couldn't fill {:?} <- {:?}", x, y),
                            }
                        } else {
                            println!("just propogating");
                            // we can't just use source.set_storage because it's
                            // a clone.
                            self.ports[v].set_storage(sink_store);
                        }
                        ControlFlow::continuing()
                    },
                    DfsEvent::Discover(n, t) => {
                        ControlFlow::continuing()
                    },
                    DfsEvent::Finish(n, t) => {
                        ControlFlow::continuing()
                    },
                    x => unimplemented!("{:?}", x),
                }
            });
        }
    }
}

pub enum Operation {
    Nop,
    Constant(JitTemp),
    Apply, // Call a Function node with arguments
    Inc,
}

mod NodeVariant {
    use super::{Operation, Region};
    use std::marker::PhantomData;
    use super::*;
    pub struct Move(pub Storage, pub Storage); // A move operation, sink <- source.
    pub struct Simple(pub Operation); // Instructions or constant operands
    pub struct Function<const A: usize, const O: usize> {
        args: u8,
        outs: u8,
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

        pub fn add_body<T: 'static + NodeBehavior, F>(
            &mut self,
            mut n: Node<T>,
            ir: &mut IR,
            f: F) where F: FnOnce(&mut Node<T>, &mut Region) -> ()
        {
            ir.in_region(self.region, |mut r, ir| {
                r.add_node(n, f)
            });
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

pub trait NodeBehavior {
    fn add_input(&mut self, p: PortIdx, r: &mut Region) {
        unimplemented!();
    }

    fn add_output(&mut self, r: &mut Region) -> PortIdx {
        unimplemented!();
    }

    fn create_ports(&mut self, r: &mut Region) {
    }

    fn ports_callback(&mut self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region) {
    }

    fn input_count(&self) -> usize {
        unimplemented!();
    }

    fn output_count(&self) -> usize {
        unimplemented!();
    }

    fn connect_input(&mut self, idx: usize, input: PortIdx, r: &mut Region) {
        unimplemented!();
    }

    fn connect_output(&mut self, idx: usize, output: PortIdx, r: &mut Region) {
        unimplemented!();
    }

    fn connect_operands(&mut self, input: usize, output: usize, r: &mut Region) {
        unimplemented!();
    }
}

impl<T: NodeBehavior> NodeBehavior for Node<T> {
    fn add_input(&mut self, p: PortIdx, r: &mut Region) {
        self.inputs.push(p)
    }

    fn add_output(&mut self, r: &mut Region) -> PortIdx {
        let p_x = r.add_port();
        self.outputs.push(p_x);
        p_x
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

    fn connect_input(&mut self, idx: usize, input: PortIdx, r: &mut Region) {
        let p = self.inputs[idx];
        r.connect_ports(input, p);
    }

    fn connect_output(&mut self, idx: usize, output: PortIdx, r: &mut Region) {
        let p = self.outputs[idx];
        r.connect_ports(p, output);
    }

    fn connect_operands(&mut self, input: usize, output: usize, r: &mut Region) {
        let input = self.inputs[input];
        let output = self.outputs[output];
        r.connect_ports(input, output);
    }
}

impl NodeBehavior for NodeVariant::Simple {
    fn input_count(&self) -> usize {
        match &self.0 {
            Operation::Inc => 1,
            _ => unimplemented!(),
        }
    }

    fn output_count(&self) -> usize {
        match &self.0 {
            Operation::Inc => 1,
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
}


impl<const A: usize, const O: usize> NodeBehavior for NodeVariant::Function<A, O> {
    fn input_count(&self) -> usize {
        0
    }

    fn output_count(&self) -> usize {
        // The output of a function node is always the function itself
        // todo lol
        0
    }

}


#[derive(Default)]
pub struct Node<T> {
    variant: T,
    inputs: Vec<PortIdx>,
    outputs: Vec<PortIdx>,
    edges: Vec<Edge>,
    label: Option<String>,
    containing_region: Option<RegionIdx>,
}

use core::ops::Deref;
impl<T> Deref for Node<T> {
    type Target = T;
    fn deref(&self) -> &<Self as Deref>::Target {
        &self.variant
    }
}
use core::ops::DerefMut;
impl<T> DerefMut for Node<T> {
    fn deref_mut(&mut self) -> &mut <Self as Deref>::Target {
        &mut self.variant
    }
}

impl<T> Node<T> {
    pub fn new(var: T) -> Node<T> {
        Node {
            variant: var,
            inputs: vec![],
            outputs: vec![],
            edges: vec![],
            label: None,
            containing_region: None,
        }
    }
    pub fn simple(op: Operation) -> Node<NodeVariant::Simple> {
        Node::new(NodeVariant::Simple(op))
    }

    pub fn r#move(sink: Storage, source: Storage) -> Node<NodeVariant::Move> {
        Node::new(NodeVariant::Move(sink, source))
    }

    pub fn function<const A: usize, const O: usize>(ir: &mut IR) -> Node<NodeVariant::Function<A, O>> {
        Node::new(NodeVariant::Function::new(ir))
    }
}

type RegionEdge = ();
type RegionIdx = NodeIndex;

#[derive(Default)]
pub struct IR {
    nodes: Vec<Box<dyn NodeBehavior>>,
    body: Option<usize>,
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
            nodes: vec![],
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

    pub fn add_function<const A: usize, const O: usize>(&mut self, f: Node<NodeVariant::Function<A, O>>) {
        self.in_region(self.master_region, |r, ir| {
            r.add_node(f, |_, _| {});
        });
    }

    pub fn set_body<const A: usize, const O: usize>(&mut self, f: Node<NodeVariant::Function<A, O>>) {
        println!("setting IR body");
        let body = self.in_region(self.master_region, |r, ir| {
            r.nodes.len()
        });
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
            r.regalloc();
        }
    }

    pub fn validate(&mut self) {
        for r in self.regions.node_weights_mut() {
            if r.idx == self.master_region {
                continue;
            }
            r.validate();
        }
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
        let mut f = Node::<S>::function::<0, 0>(&mut ir);
    }

    #[test]
    pub fn function_inc() {
        let mut ir = IR::new();
        let mut f = Node::<S>::function::<1, 1>(&mut ir);
        let port = f.add_argument(&mut ir);
        let ret_port = f.add_return(&mut ir);
        let mut inc = Node::<S>::simple(Operation::Inc);
        f.add_body(inc, &mut ir, |inc, ir| {
            inc.connect_input(0, port, ir);
            inc.connect_output(0, ret_port, ir);
        });
        ir.set_body(f);
    }

    #[test]
    pub fn function_inc_regalloc() {
        let mut ir = IR::new();
        let mut f = Node::<S>::function::<1, 1>(&mut ir);
        println!("create f");
        let port = f.add_argument(&mut ir);
        println!("create arg");
        let ret_port = f.add_return(&mut ir);
        println!("create ret");
        let mut inc = Node::<S>::simple(Operation::Inc);
        f.add_body(inc, &mut ir, |inc, r| {
            inc.connect_input(0, port, r);
            inc.connect_output(0, ret_port, r);
            inc.connect_operands(0, 0, r);
        });
        println!("create inc");
        ir.set_body(f);
        ir.regalloc();
        ir.validate();
    }
}
