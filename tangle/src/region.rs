use dynasmrt::x64::Assembler;
use petgraph::graph::{NodeIndex};
use petgraph::stable_graph::StableGraph;
use petgraph::visit::{EdgeRef, Dfs, Reversed, depth_first_search, DfsEvent, ControlFlow, IntoEdgeReferences};
use petgraph::Direction;
use yaxpeax_x86::long_mode::RegSpec;
use yaxpeax_x86::long_mode::register_class;

use crate::node::{Node, NodeIdx, NodeBehavior, NodeVariant, Operation};
use crate::port::{Port, PortMeta, PortIdx, PortEdge, Edge, Storage, OptionalStorage};
use crate::ir::{IR, VirtualRegister, VirtualRegisterMap};
use crate::time::Timestamp;

use core::cmp::max;
use std::collections::{HashMap, HashSet};

pub type RegionEdge = ();
pub type RegionIdx = NodeIndex;

#[derive(Default)]
pub struct Region {
    pub nodes: StableGraph<Node, (), petgraph::Directed>,
    /// The list of all ports inside this region, such as those attached to nodes.
    pub ports: StableGraph<Port, Edge, petgraph::Directed>,
    /// The input ports to this region
    pub sources: Vec<PortIdx>,
    /// The output ports for this region
    pub sinks: Vec<PortIdx>,
    pub live: bool,
    pub idx: RegionIdx,
    pub order: Vec<usize>,
}

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
        RegSpec::rdi(),
        RegSpec::rsi(),
        RegSpec::rdx(),
        RegSpec::rcx(),
        RegSpec::r8(),
        RegSpec::r9(),
        RegSpec::r10(),
        RegSpec::r11(),
        //RegSpec::rbx(),
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

    /// If instructions that use constants can fix the constant in an operand,
    /// convert them to that instead of using a virtual register
    pub fn move_constants_to_operands(&mut self) {
        let mut consts = self.nodes.node_weights_mut().map(|mut n| {
            let sinks = n.sinks();
            let mut s = n.as_variant_mut::<NodeVariant::Simple>();
            s.as_mut().map(|mut s| { if let Operation::Constant(c) = s.0 {
                println!("constant {}", c);
                let mut uses = self.ports.neighbors_directed(sinks[0], Direction::Incoming).detach();
                let has_uses = false;
                while let Some((an_edge, a_use)) = uses.next(&self.ports) {
                    //let node_use = &self.nodes[self.ports[a_use].node.unwrap()];
                    // TODO: sanity check that the instruction supports an operand
                    // of the given width, set has_uses = true if so
                    //println!("used {:?}", node_use);
                    let port_use = &mut self.ports[a_use];
                    // we can set the port to be immaterial instead
                    port_use.set_storage(Storage::Immaterial);
                    // and that it is a constant value
                    port_use.set_meta(PortMeta::Constant(c));
                    // and that it doesn't depend on the constant node anymore
                    self.ports.remove_edge(an_edge);
                }

                if !has_uses {
                    s.0 = Operation::Nop;
                }
            }})
        }).for_each(drop);
    }

    pub fn remove_nops(&mut self) {
        let mut removed = HashSet::new();
        self.nodes.retain_nodes(|node, idx| {
            let mut s = node[idx].as_variant::<NodeVariant::Simple>();
            s.map_or_else(|| true, |s| if let Operation::Nop = s.0 {
                removed.insert(idx);
                false
            } else { true })
        });

        self.ports.retain_nodes(|port, idx| {
            port[idx].node.map_or_else(|| true, |n| !removed.contains(&n))
        })
    }

    /// Create and populate virtual registers for all ports
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
        ports_edges.sort_by_key(|e| self.ports[e.target()].time);
        ports_edges.reverse();
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
                let mut source = &self.ports[e.target()];
                let mut sink = &self.ports[e.source()];
                println!("v{} <- v{}", sink.id, source.id);
                println!("storages {} <- {}", sink.storage, source.storage);
                if let (None, _) = (*sink.storage, *source.storage) {
                    // We don't have a target storage to progate upwards, so
                    // have to try against next time
                    println!("skip");
                    return true
                }
                let (sink_backing, source_backing) = (
                    sink.storage.and_then(|s| if let Storage::Virtual(v) = s { virts[&v.into()].backing } else { None } ),
                    source.storage.and_then(|s| if let Storage::Virtual(v) = s { virts[&v.into()].backing } else { None } ),
                );
                println!("storages {} <- {}", sink.storage, source.storage);

                match (
                    sink.storage.clone().map(|s| if let Storage::Virtual(s) = s { s } else { panic!("l") }),
                    source.storage.clone().map(|s| if let Storage::Virtual(s) = s { s } else { panic!("r") }),
                ) {
                    (Some(sink_store), Some(source_store))
                    if sink_store == source_store && sink_backing == source_backing => {
                        // Do nothing, there are no conflicts
                    },
                    (Some(p0), Some(source_store)) if p0 != source_store || sink_backing != source_backing => {
                        // we emit a move before any instruction that has conflicting
                        // registers: this could be either because there's a physical
                        // storage already allocated, or two virtual registers
                        // use the same previous register
                        self.ports.remove_edge(e.id());
                        let mut n = Node::r#move(Storage::Virtual(p0), Storage::Virtual(source_store));
                        println!("INSERT MOVE");
                        self.add_node(n, |n, r| {
                            n.connect_input(0, e.target(), r);
                            n.connect_output(0, e.source(), r);
                            // TODO: we need a way to say that these values *depend* on eachother
                            // but don't share storage
                            r.connect_ports(n.sources()[0], n.sinks()[0]);
                            r.ports[n.sources()[0]].set_storage(Storage::Virtual(source_store));
                            r.ports[n.sinks()[0]].set_storage(Storage::Virtual(p0));
                        });
                        use std::ops::BitOr;
                        let require = &virts[&p0.into()].hints.clone();
                        virts.entry(source_store.into()).and_modify(|e| {
                            e.hints = e.hints.bitor(&require);
                        });
                    },
                    (Some(p0), None) if sink_backing.is_some() => {
                        // create a new virtual register + move before any physical sinks
                        virts.insert(reg.into(), VirtualRegister { ports: vec![], hints: HashSet::from([sink_backing.unwrap()]), backing: None, allocated: false });
                        let new_virt = Storage::Virtual(reg);
                        self.ports[e.target()].set_storage(new_virt);
                        reg += 1;
                        self.ports.remove_edge(e.id());
                        let mut n = Node::r#move(Storage::Virtual(p0), new_virt);
                        println!("INSERT MOVE");
                        self.add_node(n, |n, r| {
                            n.connect_input(0, e.target(), r);
                            n.connect_output(0, e.source(), r);
                            // TODO: we need a way to say that these values *depend* on eachother
                            // but don't share storage
                            r.connect_ports(n.sources()[0], n.sinks()[0]);
                            r.ports[n.sources()[0]].set_storage(new_virt);
                            r.ports[n.sinks()[0]].set_storage(Storage::Virtual(p0));
                        });
                    },
                    (Some(sink_store), _) if sink_backing.is_none() => {
                        println!("just propogating");
                        // we can't just use source.set_storage because it's
                        // a clone.
                        self.ports[e.target()].set_storage(Storage::Virtual(sink_store));
                    },
                    (x, y) => {
                        unimplemented!("create_virtual_registers unhandled {:?} {:?} {:?} {:?}", x, sink_backing, y, source_backing);
                    },
                };
                false
            }).collect();
        };
        // Make sure all ports have storages now
        for p in self.ports.node_indices() {
            assert!(self.ports[p].storage.is_some(), "port {:?} without storage", p);
            let vreg = match self.ports[p].storage.unwrap() {
                Storage::Virtual(v) => v,
                Storage::Physical(p) => panic!("port {:?} has physical storage", p),
                Storage::Immaterial => continue,
            };
            // and add them to their virtual registers' port list
            virts.get_mut(&vreg.into()).unwrap().ports.push(p);
        }

        virts
    }

    pub fn annotate_port_times_and_hints(&mut self, virts: &mut VirtualRegisterMap) {
        use std::collections::BTreeSet;
        let mut nodes = { self.nodes.externals(Direction::Outgoing).collect::<BTreeSet<_>>() };

        {
            // The initial set of nodes with no dependants can be marked done
            for n in &nodes {
                println!("root {:?}", self.nodes[*n]);
                self.nodes[*n].done = true;
            }
        }
        println!("all nodes {:#?}", self.nodes.node_weights().collect::<Vec<_>>());

        // Then give process the nodes, adding their dependencies to the working set
        // and having their time be the max of their dependants' time
        // We work from the "bottom up" so that all instructions are scheduled the
        // latest they possibly can.
        let mut final_time = Timestamp::new();
        'process: while let Some(sink) = &nodes.pop_first() {
            let mut dependencies = self.nodes.neighbors_directed(*sink, Direction::Outgoing).detach();
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
                time = max(time, dependency.time.increment()); // TODO: latency
            }
            println!("node {:?} has time {}", self.nodes[*sink], time);
            self.nodes[*sink].time = time;
            final_time = max(final_time, time);
            self.nodes[*sink].done = true;

            let mut dependents = self.nodes.neighbors_directed(*sink, Direction::Incoming).detach();
            while let Some((e, source)) = dependents.next(&self.nodes) {
                // Add all the dependants of the node to the working set
                nodes.insert(source);
            }
        }
        // and add one for the function return ports
        final_time = final_time.increment();
        println!("final time is {}", final_time);

        // validate all nodes were given times
        for n in self.nodes.node_weights_mut().into_iter() {
            assert_eq!(n.done, true, "no time for {:?}", n);
            // renumber nodes so they are increasing in program time
            n.time.major = final_time.major - n.time.major;
            // and give its ports the correct timings
            for p in n.sources() { self.ports[p].time = Some(n.time); }
            // TODO: latency
            for p in n.sinks() { self.ports[p].time = Some(n.time.push()); }
        }

        // and our functions entry/exit ports also need a time
        for p in &self.sources {
            self.ports[*p].time = Some(Timestamp::new());
        }
        for p in &self.sinks {
            self.ports[*p].time = Some(final_time.push());
        }

        // sort the uses for virtual registers by timings for later
        for (i, vreg) in virts {
            vreg.ports.sort_by(|a, b| self.ports[*a].time.unwrap().partial_cmp(&self.ports[*b].time.unwrap()).unwrap());
        }

    }

    // Push and pull instructions forward or backwards inside their major timeslice
    // in order to create disjoint ranges
    pub fn optimize_vreg_live_ranges(&mut self, virts: &mut VirtualRegisterMap) {
        for (i, vreg) in virts {
            //let last = vreg.ports.last().unwrap();
            //self.ports[*last].time.as_mut().map(|t| *t = t.push());
            //self.ports[*last].node.map(|n| { let n = &mut self.nodes[n]; n.time = n.time.push() });

            //let first = vreg.ports.first().unwrap();
            //self.ports[*first].time.as_mut().map(|t| *t = t.pull());
            //self.ports[*first].node.map(|n| { let n = &mut self.nodes[n]; n.time = n.time.pull() });
        }
    }


    pub fn allocate_physical_for_virtual(&mut self, virts: &mut VirtualRegisterMap) {
        // TODO: all of this should just be over virtual register and not ports
        use rangemap::RangeInclusiveMap;
        // The rangemap is (end..start, vreg). vreg is the virtual register that is
        // live for that timeslice on the physical register.
        let mut live: HashMap<RegSpec, RangeInclusiveMap<Timestamp, usize>> = HashMap::new();


        // TODO: split timestamps into (major, minor), so that we can schedule
        // instructions within the scheduled timeslice.
        // this is needed so that we can e.g. allow instructions in the same timeslice
        // to re-use registers if the only instruction in the slice that 

        // Add all the constrained registers first
        for (key, reg) in &mut *virts {
            if reg.backing.is_some() {
                println!("---- constrained {}", key);
                let (start, end) = (
                    self.ports[*reg.ports.first().unwrap()].time.unwrap(),
                    self.ports[*reg.ports.last().unwrap()].time.unwrap()
                );
                let range = start..=end;
                let reg_live = live.entry(*REGMAP.get(&reg.backing.unwrap()).unwrap()).or_insert_with(|| {
                    println!("first allocation for constrained {} at {:?}", reg.backing.unwrap(), range); RangeInclusiveMap::new()
                });
                let already = reg_live.gaps(&range);
                let mut empty = false;
                for gap in already {
                    println!("gap {:?}", gap);
                    if gap.start() != range.start() || gap.end() != range.end() {
                        panic!("bad gap");
                    }
                    empty = true;
                    break;
                }
                if !empty { panic!("uh oh"); };
                reg_live.insert(start..=end.push(), *key);
                println!("allocated constrained {} register {} {:?}", *key, reg.backing.unwrap(), range);
                // we were able to allocate the physical register requirement
                continue;
            }
        }

        // and then do reverse linear scan for any unconstrained virtual registers
        let vregs = virts.clone();
        let mut vregs = vregs.iter()
            .filter(|(_, r)| r.backing.is_none() )
            .collect::<Vec<_>>();
        vregs.sort_by(|(_, v0), (_, v1)| {
            // We want registers with hints scheduled first, and registers with
            // a *smaller* hint set to be scheduled sooner also
            let v0_time = self.ports[*v0.ports.first().unwrap()].time;
            let v0_hints = v0.hints.len();
            let v1_time = self.ports[*v1.ports.first().unwrap()].time;
            let v1_hints = v1.hints.len();
            (v0_hints == 0).cmp(&(v1_hints == 0))
            .then(v0_hints.cmp(&v1_hints))
            // we also want to allocate vregs bottom-up
            .then(v0_time.cmp(&v1_time).reverse())
        });
        let mut last = Timestamp::new();
        'allocate: for (key, reg) in vregs.drain(..) {
            println!("---- uncontrained {}", key);
            let (start, end) = (
                self.ports[*reg.ports.first().unwrap()].time.unwrap(),
                self.ports[*reg.ports.last().unwrap()].time.unwrap()
            );
            last = max(last, end);
            println!("allocating virtual register alive {}-{}", start, end);
            let range = start..=end;
            // try to use a free register
            println!("hints {:?}", reg.hints);
            'candidate: for candidate in reg.hints.iter().chain(REGS.iter()) {
                let reg_live = live.entry(*candidate).or_insert_with(|| {
                    println!("first allocation for {} unconstrained at {:?}", candidate, range); RangeInclusiveMap::new()
                });
                let already = reg_live.gaps(&range);
                let mut empty = false;
                for gap in already {
                    println!("{} gap {:?}", candidate, gap);
                    if gap.start() != range.start() || gap.end() != range.end() {
                        continue 'candidate;
                    }
                    empty = true;
                    break;
                }
                if !empty { continue 'candidate };
                // we have a free register for this time slice
                reg_live.insert(start..=end.push(), *key);
                virts.get_mut(key).unwrap().backing = Some(*candidate);
                println!("allocated unconstrained {} register {} {:?}", *key, candidate, range);
                continue 'allocate;
            }
            panic!("couldn't allocate");

        }

        // print out a pretty graph of the register live ranges
        for reg in live {
            let mut graph: String = "[".to_owned() + &" ".repeat((last.major*2).into()) + &"]".to_owned();
            for range in reg.1 {
                let size = (range.0.end().major + 1) - range.0.start().major;
                let new = (range.0.start().major as usize + 1)..(range.0.end().major as usize + 2);
                graph.replace_range(new, &"=".repeat(size as usize));
            }
            println!("{}: {}", reg.0, graph);
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



