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

use petgraph::stable_graph::StableGraph;
use petgraph::graph::{NodeIndex};
use yaxpeax_x86::long_mode::{RegSpec};
use dynasmrt::x64::Assembler;
use dynasmrt::{AssemblyOffset, DynasmApi};

use std::collections::{HashMap, HashSet};

use crate::node::{NodeBehavior, NodeVariant, NodeIdx, NodeOwner};
pub use crate::port::{PortIdx, EdgeVariant};
use crate::region::{Region, RegionIdx, RegionEdge};
use crate::abi::Abi;
//use crate::opt::PassRunner;
use crate::select::PatternManager;

// yaxpeax decoder example
mod decoder {
    use yaxpeax_arch::{Decoder, Reader, ReaderBuilder};

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


#[derive(Clone)]
pub struct VirtualRegister {
    pub ports: Vec<PortIdx>, // these are reversed: the 0th element is the last port that uses it
    pub hints: HashSet<RegSpec>,
    pub backing: Option<RegSpec>,
    pub allocated: bool,
}
pub type VirtualRegisterMap = HashMap<usize, VirtualRegister>;

#[derive(Default)]
pub struct IR {
    body: Option<NodeIdx>,
    /// A directed acyclic graph of regions; if there is an edge r_1 -> r_2, then
    /// r_2 is within r_1.
    regions: StableGraph<Region, RegionEdge, petgraph::Directed>,
    /// The outer-most region that all other regions are under.
    master_region: RegionIdx,
    pub owner: Option<NodeOwner>,
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
            owner: Some(NodeOwner::new()),
        }
    }

    /// Create a region in this IR instance at the top-most level.
    pub fn new_region<ABI: Abi + 'static>(&mut self, abi: Option<ABI>) -> RegionIdx {
        let mut r = Region::new();
        r.live = true;
        r.abi = abi.map(|a| (box a) as Box<dyn Abi>);
        let r_x = self.regions.add_node(r);
        { self.regions.node_weight_mut(r_x).unwrap().idx = r_x; }
        self.regions.add_edge(self.master_region, r_x, ());
        r_x
    }

    pub fn add_function<const A: usize, const O: usize>(&mut self, f: NodeVariant::Function<A, O>) {
        let mut owner = self.owner.take().unwrap();
        self.in_region(self.master_region, |r, ir| {
            r.add_node(&mut owner, f, |n, r| {
            });
        });
        self.owner = Some(owner);
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
            r.apply_constraints();
            r.attach_ports();
            r.propogate_state_edges();
            r.observe_state_outputs();
            println!("propogated state edges");

            //r.move_constants_to_operands();
            r.remove_nops(self.owner.as_mut().unwrap());
            // Create virtual register storages for all nodes and ports
            let mut virt_map = r.create_virtual_registers(self.owner.as_mut().unwrap());
            r.create_dependencies(); // we have to re-add node dependencies for the inserted movs

            let mut patterner = PatternManager::default();
            patterner.run(r);
            //let runner = PassRunner;
            //runner.run(r);
            //panic!();

            println!("created virtual registers");
            r.annotate_port_times_and_hints(&mut virt_map);
            println!("annoated port times and hints");
            r.optimize_vreg_live_ranges(&mut virt_map);
            println!("optimized vreg live ranges");
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
        let mut owner = self.owner.take().unwrap();
        self.in_region(self.master_region, |r, ir| {
            let mut n = StableGraph::new();
            std::mem::swap(&mut r.nodes, &mut n);
            ret = Some(n[ir.body.unwrap()].codegen(&owner, vec![], vec![], r, ir, &mut ops));
            std::mem::swap(&mut r.nodes, &mut n);
        });
        let end = ops.offset();
        (ops, start, end.0 - start.0)
    }

    pub fn compile_fn<A, O>(&mut self) -> Result<(extern "C" fn(A) -> O, usize), Box<dyn std::error::Error>> {
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
        Ok((hello_fn, size))
    }

    pub fn print(&self) {
        // XXX: we want to dump a graphviz view or something else pretty here;
        // debugging a graph based IR without that sounds like hell.
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::node::{Node, Operation};

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
        let hello_fn: extern "C" fn(usize) -> usize = ir.compile_fn().unwrap().0;
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
        let hello_fn: extern "C" fn((usize, usize)) -> usize = ir.compile_fn().unwrap().0;
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
        let hello_fn: extern "C" fn((usize, usize)) -> (usize, usize) = ir.compile_fn().unwrap().0;
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
        }).0;
        let inc_1_i = f.add_body(inc_1, &mut ir, |inc_1, r| {
            inc_1.connect_input(0, port_1, r);
        }).0;
        f.add_body(add, &mut ir, |add, r| {
            add.connect_input(0, r.nodes[inc_0_i].sinks()[0], r);
            add.connect_input(1, r.nodes[inc_1_i].sinks()[0], r);
            add.connect_output(0, ret_port, r);
        });
        ir.set_body(f);

        let hello_fn: extern "C" fn((usize, usize)) -> usize = ir.compile_fn().unwrap().0;
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
        let hello_fn: extern "C" fn((usize, usize)) -> (usize, usize) = ir.compile_fn().unwrap().0;
        assert_eq!(hello_fn((1, 2)), (2, 3));
    }

    #[test]
    pub fn function_inc_a_lot() {
        let mut ir = IR::new();
        let mut f = Node::function::<1, 1>(&mut ir);
        let mut input = f.add_argument(&mut ir);
        let output = f.add_return(&mut ir);
        // TODO: make the port virtual register proprogation better so we can
        // bump this up
        let count = 200;
        for i in 0..count {
            let mut inc_0 = Node::simple(Operation::Inc);
            f.add_body(inc_0, &mut ir, |inc, r| {
                inc.connect_input(0, input, r);
                input = inc.sinks()[0];
            });
        }
        ir.in_region(f.region, |r, ir| {
            r.connect_ports(input, output);
        });


        ir.set_body(f);
        let hello_fn: extern "C" fn(usize) -> usize = ir.compile_fn().unwrap().0;
        assert_eq!(hello_fn(0), count);
    }

    #[test]
    pub fn function_add_constant() {
        let mut ir = IR::new();
        let mut f = Node::function::<1, 1>(&mut ir);
        let input = f.add_argument(&mut ir);
        let output = f.add_return(&mut ir);

        let mut two = Node::constant(2);
        let mut add = Node::simple(Operation::Add);
        let mut two_const = None;
        f.add_body(two, &mut ir, |two, r| {
            two_const = Some(two.sinks()[0]);
        });
        f.add_body(add, &mut ir, |add, r| {
            add.connect_input(0, input, r);
            add.connect_input(1, two_const.unwrap(), r);
            add.connect_output(0, output, r);
        });

        ir.set_body(f);
        let hello_fn: extern "C" fn(usize) -> usize = ir.compile_fn().unwrap().0;
        assert_eq!(hello_fn(0), 2);
        assert_eq!(hello_fn(1), 3);
    }

    #[test]
    pub fn function_use_stack() {
        let mut ir = IR::new();
        let mut f = Node::function::<1, 1>(&mut ir);
        let input = f.add_argument(&mut ir);
        let output = f.add_return(&mut ir);
        // We create a stack slot
        let mut ss1 = f.add_stack_slot(&mut ir);

        // ...and push, which should resolve to a use of ss1
        let mut push = Node::simple(Operation::StoreStack);
        ss1 = f.add_body(push, &mut ir, |i, r| {
            i.connect_input(0, ss1, r);
            i.connect_input(1, input, r);
            i.sinks()[0]
        }).1;

        // get the value
        let mut pop = Node::simple(Operation::LoadStack);
        let ss_val = f.add_body(pop, &mut ir, |i, r| {
            i.connect_input(0, ss1, r);
            i.sinks()[0]
        }).1;

        // then add to it via ss1
        let mut two = Node::constant(2);
        let mut add = Node::simple(Operation::Add);
        let mut two_const = f.add_body(two, &mut ir, |two, r| {
            two.sinks()[0]
        }).1;
        let added_val = f.add_body(add, &mut ir, |add, r| {
            println!("add closure {}", r.ports[ss1].storage);
            add.connect_input(0, ss_val, r);
            add.connect_input(1, two_const, r);
            add.sinks()[0]
        }).1;

        // and store it again
        let mut push = Node::simple(Operation::StoreStack);
        f.add_body(push, &mut ir, |i, r| {
            i.connect_input(0, ss1, r);
            i.connect_input(1, added_val, r);
            ss1 = i.sinks()[0];
        });

        // ...then pop it into the result register
        let mut pop = Node::simple(Operation::LoadStack);
        f.add_body(pop, &mut ir, |i, r| {
            i.connect_input(0, ss1, r);
            i.connect_output(0, output, r);
        });

        ir.set_body(f);
        let hello_fn: extern "C" fn(usize) -> usize = ir.compile_fn().unwrap().0;
        assert_eq!(hello_fn(0), 2);
        assert_eq!(hello_fn(1), 3);
    }

    #[test]
    pub fn function_stack_ordering() {
        let mut ir = IR::new();
        let mut f = Node::function::<1, 1>(&mut ir);
        let input = f.add_argument(&mut ir);
        let output = f.add_return(&mut ir);
        // We create a stack slot
        let mut ss1 = f.add_stack_slot(&mut ir);
        let initial_ss = ss1;

        // ...and push, which should resolve to a use of ss1
        let mut push = Node::simple(Operation::StoreStack);
        ss1 = f.add_body(push, &mut ir, |i, r| {
            i.connect_input(0, ss1, r);
            i.connect_input(1, input, r);
            i.sinks()[0]
        }).1;

        let mut pop = Node::simple(Operation::LoadStack);
        let ss_val_0 = f.add_body(pop, &mut ir, |i, r| {
            i.connect_input(0, ss1, r);
            i.sinks()[0]
        }).1;

        // then add to it via ss1
        let mut two = Node::constant(2);
        let mut add = Node::simple(Operation::Add);
        let mut two_const = f.add_body(two, &mut ir, |two, r| {
            two.sinks()[0]
        }).1;
        let added_val = f.add_body(add, &mut ir, |add, r| {
            println!("add closure {}", r.ports[ss1].storage);
            add.connect_input(0, ss_val_0, r);
            add.connect_input(1, two_const, r);
            add.sinks()[0]
        }).1;

        // and store it again
        let mut push = Node::simple(Operation::StoreStack);
        f.add_body(push, &mut ir, |i, r| {
            i.connect_input(0, ss1, r);
            i.connect_input(1, added_val, r);
            ss1 = i.sinks()[0];
        });

        // make a use of the *initial* stack value from before the load
        let mut pop = Node::simple(Operation::LoadStack);
        let ss_val_1 = f.add_body(pop, &mut ir, |i, r| {
            i.connect_input(0, initial_ss, r);
            i.sinks()[0]
        }).1;

        let mut three = Node::constant(3);
        let mut add = Node::simple(Operation::Add);
        let mut three_const = f.add_body(three, &mut ir, |three, r| {
            three.sinks()[0]
        }).1;
        f.add_body(add, &mut ir, |add, r| {
            add.connect_input(0, ss_val_1, r);
            add.connect_input(1, three_const, r);
            add.connect_output(0, output, r);
        });


        ir.set_body(f);
        let hello_fn: extern "C" fn(usize) -> usize = ir.compile_fn().unwrap().0;
        assert_eq!(hello_fn(0), 3);
        assert_eq!(hello_fn(1), 4);
    }

    #[test]
    pub fn function_tailcall_external() {
        let mut ir = IR::new();
        let mut f = Node::function::<1, 1>(&mut ir);
        let input = f.add_argument(&mut ir);
        let output = f.add_return(&mut ir);

        extern "C" fn external_function(a: usize) -> usize {
            a + 2
        }

        let mut addr = Node::constant(external_function as *const () as isize);
        let mut tailcall = Node::leave();
        let mut addr_const = None;
        f.add_body(addr, &mut ir, |addr, r| {
            addr_const = Some(addr.sinks()[0]);
        });
        f.add_body(tailcall, &mut ir, |tailcall, r| {
            tailcall.connect_input(0, addr_const.unwrap(), r);
        });

        ir.set_body(f);
        let hello_fn: extern "C" fn(usize) -> usize = ir.compile_fn().unwrap().0;
        assert_eq!(hello_fn(0), 2);
        assert_eq!(hello_fn(1), 3);
    }

    #[test]
    pub fn function_tailcall_with_shuffle() {
        let mut ir = IR::new();
        let mut f = Node::function::<2, 1>(&mut ir);
        let input_0 = f.add_argument(&mut ir);
        let input_1 = f.add_argument(&mut ir);
        let output = f.add_return(&mut ir);

        extern "C" fn external_function(a: usize) -> usize {
            a + 2
        }

        let mut addr = Node::constant(external_function as *const () as isize);
        let mut tailcall = Node::leave();
        let mut addr_const = None;
        f.add_body(addr, &mut ir, |addr, r| {
            addr_const = Some(addr.sinks()[0]);
        });
        f.add_body(tailcall, &mut ir, |tailcall, r| {
            tailcall.connect_input(0, addr_const.unwrap(), r);
            let arg = r.add_port();
            r.constrain(arg, crate::port::Storage::Physical(RegSpec::rdi()));
            tailcall.add_input(arg, r);
            tailcall.connect_input(1, input_1, r);
        });

        ir.set_body(f);
        let hello_fn: extern "C" fn((usize, usize)) -> usize = ir.compile_fn().unwrap().0;
        assert_eq!(hello_fn((0, 0)), 2);
        assert_eq!(hello_fn((0, 1)), 3);
    }
}
