use dynasmrt::x64::Assembler;
use dynasmrt::{dynasm, DynasmApi};
use yaxpeax_x86::long_mode::RegSpec;
use yaxpeax_x86::long_mode::{register_class, Instruction};
use petgraph::graph::{NodeIndex, EdgeIndex};

use crate::time::Timestamp;
use crate::ir::{IR};
use crate::port::{PortMeta, PortIdx, PortEdge, Storage, EdgeVariant};
use crate::region::{Region, RegionIdx, State, StateVariant};
use crate::abi::{x86_64, Abi};

use std::rc::Rc;
#[derive(Hash, PartialOrd, Ord, PartialEq, Eq, Clone, Copy, Default)]
pub struct NodeIdxToken(u32);
pub type NodeIdx = NodeIndex<NodeIdxToken>;
pub type NodeEdge = EdgeIndex<NodeIdxToken>;
unsafe impl petgraph::matrix_graph::IndexType for NodeIdxToken {
    #[inline(always)]
    fn new(x: usize) -> Self {
        NodeIdxToken(x as u32)
    }
    #[inline(always)]
    fn index(&self) -> usize {
        self.0 as usize
    }
    #[inline(always)]
    fn max() -> Self {
        NodeIdxToken(::std::u32::MAX)
    }
}

impl core::fmt::Debug for NodeIdxToken {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        write!(fmt, "n{}", self.0)
    }
}

use qcell::{TCell, TCellOwner};
use qcell::{QCell, QCellOwner};
//pub struct NodeMarker;
pub type NodeOwner = QCellOwner;
pub type NodeCell = QCell<Box<dyn NodeBehavior>>;

//#[derive(Debug)]
pub struct Node {
    pub variant: Rc<NodeCell>,
    pub inputs: Vec<PortIdx>,
    pub outputs: Vec<PortIdx>,
    pub label: Option<String>,
    pub containing_region: Option<RegionIdx>,
    pub time: Timestamp,
    pub done: bool,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Operation {
    Nop,
    Apply, // Call a Function node with arguments
    Inc,
    Add,
    LoadStack,
    StoreStack
}

#[derive(Debug, PartialEq)]
pub enum Continuation {
    Return,
    Jmp(PortIdx),
}

pub mod NodeVariant {
    use super::{Operation, Region};

    use super::*;
    #[derive(Debug, Clone)]
    pub struct Constant(pub isize);
    #[derive(Debug, Clone)]
    pub struct Move(pub Storage, pub Storage); // A move operation, sink <- source.
    #[derive(Debug, Clone)]
    pub struct Simple(pub Operation); // Instructions or constant operands
    #[derive(Debug)]
    pub struct Function<const A: usize, const O: usize> {
        pub args: u8,
        pub outs: u8,
        pub stack_slots: Vec<PortIdx>,
        pub highwater: u8,
        pub region: RegionIdx,
        pub cont: Continuation,
    } // "Lambda-Nodes"; procedures and functions
    impl<const A: usize, const O: usize> Function<A, O> {
        pub fn new<ABI: Abi + Default + 'static>(ir: &mut IR) -> Function<A, O> {
            let r = ir.new_region(Some(<ABI as Default>::default()));
            Self {
                region: r,
                args: 0,
                outs: 0,
                stack_slots: vec![],
                highwater: 0,
                cont: Continuation::Return,
            }
        }

        pub fn add_body<'id, T, F, F_O>(
            &mut self,
            mut n: T,
            ir: &mut IR,
            f: F) -> (NodeIdx, F_O) where F: FnOnce(&mut Node, &mut Region) -> F_O, T: NodeBehavior + core::any::Any + 'static + core::fmt::Debug
        {
            ir.in_region(self.region, |mut r, ir| {
                r.add_node(ir.owner.as_mut().unwrap(), n, f)
            })
        }

        pub fn add_argument(&mut self, ir: &mut IR) -> PortIdx {
            let port = ir.in_region(self.region, |mut r, ir| {
                let port = r.add_source();
                port
            });
            self.args += 1;
            port
        }

        pub fn add_return(&mut self, ir: &mut IR) -> PortIdx {
            let port = ir.in_region(self.region, |mut r, ir| {
                let port = r.add_sink();
                port
            });
            self.outs += 1;
            port
        }

        pub fn add_stack_slot(&mut self, ir: &mut IR) -> PortIdx {
            let port = ir.in_region(self.region, |mut r, ir| {
                let new_state = r.states.len();
                let port = r.add_port();
                r.states.push(State {
                    name: "stack".to_string(),
                    variant: StateVariant::Stack(self.stack_slots.len().try_into().unwrap()),
                    producers: vec![],
                });

                r.constrain(port, Storage::Immaterial(Some(new_state.try_into().unwrap())));
                r.ports[port].set_variant(EdgeVariant::State);
                port
            });

            self.stack_slots.push(port);
            self.highwater = core::cmp::max(self.highwater, self.stack_slots.len().try_into().unwrap());
            port
        }
    }
    #[derive(Debug)]
    pub struct BrEntry; // "Block Entry"; header of a basic block, source of bb params
    #[derive(Debug)]
    pub struct BrCall; // "Block Call"; jump to a block entry, with arguments
    /// Tailcalls or jumps into native code are represented as Leave nodes.
    /// These nodes should have:
    ///     1) an input port for the address to jump to
    ///     2) some arbitrary number of input state or value ports for values
    ///         that should be observed by the jump target (e.g. register state or side-effects)
    ///     3) an output port state edge that should be connected to the function return
    #[derive(Debug)]
    pub struct Leave;
}

pub use NodeVariant::*;

pub trait NodeBehavior: core::fmt::Debug + core::any::Any {
    fn set_time(&mut self, time: Timestamp) {
       unimplemented!();
    }
    fn get_time(&self) -> Timestamp {
        unimplemented!();
    }

    fn create_ports(&self, r: &mut Region) {
    }

    fn ports_callback(&mut self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region) {
    }

    fn codegen(&self, token: &NodeOwner, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        unimplemented!();
    }


    fn tag(&self) -> String;

    fn input_count(&self) -> usize {
        unimplemented!();
    }
    fn output_count(&self) -> usize {
        unimplemented!();
    }
}

impl Node {
    pub fn as_variant<'a, T>(&'a self, token: &'a NodeOwner) -> Option<&'a T> where T: 'static {
        (&*self.variant.ro(token).deref() as &dyn NodeBehavior as &(dyn core::any::Any + 'static)).downcast_ref::<T>()
    }

    pub fn as_variant_mut<'a, T>(&'a mut self, token: &'a mut NodeOwner) -> Option<&'a mut T> where T: 'static + Clone {
        let x = self.as_variant::<T>(token);
        //(&mut x?.clone() as &mut (dyn core::any::Any + 'static)).downcast_mut::<T>()
        panic!()
    }

    fn set_time(&mut self, time: Timestamp) {
        self.time = time;
    }
    fn get_time(&self) -> Timestamp {
        self.time
    }

    pub fn sinks(&self) -> Vec<PortIdx> {
        self.outputs.clone()
    }

    pub fn sources(&self) -> Vec<PortIdx> {
        self.inputs.clone()
    }

    pub fn ports(&self) -> Vec<PortIdx> {
        let mut p = self.sources();
        p.append(&mut self.sinks());
        p
    }

    pub fn add_input(&mut self, p: PortIdx, r: &mut Region) {
        self.inputs.push(p)
    }

    pub fn add_output(&mut self, r: &mut Region) -> PortIdx {
        let p_x = r.add_port();
        self.outputs.push(p_x);
        p_x
    }

    pub fn connect_input<'a>(&'a mut self, idx: usize, input: PortIdx, r: &'a mut Region) -> PortEdge {
        let p = self.inputs[idx];
        r.connect_ports(input, p)
    }

    pub fn connect_output(&mut self, idx: usize, output: PortIdx, r: &mut Region) -> PortEdge {
        let p = self.outputs[idx];
        r.connect_ports(p, output)
    }

    pub fn connect_operands(&mut self, input: usize, output: usize, r: &mut Region) -> PortEdge {
        let input = self.inputs[input];
        let output = self.outputs[output];
        r.connect_ports(input, output)
    }

    pub fn create_ports(&mut self, token: &mut NodeOwner, r: &mut Region) {
        println!("create_ports called");
        self.variant.rw(token).create_ports(r);
        let mut inputs = vec![];
        let mut outputs = vec![];
        for i in 0..self.input_count(token) {
            let p = r.add_port();
            self.add_input(p, r);
            inputs.push(p);
        }
        for i in 0..self.output_count(token) {
            outputs.push(self.add_output(r));
        }
        self.variant.rw(token).ports_callback(inputs, outputs, r);
    }

   pub fn input_count(&self, token: &NodeOwner) -> usize {
        self.variant.ro(token).input_count()
    }

    pub fn output_count(&self, token: &NodeOwner) -> usize {
        self.variant.ro(token).output_count()
    }

    pub fn codegen(&self, token: &NodeOwner, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        println!("node codegen for {:?} @ {}", self.variant.ro(token), self.time);
        self.variant.ro(token).codegen(token, self.inputs.clone(), self.outputs.clone(), r, ir, ops)
    }
}

impl NodeBehavior for NodeVariant::Constant {
    fn input_count(&self) -> usize {
        0
    }

    fn output_count(&self) -> usize {
        1
    }

    fn codegen(&self, token: &NodeOwner, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        let output = &r.ports[outputs[0]];
        match output.storage.as_ref().unwrap() {
            Storage::Physical(r0) => match r0.class() {
                register_class::Q => dynasm!(ops
                    ; mov Rq(r0.num()), QWORD (self.0) as i64
                ),
                x => unimplemented!("unknown class {:?} for constant", x),
            },
            _ => unimplemented!(),
        }
    }

    fn tag(&self) -> String {
        self.0.to_string()
    }
}

impl NodeBehavior for NodeVariant::BrEntry {
    fn input_count(&self) -> usize {
        0
    }

    fn output_count(&self) -> usize {
        // Start with one port output, which is the block itself for use in br_call
        1
    }

    fn ports_callback(&mut self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region) {
        // set the block port as a state edge, of the block itself
        let port = outputs[0];
        let new_state = r.states.len();
        r.states.push(State {
            name: format!("bb{}", new_state),
            variant: StateVariant::Block(NodeIdx::new(0)),
            producers: vec![],
        });

        r.constrain(port, Storage::Immaterial(Some(new_state.try_into().unwrap())));
        r.ports[port].set_variant(EdgeVariant::State);
    }

    fn codegen(&self, token: &NodeOwner, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        // block entries don't codegen to anything
    }

    fn tag(&self) -> String {
        "br_entry".to_string()
    }
}

impl NodeBehavior for NodeVariant::BrCall {
    fn input_count(&self) -> usize {
        // takes as its first input the block to jump to
        1
    }

    fn output_count(&self) -> usize {
        0
    }

    fn ports_callback(&mut self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region) {
        r.ports[inputs[0]].set_variant(EdgeVariant::State);
    }

    fn codegen(&self, token: &NodeOwner, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        panic!()
    }

    fn tag(&self) -> String {
        "br_call".to_string()
    }
}

impl NodeBehavior for NodeVariant::Simple {
    fn input_count(&self) -> usize {
        match &self.0 {
            Operation::Inc => 1,
            Operation::Add => 2,
            Operation::LoadStack => 1,
            Operation::StoreStack => 2,
            Operation::Nop => 0,
            Operation::Apply => unimplemented!()
        }
    }

    fn output_count(&self) -> usize {
        match &self.0 {
            Operation::Inc => 1,
            Operation::Add => 1,
            Operation::LoadStack | Operation::StoreStack => 1,
            Operation::Nop => 0,
            Operation::Apply => unimplemented!()
        }
    }


    fn codegen(&self, token: &NodeOwner, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
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
                    //(Storage::Physical(r0), Storage::Immaterial(None)) => match r0.class() {
                    //    register_class::Q => dynasm!(ops
                    //        ; add Rq(r0.num()),
                    //            operand_1.get_meta::<PortMeta::Constant, _>().unwrap().0.try_into().unwrap()
                    //    ),
                    //    x => unimplemented!("unknown class {:?} for add", x),
                    //}
                    _ => unimplemented!(),
                }
            },
            // val <- ss
            // out: val'
            // THIS IS FUCKED:
            // stack slots actually have to be a STATE edge and not a data edge,
            // so that we can propogate them without having any conflicts.
            // otherwise we have a Stack storage for the ss, but not any uses,
            // and physical registers propogate upwards into it and it doesn't
            // know what it is anymore.
            Operation::LoadStack => {
                let ss = &r.ports[inputs[0]];
                let output = &r.ports[outputs[0]];
                NodeVariant::Move::codegen(&NodeVariant::Move(output.storage.unwrap(), ss.storage.unwrap()),
                    token, vec![inputs[0]], vec![outputs[0]], r, ir, ops);
                //match output.storage.as_ref().unwrap() {
                //    Storage::Physical(r0) => match r0.class() {
                //        register_class::Q => dynasm!(ops
                //            ; mov Rq(r0.num()), QWORD [rsp+ss_off]
                //        ),
                //        x => unimplemented!("unknown class {:?} for load_ss", x)
                //    },
                //    _ => unimplemented!(),
                //}
            },
            // ss <- val
            // out: ss'
            Operation::StoreStack => {
                let ss = &r.ports[inputs[0]];
                let input = &r.ports[inputs[1]];
                if let Storage::Immaterial(Some(state)) = ss.storage.unwrap() {
                    if let Some(state) = r.states.get(state as usize) {
                        NodeVariant::Move::codegen(&NodeVariant::Move(ss.storage.unwrap(), input.storage.unwrap()),
                            token, vec![inputs[1]], vec![inputs[0]], r, ir, ops);
                    } else {
                        panic!("bad state for ss storage")
                    }
                } else { panic!("bad storage for ss {:?}", ss) }
                //let ss_off = ss.get_meta::<PortMeta::StackOff, _>().unwrap().0;
                //match input.storage.as_ref().unwrap() {
                //    Storage::Physical(r0) => match r0.class() {
                //        register_class::Q => dynasm!(ops
                //            ; mov QWORD [rsp+ss_off], Rq(r0.num())
                //        ),
                //        x => unimplemented!("unknown class {:?} for load_ss", x)
                //    },
                //    _ => unimplemented!(),
                //}
            },
            x => unimplemented!("unimplemented codegen for {:?}", x),
        }
    }

    fn ports_callback(&mut self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region) {
        println!("{:?} <- {:?} ", outputs, inputs);
        match &self.0 {
            Operation::Inc =>
                { r.connect_ports(inputs[0], outputs[0]); },
            Operation::Add =>
                { r.connect_ports(inputs[0], outputs[0]); },
            Operation::LoadStack => { r.ports[inputs[0]].set_variant(EdgeVariant::State); },
            Operation::StoreStack => {
                r.ports[inputs[0]].set_variant(EdgeVariant::State);
                r.ports[outputs[0]].set_variant(EdgeVariant::State);
                r.connect_ports(inputs[0], outputs[0]);
            }, // this connects the state ports
            Operation::Nop => {},
            Operation::Apply => unimplemented!(),
        };
    }

    fn tag(&self) -> String {
        match &self.0 {
            Operation::Inc => "inc".to_string(),
            Operation::Add => "add".to_string(),
            Operation::LoadStack => "load_ss".to_string(),
            Operation::StoreStack => "store_ss".to_string(),
            Operation::Nop => "nop".to_string(),
            Operation::Apply => "apply".to_string(),
        }
    }
}

impl NodeBehavior for NodeVariant::Leave {
    fn tag(&self) -> String {
        "leave".to_string()
    }

    fn input_count(&self) -> usize {
        1
    }

    fn output_count(&self) -> usize {
        1
    }

    fn ports_callback(&mut self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region) {
        println!("tailcall leave ");
        r.constrain(outputs[0], Storage::Immaterial(None));
    }

    fn codegen(&self, token: &NodeOwner, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        // "what happens if you try to tailcall with stack slots allocated?"
        // haha. yeah.
        let source = &r.ports[inputs[0]];
        match source.storage.as_ref().unwrap() {
            Storage::Physical(r0) => {
                match r0.class() {
                    register_class::Q => {
                        dynasm!(ops
                            ; jmp Rq(r0.num())
                        );
                    },
                    _ => unimplemented!("tailcall class {:?}", r0.class())
                }
            },
            _ => unimplemented!("unknown tailcall target")
        }
    }
}

impl NodeBehavior for NodeVariant::Move {

    fn tag(&self) -> String {
        format!("mov {} <- {}", self.0, self.1)
    }

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

    fn codegen(&self, token: &NodeOwner, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        let sink = &r.ports[outputs[0]];
        let source = &r.ports[inputs[0]];
        match (sink.storage.as_ref().unwrap(), source.storage.as_ref().unwrap()) {
            (Storage::Physical(r0), Storage::Physical(r1)) => {
                // we can simply not emit any move at all if it was trying to move
                // a register into itself
                if r0 == r1 { return; }
                match (r0.class(), r1.class()) {
                    (register_class::Q, register_class::Q) =>
                        dynasm!(ops
                            ; mov Rq(r0.num()), Rq(r1.num())
                        ),
                    (x, y) => unimplemented!("{:?} <- {:?} unimplemented", x, y),
                }
            },
            (Storage::Physical(r0), Storage::Immaterial(Some(state))) => {
                let off = match r.states[*state as usize].variant {
                    StateVariant::Stack(o) => (o * 8).try_into().unwrap(),
                    _ => panic!(),
                };
                match r0.class() {
                    register_class::Q => dynasm!(ops
                        ; mov Rq(r0.num()), QWORD [rsp+off]
                    ),
                    _ => unimplemented!()
                }
            },
            (Storage::Immaterial(Some(state)), Storage::Physical(r1)) => {
                let off = match r.states[*state as usize].variant {
                    StateVariant::Stack(o) => (o * 8).try_into().unwrap(),
                    _ => panic!(),
                };
                match r1.class() {
                    register_class::Q => dynasm!(ops
                        ; mov QWORD [rsp+off], Rq(r1.num())
                    ),
                    _ => unimplemented!()
                }
            },
            (x, y) => unimplemented!("codegen for {:?} <- {:?}", x, y),
        }
    }

}


impl<const A: usize, const O: usize> NodeBehavior for NodeVariant::Function<A, O> {
    fn tag(&self) -> String {
        "function".to_string()
    }

    fn input_count(&self) -> usize {
        0
    }

    fn output_count(&self) -> usize {
        // The output of a function node is always the function itself
        // todo lol
        1
    }

    fn codegen(&self, token: &NodeOwner, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        assert_eq!(self.args as usize, A);
        if self.highwater != 0 {
            // allocate stack space
            dynasm!(ops
                ; sub rsp, (self.highwater*8).try_into().unwrap()
            );
        }
        // if we're calling codegen on a function, it should be the only one.
        ir.in_region(self.region, |r, ir| { r.codegen(token, ir, ops); });
        if self.highwater != 0 {
            // cleanup stack space
            dynasm!(ops
                ; add rsp, (self.highwater*8).try_into().unwrap()
            );
        }
        match self.cont {
            Continuation::Return => {
                assert_eq!(self.outs as usize, O);
                dynasm!(ops
                    ; ret
                )
            },
            Continuation::Jmp(o) => {
                // TODO: assert that the o port is connected to a Leave node
            },
        }
    }
}

use core::ops::Deref;
impl Deref for Node {
    type Target = Rc<NodeCell>;
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
    pub fn new(owner: &NodeOwner, var: Box<dyn NodeBehavior>) -> Node {
        Node {
            variant: Rc::new(NodeCell::new(owner, var)),
            inputs: vec![],
            outputs: vec![],
            label: None,
            containing_region: None,
            time: Timestamp::new().increment(),
            done: false,
        }
    }
    pub fn constant(n: isize) -> NodeVariant::Constant {
        NodeVariant::Constant(n)
    }

    pub fn simple(op: Operation) -> NodeVariant::Simple {
        NodeVariant::Simple(op)
    }

    pub fn r#move(sink: Storage, source: Storage) -> NodeVariant::Move {
        NodeVariant::Move(sink, source)
    }

    // id like for this to just take an ABI parameter but rust deprececated
    // default generic arguments for functions :/
    pub fn function<const A: usize, const O: usize>(ir: &mut IR) -> NodeVariant::Function<A, O> {
        NodeVariant::Function::new::<x86_64>(ir)
    }

    pub fn leave() -> NodeVariant::Leave {
        NodeVariant::Leave
    }

    pub fn bb() -> NodeVariant::BrEntry {
        NodeVariant::BrEntry
    }

    pub fn bcall() -> NodeVariant::BrCall {
        NodeVariant::BrCall
    }
}


