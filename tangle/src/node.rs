use dynasmrt::x64::Assembler;
use dynasmrt::{dynasm, DynasmApi};
use yaxpeax_x86::long_mode::RegSpec;
use yaxpeax_x86::long_mode::register_class;
use petgraph::graph::NodeIndex;

use crate::time::Timestamp;
use crate::ir::IR;
use crate::port::{PortMeta, PortIdx, PortEdge, Storage, EdgeVariant};
use crate::region::{Region, RegionIdx, State, StateVariant};

pub type NodeIdx = NodeIndex;
#[derive(Debug)]
pub struct Node {
    pub variant: Box<dyn NodeBehavior>,
    pub inputs: Vec<PortIdx>,
    pub outputs: Vec<PortIdx>,
    pub label: Option<String>,
    pub containing_region: Option<RegionIdx>,
    pub time: Timestamp,
    pub done: bool,
}

#[derive(Debug)]
pub enum Operation {
    Nop,
    Constant(usize),
    Apply, // Call a Function node with arguments
    Inc,
    Add,
    LoadStack,
    StoreStack
}

pub mod NodeVariant {
    use super::{Operation, Region};
    
    use super::*;
    #[derive(Debug)]
    pub struct Move(pub Storage, pub Storage); // A move operation, sink <- source.
    #[derive(Debug)]
    pub struct Simple(pub Operation); // Instructions or constant operands
    #[derive(Debug)]
    pub struct Function<const A: usize, const O: usize> {
        pub args: u8,
        pub outs: u8,
        pub stack_slots: u32,
        pub region: RegionIdx,
    } // "Lambda-Nodes"; procedures and functions
    impl<const A: usize, const O: usize> Function<A, O> {
        pub fn new(ir: &mut IR) -> Function<A, O> {
            let r = ir.new_region();
            Self {
                region: r,
                args: 0,
                outs: 0,
                stack_slots: 0,
            }
        }

        pub fn add_body<T, F, F_O>(
            &mut self,
            mut n: T,
            ir: &mut IR,
            f: F) -> (NodeIdx, F_O) where F: FnOnce(&mut Node, &mut Region) -> F_O, T: NodeBehavior + core::any::Any + 'static + core::fmt::Debug
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

        pub fn add_stack_slot(&mut self, ir: &mut IR) -> PortIdx {
            let port = ir.in_region(self.region, |mut r, ir| {
                let new_state = r.states.len();
                let port = r.add_port();
                r.states.push(State {
                    name: "stack".to_string(),
                    variant: StateVariant::Stack(self.stack_slots),
                    producers: vec![port],
                });

                r.constrain(port, Storage::Immaterial(Some(new_state.try_into().unwrap())));
                r.ports[port].set_variant(EdgeVariant::State);
                port
            });

            self.stack_slots += 1;
            port
        }
    }
    pub struct Global(pub Region); // "Delta-Nodes"; global variables
    pub struct Loop(pub Region); // "Theta-Nodes"; do-while loops. Only ever tail-controlled.
    pub struct Partition(pub Vec<Region>); // "Gamma-Nodes"; if-then-else statements and case-switch
    // The paper also has "Phi-Nodes" (mutually recursive functions) and
    // "Omega-Nodes" (translation units). We only ever JIT one function at a time.
}

pub use NodeVariant::*;

pub trait NodeBehavior: core::fmt::Debug + core::any::Any {
    fn set_time(&mut self, time: Timestamp) {
       unimplemented!();
    }
    fn get_time(&self) -> Timestamp {
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
    pub fn as_variant<T>(&self) -> Option<&T> where T: 'static {
        (&*self.variant as &(dyn core::any::Any + 'static)).downcast_ref::<T>()
    }

    pub fn as_variant_mut<T>(&mut self) -> Option<&mut T> where T: 'static {
        (&mut *self.variant as &mut (dyn core::any::Any + 'static)).downcast_mut::<T>()
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

    pub fn connect_input(&mut self, idx: usize, input: PortIdx, r: &mut Region) -> PortEdge {
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

    pub fn create_ports(&mut self, r: &mut Region) {
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

   pub fn input_count(&self) -> usize {
        self.variant.input_count()
    }

    pub fn output_count(&self) -> usize {
        self.variant.output_count()
    }

    pub fn codegen(&self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        println!("node codegen for {:?} @ {}", self.variant, self.time);
        self.variant.codegen(self.inputs.clone(), self.outputs.clone(), r, ir, ops)
    }
}

impl NodeBehavior for NodeVariant::Simple {
    fn input_count(&self) -> usize {
        match &self.0 {
            Operation::Inc => 1,
            Operation::Add => 2,
            Operation::Constant(_) => 0,
            Operation::LoadStack => 1,
            Operation::StoreStack => 2,
            _ => unimplemented!(),
        }
    }

    fn output_count(&self) -> usize {
        match &self.0 {
            Operation::Inc => 1,
            Operation::Add => 1,
            Operation::Constant(_) => 1,
            Operation::LoadStack | Operation::StoreStack => 1,
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
                    (Storage::Physical(r0), Storage::Immaterial(None)) => match r0.class() {
                        register_class::Q => dynasm!(ops
                            ; add Rq(r0.num()),
                                operand_1.get_meta::<PortMeta::Constant, _>().unwrap().0.try_into().unwrap()
                        ),
                        x => unimplemented!("unknown class {:?} for add", x),
                    }
                    _ => unimplemented!(),
                }
            },
            Operation::Constant(n) => {
                let output = &r.ports[outputs[0]];
                match output.storage.as_ref().unwrap() {
                    Storage::Physical(r0) => match r0.class() {
                        register_class::Q => dynasm!(ops
                            ; mov Rq(r0.num()), (*n).try_into().unwrap()
                        ),
                        x => unimplemented!("unknown class {:?} for constant", x),
                    },
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
                    vec![inputs[0]], vec![outputs[0]], r, ir, ops);
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
                            vec![inputs[1]], vec![inputs[0]], r, ir, ops);
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
            Operation::Constant(_) => {},
            Operation::LoadStack => { r.ports[inputs[0]].set_variant(EdgeVariant::State); },
            Operation::StoreStack => {
                r.ports[inputs[0]].set_variant(EdgeVariant::State);
                r.ports[outputs[0]].set_variant(EdgeVariant::State);
                r.connect_ports(inputs[0], outputs[0]);
            }, // this connects the state ports
            _ => unimplemented!("ports_callback for {:?}", self.tag()),
        };
    }

    fn tag(&self) -> String {
        match &self.0 {
            Operation::Inc => "inc".to_string(),
            Operation::Add => "add".to_string(),
            Operation::Constant(n) => n.to_string(),
            Operation::LoadStack => "load_ss".to_string(),
            Operation::StoreStack => "store_ss".to_string(),
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
    fn input_count(&self) -> usize {
        0
    }

    fn output_count(&self) -> usize {
        // The output of a function node is always the function itself
        // todo lol
        1
    }

    fn codegen(&self, inputs: Vec<PortIdx>, outputs: Vec<PortIdx>, r: &mut Region, ir: &mut IR, ops: &mut Assembler) {
        if self.stack_slots != 0 {
            // allocate stack space
            dynasm!(ops
                ; sub rsp, (self.stack_slots*8).try_into().unwrap()
            );
        }
        // if we're calling codegen on a function, it should be the only one.
        ir.in_region(self.region, |r, ir| { r.codegen(ir, ops); });
        if self.stack_slots != 0 {
            // cleanup stack space
            dynasm!(ops
                ; add rsp, (self.stack_slots*8).try_into().unwrap()
            );
        }
        dynasm!(ops
            ; ret
        );
    }
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
            time: Timestamp::new().increment(),
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


