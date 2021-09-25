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

pub enum EdgeVariant {
    State,
    Data,
}

pub type NodeId = u64;

pub type Port = u32;
pub type PortIdx = NodeIndex;
use std::sync::Mutex;
lazy_static::lazy_static! {
    static ref PORT_COUNT: Mutex<Port> = Mutex::new(0);
}
fn new_port() -> Port {
    let mut guard = PORT_COUNT.lock().unwrap();
    let curr = *guard;
    *guard += 1;
    curr
}
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
}

impl Region {
    pub fn new() -> Self {
        Self {
            live: false,
            ..Default::default()
        }
    }

    pub fn add_node<T: 'static + NodeBehavior>(&mut self, n: Node<T>) {
        self.nodes.push(box n)
    }

    pub fn add_port(&mut self) -> PortIdx {
        let p = new_port();
        self.ports.add_node(p)
    }

    pub fn connect_ports(&mut self, input: PortIdx, output: PortIdx) {
        // TODO: support other edge metadata?
        let e = Edge {
            variant: EdgeVariant::Data,
        };
        self.ports.add_edge(input, output, e);
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
    pub struct Simple(pub Operation); // Instructions or constant operands
    pub struct Function<const A: usize, const O: usize>(pub RegionIdx); // "Lambda-Nodes"; procedures and functions
    impl<const A: usize, const O: usize> Function<A, O> {
        pub fn new(ir: &mut IR) -> Self {
            let r = ir.new_region();
            Self(r)
        }

        pub fn add_body<T: 'static + NodeBehavior, F>(
            &mut self,
            mut n: Node<T>,
            ir: &mut IR,
            f: F) where F: FnOnce(&mut Node<T>, &mut IR) -> ()
        {
            n.containing_region = Some(self.0);
            n.create_ports(ir);
            f(&mut n, ir);
            ir.in_region(self.0, |mut r, ir| { r.add_node(n) });
        }

        pub fn add_argument(&mut self, ir: &mut IR) -> PortIdx {
            ir.in_region(self.0, |mut r, ir| { r.add_source() })
        }

        pub fn add_return(&mut self, ir: &mut IR) -> PortIdx {
            ir.in_region(self.0, |mut r, ir| { r.add_sink() })
        }
    }
    pub struct Global(pub Region); // "Delta-Nodes"; global variables
    pub struct Loop(pub Region); // "Theta-Nodes"; do-while loops. Only ever tail-controlled.
    pub struct Partition(pub Vec<Region>); // "Gamma-Nodes"; if-then-else statements and case-switch
    // The paper also has "Phi-Nodes" (mutually recursive functions) and
    // "Omega-Nodes" (translation units). We only ever JIT one function at a time.
}

pub trait NodeBehavior {
    fn add_input(&mut self, p: PortIdx, ir: &mut IR) {
        unimplemented!();
    }

    fn add_output(&mut self, r: &mut Region, ir: &mut IR) -> PortIdx {
        unimplemented!();
    }

    fn create_ports(&mut self, ir: &mut IR) {
        unimplemented!();
    }

    fn input_count(&self) -> usize {
        unimplemented!();
    }

    fn output_count(&self) -> usize {
        unimplemented!();
    }

    fn connect_input(&mut self, idx: usize, input: PortIdx, ir: &mut IR) {
        unimplemented!();
    }

    fn connect_output(&mut self, idx: usize, output: PortIdx, ir: &mut IR) {
        unimplemented!();
    }
}

impl<T: NodeBehavior> NodeBehavior for Node<T> {
    fn add_input(&mut self, p: PortIdx, ir: &mut IR) {
        self.inputs.push(p)
    }

    fn add_output(&mut self, r: &mut Region, ir: &mut IR) -> PortIdx {
        let p_x = r.add_port();
        self.outputs.push(p_x);
        p_x
    }

    fn create_ports(&mut self, ir: &mut IR) {
        ir.in_region(self.containing_region.unwrap(), |mut r, ir| {
            for i in 0..self.input_count() {
                let p = r.add_port();
                self.add_input(p, ir);
            }
            for i in 0..self.output_count() {
                self.add_output(r, ir);
            }
        })
    }

    fn input_count(&self) -> usize {
        self.variant.input_count()
    }

    fn output_count(&self) -> usize {
        self.variant.output_count()
    }

    fn connect_input(&mut self, idx: usize, input: PortIdx, ir: &mut IR) {
        let p = self.inputs[idx];
        ir.in_region(self.containing_region.unwrap(), |r, ir| {
            r.connect_ports(input, p);
        });
    }

    fn connect_output(&mut self, idx: usize, output: PortIdx, ir: &mut IR) {
        let p = self.inputs[idx];
        ir.in_region(self.containing_region.unwrap(), |r, ir| {
            r.connect_ports(p, output);
        });
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

impl<const A: usize, const O: usize> NodeBehavior for NodeVariant::Function<A, O> {
    fn input_count(&self) -> usize {
        A
    }

    fn output_count(&self) -> usize {
        // The output of a function node is always the function itself
        1
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
        self.regions.add_edge(self.master_region, r_x, ());
        r_x
    }

    pub fn add_function<const A: usize, const O: usize>(&mut self, f: Node<NodeVariant::Function<A, O>>) {
        self.in_region(self.master_region, |r, ir| {
            r.add_node(f);
        });
    }

    pub fn set_body<const A: usize, const O: usize>(&mut self, f: Node<NodeVariant::Function<A, O>>) {
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
        let o = f(&mut dummy, self);
        std::mem::swap(&mut dummy, &mut self.regions[r]);
        o
    }

    pub fn optimize(&mut self) -> &mut Self {
        self
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

}
