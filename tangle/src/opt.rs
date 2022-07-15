use crate::node::{Node, Operation, NodeVariant};
use crate::port::{Port, PortMeta, Edge, EdgeVariant};
use crate::region::{Region, NodeGraph, PortGraph};

use crate::petgraph::visit::{IntoEdgeReferences, EdgeRef};

//trait Pass<F> where
//    F: Pass<F>
//{
//    type First: Pass<F> = F;
//    type Next: Pass<F>;
//    fn visit_node(nodes: &NodeGraph, node: Node) -> PassEffect;
//}
//
//enum PassEffect {
//    Return(Node),
//}
//
//struct ConstantAdd;
//impl<F: Pass<F>> Pass<F> for ConstantAdd {
//    // {Constant, Constant} -> Add -> X; Constant -> X
//    // incoming count for input ports is always 1
//    // really we want a dependantly typed Node.become function that forces you
//    // to provide a mapping function from Variant ports->Variant ports
//    type Next = Nop;
//    fn visit_node(nodes: &NodeGraph, node: Node) -> PassEffect {
//        // do something
//        let mut add_node = node.as_variant::<NodeVariant::Simple>();
//        if let Some(add_node) = add_node && add_node.0 == Operation::Add {
//            println!("add");
//        }
//
//        if 1 == 1 {
//            return <Self::Next as Pass<F>>::visit_node(nodes, node)
//        } else {
//            return <Self::First as Pass<F>>::visit_node(nodes, node)
//        }
//    }
//}
//
//struct Nop;
//impl<F: Pass<F>> Pass<F> for Nop {
//    type Next = ();
//    fn visit_node(nodes: &NodeGraph, node: Node) -> PassEffect {
//        return PassEffect::Return(node);
//    }
//}
//
//impl<F: Pass<F>> Pass<F> for () {
//    type Next = ();
//    fn visit_node(nodes: &NodeGraph, node: Node) -> PassEffect {
//        panic!();
//    }
//}
//
//struct Fusor;
//impl Pass<Fusor> for Fusor {
//    type First = Fusor;
//    type Next = ConstantAdd;
//    fn visit_node(nodes: &NodeGraph, node: Node) -> PassEffect {
//        return <Self::Next as Pass<Fusor>>::visit_node(nodes, node)
//    }
//}
//
//pub struct PassRunner;
//impl PassRunner {
//    pub fn run(&self, region: &mut Region) {
//        let Region { nodes, ports, .. } = region;
//
        //let mut nodes_weights = nodes.node_indices().collect::<Vec<_>>();
        //while let Some(node) = nodes_weights.pop() {
        //    let mut tmp_node = Node::new(box Node::simple(Operation::Nop));
        //    core::mem::swap(&mut tmp_node, &mut nodes[node]);
        //    let res = Fusor::visit_node(nodes, tmp_node);
        //    match res {
        //        PassEffect::Return(mut n) =>
        //            core::mem::swap(&mut n, &mut nodes[node]),
        //        _ => panic!(),
        //    }
        //}
//    }
//}
