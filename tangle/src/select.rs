#![deny(unreachable_code)]

//! This is a graph pattern matcher based loosely off "Generating Instruction
//! Selectors For Large Pattern Sets", Markus Schlegel.
//!
//! The paper has a flaw, in that it is 310x slower than the normal libFIRM instruction
//! selector. That's kinda bad.
//!
//! We implement their third suggestion for how to make it more efficient, parameterizing
//! the pattern fragments so that pattern trunks can structurally share more often.
//!
//! We also don't implement nearly as many patterns (60000!) since we're just homerolling
//! them for now, instead of automatically generating patterns for every ia-32 instruction.
//!
//! Additionally, we don't have multi-root patterns; if I do end up adding them, I
//! plan on replacing the bulletin callback system with simply putting the pointer
//! of one bulletin board on another when needed; I can't think of a good reason why
//! this wasn't done in the original paper, and should make multi-root patterns more efficient.
//!
//! Tl;dr - We match nodes and their inputs with *patterns*, and if the pattern match
//! give the node an *annotation*. The annotation additionally can bind some of the
//! inputs as *variables*. The inputs can themselves be patterns, which we check
//! by simply checking if the node has the correct annotation. Non-leaf nodes of a pattern
//! must have outgoing degree == 1.
//!
//! When doing codegen we instead emit a topological sort of the patterns, which
//! corrospond to instruction forms. We also only need to do register allocation over
//! edges between patterns, instead of all port->port edges.
//!
//! Example: Pattern A is {Constant(n) | n}, Pattern B is {A -> Leave}
//! Constant(n) -> Leave then becomes an instance of B, which can be `JMP N` (instead
//! of `MOV R0, N;` followed by `JMP R0`, for example).
//!
//! One neat thing we can do that the paper can't is that the primary use of tangle
//! is for a *lifter*; that is, we already start with some instruction pattern when
//! we insert nodes, and thus by definition can give them a pattern without needing
//! to run the pattern matchers. After rewriting the nodes for e.g. optimization
//! passes we need to make sure that the patterns are still valid, or if not match
//! new ones, but in the default case it allows us to "for free" lower to the exact
//! same instructions as we lifted.
//!
//! The patterns themselves use an open recursion scheme, which should hopefully allow
//! for the Rust compiler to fuse them together, instead of requiring a pre-build
//! codegen step.
use crate::node::{Node, NodeIdx, NodeVariant, NodeBehavior, Operation, NodeOwner, NodeCell};
use crate::node::NodeVariant::*;
use crate::region::{Region, NodeGraph};

use petgraph::Direction;
use petgraph::visit::Visitable;

use frunk::prelude::HList;
use frunk::{HList, HCons, HNil};
use frunk::hlist::Plucker;
use frunk::hlist::LiftFrom;
use frunk::hlist::h_cons;
use frunk::traits::{ToRef, ToMut};
use ascent::{ascent, ascent_run};

use std::collections::{HashMap, BTreeSet};
use std::any::type_name;

//// A bitmap for all of the possible patterns we can record on a node.
//// Add a HashMap<T, T::Variables> probably for recording variables in a pattern?
//type All = HList![
//    (bool,Constant16),
//    (bool,Constant16Jmp)
//];
//
//#[derive(Default, Copy, Clone, Hash, PartialEq, Eq)]
//struct Annotation(All);
//impl Annotation {
//    pub fn set_label<'this, 'a, K, T>(&'this mut self) where
//        'this: 'a,
//        K: 'static,
//        <All as ToMut<'a>>::Output: Plucker<&'a mut (bool, K), T>,
//        //All: Plucker<&'a mut (bool, K), T>,
//    {
//        let mut annot: HCons<&'a mut _, _> = self.0.to_mut();
//        let (head, tail): (&'a mut (bool, K), _) = annot.pluck();
//        (*head).0 = true;
//    }
//
//    pub fn get_label<'this, 'a, K, T>(&'this self) -> bool where
//        'this: 'a,
//        K: 'static,
//        <All as ToRef<'a>>::Output: Plucker<&'a (bool, K), T>,
//        //All: Plucker<&'a mut (bool, K), T>,
//    {
//        let mut annot: HCons<&'a _, _> = self.0.to_ref();
//        let (head, tail): (&'a (bool, K), _) = annot.pluck();
//        (*head).0
//    }
//}


#[derive(Clone)]
pub struct RefEquality<T: Sized>(T) where RefEquality<Rc<T>>: PartialEq;

impl<T: ?Sized> std::hash::Hash for RefEquality<Rc<T>> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (self.0.as_ref() as *const T).hash(state)
    }
}

impl<'a, T: ?Sized> std::hash::Hash for RefEquality<&'a T> {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (self.0 as *const T).hash(state)
    }
}

impl<T: ?Sized> PartialEq<RefEquality<Rc<T>>> for RefEquality<Rc<T>> {
    fn eq(&self, other: &RefEquality<Rc<T>>) -> bool {
        self.0.as_ref() as *const T == other.0.as_ref() as *const T
    }
}

impl<'a, 'b, T: ?Sized> PartialEq<RefEquality<&'b T>> for RefEquality<&'a T> {
    fn eq(&self, other: &RefEquality<&'b T>) -> bool {
        self.0 as *const T == other.0 as *const T
    }
}

impl<T: ?Sized> Eq for RefEquality<Rc<T>> where RefEquality<Rc<T>>: PartialEq { }
impl<'a, T: ?Sized> Eq for RefEquality<&'a T> where RefEquality<&'a T>: PartialEq { }



#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Pattern {
    Constant16 = 0isize,
    Constant16Jmp,
    MoveRegReg,
}

use ascent::Lattice;
impl Lattice for Pattern {
    fn meet(self, other: Self) -> Self {
        self.min(other)
    }
    fn join(self, other: Self) -> Self {
        self.max(other)
    }
}

use ascent::lattice::set::Set;
type PatternSet = Set<Option<Pattern>>;

type NodeRow = RefEquality<Rc<NodeCell>>;

use std::rc::Rc;
use ascent::lattice::Product;

use core::any::Any;
fn variant<T: 'static + NodeBehavior>(token: &RefEquality<&NodeOwner>, n: &RefEquality<Rc<NodeCell>>) -> bool {
    (n.0.ro(token.0).as_ref() as &dyn Any).downcast_ref::<T>().is_some()
}

#[derive(Default)]
pub struct PatternManager;

ascent! {
    struct AscentProgram<'a>;
    /// Stage 1
    // Indicated that A is the C'th input of B
    relation edge(NodeIdx, NodeIdx, usize);
    // Indicated what kind of operation a node is
    relation kind(NodeIdx, NodeRow);
    // Capture the NodeCell token for query use
    relation token(RefEquality<&'a NodeOwner>);
    // Output the annotations that a node was given
    lattice pattern(NodeIdx, Pattern, Set<NodeIdx>);

    // Constant patterns
    pattern(n, Pattern::Constant16, Set::singleton(*n)) <--
        token(?t), kind(n, ?c), if variant::<NodeVariant::Constant>(t, c);

    // Mov patterns
    pattern(n, Pattern::MoveRegReg, Set::singleton(*n)) <--
        token(?t), kind(n, ?c), if variant::<NodeVariant::Move>(t, c);

    // Leave patterns
    // jmp constant
    pattern(jmp, Pattern::Constant16Jmp, Set::singleton(*jmp).join(c_set.clone())) <--
        token(?t), kind(jmp, ?jmp_kind), edge(c, jmp, 0), pattern(c, Pattern::Constant16, c_set),
        if variant::<NodeVariant::Leave>(t, jmp_kind);
}

impl PatternManager {
    pub fn run(&mut self, token: &NodeOwner, region: &mut Region) {
        let Region { nodes, ports, sinks, .. } = region;


        use petgraph::visit::Walker;
        use petgraph::algo::DfsSpace;
        let mut dfs_space = DfsSpace::new(&*nodes);
        let mut visit_nodes: Vec<_> = petgraph::algo::toposort(&*nodes, Some(&mut dfs_space)).unwrap();
        let toposorted = visit_nodes.clone().drain(..).enumerate().map(|(i, n)| (n, i)).collect::<HashMap<_,_>>();
        let visit_nodes = visit_nodes.drain(..).map(|n| (n, RefEquality(nodes[n].variant.clone()))).collect();

        let mut edges = Vec::with_capacity(nodes.edge_count());
        for local in nodes.node_indices() {
            for (i, p) in nodes[local].inputs.iter().enumerate() {
                for neighbor in ports.neighbors_directed(*p, Direction::Outgoing) {
                    let neighbor_port = &ports[neighbor];
                    neighbor_port.node.map(|remote| {
                        let new_edge = (remote, local, i,);
                        println!("new edge {:?}", new_edge);
                        edges.push(new_edge);
                    });
                }
            }
        }

        let mut ascent = AscentProgram::default();
        ascent.token = vec![(RefEquality(token),)];
        ascent.kind = visit_nodes;
        ascent.edge = edges;
        ascent.run();

        println!("after ascent");
        let mut emitted: Option<BTreeSet<_>> = None;
        ascent.pattern.sort_by(|a, b|
            toposorted[&a.0].cmp(&toposorted[&b.0]).reverse()
            // for now we just return the largest pattern that matches first
            // later on this can be some shortest-path (lowest cost) thing ig
            .then(a.2.len().cmp(&b.2.len()))
        );
        let mut roots = ascent.pattern.drain(..).flat_map(|(root, pat, include_set)| {
            // for not we just get the first pattern that matches

            // If we already emitted the root, then it was a part of a pattern
            // from higher topologically. (this can be done smarter)
            if let Some(e) = emitted.as_ref() && e.contains(&root) {
                return None
            }
            println!("pattern {:?} {:?} {:?} {:?}",
                    root,
                    nodes[root].variant.ro(token),
                    pat,
                    include_set.iter().collect::<Vec<_>>());

            use std::ops::BitOr;
            emitted = emitted.as_ref().map(|e| e.bitor(&include_set.0)).or_else(|| Some(include_set.0.clone()));
            Some((root,pat,include_set,))
        }).collect::<Vec<_>>();

        for idx in &ascent.kind {
            assert!(emitted.as_ref().unwrap().contains(&idx.0), "{:?} ({:?}) not covered", idx.0, idx.1.0.ro(&token).tag());
        }

        //let mut phase2 = ascent_run! {
        //    relation root(NodeIdx, Pattern, Set<NodeIdx>) = roots;
        //    relation edge(NodeIdx, NodeIdx, usize) = ascent.edge;
        //    relation external(NodeIdx, NodeIdx);

        //    // An edge is external to a pattern if there is any edge that
        //    external(a, b) <-- edge(a, b), 
        //};

        //for external in phase2.root {
        //    //println!("external {:?}", external);
        //}
    }
}

