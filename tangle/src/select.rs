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
use crate::ir::VirtualRegisterMap;
use crate::node::{Node, NodeIdx, NodeVariant, NodeBehavior, Operation, NodeOwner, NodeCell};
use crate::node::NodeVariant::*;
use crate::port::{Storage, OptionalStorage, PortEdge};
use crate::region::{Region, NodeGraph, StateVariant};
use crate::time::Timestamp;

use petgraph::Direction;
use petgraph::visit::{Visitable, EdgeRef};
use petgraph::algo::DfsSpace;
use fixedbitset::FixedBitSet;

use yaxpeax_x86::long_mode::RegSpec;
use yaxpeax_x86::long_mode::register_class;

use frunk::prelude::HList;
use frunk::{HList, HCons, HNil};
use frunk::hlist::Plucker;
use frunk::hlist::LiftFrom;
use frunk::hlist::h_cons;
use frunk::traits::{ToRef, ToMut};
use ascent::{ascent, ascent_run};

use dynasmrt::x64::Assembler;
use dynasmrt::{dynasm, DynasmApi};

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
    Constant8 = 0isize,
    Constant16,
    Constant32,
    Constant64,
    Constant16Jmp,
    RegJmp,
    MoveRegReg,
    Inc,
    AddRegConstant8,
    AddRegConstant16,
    AddRegConstant32,
    AddRegReg,
    StoreStackReg,
    LoadStackReg,
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

fn operation(token: &RefEquality<&NodeOwner>, n: &RefEquality<Rc<NodeCell>>, op: Operation) -> bool {
    (n.0.ro(token.0).as_ref() as &dyn Any).downcast_ref::<NodeVariant::Simple>().map(|n| n.0 == op) == Some(true)
}



#[derive(Default)]
pub struct PatternManager {
    roots: Vec<(NodeIdx, Pattern, Set<NodeIdx>)>,
    toposorted: HashMap<NodeIdx, usize>,
    pub virt_map: VirtualRegisterMap,
}

use ascent::lattice::constant_propagation::ConstPropagation;
ascent! {
    struct AscentProgram<'a>;
    /// Stage 1
    // Indicated that Edge from A->B is the Nth input of B, which uses Vreg for storage
    relation edge(petgraph::stable_graph::EdgeIndex, Option<NodeIdx>, Option<NodeIdx>, usize, u16);
    // Indicates the storage of a Vreg is restricted to RegSpec
    relation restricted(u16, RegSpec);
    // Indicated what kind of operation a node is
    relation kind(NodeIdx, NodeRow);
    // Capture the NodeCell token for query use
    relation token(RefEquality<&'a NodeOwner>);
    // Outgoing degree count for each node
    relation outgoing(NodeIdx, u8);
    // Output the annotations that a node was given
    lattice pattern(NodeIdx, Pattern, Set<NodeIdx>);
    // Constant propogation; a node is a constant if it can be encoded as an N bit
    // width immediate.
    lattice constant(NodeIdx, u8, ConstPropagation<i64>);

    constant(n, 8, ConstPropagation::Constant(*imm)) <--
        constant(n, _, ?ConstPropagation::Constant(imm)), if TryInto::<i8>::try_into(*imm).is_ok();

    // Constant patterns
    pattern(n, Pattern::Constant8, Set::singleton(*n)) <--
        constant(n, 8, _);

    // Inc patterns
    pattern(n, Pattern::Inc, Set::singleton(*n)) <--
        token(?t), kind(n, ?c), if operation(t, c, Operation::Inc);

    // Add patterns
    pattern(n, Pattern::AddRegReg, Set::singleton(*n)) <--
        token(?t), kind(n, ?c), if operation(t, c, Operation::Add);

    pattern(add, Pattern::AddRegConstant8, Set::singleton(*add).join(Set::singleton(*c))) <--
        token(?t), kind(add, ?add_kind),
        edge(e, ?Some(c), Some(*add), 1, _), constant(c, 8, _), outgoing(c, 1),
        if operation(t, add_kind, Operation::Add);

    // Mov patterns
    // mov reg, _
    pattern(n, Pattern::MoveRegReg, Set::singleton(*n)) <--
        token(?t), kind(n, ?c),
        if variant::<NodeVariant::Move>(t, c);

    // Leave patterns
    // jmp constant
    pattern(jmp, Pattern::RegJmp, Set::singleton(*jmp)) <--
        token(?t), kind(jmp, ?jmp_kind),
        if variant::<NodeVariant::Leave>(t, jmp_kind);

    // Store_ss pattern
    pattern(store, Pattern::StoreStackReg, Set::singleton(*store)) <--
        token(?t), kind(store, ?store_kind),
        if operation(t, store_kind, Operation::StoreStack);

    pattern(load, Pattern::LoadStackReg, Set::singleton(*load)) <--
        token(?t), kind(load, ?load_kind),
        if operation(t, load_kind, Operation::LoadStack);
}

impl PatternManager {
    fn edges_row(&self, region: &Region) -> Vec<(petgraph::stable_graph::EdgeIndex, Option<NodeIdx>, Option<NodeIdx>, usize, u16)> {
        let Region { nodes, ports, sinks, .. } = region;
        let mut edges = Vec::with_capacity(nodes.edge_count());
        // hook up all the edges to node inputs. this includes from the region sources
        for local in nodes.node_indices() {
            for (i, p) in nodes[local].inputs.iter().enumerate() {
                let vreg: u16 = match ports[*p].storage{
                    OptionalStorage(Some(Storage::Immaterial(state))) => continue,
                    OptionalStorage(Some(Storage::Virtual(vreg))) => vreg,
                    _ => panic!(),
                };
                for e in ports.edges_directed(*p, Direction::Outgoing) {
                    let neighbor_port = &ports[e.target()];
                    let new_edge = (e.id(), neighbor_port.node, Some(local), i, vreg);
                    println!("new edge {:?}", new_edge);
                    edges.push(new_edge);
                }
            }
        }
        // we also hook up edges to the region sinks
        for (i, output) in sinks.iter().enumerate() {
            let vreg: u16 = match ports[*output].storage{
                OptionalStorage(Some(Storage::Immaterial(state))) => continue,
                OptionalStorage(Some(Storage::Virtual(vreg))) => vreg,
                _ => panic!(),
            };
            for e in ports.edges_directed(*output, Direction::Outgoing) {
                let neighbor_port = &ports[e.target()];
                let new_edge = (e.id(), neighbor_port.node, None, i, vreg);
                println!("new sink edge {:?}", new_edge);
                edges.push(new_edge);
             }
        }
        edges
    }

    pub fn run(&mut self, token: &NodeOwner, region: &mut Region, virt_map: &mut VirtualRegisterMap) {
        let mut edges = self.edges_row(region);
        let Region { nodes, ports, sinks, .. } = region;


        use petgraph::visit::Walker;
        let mut dfs_space = DfsSpace::new(&*nodes);
        let mut visit_nodes: Vec<_> = petgraph::algo::toposort(&*nodes, Some(&mut dfs_space)).unwrap();
        let toposorted = visit_nodes.clone().drain(..).enumerate().map(|(i, n)| (n, i)).collect::<HashMap<_,_>>();
        let visit_nodes = visit_nodes.drain(..).map(|n| (n, RefEquality(nodes[n].variant.clone()))).collect();

        let constants = nodes.node_indices().filter_map(|n| {
            nodes[n].as_variant::<NodeVariant::Constant>(token).map(|c| (n, 64, ConstPropagation::Constant(c.0 as i64)))
        }).collect::<Vec<_>>();
        let outgoing = nodes.node_indices().map(|n| {
            (n, nodes.edges(n).count().try_into().unwrap())
        }).collect::<Vec<_>>();
        dbg!(constants.clone());
        let mut ascent: AscentProgram::<'_> = AscentProgram::default();
        ascent.token = vec![(RefEquality(token),)];
        ascent.kind = visit_nodes;
        ascent.edge = edges;
        ascent.restricted = virt_map.iter().flat_map(|(i,v)| v.backing.map(|back| (*i as u16,back))).collect::<Vec<_>>();
        ascent.constant = constants;
        ascent.outgoing = outgoing;
        ascent.run();

        println!("after ascent");
        let mut emitted: Option<BTreeSet<_>> = None;
        ascent.pattern.sort_by(|a, b|
            toposorted[&a.0].cmp(&toposorted[&b.0]).reverse()
            // for now we just return the largest pattern that matches first
            // later on this can be some shortest-path (lowest cost) thing ig
            .then(a.2.len().cmp(&b.2.len()).reverse())
            .then(a.1.cmp(&b.1))
        );
        let mut roots = ascent.pattern.drain(..).flat_map(|(root, pat, include_set)| {
            dbg!(root, pat);
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

        let mut phase2 = ascent_run! {
            relation root(NodeIdx, Pattern, Set<NodeIdx>) = roots;
            relation edge(PortEdge, Option<NodeIdx>, Option<NodeIdx>, usize, u16) = ascent.edge;
            relation restricted(u16, RegSpec) = ascent.restricted;

            // given a pattern and a root we can have a Pattern::variables function
            // that populates variables required as needed.
            //relation variables(NodeIdx, NodeIdx);

            // We need all the external edges between patterns, which must be
            // allocated vregs.
            relation external(PortEdge, Option<NodeIdx>, Option<NodeIdx>, usize, u16);

            // An edge is external if it is the result of a root node
            //external(a, b) <-- edge(a, b, _), root(b, _, _);
            // An edge is external if it isn't internal to a pattern
            relation reachable(NodeIdx, NodeIdx);
            // The only edges with None set for an idx are ones going to region
            // input or outputs; those are always externals.
            reachable(root, root) <-- root(root, _, _);
            reachable(root, a) <-- edge(e, ?Some(a), ?Some(root), _, _), root(root, _, _);
            reachable(root, b) <-- edge(e, ?Some(a), ?Some(b), _, _), reachable(root, b);
            external(e, Some(*a), Some(*b), n, r) <-- edge(e, ?Some(a), ?Some(b), n, r), reachable(root, a), !reachable(root, b);
            external(e, None, b, n, r) <-- edge(e, ?None, b, n, r);
            external(e, a, None, n, r) <-- edge(e, a, ?None, n, r);
        };

        let mut observed = BTreeSet::<u16>::new();
        for external in phase2.external {
            println!("external {:?}", external);
            observed.insert(external.4);
        }

        virt_map.retain(|k, v| observed.contains(&(*k as u16)));
        self.roots = phase2.root;
        self.toposorted = toposorted;
    }

    pub fn codegen<'a>(&mut self, token: &NodeOwner, region: &mut Region, ops: &mut Assembler) {
        let mut edges = self.edges_row(region);
        let Region { nodes, ports, sinks, states, .. } = region;

        let constants = nodes.node_indices().flat_map(|n| {
            (nodes[n].ro(token).as_ref() as &dyn Any).downcast_ref::<NodeVariant::Constant>().map(|c| (n, c.0))
        }).collect::<Vec<_>>();

        let vregs = self.virt_map.iter().map(|(i, vr)| (*i as u16, vr.backing.unwrap())).collect::<Vec<(_,_)>>();
        use crate::petgraph::visit::IntoEdgeReferences;
        // this is messy and state edges should probably work differently
        let states_row = ports.edge_references().flat_map(|e| {
            if let OptionalStorage(Some(Storage::Immaterial(Some(state)))) = ports[e.target()].storage {
                ports[e.target()].node.map(|n| Some((n, state))).iter()
                    .chain(ports[e.source()].node.map(|n| Some((n, state))).iter())
                    .flatten().map(Clone::clone).collect::<Vec<_>>()
            } else {
                vec![]
            }
        }).collect::<Vec<_>>();

        let mut clock = Timestamp::new();
        self.roots.sort_by(|a, b| nodes[a.0].time.cmp(&nodes[b.0].time));
        let mut binder = ascent_run! {
            struct VarBinder;
             // Indicated that Edge from A->B is the Nth input of B, which uses Vreg for storage
            relation edge(petgraph::stable_graph::EdgeIndex, Option<NodeIdx>, Option<NodeIdx>, usize, u16) =
                edges;
            // The physical register used for each vreg
            relation vreg(u16, RegSpec) = vregs;
            // Indicates that a Node uses the state variable S
            relation state(NodeIdx, u16) = states_row;
            // Nodes that are constant values
            relation constant(NodeIdx, isize) = constants;
            // Output the annotations that a node was given
            lattice pattern(NodeIdx, Pattern, Set<NodeIdx>) = self.roots.clone();
            relation emit(NodeIdx, CodegenFn);

            // emit constants
            emit(c, CodegenFn(box move |ops| dynasm!(ops ;mov Rq(r0.num()), QWORD imm as i64))) <--
                edge(e, ?Some(c), _, _, r),
                vreg(r, ?&r0),
                constant(c, ?&imm) if r0.class() == register_class::Q;

            // emit adds
            emit(add, CodegenFn(box move |ops| dynasm!(ops; add Rq(r_out.num()), Rq(r_in.num()) ))) <--
                pattern(add, Pattern::AddRegReg, _),
                edge(e2, _, Some(*add), 0, vr_out),
                edge(e1, _, Some(*add), 1, vr_in),
                vreg(vr_out, ?&r_out),
                vreg(vr_in, ?&r_in),
                if r_in.class() == register_class::Q && r_out.class() == register_class::Q;

            emit(add, CodegenFn(box move |ops| dynasm!(ops; add Rq(r_out.num()), BYTE imm as i8 ))) <--
                pattern(add, Pattern::AddRegConstant8, _),
                edge(e2, _, Some(*add), 0, vr_out),
                edge(e1, ?Some(c), Some(*add), 1, vr_in),
                vreg(vr_out, ?&r_out),
                constant(c, ?&imm),
                if r_out.class() == register_class::Q;

            // emit inc
            emit(inc, CodegenFn(box move |ops| dynasm!(ops ;inc Rq(r0.num())))) <--
                edge(e, ?Some(c), ?Some(inc), 0, r), pattern(inc, Pattern::Inc, _),
                vreg(r, ?&r0),
                if r0.class() == register_class::Q;

            // emit jmps
            emit(jmp, CodegenFn(box move |ops| dynasm!(ops ;jmp Rq(r0.num())))) <--
                edge(e, ?Some(c), ?Some(jmp), 0, r), pattern(jmp, Pattern::RegJmp, _),
                vreg(r, ?&r0),
                if r0.class() == register_class::Q;

            // emit movs
            emit(mov, CodegenFn(box |ops| () )) <--
                pattern(mov, Pattern::MoveRegReg, _),
                edge(e1, _, Some(*mov), _, vr_in),
                edge(e2, Some(*mov), _, _, vr_out),
                vreg(vr_in, ?&r_in),
                vreg(vr_out, ?&r_out),
                if r_in == r_out;

            emit(mov, CodegenFn(box move |ops| dynasm!(ops; mov Rq(r_out.num()), Rq(r_in.num()) ))) <--
                pattern(mov, Pattern::MoveRegReg, _),
                edge(e1, _, Some(*mov), _, vr_in),
                edge(e2, Some(*mov), _, _, vr_out),
                vreg(vr_in, ?&r_in),
                vreg(vr_out, ?&r_out),
                if r_in != r_out && r_in.class() == register_class::Q && r_out.class() == register_class::Q;

            // emit stack load
            // XXX: this should probably do something else!
            emit(load, { if let StateVariant::Stack(ss) = states[*state as usize].variant {
                CodegenFn(box move |ops|
                    dynasm!(ops; mov Rq(r_out.num()), QWORD [rsp+(ss*8).try_into().unwrap()]))
            } else { panic!() } }) <--
                pattern(load, Pattern::LoadStackReg, _),
                state(load, ?state),
                edge(e1, Some(*load), _, _, vr_out),
                vreg(vr_out, ?&r_out);

            emit(store, { if let StateVariant::Stack(ss) = states[*state as usize].variant {
                CodegenFn(box move |ops|
                    dynasm!(ops; mov QWORD [rsp+(ss*8).try_into().unwrap()], Rq(r_in.num())))
            } else { panic!() } }) <--
                pattern(store, Pattern::StoreStackReg, _),
                state(store, ?state),
                edge(e1, _, Some(*store), 1, vr_in),
                vreg(vr_in, ?&r_in);
        };
        binder.emit.sort_by(|a, b| nodes[a.0].time.cmp(&nodes[b.0].time));

        use std::collections::HashSet;
        use std::ops::BitAnd;
        let emitted = binder.emit.iter().map(|emit| emit.0).collect::<HashSet<_>>();
        let roots = binder.pattern.iter().map(|pat| pat.0).collect::<HashSet<_>>();
        let missing = roots.difference(&emitted).collect::<Vec<_>>();
        if missing.len() != 0 {
            for miss in missing {
                println!("{:?} missing {:?}", miss, nodes[*miss].variant.ro(token));
                println!("pattern {:?}", binder.pattern.iter().filter(|e| e.0 == *miss).next().unwrap().1);
            }
            panic!();
        }

        for (root, emit) in binder.emit {
            println!("{}, {}  - {:?}", clock, nodes[root].time, nodes[root].variant.ro(token));
            emit.0(ops);
            //pat.codegen(root, &binder, ops);
            //assert!(clock <= nodes[*root].time, "{} under clock", nodes[*root].time);
            clock = nodes[root].time;
        }
    }
}

struct CodegenFn(Box<dyn FnOnce(&mut Assembler) -> ()>);
impl PartialEq for CodegenFn {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for CodegenFn { }
impl core::hash::Hash for CodegenFn {
    fn hash<H>(&self, hasher: &mut H) where H: core::hash::Hasher {
        use std::borrow::Borrow;
        use core::ffi::c_void;
        //hasher.write_u64(self.0.borrow() as *const dyn FnOnce(&mut Assembler)->() as *const c_void as u64);
        hasher.write_u64(0);
    }
}
impl Clone for CodegenFn {
    fn clone(&self) -> Self {
        CodegenFn(box |op|{panic!("cloned")})
    }
}

