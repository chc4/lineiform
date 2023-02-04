//#![deny(unreachable_code)]

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
use dynasmrt::{dynasm, DynasmApi, DynasmLabelApi};

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
pub struct VReg(u16);

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[repr(usize)]
pub enum Pattern {
    Constant8(VReg) = 0usize,
    Constant16(VReg),
    Constant32(VReg),
    Constant64(VReg),
    Constant16Jmp,
    BrFuse,
    BrEntry(u16),
    BrCall(u16 /* state */),

    BrIf,

    RegJmp(VReg),
    MoveRegReg(VReg, VReg),
    Inc(VReg),
    AddRegConstant8(VReg, i8),
    AddRegConstant16,
    AddRegConstant32,
    AddRegReg(VReg, VReg),
    StoreStackReg(u16, VReg),
    LoadStackReg(u16, VReg),
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


// block layout:
// recursively put all their children in entry, until you hit all the block call edges
// pick a random target block, recursively put all reachable nodes from its parameters in the block
// until you hit block call edges.
// now you have all nodes in blocks, and a cfg of edges between blocks.
// do reverse postorder traversal of the cfg to pick an order of blocks, if you find
// backwards edges to blocks you already visited then you ignore them.
// should probably sink any nodes in entry that don't depend on the function arguments to the
// least common ancestor of all its uses...?
// visit blocks in reverse order, compute timings for all the nodes in it
// then do you just allocate registers for all the vregs using the timing as live ranges...?
// like visit the last block, give it register allocations every time you visit a node
// with a vreg that hasn't already been visited, then put all the blocks with edges to it
// in a list and loop popping from the list, the register map after the end of the block is the
// same reg map, union the hit for the vregs of the br_call arguments with the block parameters,
// then just allocate in the block again.
//
// does this give too long of live ranges? i think you'd want to be able to give two blocks
// that are in parallel and not sequential the same timings instead of sequential ones, so that
// like both sides of an if can use the same live range for registers for spilling. care about that
// once i actually need to optimize shit ig?
// ENTRY
// |  \
// |  A
// |  |
// |  B
// |  /
// TERM
// i think you want to like "stratify" a cfg into levels and then give all the blocks in a level
// the same timings
// wait this is just max(predecessors) again i think. woops.
//
// entry: one = 1; bb0: add a, one; bb1: add b, one;
// one would be placed in entry correctly
//
// i probably want to get rid of the function-level sources and sinks and just have an entry and
// exit block for functions pre-generated, and then the function arity is
// entry[params]->exit[returns] and just validate that exit is empty.
//
// how does constant folding blocks away work? does it just need a way of marking edges in patterns
// as not actually external, so that BrIf -> BrCall(bb0), not_used(bb1) sees bb1 isn't used and
// doesn't count it as needed when doing node timings? this is also needed for all other constant
// folding i think, which might be tedious and easy to mess up.
// the paper this is based off of has the patterns always list their inputs, which is the opposite,
// just the lattice update of (BrIf, [bb0, bb1]) -> (BrCall(bb0), [bb0]) would implicitly drop the bb1 edge and
// cause it to be eliminated instead.
// would need the outgoing(node, count) row to be updated whenever we do a pattern rewrite though
// because nodes would be subsumed by patterns, removing observers - a BrIf->BrCall dropping an
// observation of a block may make it go from 2->1, and now the only observer can fold into a
// BrFuse and elide a jump
//
// if you have entry[A]: C = foo(A); bb0[B]: bar(B, C); [bar,B,C] might be assigned a pattern
// that covers it. i think this isn't a valid constructions, because you should only be able to
// depend on values that have transitively dependencies of your own block parameters, but we'd at
// least want to make a validation pass for it because it sounds easy to accidentally mess up and
// emit.
//
// i think actually *none* of the emit rules should have edge rules, and probably shouldn't even
// have access to the row at all, with all the parameters needed for the emit rules being provided
// as Pattern arguments. otherwise you can't do simplication rewrites of nodes like the
// BrIf->BrCall because they'll be checking hardcoded ports that won't be correct. MovRegReg should
// actually be MovRegReg(vreg, vreg), so that like a Mov+Mov->Mov rewrite that subsumes the second
// one can actually provide the emission with the correct vregs.

use ascent::lattice::constant_propagation::ConstPropagation;
ascent! {
    struct AscentProgram<'a>;
    /// Stage 1
    // Indicated that Edge from nodes A->B is the Nth input of B, which uses Vreg for storage
    relation edge(crate::port::PortEdge, Option<NodeIdx>, Option<NodeIdx>, usize, VReg);
    // Indicates there is a state edge from nodes A->B with stateid
    relation state(crate::port::PortEdge, Option<NodeIdx>, Option<NodeIdx>, Option<usize>, Option<usize>, u16);
    // Indicates the storage of a Vreg is restricted to RegSpec
    relation restricted(VReg, RegSpec);
    // Indicated what kind of operation a node is
    relation kind(NodeIdx, NodeRow);
    // Capture the NodeCell token for query use
    relation token(RefEquality<&'a NodeOwner>);
    // Outgoing degree count for each node
    relation outgoing(NodeIdx, u8);
    // Output the annotations that a node was given
    lattice pattern(NodeIdx, Pattern, Set<NodeIdx>);

    // If we can emit a wider constant as a u8, do
    pattern(n, Pattern::Constant8(*vreg), const_cover) <--
        pattern(n, ?Pattern::Constant64(vreg), const_cover),
        constant(n, value, ?ConstPropagation::Constant(imm)),
        if TryInto::<i8>::try_into(*imm).is_ok();
    //// Constant propogation; a node is a constant if it can be encoded as an N bit
    //// width immediate.
    lattice constant(NodeIdx, u8, ConstPropagation<i64>);

    //constant(n, 8, ConstPropagation::Constant(*imm)) <--
    //    constant(n, _, ?ConstPropagation::Constant(imm)), if TryInto::<i8>::try_into(*imm).is_ok();
    //constant(n, 16, ConstPropagation::Constant(*imm)) <--
    //    constant(n, _, ?ConstPropagation::Constant(imm)), if TryInto::<i16>::try_into(*imm).is_ok();
    //constant(n, 32, ConstPropagation::Constant(*imm)) <--
    //    constant(n, _, ?ConstPropagation::Constant(imm)), if TryInto::<i32>::try_into(*imm).is_ok();
    //constant(n, 64, ConstPropagation::Constant(*imm)) <--
    //    constant(n, _, ?ConstPropagation::Constant(imm)), if TryInto::<i64>::try_into(*imm).is_ok();

    //// Constant patterns
    //pattern(n, Pattern::Constant8, Set::singleton(*n)) <--
    //    constant(n, 8, _);
    //pattern(n, Pattern::Constant16, Set::singleton(*n)) <--
    //    constant(n, 16, _);
    //pattern(n, Pattern::Constant32, Set::singleton(*n)) <--
    //    constant(n, 32, _);
    //pattern(n, Pattern::Constant64, Set::singleton(*n)) <--
    //    constant(n, 64, _);

    // Inc patterns
    pattern(n, Pattern::Inc(*r0), Set::singleton(*n)) <--
        edge(_, _, ?Some(n), 0, r0),
        token(?t), kind(n, ?c), if operation(t, c, Operation::Inc);

    // Add patterns
    pattern(n, Pattern::AddRegReg(*left, *right), Set::singleton(*n)) <--
        edge(_, _, ?Some(n), 0, left),
        edge(_, _, Some(*n), 1, right),
        token(?t), kind(n, ?c), if operation(t, c, Operation::Add);

    //pattern(add, Pattern::AddRegConstant8(*left, *c_val as i8), add_cover.clone().join(Set::singleton(*c))) <--
    //    token(?t), kind(add, ?add_kind),
    //    pattern(add, ?Pattern::AddRegReg(left, right), add_cover),
    //    edge(e, ?Some(c), Some(*add), 1, _), constant(c, 8, ?ConstPropagation::Constant(c_val)), outgoing(c, 1);

    // Mov patterns
    // mov reg, _
    pattern(n, Pattern::MoveRegReg(*r1, *r0,), Set::singleton(*n)) <--
        edge(_, _, ?Some(n), 0, r0),
        edge(_, Some(*n), _, _, r1),
        token(?t), kind(n, ?c),
        if variant::<NodeVariant::Move>(t, c);

    // Leave patterns
    // jmp constant
    pattern(jmp, Pattern::RegJmp(*r0), Set::singleton(*jmp)) <--
        edge(_, _, ?Some(jmp), 0, r0),
        token(?t), kind(jmp, ?jmp_kind),
        if variant::<NodeVariant::Leave>(t, jmp_kind);

    // Store_ss pattern
    pattern(store, Pattern::StoreStackReg(*state, *r0), Set::singleton(*store)) <--
        state(_, _, ?Some(store), _, Some(0), state),
        edge(_, _, ?Some(n), 1, r0),
        token(?t), kind(store, ?store_kind),
        if operation(t, store_kind, Operation::StoreStack);

    pattern(load, Pattern::LoadStackReg(*state, *r0), Set::singleton(*load)) <--
        state(_, _, ?Some(store), _, Some(0), state),
        edge(_, ?Some(n), _, 0, r0),
        token(?t), kind(load, ?load_kind),
        if operation(t, load_kind, Operation::LoadStack);

    // basic block patterns
    // jmp constant
    // br_if with constant selector
    pattern(jmp, Pattern::BrEntry(*bb), Set::singleton(*jmp)) <--
        state(_, ?Some(jmp), _, Some(0), _, bb),
        token(?t), kind(jmp, ?jmp_kind),
        if variant::<NodeVariant::BrEntry>(t, jmp_kind);
    pattern(jmp, Pattern::BrCall(*block), Set::singleton(*jmp)) <--
        token(?t), kind(jmp, ?jmp_kind),
        state(e, _, Some(*jmp), _, Some(0), block),
        if variant::<NodeVariant::BrCall>(t, jmp_kind);

    // branch patterns
    // br_if
    pattern(bif, Pattern::BrIf, Set::singleton(*bif)) <--
        token(?t), kind(bif, ?bif_kind),
        if variant::<NodeVariant::BrIf>(t, bif_kind);
    // br_if with a selector that is never observed otherwise; that means we can
    // avoid materializing the value in a register.
    //pattern(bif, Pattern::BrIfDirectly, Set::singleton(*bif).join(Set::singleton(*selector))) <--
    //    token(?t), kind(bif, ?bif_kind),
    //    edge(e, ?Some(selector), Some(*bif), 0, _), outgoing(selector, 1),
    //    if variant::<NodeVariant::BrIf>(t, bif_kind);

    // br_if with constant selector
    // it doesn't cover the constant, because we emit the direct branch even if there
    // is another use of the selector.
    pattern(bif, Pattern::BrCall(*bb0), Set::singleton(*bif)) <--
        token(?t), kind(bif, ?bif_kind),
        edge(e, ?Some(c), Some(*bif), 0, _), constant(c, _, ConstPropagation::Constant(0)),
        state(_, _, Some(*bif), _, Some(1), bb0),
        if variant::<NodeVariant::BrIf>(t, bif_kind);
    pattern(bif, Pattern::BrCall(*bb1), Set::singleton(*bif)) <--
        token(?t), kind(bif, ?bif_kind),
        state(_, _, Some(*bif), _, Some(2), bb1),
        edge(e, ?Some(c), Some(*bif), 0, _), constant(c, _, ConstPropagation::Constant(1)),
        if variant::<NodeVariant::BrIf>(t, bif_kind);
    // patterns that we can fold the selector entirely, and are on the only observer of it.
    pattern(bif, Pattern::BrCall(*bb0), Set::singleton(*bif).join(c_cover.clone())) <--
        token(?t), kind(bif, ?bif_kind),
        pattern(c, const_pattern, c_cover),
        edge(e, Some(*c), Some(*bif), 0, _), constant(c, _, ConstPropagation::Constant(0)),
        state(_, _, Some(*bif), _, Some(1), bb0),
        if variant::<NodeVariant::BrIf>(t, bif_kind),
        if let (Pattern::Constant8(vreg)
            |Pattern::Constant16(vreg)
            |Pattern::Constant32(vreg)
            |Pattern::Constant64(vreg)) = const_pattern;

    pattern(bif, Pattern::BrCall(*bb1), Set::singleton(*bif).join(c_cover.clone())) <--
        token(?t), kind(bif, ?bif_kind),
        pattern(c, const_pattern, c_cover),
        edge(e, Some(*c), Some(*bif), 0, _), constant(c, _, ConstPropagation::Constant(1)),
        state(_, _, Some(*bif), _, Some(2), bb1),
        if variant::<NodeVariant::BrIf>(t, bif_kind),
        if let (Pattern::Constant8(vreg)
            |Pattern::Constant16(vreg)
            |Pattern::Constant32(vreg)
            |Pattern::Constant64(vreg)) = const_pattern;

    // fused brcall+entry with no other brcalls
    pattern(call, Pattern::BrFuse, call_cover.clone().join(entry_cover.clone())) <--
        pattern(call, ?Pattern::BrCall(block), call_cover),
        pattern(entry, Pattern::BrEntry(*block), entry_cover),
        // this is backwards due to Region::create_dependencies creating inverse dependencies
        // this can't mention the port that the call uses, because it could be from a constant
        // br_if
        state(e, Some(*entry), Some(*call), Some(0), _, block),
        agg incoming = ascent::aggregators::count() in state(_, Some(*entry), _, Some(0), _, block),
        if incoming == 1;
}

impl PatternManager {
    fn edges_row(&self, region: &Region) -> (
        Vec<(crate::port::PortEdge, Option<NodeIdx>, Option<NodeIdx>, usize, VReg)>,
        Vec<(crate::port::PortEdge, Option<NodeIdx>, Option<NodeIdx>, Option<usize>, Option<usize>, u16)>
    ) {
        let Region { nodes, ports, sinks, .. } = region;
        let mut edges = Vec::with_capacity(nodes.edge_count());
        let mut states = Vec::new();
        // hook up all the edges to node inputs. this includes from the region sources
        for local in nodes.node_indices() {
            for (i, p) in nodes[local].inputs.iter().enumerate() {
                let vreg: Result<VReg, u16> = match ports[*p].storage{
                    OptionalStorage(Some(Storage::Immaterial(Some(state)))) => Err(state),
                    OptionalStorage(Some(Storage::Virtual(vreg))) => Ok(VReg(vreg)),
                    _ => panic!(),
                };
                for e in ports.edges_directed(*p, Direction::Outgoing) {
                    let neighbor_port = &ports[e.target()];
                    match vreg {
                        Ok(vreg) => {
                            let new_edge = (e.id(), neighbor_port.node, Some(local), i, vreg);
                            println!("new edge {:?}", new_edge);
                            edges.push(new_edge);
                        },
                        Err(state) => {
                            let output_idx = neighbor_port.node.map(|node| {
                                nodes[node].outputs.iter().enumerate().find(|(i, p)| **p == e.target())
                                .unwrap().0
                            });
                            let new_state = (e.id(), neighbor_port.node, Some(local), output_idx, Some(i), state);
                            println!("new state {:?}", new_state);
                            states.push(new_state);
                        },
                    }
                }
            }
        }
        // we also hook up edges to the region sinks
        for (i, output) in sinks.iter().enumerate() {
            let vreg: VReg = match ports[*output].storage{
                OptionalStorage(Some(Storage::Immaterial(state))) => continue,
                OptionalStorage(Some(Storage::Virtual(vreg))) => VReg(vreg),
                _ => panic!(),
            };
            for e in ports.edges_directed(*output, Direction::Outgoing) {
                let neighbor_port = &ports[e.target()];
                let new_edge = (e.id(), neighbor_port.node, None, i, vreg);
                println!("new sink edge {:?}", new_edge);
                edges.push(new_edge);
             }
        }
        (edges, states)
    }

    pub fn run(&mut self, token: &NodeOwner, region: &mut Region, virt_map: &mut VirtualRegisterMap) {
        let (mut edges, states) = self.edges_row(region);
        let Region { nodes, ports, sinks, .. } = region;


        use petgraph::visit::Walker;
        let mut dfs_space = DfsSpace::new(&*nodes);
        let mut visit_nodes: Vec<_> = petgraph::algo::toposort(&*nodes, Some(&mut dfs_space)).unwrap();
        let toposorted = visit_nodes.clone().drain(..).enumerate().map(|(i, n)| (n, i)).collect::<HashMap<_,_>>();
        let visit_nodes = visit_nodes.drain(..).map(|n| (n, RefEquality(nodes[n].variant.clone()))).collect();

        let constants = nodes.node_indices().filter_map(|n| {
            nodes[n].as_variant::<NodeVariant::Constant>(token).and_then(|c| {
                let Some(Storage::Virtual(vreg)) = ports[nodes[n].sinks()[0]].storage.0 else { return None };
                Some((n, Pattern::Constant64(VReg(vreg)), Set::singleton(n)))
            })
                //(n, 64, ConstPropagation::Constant(c.0 as i64)))
        }).collect::<Vec<_>>();
        let outgoing = nodes.node_indices().map(|n| {
            (n, nodes.edges(n).count().try_into().unwrap())
        }).collect::<Vec<_>>();
        //dbg!(constants.clone());
        let mut ascent: AscentProgram::<'_> = AscentProgram::default();
        ascent.pattern = constants; // feed in the constants as initial patterns
        ascent.token = vec![(RefEquality(token),)];
        ascent.kind = visit_nodes;
        ascent.edge = edges;
        ascent.state = states;
        ascent.restricted = virt_map.iter().flat_map(|(i,v)| v.backing.map(|back| ((VReg(*i as u16),back)))).collect::<Vec<_>>();
        //ascent.constant = constants;
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
            //dbg!(root, pat);
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
            relation edge(PortEdge, Option<NodeIdx>, Option<NodeIdx>, usize, VReg) = ascent.edge;
            relation restricted(VReg, RegSpec) = ascent.restricted;

            // given a pattern and a root we can have a Pattern::variables function
            // that populates variables required as needed.
            //relation variables(NodeIdx, NodeIdx);

            // We need all the external edges between patterns, which must be
            // allocated vregs.
            relation external(PortEdge, Option<NodeIdx>, Option<NodeIdx>, usize, VReg);

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

        let mut observed = BTreeSet::<VReg>::new();
        for external in phase2.external {
            println!("external {:?}", external);
            observed.insert(external.4);
        }

        virt_map.retain(|k, v| observed.contains(&VReg(*k as u16)));
        self.roots = phase2.root;
        self.toposorted = toposorted;
    }

    pub fn codegen<'a>(&mut self, token: &NodeOwner, region: &mut Region, ops: &mut Assembler) {
        let (mut edges, states_row) = self.edges_row(region);
        let Region { nodes, ports, sinks, states, .. } = region;
        let states_map = states;
        let states = states_row;

        let constants = nodes.node_indices().flat_map(|n| {
            (nodes[n].ro(token).as_ref() as &dyn Any).downcast_ref::<NodeVariant::Constant>().map(|c| (n, c.0))
        }).collect::<Vec<_>>();

        let vregs = self.virt_map.iter().map(|(i, vr)| (VReg(*i as u16), vr.backing.unwrap())).collect::<Vec<(_,_)>>();
        use crate::petgraph::visit::IntoEdgeReferences;
        // this is messy and state edges should probably work differently
        //let states_row = ports.edge_references().flat_map(|e| {
        //    if let OptionalStorage(Some(Storage::Immaterial(Some(state)))) = ports[e.target()].storage {
        //        ports[e.target()].node.map(|n| Some((n, state))).iter()
        //            //.chain(ports[e.source()].node.map(|n| Some((n, state))).iter())
        //            .flatten().map(|(n, state)| (n, state, nodes[n].sources().iter().find(|)).map(Clone::clone).collect::<Vec<_>>()
        //    } else {
        //        vec![]
        //    }
        //}).collect::<Vec<_>>();

        let mut clock = Timestamp::new();
        self.roots.sort_by(|a, b| nodes[a.0].time.cmp(&nodes[b.0].time));
        let mut blocks = HashMap::new();
        let mut binder = ascent_run! {
            struct VarBinder;
             // Indicated that Edge from A->B is the Nth input of B, which uses Vreg for storage
            //relation edge(crate::port::PortEdge, Option<NodeIdx>, Option<NodeIdx>, usize, VReg) =
            //    edges;
            // The physical register used for each vreg
            relation vreg(VReg, RegSpec) = vregs;
            // Indicates that Edge from A->B is the Nth output of A and Mth input of B, and uses State
            //relation state(crate::port::PortEdge, Option<NodeIdx>, Option<NodeIdx>, Option<usize>, Option<usize>, u16) =
            //    states;
            // Nodes that are constant values
            relation constant(NodeIdx, isize) = constants;
            // Output the annotations that a node was given
            lattice pattern(NodeIdx, Pattern, Set<NodeIdx>) = self.roots.clone();
            relation emit(NodeIdx, CodegenFn);

            // emit constants
            emit(c, CodegenFn(box move |ops| dynasm!(ops ;mov Rq(r0.num()), QWORD imm as i64))) <--
                //edge(e, ?Some(c), _, _, r),
                pattern(c, const_pattern, _),
                if let (Pattern::Constant8(vreg)
                    |Pattern::Constant16(vreg)
                    |Pattern::Constant32(vreg)
                    |Pattern::Constant64(vreg)) = const_pattern,
                vreg(vreg, ?&r0),
                constant(c, ?&imm) if { println!("constant with r0 class {:?}", r0.class()); r0.class() } == register_class::Q;

            // emit adds
            emit(add, CodegenFn(box move |ops| dynasm!(ops; add Rq(r_out.num()), Rq(r_in.num()) ))) <--
                pattern(add, ?Pattern::AddRegReg(vr_out, vr_in), _),
                vreg(vr_out, ?&r_out),
                vreg(vr_in, ?&r_in),
                //edge(_, _, Some(*add), 0, vr_out_),
                //edge(_, _, Some(*add), 1, vr_in_),
                if r_in.class() == register_class::Q && r_out.class() == register_class::Q;
                //if { dbg!(vr_out_, vr_out, vr_in_, vr_in); true };

            //emit(add, { let imm = *imm; CodegenFn(box move |ops| dynasm!(ops; add Rq(r_out.num()), BYTE imm as i8 ))}) <--
            //    pattern(add, ?Pattern::AddRegConstant8(vr_out, imm), _),
            //    vreg(vr_out, ?&r_out),
            //    if r_out.class() == register_class::Q;

            // emit inc
            emit(inc, CodegenFn(box move |ops| dynasm!(ops ;inc Rq(r0.num())))) <--
                pattern(inc, ?Pattern::Inc(r), _),
                vreg(r, ?&r0),
                if r0.class() == register_class::Q;

            // emit jmps
            emit(jmp, CodegenFn(box move |ops| dynasm!(ops ;jmp Rq(r0.num())))) <--
                pattern(jmp, ?Pattern::RegJmp(r), _),
                vreg(r, ?&r0),
                if r0.class() == register_class::Q;

            // emit basic blocks
            emit(bentry, { let bb = *bb as usize;
                let label = *blocks.entry(bb).or_insert_with(|| ops.new_dynamic_label() );
                CodegenFn(box move |ops| {
                    dynasm!(ops ; => label)
                })})  <--
                pattern(bentry, ?Pattern::BrEntry(bb), _);
            // emit jumps to basic blocks
            emit(bcall, { let bb = *bb as usize;
                let label = blocks[&bb];
                CodegenFn(box move |ops| {
                    dynasm!(ops ; jmp => label)
                })})  <--
            pattern(bcall, ?Pattern::BrCall(bb), _);
            // emit fused brcall+entry
            emit(bfused, CodegenFn(box |ops| () )) <--
                pattern(bfused, Pattern::BrFuse, _);

            //// emit br_if with materialized selector
            //emit(bif, { let bb = *state as usize;
            //    let label = blocks[&bb];
            //    CodegenFn(box move |ops| {
            //        dynasm!(ops
            //            ; test Rq(r0.num()), 0
            //            ; jnz b1
            //            ; jmp b0
            //        )
            //    })
            //}) <--
            //pattern(bif, Pattern::BrIf, _),
            //state(bif, ?state),
            //if matches!(states[*state as usize].variant, StateVariant::Block(_));
            //    }
            //emit(bif, { let bb0 = *bb0 as usize;
            //    let bb0 = blocks[&bb0];
            //    let bb1 = *bb1 as usize;
            //    let bb1 = blocks[&bb1];
            //    dbg!(bb0, bb1, vr_selector, r_selector);
            //    unimplemented!()
            //}) <--
            //pattern(bif, Pattern::BrIfDirectly, _),
            //edge(e0, _, Some(*bif), 0, vr_selector),
            //vreg(vr_selector, ?&r_selector),
            //state(e1, _, Some(*bif), _, Some(1), bb0),
            //state(e2, _, Some(*bif), _, Some(2), bb1);

            // emit movs
            emit(mov, CodegenFn(box |ops| () )) <--
                pattern(mov, ?Pattern::MoveRegReg(vr_out, vr_in), _),
                vreg(vr_in, ?&r_in),
                vreg(vr_out, ?&r_out),
                if r_in == r_out;

            emit(mov, CodegenFn(box move |ops| dynasm!(ops; mov Rq(r_out.num()), Rq(r_in.num()) ))) <--
                pattern(mov, ?Pattern::MoveRegReg(vr_out, vr_in), _),
                vreg(vr_in, ?&r_in),
                vreg(vr_out, ?&r_out),
                if r_in != r_out && r_in.class() == register_class::Q && r_out.class() == register_class::Q;

            // emit stack load
            // XXX: this should probably do something else!
            emit(load, { if let StateVariant::Stack(ss) = states_map[*state as usize].variant {
                CodegenFn(box move |ops|
                    dynasm!(ops; mov Rq(r_out.num()), QWORD [rsp+(ss*8).try_into().unwrap()]))
            } else { panic!() } }) <--
                pattern(load, ?Pattern::LoadStackReg(state, vr_out), _),
                vreg(vr_out, ?&r_out);

            emit(store, { if let StateVariant::Stack(ss) = states_map[*state as usize].variant {
                CodegenFn(box move |ops|
                    dynasm!(ops; mov QWORD [rsp+(ss*8).try_into().unwrap()], Rq(r_in.num())))
            } else { panic!() } }) <--
                pattern(store, ?Pattern::StoreStackReg(state, vr_in), _),
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

