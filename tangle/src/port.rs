use petgraph::graph::{NodeIndex, EdgeIndex};
use frunk::prelude::*;
use frunk::hlist::*;
use frunk::*;
use yaxpeax_x86::long_mode::RegSpec;

use core::ops::{Deref};

use crate::node::{NodeIdx};
use crate::time::Timestamp;

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum EdgeVariant {
    State,
    Data,
}

#[derive(Clone, Copy, PartialEq, Debug, Eq)]
pub enum Storage {
    Virtual(u16), // todo: width?
    Physical(RegSpec),
    Immaterial(Option<u16>), // used for constant operands and state edges - does not receive a vreg
}

impl core::fmt::Display for Storage {
    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self {
            Storage::Virtual(v) => write!(fmt, "v{}", v),
            Storage::Physical(p) => write!(fmt, "{}", p),
            Storage::Immaterial(_) => write!(fmt, "imm"),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct OptionalStorage(pub Option<Storage>);
impl core::fmt::Display for OptionalStorage {
    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match self.0 {
            None => write!(fmt, "()"),
            Some(r) => write!(fmt, "{}", r),
        }
    }
}

impl Deref for OptionalStorage {
    type Target = Option<Storage>;
    fn deref(&self) -> &<Self as Deref>::Target {
        &self.0
    }
}



pub mod PortMeta {
    use frunk::HList;
    #[derive(Debug, Clone)]
    pub struct Constant(pub isize);
    #[derive(Debug, Clone)]
    pub struct StackOff(pub i32);
    pub type All = HList![Option<Constant>, Option<StackOff>];
}

#[derive(Clone, Debug)]
pub struct Port {
    pub id: u32,
    pub variant: EdgeVariant,
    pub meta: Option<PortMeta::All>,
    pub storage: OptionalStorage,
    pub time: Option<Timestamp>,
    pub done: bool,
    // The node the port is attached to. If none, it isn't attached to any (e.g. a region
    // source/sink)
    pub node: Option<NodeIdx>,
}
impl Port {
    pub fn new() -> Self {
        let mut guard = PORT_COUNT.lock().unwrap();
        let curr = *guard;
        *guard += 1;
        println!("created port v{:?}", curr);
        Port {
            id: curr,
            variant: EdgeVariant::Data,
            storage: OptionalStorage(None),
            time: None,
            done: false,
            node: None,
            meta: None,
        }
    }

    pub fn set_variant(&mut self, var: EdgeVariant) {
        self.variant = var;
    }

    pub fn set_storage(&mut self, store: Storage) {
        //assert!(self.variant != EdgeVariant::State, "tried to set storage on a state port");
        if let Some(exist) = self.storage.0 {
            if exist != store {
                println!("port already has storage {}, setting to {}", exist, store);
            }
        }
        self.storage = OptionalStorage(Some(store));
    }

    pub fn set_meta<'this, 'a, K, T>(&'this mut self, meta_val: K) where
        PortMeta::All: LiftFrom<Option<K>, T>,
        <PortMeta::All as ToMut<'this>>::Output: Plucker<&'a mut Option<K>, T>,
        Option<K>: core::fmt::Debug,
        'this: 'a,
        K: 'static,
    {
        if let None = self.meta {
            let x: Option<PortMeta::All> = Some(Some(meta_val).lift_into());
            self.meta = x;
        } else {
            self.meta.as_mut().map(|mut m| {
                let (head, _): (&'a mut Option<K>, _) = m.to_mut().pluck();
                *head = Some(meta_val);
            });
        }
    }

    pub fn get_meta<'this, 'a, K, T>(&'this self) -> Option<&'a K> where
        <PortMeta::All as ToRef<'a>>::Output: Plucker<&'this Option<K>, T>,
        K: 'static + Clone,
        'this: 'a,
    {
        self.meta.as_ref().and_then(|m| {
            let (head, _) = m.to_ref().pluck::<&'this Option<K>, _>();
             head.as_ref()
        })
    }

    pub fn set_node(&mut self, n: NodeIdx) {
        self.node = Some(n);
    }
}

pub type PortIdx = NodeIndex;
use std::sync::Mutex;
lazy_static::lazy_static! {
    static ref PORT_COUNT: Mutex<u32> = Mutex::new(0);
}

#[derive(Clone, Debug)]
pub struct Edge {
    pub variant: EdgeVariant,
}
pub type PortEdge = EdgeIndex;


