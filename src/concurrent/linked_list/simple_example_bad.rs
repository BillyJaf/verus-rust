#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use verus_state_machines_macros::tokenized_state_machine;
use verus_builtin::*;
use verus_builtin_macros::*;
use std::sync::Arc;
use std::cmp::Ordering;
use vstd::atomic_ghost::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::{pervasive::*, prelude::*, *};
use vstd::cell::pcell;

verus! {

pub struct Node {
    pub data: u32,
    pub next_node: Option<Box<LockedNode>>,
}

struct_with_invariants!{
    pub struct LockedNode {
        pub atomic: AtomicBool<_, Option<pcell::PointsTo<Node>>, _>,
        pub cell: pcell::PCell<Node>,
    }

    pub open spec fn wf(&self) -> bool 
    {
        invariant on atomic with (cell) is (v: bool, g: Option<pcell::PointsTo<Node>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    (points_to.value().next_node.is_some() ==> 
                        points_to.value().next_node.unwrap().wf()) 
                }
            }
        }
    }
}

impl LockedNode {
    fn new(data: u32, next_node: Option<Box<LockedNode>>) -> (new_node: Self)
        requires
            next_node.is_some() ==> next_node.unwrap().wf()
        ensures 
            new_node.wf()
    {   
        let node = Node { data, next_node };
        let (cell, Tracked(perm)) = pcell::PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell)), false, Tracked(Some(perm)));
        Self { atomic, cell }
    }
}

fn main() {
}
}