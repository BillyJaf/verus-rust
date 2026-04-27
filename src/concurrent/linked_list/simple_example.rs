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
use vstd::cell::pcell::*;

verus! {

pub struct Node {
    pub data: u32,
    pub next_node: Option<Box<LockedNode>>,
}

struct_with_invariants!{
    pub struct LockedNode {
        pub atomic: AtomicBool<_, Option<cell::PointsTo<Node>>, _>,
        pub cell: PCell<Node>,
        pub node_id: u32,
    }

    pub open spec fn wf(&self) -> bool 
        decreases self.node_id
    {
        invariant on atomic with (cell, node_id) is (v: bool, g: Option<cell::PointsTo<Node>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    points_to.is_init() &&

                    (node_id == 0 ==> points_to.value().next_node.is_none()) &&

                    (points_to.value().next_node.is_some() ==> 
                        points_to.value().next_node.unwrap().node_id < node_id) && 

                    (points_to.value().next_node.is_some() ==> 
                        points_to.value().next_node.unwrap().wf()) 
                }
            }
        }
    }
}

fn main() {

}
}