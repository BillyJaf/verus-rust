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
    pub next_node: Option<Arc<Node>>,
}

struct_with_invariants!{
    pub struct LockedNode {
        pub atomic: AtomicBool<_, Option<pcell::PointsTo<Node>>, _>,
        pub cell: pcell::PCell<Node>,
    }

    spec fn wf(&self) -> bool 
    {
        invariant on atomic with (cell) is (v: bool, g: Option<pcell::PointsTo<Node>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id()
                }
            }
        }
    }
}

impl LockedNode {
    fn new(data: u32) -> (new_node: Self)
        ensures 
            new_node.wf(),
    {
        let node = Node { data, next_node: None };
        let (cell, Tracked(cell_perm)) = pcell::PCell::new(node);
        let atomic = AtomicBool::new(Ghost(cell), false, Tracked(Some(cell_perm)));
        Self { atomic, cell }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<pcell::PointsTo<Node>>)
        requires 
            self.wf(),
        ensures 
            points_to@.id() == self.cell.id(),
            self.wf()
    {
        loop
            invariant self.wf(),
        {
            let tracked mut points_to_opt = None;
            let res = atomic_with_ghost!(
                &self.atomic => compare_exchange(false, true);
                ghost points_to_inv => {
                    tracked_swap(&mut points_to_opt, &mut points_to_inv);
                }
            );
            if res.is_ok() {
                return Tracked(points_to_opt.tracked_unwrap());
            }
        }
    }

    fn release_lock(&self, points_to: Tracked<pcell::PointsTo<Node>>)
        requires
            self.wf(),
            points_to@.id() == self.cell.id(),
        ensures
            self.wf()
    {
        atomic_with_ghost!(
            &self.atomic => store(false);
            ghost points_to_inv => {
                points_to_inv = Some(points_to.get());
            }
        );
    }
}

pub closed spec fn contains(node: &LockedNode) -> bool
{
    let mut locked_node_perm = node.acquire_lock();
    // let mut dummy_node_view = locked_dummy_node.cell.borrow(Tracked(dummy_node_perm.borrow_mut()));
    return true;
}

fn main() {

}
}