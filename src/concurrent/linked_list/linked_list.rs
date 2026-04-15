#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use verus_state_machines_macros::tokenized_state_machine;
use verus_builtin::*;
use verus_builtin_macros::*;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::{pervasive::*, prelude::*, *};
use vstd::cell::*;

verus! {

tokenized_state_machine!{
    machine {
        fields {
            // Map<node_id, node>
            #[sharding(map)]
            pub nodes: Map<nat, Node>,

            #[sharding(map)]
            pub next_nodes: Map<nat, Option<nat>>,

            #[sharding(constant)]
            pub dummy_id: nat,
        }

        // #[invariant]
        // pub fn main_inv(&self) -> bool {
        //     self.counter == self.stamped_tickets
        //     && self.stamped_tickets + self.unstamped_tickets == self.num_threads
        // }

        // init!{
        //     initialize(num_threads: nat) {
        //         init num_threads = num_threads;
        //         init counter = 0;
        //         init unstamped_tickets = num_threads;
        //         init stamped_tickets = 0;
        //     }
        // }

        // transition!{
        //     tr_inc() {
        //         // Equivalent to:
        //         //    require(pre.unstamped_tickets >= 1);
        //         //    update unstampted_tickets = pre.unstamped_tickets - 1
        //         // (In any `remove` statement, the `>=` condition is always implicit.)
        //         remove unstamped_tickets -= (1);

        //         // Equivalent to:
        //         //    update stamped_tickets = pre.stamped_tickets + 1
        //         add stamped_tickets += (1);

        //         // These still use ordinary 'update' syntax, because `pre.counter`
        //         // uses the `variable` sharding strategy.
        //         assert(pre.counter < pre.num_threads);
        //         update counter = pre.counter + 1;
        //     }
        // }

        // property!{
        //     finalize() {
        //         // Equivalent to:
        //         //    require(pre.unstamped_tickets >= pre.num_threads);
        //         have stamped_tickets >= (pre.num_threads);

        //         assert(pre.counter == pre.num_threads);
        //     }
        // }

        // #[inductive(initialize)]
        // fn initialize_inductive(post: Self, num_threads: nat) { }

        // #[inductive(tr_inc)]
        // fn tr_inc_preserves(pre: Self, post: Self) {
        // }
    }
}

pub struct Node {
    pub id: u32,
    pub next_id: Option<u32>,
    pub data: u32,
    // pub ghost_nodes: Tracked<machine::counter>,
    // pub ghost_next_nodes: 
}

struct_with_invariants!{
    pub struct LockedNode {
        pub atomic: AtomicBool<_, Option<cell::PointsTo<Node>>, _>,
        pub cell: PCell<Node>,
        pub instance: Tracked<machine::Instance>,
    }

    spec fn wf(&self) -> bool {
        invariant on atomic with (cell, instance) is (v: bool, g: Option<cell::PointsTo<Node>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    points_to.is_init()
                    // points_to.value().ghost_token@.instance_id() == instance@.id() &&
                    // points_to.value().ghost_token@.value() == points_to.value().val as int
                }
            }
        }
    }
}
}