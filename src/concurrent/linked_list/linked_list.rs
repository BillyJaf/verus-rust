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

pub ghost struct GhostNodeState {
    pub data: u32,
    pub next_node_id: Option<nat>
}

tokenized_state_machine!{
    machine {
        fields {
            // Map<node_id, node>
            #[sharding(map)]
            pub nodes: Map<nat, GhostNodeState>,

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
    pub data: u32,
    pub id: nat,
    pub next_node_id: Option<nat>,
    pub next_node: Option<Box<LockedNode>>,
    pub ghost_map_entry: Tracked<machine::nodes>,
}

struct_with_invariants!{
    pub struct LockedNode {
        pub atomic: AtomicBool<_, Option<cell::PointsTo<Node>>, _>,
        pub cell: PCell<Node>,
        pub instance: Tracked<machine::Instance>,
        pub id: nat,
    }

    spec fn wf(&self) -> bool {
        invariant on atomic with (cell, instance, id) is (v: bool, g: Option<cell::PointsTo<Node>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    points_to.is_init() &&
                    points_to.value().id == id &&
                    points_to.value().ghost_map_entry@.instance_id() == instance@.id() &&
                    points_to.value().ghost_map_entry@.key() == points_to.value().id &&
                    points_to.value().ghost_map_entry@.value() == GhostNodeState { next_node_id: points_to.value().next_node_id, data: points_to.value().data } &&
                    (points_to.value().next_node_id.is_none() <==> points_to.value().next_node.is_none()) &&
                    (points_to.value().next_node_id.is_some() ==> points_to.value().next_node.unwrap().id == points_to.value().next_node_id.unwrap())
                }
            }
        }
    }
}

impl LockedNode {
    fn new(node: Node, instance: Tracked<machine::Instance>) -> (linked_list: Self)
        requires
            node.ghost_map_entry@.instance_id() == instance@.id(),
            node.ghost_map_entry@.key() == node.id,
            node.next_node_id == None::<nat>,
            node.next_node == None::<Box<LockedNode>>,
            node.ghost_map_entry@.value() == (GhostNodeState { next_node_id: None, data: node.data })
        ensures 
            linked_list.wf(),
            linked_list.instance == instance,
    {
        let id = node.id;
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance, perm.value().id)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance, id: id }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<cell::PointsTo<Node>>)
        requires 
            self.wf(),
        ensures 
            points_to@.id() == self.cell.id() &&
            points_to@.is_init() &&
            points_to@.value().id == self.id &&
            points_to@.value().ghost_map_entry@.instance_id() == self.instance@.id() &&
            points_to@.value().ghost_map_entry@.key() == points_to@.value().id &&
            points_to@.value().ghost_map_entry@.value() == (GhostNodeState { next_node_id: points_to@.value().next_node_id, data: points_to@.value().data }) &&
            (points_to@.value().next_node_id.is_none() <==> points_to@.value().next_node.is_none()) &&
            (points_to@.value().next_node_id.is_some() ==> points_to@.value().next_node.unwrap().id == points_to@.value().next_node_id.unwrap()) &&
            self.wf(),
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

    fn release_lock(&self, points_to: Tracked<cell::PointsTo<Node>>)
        requires
            self.wf(),
            points_to@.id() == self.cell.id() &&
            points_to@.is_init() &&
            points_to@.value().id == self.id &&
            points_to@.value().ghost_map_entry@.instance_id() == self.instance@.id() &&
            points_to@.value().ghost_map_entry@.key() == points_to@.value().id &&
            points_to@.value().ghost_map_entry@.value() == (GhostNodeState { next_node_id: points_to@.value().next_node_id, data: points_to@.value().data }) &&
            (points_to@.value().next_node_id.is_none() <==> points_to@.value().next_node.is_none()) &&
            (points_to@.value().next_node_id.is_some() ==> points_to@.value().next_node.unwrap().id == points_to@.value().next_node_id.unwrap())
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
}