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


pub enum NodeData {
    Dummy,
    Node(u32)
}

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(map)]
            pub nodes: Map<NodeData, Option<NodeData>>,

            #[sharding(set)]
            pub lock_tokens: Set<NodeData>,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            // The dummy node always exists
            &&& self.nodes.dom().contains(NodeData::Dummy)
            // The dummy node points to the smallest element or nothing
            &&& self.nodes[NodeData::Dummy] == None::<NodeData> || 
                (
                    exists |i: u32| #![auto] 
                        self.nodes[NodeData::Dummy] == Some(NodeData::Node(i)) &&
                        forall |j: u32| #![auto] self.nodes.dom().contains(NodeData::Node(j)) ==> i <= j
                    
                )
            // Everything else is sorted with unique data
            &&& (
                    forall |i: u32| #![auto] self.nodes.dom().contains(NodeData::Node(i)) ==> 
                        (
                            self.nodes[NodeData::Node(i)] == None::<NodeData> ||
                            (exists |j: u32| #![auto] self.nodes[NodeData::Node(i)] == Some(NodeData::Node(j)) && i < j)
                        )
                )
            // Every map entry (except for the dummy) is pointed to by another entry
            &&& (forall |i: u32| #![auto] self.nodes.dom().contains(NodeData::Node(i)) ==>
                    (
                        self.nodes[NodeData::Dummy] == Some(NodeData::Node(i)) ||
                        (exists |j: u32| #![auto] self.nodes[NodeData::Node(j)] == Some(NodeData::Node(i)) && j < i)
                    )
                )
        }

        init!{
            initialize()
            {
                init nodes = Map::empty().insert(NodeData::Dummy, None::<NodeData>);
                init lock_tokens = Set::empty().insert(NodeData::Dummy);
            }
        }

        // transition!{
        //     insert_element() {
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

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { 
        }

        // #[inductive(tr_inc)]
        // fn tr_inc_preserves(pre: Self, post: Self) {
        // }
    }
}

pub struct Node {
    pub data: NodeData,
    pub next_node: Option<Box<LockedNode>>,
    pub lock_token: Tracked<machine::lock_tokens>,
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
                    points_to.is_init() &&
                    points_to.value().lock_token@.instance_id() == instance@.id() &&
                    points_to.value().lock_token@.element() == points_to.value().data
                }
            }
        }
    }
}

impl LockedNode {
    fn start(dummy_lock_token: Tracked<machine::lock_tokens>, instance: Tracked<machine::Instance>) -> (dummy_node: Self)
        requires
            dummy_lock_token@.instance_id() == instance@.id(),
            dummy_lock_token@.element() == NodeData::Dummy
        ensures 
            dummy_node.wf(),
            dummy_node.instance == instance,
    {
        let node = Node { data: NodeData::Dummy, next_node: None::<Box<LockedNode>>, lock_token: dummy_lock_token };
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance }
    }

    fn new(node: Node, lock_token: Tracked<machine::lock_tokens>, instance: Tracked<machine::Instance>) -> (normal_node: Self)
        requires
            lock_token@.instance_id() == instance@.id(),
            node.data == lock_token@.element(),
            node.next_node == None::<Box<LockedNode>>,
        ensures 
            normal_node.wf(),
            normal_node.instance == instance,
    {
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance}
    }

    // fn acquire_lock(&self) -> (points_to: Tracked<cell::PointsTo<Node>>)
    //     requires 
    //         self.wf(),
    //     ensures 
    //         points_to@.id() == self.cell.id() &&
    //         points_to@.is_init() &&
    //         points_to@.value().data == self.data_view &&
    //         points_to@.value().ghost_map_entry@.instance_id() == self.instance@.id() &&
    //         points_to@.value().ghost_map_entry@.key() == points_to@.value().data &&
    //         (points_to@.value().ghost_map_entry@.value().is_none() <==> points_to@.value().next_node.is_none()) &&
    //         (points_to@.value().ghost_map_entry@.value().is_some() ==> 
    //         points_to@.value().next_node.unwrap().data_view == points_to@.value().ghost_map_entry@.value().unwrap()) &&
    //         self.wf(),
    // {
    //     loop
    //         invariant self.wf(),
    //     {
    //         let tracked mut points_to_opt = None;
    //         let res = atomic_with_ghost!(
    //             &self.atomic => compare_exchange(false, true);
    //             ghost points_to_inv => {
    //                 tracked_swap(&mut points_to_opt, &mut points_to_inv);
    //             }
    //         );
    //         if res.is_ok() {
    //             return Tracked(points_to_opt.tracked_unwrap());
    //         }
    //     }
    // }

    // fn release_lock(&self, points_to: Tracked<cell::PointsTo<Node>>)
    //     requires
    //         self.wf() &&
    //         points_to@.id() == self.cell.id() &&
    //         points_to@.is_init() &&
    //         points_to@.value().data == self.data_view &&
    //         points_to@.value().ghost_map_entry@.instance_id() == self.instance@.id() &&
    //         points_to@.value().ghost_map_entry@.key() == points_to@.value().data &&
    //         (points_to@.value().ghost_map_entry@.value().is_none() <==> points_to@.value().next_node.is_none()) &&
    //         (points_to@.value().ghost_map_entry@.value().is_some() ==> 
    //         points_to@.value().next_node.unwrap().data_view == points_to@.value().ghost_map_entry@.value().unwrap())
    //     ensures
    //         self.wf()
    // {
    //     atomic_with_ghost!(
    //         &self.atomic => store(false);
    //         ghost points_to_inv => {
    //             points_to_inv = Some(points_to.get());
    //         }
    //     );
    // }
}

fn main() {
    let tracked (
        Tracked(instance),
        Tracked(nodes),
        Tracked(lock_tokens),
    ) = machine::Instance::initialize();

    let tracked dummy_lock_token = lock_tokens.remove(NodeData::Dummy);
    let linked_list = LockedNode::start(Tracked(dummy_lock_token), Tracked(instance.clone()));
}
}