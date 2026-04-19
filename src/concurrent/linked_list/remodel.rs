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
            #[sharding(variable)]
            pub nodes: Map<NodeData, Option<NodeData>>,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            // The dummy node always exists and is not pointed to by anything
            &&& self.nodes.dom().contains(NodeData::Dummy)
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
            }
        }

        transition!{
            insert_at_dummy_tail(tail_node_perm: cell::PointsTo<DummyNode>, new_tail_node_perm: cell::PointsTo<Node>) {
                // We have actually passed in the dummy node perm and a valid new tail perm:
                require(tail_node_perm.value().data == NodeData::Dummy);
                require(new_tail_node_perm.value().data != NodeData::Dummy);

                // The dummy node must exist in the map by the invariant:
                assert(pre.nodes.dom().contains(tail_node_perm.value().data));

                // The dummy node actually has no next node:
                require(pre.nodes[NodeData::Dummy] == None::<NodeData>);

                // Now we may add our new node:
                update nodes = Map::empty().insert(NodeData::Dummy, Some(new_tail_node_perm.value().data))
                                           .insert(new_tail_node_perm.value().data, None::<NodeData>);
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
        //         assert(real_reflects_state(linked_list, pre.nodes));
        //     }
        // }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { 
        }

        #[inductive(insert_at_dummy_tail)]
        fn insert_at_dummy_tail_inductive(pre: Self, post: Self, tail_node_perm: cell::PointsTo<DummyNode>, new_tail_node_perm: cell::PointsTo<Node>) { 
            assert(new_tail_node_perm.value().data != NodeData::Dummy);
            match new_tail_node_perm.value().data {
                NodeData::Dummy => assert(false),
                NodeData::Node(data) => {
                    assert(post.nodes[NodeData::Dummy] == Some(NodeData::Node(data)));
                    assert(exists |i: u32| #![auto] post.nodes[NodeData::Dummy] == Some(NodeData::Node(i)));
                }
            }
        }

        // #[inductive(tr_inc)]
        // fn tr_inc_preserves(pre: Self, post: Self) {
        // }
    }
}

// pub open spec fn real_reflects_state(head: LockedNode, nodes: Tracked<machine::nodes>) {
//     true
// }

pub struct DummyNode {
    pub data: NodeData,
    pub next_node: Option<Box<LockedNode>>,
}

struct_with_invariants!{
    pub struct LockedDummyNode {
        pub atomic: AtomicBool<_, Option<cell::PointsTo<DummyNode>>, _>,
        pub cell: PCell<DummyNode>,
        pub instance: Tracked<machine::Instance>,
        pub ghost_token: Tracked<machine::nodes>
    }

    spec fn wf(&self) -> bool {
        invariant on atomic with (cell, instance, ghost_token) is (v: bool, g: Option<cell::PointsTo<DummyNode>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    points_to.is_init() &&
                    points_to.value().data == NodeData::Dummy &&
                    ghost_token@.instance_id() == instance@.id()
                }
            }
        }
    }
}

impl LockedDummyNode {
    fn new(ghost_token: Tracked<machine::nodes>, instance: Tracked<machine::Instance>) -> (dummy_node: Self)
        requires
            ghost_token@.instance_id() == instance@.id()
        ensures 
            dummy_node.wf(),
            dummy_node.instance == instance,
    {
        let node = DummyNode { data: NodeData::Dummy, next_node: None::<Box<LockedNode>>};
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance, ghost_token)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance, ghost_token }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<cell::PointsTo<DummyNode>>)
        requires 
            self.wf(),
        ensures 
            points_to@.id() == self.cell.id() &&
            points_to@.is_init() &&
            points_to@.value().data == NodeData::Dummy &&
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

    fn release_lock(&self, points_to: Tracked<cell::PointsTo<DummyNode>>)
        requires
            self.wf() &&
            points_to@.id() == self.cell.id() &&
            points_to@.is_init() &&
            points_to@.value().data == NodeData::Dummy
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

pub struct Node {
    pub data: NodeData,
    pub next_node: Option<Box<LockedNode>>,
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
                    points_to.value().data != NodeData::Dummy
                }
            }
        }
    }
}

impl LockedNode {
    fn new(data: u32, next_node: Option<Box<LockedNode>>, instance: Tracked<machine::Instance>) -> (new_node: Self)
        ensures 
            new_node.wf(),
            new_node.instance == instance,
    {
        let node = Node { data: NodeData::Node(data), next_node};
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<cell::PointsTo<Node>>)
        requires 
            self.wf(),
        ensures 
            points_to@.id() == self.cell.id() &&
            points_to@.is_init() &&
            points_to@.value().data != NodeData::Dummy &&
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

    fn release_lock(&self, points_to: Tracked<cell::PointsTo<Node>>)
        requires
            self.wf() &&
            points_to@.id() == self.cell.id() &&
            points_to@.is_init() &&
            points_to@.value().data != NodeData::Dummy
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

// fn insert_at_dummy_tail(perm: cell::PointsTo<DummyNode>, node: LockedNode, instance: Tracked<machine::Instance>) 
//     requires
//         perm.value().ghost_token@.instance_id == instance@.id()
// {

// }

// fn insert(list: &LockedDummyNode, data: u32, instance: Tracked<machine::Instance>)
//     requires
//         list.wf()
//     ensures
//         list.wf()
// {
//     let mut perm = list.acquire_lock();
//     let mut current_node = list.cell.take(Tracked(perm.borrow_mut())); 

//     if (current_node.next_node.is_none()) {
//         let new_node = LockedNode::new(data, None::<Box<LockedNode>>, instance);
//         let mut new_tail_node_perm = new_node.acquire_lock();
//         proof {
//             list.instance.borrow().insert_at_dummy_tail(perm@, new_tail_node_perm@, current_node.ghost_token.borrow_mut());
//         }
//     }

//     list.cell.put(Tracked(perm.borrow_mut()), current_node);
//     list.release_lock(perm);
// }

fn insert(list: &LockedDummyNode, data: u32, instance: Tracked<machine::Instance>)
    requires
        list.wf(),
    ensures
        list.wf()
{
    let mut perm = list.acquire_lock();
    assert(perm@.value().data == NodeData::Dummy);

    let mut current_node = list.cell.borrow(Tracked(perm.borrow_mut()));


    if (current_node.next_node.is_none()) {
        let new_node = LockedNode::new(data, None::<Box<LockedNode>>, instance);
        let mut new_tail_node_perm = new_node.acquire_lock();

        assert(perm@.value().data == NodeData::Dummy);
        assert(new_tail_node_perm@.value().data != NodeData::Dummy);
        proof {
            list.instance.borrow().insert_at_dummy_tail(perm@, new_tail_node_perm@, list.ghost_token.borrow_mut());
        }
    }

    // list.cell.put(Tracked(perm.borrow_mut()), current_node);
    list.release_lock(perm);
}

fn main() {
    let tracked (
        Tracked(instance),
        Tracked(nodes),
    ) = machine::Instance::initialize();

    let linked_list = LockedDummyNode::new(Tracked(nodes), Tracked(instance.clone()));
    let shared_linked_list = Arc::new(linked_list);

    insert(&shared_linked_list, 5, Tracked(instance.clone()));
}
}