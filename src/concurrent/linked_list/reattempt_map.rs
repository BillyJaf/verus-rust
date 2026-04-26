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
use vstd::cell::*;

verus! {

pub enum NodeData {
    Dummy,
    Node(u32)
}

impl NodeData {
    pub fn clone(&self) -> (cloned: Self) 
        ensures
            *self == cloned
    {
        match self {
            NodeData::Dummy => NodeData::Dummy,
            NodeData::Node(i) => NodeData::Node(*i),
        }
    }

    pub fn get(&self) -> (value: u32) 
        requires
            *self != NodeData::Dummy
        ensures
            forall |i: u32| #![auto] *self == NodeData::Node(i) ==> value == i
    {
        match self {
            NodeData::Node(i) => *i,
            _ => u32::MIN
        }
    }
}

impl NodeData {
    pub open spec fn spec_lt(self, other: Self) -> bool {
        match (self, other) {
            (NodeData::Dummy, NodeData::Dummy) => false,
            (NodeData::Dummy, _) => true,
            (_, NodeData::Dummy) => false,
            (NodeData::Node(a), NodeData::Node(b)) => a < b,
        }
    }
}

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(map)]
            pub nodes: Map<NodeData, Option<NodeData>>,

            #[sharding(variable)]
            pub initialized: bool,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            // If the map is uninitialised, then it doesn't contain anything, not even the dummy node (and vice versa)
            (!self.initialized <==> self.nodes.is_empty()) &&

            // If the map is initialised, then it must at least have the dummy node:
            // This case looks redundant, but I believe it will help the SMT solver.
            (self.initialized <==> self.nodes.dom().contains(NodeData::Dummy)) &&

            // If the map contains [NodeData::Dummy => None], then it can't contain anything else
            (
                (self.initialized && self.nodes[NodeData::Dummy] == None::<NodeData>) <==> 
                (self.nodes =~= Map::empty().insert(NodeData::Dummy, None::<NodeData>))
            ) &&

            // The remaining conditions are checked if the map contains real data:
            (
                // If the map is initialised with real data
                (self.initialized && self.nodes[NodeData::Dummy] != None::<NodeData>) ==> 
                    (
                        // The dummy node points to the smallest element in the list:
                        (
                            forall |i: u32| #![auto] 
                                self.nodes[NodeData::Dummy] == Some(NodeData::Node(i)) ==>
                                forall |j: u32| #![auto] j < i ==> !self.nodes.dom().contains(NodeData::Node(j))
                        
                        ) &&

                        // The tail node points to the largest element in the list:
                        (
                            forall |i: u32| #![auto]
                                (
                                    self.nodes.dom().contains(NodeData::Node(i)) && 
                                    self.nodes[NodeData::Node(i)] == None::<NodeData>
                                ) ==>
                                (
                                    (forall |j: u32| #![auto] i < j ==> !self.nodes.dom().contains(NodeData::Node(j)))
                                )
                        ) &&

                        // Everything in the list is sorted (smallest to largest).
                        // Nodes either point to something strictly larger, or to None
                        (
                            forall |i: u32| #![auto] 
                                (
                                    self.nodes.dom().contains(NodeData::Node(i)) && 
                                    self.nodes[NodeData::Node(i)] != None::<NodeData>
                                ) ==> (
                                    (exists |j: u32| #![auto] self.nodes[NodeData::Node(i)] == Some(NodeData::Node(j)) && i < j)
                                )
                        ) &&

                        // // We must assert that for any mapping [a => c], there are no entries in the map
                        // // with key b such that a < b < c. 
                        (
                            forall |i: u32| #![auto] 
                                (
                                    self.nodes.dom().contains(NodeData::Node(i)) && 
                                    self.nodes[NodeData::Node(i)] != None::<NodeData>
                                ) ==> (
                                    exists |j: u32| #![auto] self.nodes[NodeData::Node(i)] == Some(NodeData::Node(j)) && 
                                    forall |k: u32| #![auto] i < k < j ==> !self.nodes.dom().contains(NodeData::Node(k))
                                )
                        )
                    )
            )
        }

        init!{
            initialize()
            {
                init nodes = Map::empty();
                init initialized = false;
            }
        }

        transition!{
            add_dummy_node()
            {   
                require(!pre.initialized);
                update initialized = true;
                add nodes += [NodeData::Dummy => None];
            }
        }

        transition!{
            add_to_dummy_tail(new_tail: u32)
            {   
                remove nodes -= [NodeData::Dummy => None];
                add nodes += [NodeData::Dummy => Some(NodeData::Node(new_tail))];
                add nodes += [NodeData::Node(new_tail) => None];
            }
        }

        transition!{
            add_to_node_tail(current_tail: u32, new_tail: u32)
            {   
                require(new_tail > current_tail);
                remove nodes -= [NodeData::Node(current_tail) => None];
                add nodes += [NodeData::Node(current_tail) => Some(NodeData::Node(new_tail))];
                add nodes += [NodeData::Node(new_tail) => None];
            }
        }

        transition!{
            insert_node_inbetween(lower_node: u32, upper_node: u32, new_node: u32)
            {   
                require(lower_node < new_node);
                require(new_node < upper_node);
                remove nodes -= [NodeData::Node(lower_node) => Some(NodeData::Node(upper_node))];
                add nodes += [NodeData::Node(lower_node) => Some(NodeData::Node(new_node))];
                add nodes += [NodeData::Node(new_node) => Some(NodeData::Node(upper_node))];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { 
        }

        #[inductive(add_dummy_node)]
        fn add_dummy_node_inductive(pre: Self, post: Self) { 
        }

        #[inductive(add_to_dummy_tail)]
        fn add_to_dummy_tail_inductive(pre: Self, post: Self, new_tail: u32) { 
        }

        #[inductive(add_to_node_tail)]
        fn add_to_node_tail_inductive(pre: Self, post: Self, current_tail: u32, new_tail: u32) { 
        }

        #[inductive(insert_node_inbetween)]
        fn insert_node_inbetween_inductive(pre: Self, post: Self, lower_node: u32, upper_node: u32, new_node: u32) { 
        }
    }
}

pub struct DummyNode {
    pub data: NodeData,
    pub next_node: Option<Box<LockedNode>>,
    pub map_token: Tracked<machine::nodes>
}

struct_with_invariants!{
    pub struct LockedDummyNode {
        pub atomic: AtomicBool<_, Option<cell::PointsTo<DummyNode>>, _>,
        pub cell: PCell<DummyNode>,
        pub instance: Tracked<machine::Instance>,
    }

    spec fn wf(&self) -> bool 
    {
        invariant on atomic with (cell, instance) is (v: bool, g: Option<cell::PointsTo<DummyNode>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    points_to.is_init() &&
                    points_to.value().data == NodeData::Dummy &&
                    points_to.value().map_token@.instance_id() == instance@.id() && 
                    points_to.value().map_token@.key() == NodeData::Dummy &&
                    (points_to.value().map_token@.value().is_none() <==> points_to.value().next_node.is_none()) && 
                    (points_to.value().map_token@.value().is_some() ==> 
                        (
                            points_to.value().map_token@.value().unwrap() == points_to.value().next_node.unwrap().data_view &&
                            points_to.value().next_node.unwrap().wf()
                        )
                    )
                }
            }
        }
    }
}

impl LockedDummyNode {
    fn new(map_token: Tracked<machine::nodes>, instance: Tracked<machine::Instance>) -> (dummy_node: Self)
        requires
            map_token@.instance_id() == instance@.id(),
            map_token@.key() == NodeData::Dummy,
            map_token@.value() == None::<NodeData>,
        ensures 
            dummy_node.wf(),
            dummy_node.instance == instance,
    {
        let node = DummyNode { data: NodeData::Dummy, next_node: None::<Box<LockedNode>>, map_token};
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<cell::PointsTo<DummyNode>>)
        requires 
            self.wf(),
        ensures 
            points_to@.id() == self.cell.id(),
            points_to@.is_init(),
            points_to@.value().data == NodeData::Dummy,
            points_to@.value().map_token@.instance_id() == self.instance@.id(),
            points_to@.value().map_token@.key() == NodeData::Dummy,
            (points_to@.value().map_token@.value().is_none() <==> points_to@.value().next_node.is_none()), 
            (points_to@.value().map_token@.value().is_some() ==> 
                (
                    points_to@.value().map_token@.value().unwrap() == points_to@.value().next_node.unwrap().data_view &&
                    points_to@.value().next_node.unwrap().wf()
                )
            ),
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
            self.wf(),
            points_to@.id() == self.cell.id(),
            points_to@.is_init(),
            points_to@.value().data == NodeData::Dummy,
            points_to@.value().map_token@.instance_id() == self.instance@.id(),
            points_to@.value().map_token@.key() == NodeData::Dummy,
            (points_to@.value().map_token@.value().is_none() <==> points_to@.value().next_node.is_none()), 
            (points_to@.value().map_token@.value().is_some() ==> 
                (
                    points_to@.value().map_token@.value().unwrap() == points_to@.value().next_node.unwrap().data_view &&
                    points_to@.value().next_node.unwrap().wf()
                )
            ),
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
    pub map_token: Tracked<machine::nodes>
}

struct_with_invariants!{
    pub struct LockedNode {
        pub atomic: AtomicBool<_, Option<cell::PointsTo<Node>>, _>,
        pub cell: PCell<Node>,
        pub instance: Tracked<machine::Instance>,
        pub data_view: NodeData,
    }

    pub open spec fn wf(&self) -> bool {
        invariant on atomic with (cell, instance, data_view) is (v: bool, g: Option<cell::PointsTo<Node>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    points_to.is_init() &&
                    points_to.value().data == data_view &&
                    points_to.value().data != NodeData::Dummy &&
                    points_to.value().map_token@.instance_id() == instance@.id() &&
                    points_to.value().map_token@.key() == points_to.value().data &&
                    (points_to.value().map_token@.value().is_none() <==> points_to.value().next_node.is_none()) && 
                    (points_to.value().map_token@.value().is_some() ==> 
                        (
                            points_to.value().map_token@.value().unwrap() == points_to.value().next_node.unwrap().data_view
                        )
                    )
                }
            }
        }
    }
}

impl LockedNode {
    fn new(data: NodeData, map_token: Tracked<machine::nodes>, next_node: Option<Box<LockedNode>>, instance: Tracked<machine::Instance>) -> (new_node: Self)
        requires
            data != NodeData::Dummy,
            map_token@.instance_id() == instance@.id(),
            map_token@.key() == data,
            map_token@.value().is_none() <==> next_node.is_none(),
            map_token@.value().is_some() ==> (
                map_token@.value().unwrap() == next_node.unwrap().data_view &&
                next_node.unwrap().wf()
            )
        ensures 
            new_node.wf(),
            new_node.instance == instance,
            new_node.data_view == data,
            next_node.is_some() ==> (
                next_node.unwrap().wf()
            )
    {   
        let data_view = data.clone();
        let node = Node { data, next_node, map_token };
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance, data_view)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance, data_view }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<cell::PointsTo<Node>>)
        requires 
            self.wf(),
        ensures 
            points_to@.id() == self.cell.id(),
            points_to@.is_init(),
            points_to@.value().data == self.data_view,
            points_to@.value().data != NodeData::Dummy,
            points_to@.value().map_token@.instance_id() == self.instance@.id(),
            points_to@.value().map_token@.key() == points_to@.value().data,
            (points_to@.value().map_token@.value().is_none() <==> points_to@.value().next_node.is_none()), 
            (points_to@.value().map_token@.value().is_some() ==> 
                (
                    points_to@.value().map_token@.value().unwrap() == points_to@.value().next_node.unwrap().data_view &&
                    points_to@.value().next_node.unwrap().wf()
                )
            ),
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
            self.wf(),
            points_to@.id() == self.cell.id(),
            points_to@.is_init(),
            points_to@.value().data == self.data_view,
            points_to@.value().data != NodeData::Dummy,
            points_to@.value().map_token@.instance_id() == self.instance@.id(),
            points_to@.value().map_token@.key() == points_to@.value().data,
            (points_to@.value().map_token@.value().is_none() <==> points_to@.value().next_node.is_none()), 
            (points_to@.value().map_token@.value().is_some() ==> 
                (
                    points_to@.value().map_token@.value().unwrap() == points_to@.value().next_node.unwrap().data_view &&
                    points_to@.value().next_node.unwrap().wf()
                )
            ),
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

fn insert(dummy_node: &LockedDummyNode, insert_data: u32)
    requires
        dummy_node.wf()
    ensures
        dummy_node.wf()
{
    let mut locked_current_node = dummy_node;
    let mut current_node_perm = dummy_node.acquire_lock();
    let mut current_node_view = dummy_node.cell.borrow(Tracked(current_node_perm.borrow_mut()));

    // If the next node of the dummy is none, then we just have to insert where we are:
    if (current_node_view.next_node.is_none()) {

        // let mut current_node = dummy_node.cell.take(Tracked(current_node_perm.borrow_mut()));
        // let tracked tuple;
        // let tracked head_map_token;
        // let tracked next_node_map_token;

        // proof {
        //     tuple = dummy_node.instance.borrow().add_to_dummy_tail(insert_data, current_node.map_token.get());
        //     head_map_token = tuple.0.get();
        //     next_node_map_token = tuple.1.get();
        // }

        // let next_node = LockedNode::new(
        //     NodeData::Node(insert_data), 
        //     Tracked(next_node_map_token), 
        //     None::<Box<LockedNode>>, 
        //     dummy_node.instance.clone()
        // );

        // current_node.map_token = Tracked(head_map_token);
        // current_node.next_node = Some(Box::new(next_node));

        // dummy_node.cell.put(Tracked(current_node_perm.borrow_mut()), current_node);
        // dummy_node.release_lock(current_node_perm);
        // return;
    } 
    // Otherwise, we need to begin the loop of grabbing the next lock
    else {
        // We want to start from a LockedNode instead of a LockedDummyNode
        // AKA we want to move forward 1 before beginning our loop (for SMT solver)
        let mut locked_next_node = current_node_view.next_node.as_ref().unwrap();
        let mut next_node_perm = locked_next_node.acquire_lock();
        let mut next_node_view = locked_next_node.cell.borrow(Tracked(next_node_perm.borrow_mut()));

        // loop {
        //     // If the next node is none, then we are inserting at the end, but not to the dummy
        //     if (current_node.next_node.is_none()) {
        //         let tracked tuple;
        //         let tracked head_map_token;
        //         let tracked next_node_map_token;

        //         let curr_data = current_node.data.clone().get();

        //         proof {
        //             tuple = locked_current_node.instance.borrow().add_to_node_tail(curr_data, insert_data, current_node.map_token.get());
        //             head_map_token = tuple.0.get();
        //             next_node_map_token = tuple.1.get();
        //         }

        //         let next_node = LockedNode::new(
        //             NodeData::Node(insert_data), 
        //             Tracked(next_node_map_token), 
        //             None::<Box<LockedNode>>, 
        //             locked_current_node.instance.clone()
        //         );

        //         current_node.map_token = Tracked(head_map_token);
        //         current_node.next_node = Some(Box::new(next_node));

        //         locked_current_node.cell.put(Tracked(current_node_perm.borrow_mut()), current_node);
        //         locked_current_node.release_lock(current_node_perm);
        //         return;
        //     }
        //     return;
        // }
    }
    // else {
    //     loop {
    //         let mut next_node_perm = current_node.next_node.unwrap().acquire_lock();
    //         let mut next_node = current_node.next_node.unwrap().cell.take(Tracked(next_node_perm.borrow_mut()));
    //         // if (insert_data < next_node.data.get()) {
    //         //     // INSERT HERE INBETWEEN
    //         // } else {
    //         //     // Keep going, we need to insert the data further in the list:
    //         //     linked_list_head.cell.put(Tracked(current_node_perm.borrow_mut()), current_node);
    //         //     linked_list_head.release_lock(current_node_perm);
    //         // }
    //     }
    // }
}

fn main() {
    let tracked (
        Tracked(instance),
        Tracked(nodes),
        Tracked(initialized),
    ) = machine::Instance::initialize();

    let tracked dummy_token;

    proof {
        dummy_token = instance.add_dummy_node(&mut initialized);
    }

    let linked_list = LockedDummyNode::new(Tracked(dummy_token), Tracked(instance.clone()));

    let a = NodeData::Node(1);
    let b = a.get();
}
}