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
use vstd::set::*;

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
            *self == NodeData::Node(value)
    {
        match self {
            NodeData::Node(i) => *i,
            _ => u32::MIN
        }
    }

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

            #[sharding(set)]
            pub node_witnesses: Set<NodeData>,

            #[sharding(variable)]
            pub initialized: bool,
        }

        #[invariant]
        pub fn sorted_inv(&self) -> bool {
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

        #[invariant]
        pub fn main_inv(&self) -> bool {
            // The node witnesses reflect the nodes:
            (forall |i: u32| #![auto] self.node_witnesses.contains(NodeData::Node(i)) <==> self.nodes.dom().contains(NodeData::Node(i))) &&

            // If the map is uninitialised, then it doesn't contain anything, not even the dummy node (and vice versa)
            (!self.initialized <==> self.nodes.is_empty()) &&
            (!self.initialized <==> self.node_witnesses.is_empty()) &&

            // If the map is initialised, then it must at least have the dummy node:
            // This case looks redundant, but I believe it will help the SMT solver.
            (self.initialized <==> self.nodes.dom().contains(NodeData::Dummy)) &&

            // If the map contains [NodeData::Dummy => None], then it can't contain anything else
            (
                (self.initialized && self.nodes[NodeData::Dummy] == None::<NodeData>) <==> 
                (self.nodes =~= Map::empty().insert(NodeData::Dummy, None::<NodeData>))
            )
        }

        init!{
            initialize()
            {
                init nodes = Map::empty();
                init initialized = false;
                init node_witnesses = Set::empty();
            }
        }

        transition!{
            add_dummy_node()
            {   
                require(!pre.initialized);
                update initialized = true;
                add nodes += [NodeData::Dummy => None];
                add node_witnesses += set {NodeData::Dummy};
            }
        }

        transition!{
            add_to_dummy_tail(new_tail: u32)
            {   
                remove nodes -= [NodeData::Dummy => None];
                add nodes += [NodeData::Dummy => Some(NodeData::Node(new_tail))];
                add nodes += [NodeData::Node(new_tail) => None];
                add node_witnesses += set {NodeData::Node(new_tail)};
            }
        }

        transition!{
            add_to_node_tail(current_tail: u32, new_tail: u32)
            {   
                require(new_tail > current_tail);
                remove nodes -= [NodeData::Node(current_tail) => None];
                add nodes += [NodeData::Node(current_tail) => Some(NodeData::Node(new_tail))];
                add nodes += [NodeData::Node(new_tail) => None];
                add node_witnesses += set {NodeData::Node(new_tail)};

            }
        }

        transition!{
            insert_node_inbetween_normal_and_normal(lower_node: u32, upper_node: u32, new_node: u32)
            {   
                require(lower_node < new_node);
                require(new_node < upper_node);
                remove nodes -= [NodeData::Node(lower_node) => Some(NodeData::Node(upper_node))];
                add nodes += [NodeData::Node(lower_node) => Some(NodeData::Node(new_node))];
                add nodes += [NodeData::Node(new_node) => Some(NodeData::Node(upper_node))];
                add node_witnesses += set {NodeData::Node(new_node)};
            }
        }

        transition!{
            insert_node_inbetween_dummy_and_normal(upper_node: u32, new_node: u32)
            {   
                require(new_node < upper_node);
                remove nodes -= [NodeData::Dummy => Some(NodeData::Node(upper_node))];
                add nodes += [NodeData::Dummy => Some(NodeData::Node(new_node))];
                add nodes += [NodeData::Node(new_node) => Some(NodeData::Node(upper_node))];
                add node_witnesses += set {NodeData::Node(new_node)};
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

        #[inductive(insert_node_inbetween_normal_and_normal)]
        fn insert_node_inbetween_normal_and_normal_inductive(pre: Self, post: Self, lower_node: u32, upper_node: u32, new_node: u32) { 
        }

        #[inductive(insert_node_inbetween_dummy_and_normal)]
        fn insert_node_inbetween_dummy_and_normal_inductive(pre: Self, post: Self, upper_node: u32, new_node: u32) { 
        }
    }
}

pub struct DummyNode {
    pub head: Option<Arc<LockedNode>>,
    pub map_token: Option<Tracked<machine::nodes>>
}

struct_with_invariants!{
    pub struct LinkedList {
        pub atomic: AtomicBool<_, Option<pcell::PointsTo<DummyNode>>, _>,
        pub cell: pcell::PCell<DummyNode>,
        pub instance: Tracked<machine::Instance>,
    }

    spec fn wf(&self) -> bool 
    {
        invariant on atomic with (cell, instance) is (v: bool, g: Option<pcell::PointsTo<DummyNode>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    points_to.value().map_token.is_some() &&
                    points_to.value().map_token.unwrap()@.instance_id() == instance@.id() && 
                    points_to.value().map_token.unwrap()@.key() == NodeData::Dummy &&
                    (points_to.value().map_token.unwrap()@.value().is_none() <==> points_to.value().head.is_none()) && 
                    (points_to.value().map_token.unwrap()@.value().is_some() ==> 
                        (
                            points_to.value().head.unwrap().wf() &&
                            points_to.value().head.unwrap().instance == instance &&
                            points_to.value().head.unwrap().data_view == points_to.value().map_token.unwrap()@.value().unwrap()
                        )
                    )
                }
            }
        }
    }
}

impl LinkedList {
    fn new() -> (locked_dummy_node: Self)
        ensures 
            locked_dummy_node.wf()
    {
        let tracked (
            Tracked(instance),
            Tracked(nodes),
            Tracked(node_witnesses),
            Tracked(initialized),
        ) = machine::Instance::initialize();

        let tracked tuple;
        let tracked map_token;
        proof {
            tuple = instance.add_dummy_node(&mut initialized);
            map_token = tuple.0.get()
        }

        let node = DummyNode { head: None::<Arc<LockedNode>>, map_token: Some(Tracked(map_token)) };
        let (cell, Tracked(perm)) = pcell::PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, Tracked(instance))), false, Tracked(Some(perm)));

        Self { 
            atomic, 
            cell, 
            instance: Tracked(instance)
        }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<pcell::PointsTo<DummyNode>>)
        requires 
            self.wf(),
        ensures 
            points_to.id() == self.cell.id(),
            points_to.value().map_token.is_some(),
            points_to.value().map_token.unwrap()@.instance_id() == self.instance@.id(), 
            points_to.value().map_token.unwrap()@.key() == NodeData::Dummy,
            (points_to.value().map_token.unwrap()@.value().is_none() <==> points_to.value().head.is_none()), 
            (points_to.value().map_token.unwrap()@.value().is_some() ==> 
                (
                    points_to.value().head.unwrap().wf() &&
                    points_to.value().head.unwrap().instance == self.instance &&
                    points_to.value().head.unwrap().data_view == points_to.value().map_token.unwrap()@.value().unwrap()
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

    fn release_lock(&self, points_to: Tracked<pcell::PointsTo<DummyNode>>)
        requires
            self.wf(),
            points_to.id() == self.cell.id(),
            points_to.value().map_token.is_some(),
            points_to.value().map_token.unwrap()@.instance_id() == self.instance@.id(), 
            points_to.value().map_token.unwrap()@.key() == NodeData::Dummy,
            (points_to.value().map_token.unwrap()@.value().is_none() <==> points_to.value().head.is_none()), 
            (points_to.value().map_token.unwrap()@.value().is_some() ==> 
                (
                    points_to.value().head.unwrap().wf() &&
                    points_to.value().head.unwrap().instance == self.instance &&
                    points_to.value().head.unwrap().data_view == points_to.value().map_token.unwrap()@.value().unwrap()
                )
            )
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
    pub data: u32,
    pub next_node: Option<Arc<LockedNode>>,
    pub map_token: Option<Tracked<machine::nodes>>
}

struct_with_invariants!{
    pub struct LockedNode {
        pub atomic: AtomicBool<_, Option<pcell::PointsTo<Node>>, _>,
        pub cell: pcell::PCell<Node>,
        pub instance: Tracked<machine::Instance>,
        pub data_view: NodeData,
    }

    pub open spec fn wf(&self) -> bool {
        invariant on atomic with (cell, instance, data_view) is (v: bool, g: Option<pcell::PointsTo<Node>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    NodeData::Node(points_to.value().data) == data_view &&
                    points_to.value().map_token.is_some() &&
                    points_to.value().map_token.unwrap()@.instance_id() == instance@.id() &&
                    points_to.value().map_token.unwrap()@.key() == NodeData::Node(points_to.value().data) &&
                    (points_to.value().map_token.unwrap()@.value().is_none() <==> points_to.value().next_node.is_none()) && 
                    (points_to.value().map_token.unwrap()@.value().is_some() ==> 
                        (
                            points_to.value().next_node.unwrap().wf() &&
                            points_to.value().next_node.unwrap().instance == instance &&
                            NodeData::Node(points_to.value().data) < points_to.value().next_node.unwrap().data_view &&
                            points_to.value().next_node.unwrap().data_view == points_to.value().map_token.unwrap()@.value().unwrap()
                        )
                    )
                }
            }
        }
    }
}

impl LockedNode {
    fn new(data: u32, map_token: Tracked<machine::nodes>, next_node: Option<Arc<LockedNode>>, instance: Tracked<machine::Instance>) -> (new_node: Self)
        requires
            map_token@.instance_id() == instance@.id(),
            map_token@.key() == NodeData::Node(data),
            map_token@.value().is_none() <==> next_node.is_none(),
            map_token@.value().is_some() ==> (
                next_node.is_some() &&
                next_node.unwrap().wf() &&
                next_node.unwrap().instance == instance &&
                NodeData::Node(data) < next_node.unwrap().data_view &&
                next_node.unwrap().data_view == map_token@.value().unwrap()
            ),
        ensures 
            new_node.wf(),
            new_node.instance == instance,
            new_node.data_view == NodeData::Node(data),
    {   
        let data_view = NodeData::Node(data);
        let node = Node { data, next_node, map_token: Some(map_token) };
        let (cell, Tracked(perm)) = pcell::PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance, data_view)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance, data_view }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<pcell::PointsTo<Node>>)
        requires 
            self.wf(),
        ensures 
            points_to.id() == self.cell.id(),
            NodeData::Node(points_to.value().data) == self.data_view,
            points_to.value().map_token.is_some(),
            points_to.value().map_token.unwrap()@.instance_id() == self.instance@.id(),
            points_to.value().map_token.unwrap()@.key() == NodeData::Node(points_to.value().data),
            (points_to.value().map_token.unwrap()@.value().is_none() <==> points_to.value().next_node.is_none()), 
            (points_to.value().map_token.unwrap()@.value().is_some() ==> 
                (
                    points_to.value().next_node.unwrap().wf() &&
                    points_to.value().next_node.unwrap().instance == self.instance &&
                    NodeData::Node(points_to.value().data) < points_to.value().next_node.unwrap().data_view &&
                    points_to.value().next_node.unwrap().data_view == points_to.value().map_token.unwrap()@.value().unwrap()
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

    fn release_lock(&self, points_to: Tracked<pcell::PointsTo<Node>>)
        requires
            self.wf(),
            points_to.id() == self.cell.id(),
            NodeData::Node(points_to.value().data) == self.data_view,
            points_to.value().map_token.is_some(),
            points_to.value().map_token.unwrap()@.instance_id() == self.instance@.id(),
            points_to.value().map_token.unwrap()@.key() == NodeData::Node(points_to.value().data),
            (points_to.value().map_token.unwrap()@.value().is_none() <==> points_to.value().next_node.is_none()), 
            (points_to.value().map_token.unwrap()@.value().is_some() ==> 
                (
                    points_to.value().next_node.unwrap().wf() &&
                    points_to.value().next_node.unwrap().instance == self.instance &&
                    NodeData::Node(points_to.value().data) < points_to.value().next_node.unwrap().data_view &&
                    points_to.value().next_node.unwrap().data_view == points_to.value().map_token.unwrap()@.value().unwrap()
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

impl LinkedList {
    fn insert(linked_list: Arc<LinkedList>, insert_data: u32) -> (witness: Option<Tracked<machine::node_witnesses>>)
        requires
            linked_list.wf()
        ensures
            linked_list.wf(),
            witness.is_some() ==> (
                witness.unwrap().instance_id() == linked_list.instance@.id() &&
                witness.unwrap().element() == NodeData::Node(insert_data) &&
                exists |locked_node: LockedNode| #![auto]
                    locked_node.wf() && 
                    locked_node.instance@.id() == witness.unwrap().instance_id() &&
                    locked_node.data_view == witness.unwrap().element()
            ),
            witness.is_none() ==> (
                exists |locked_node: LockedNode| #![auto]
                    locked_node.wf() && 
                    locked_node.instance == linked_list.instance &&
                    locked_node.data_view == NodeData::Node(insert_data)
            )
    {
        let mut dummy_node_perm = linked_list.acquire_lock();
        let mut dummy_node_view = linked_list.cell.borrow(Tracked(dummy_node_perm.borrow_mut()));

        // If the next node of the dummy is none, then we just have to insert where we are:
        if (dummy_node_view.head.is_none()) {

            let temp_dummy_node = DummyNode {
                head: None,
                map_token: None
            };

            let mut dummy_node = linked_list.cell.replace(Tracked(dummy_node_perm.borrow_mut()), temp_dummy_node);
            let old_dummy_node_token = dummy_node.map_token.unwrap();

            let tracked tuple;
            let tracked updated_dummy_node_token;
            let tracked new_node_token;
            let tracked new_node_witness;

            proof {
                tuple = linked_list.instance.borrow().add_to_dummy_tail(insert_data, old_dummy_node_token.get());
                updated_dummy_node_token = tuple.0.get();
                new_node_token = tuple.1.get();
                new_node_witness = tuple.2.get();
            }

            let next_locked_node = LockedNode::new(
                insert_data, 
                Tracked(new_node_token), 
                None::<Arc<LockedNode>>, 
                linked_list.instance.clone()
            );

            let dummy_node = DummyNode {
                head: Some(Arc::new(next_locked_node)),
                map_token: Some(Tracked(updated_dummy_node_token))
            };

            linked_list.cell.replace(Tracked(dummy_node_perm.borrow_mut()), dummy_node);
            linked_list.release_lock(dummy_node_perm);
            return Some(Tracked(new_node_witness));
        } 
        // Otherwise, we need to begin the loop of grabbing the next lock
        else {
            // We want to start from a LockedNode instead of a LockedDummyNode

            // AKA we want to move forward 1 before beginning our loop (for SMT solver)
            let mut current_locked_node = dummy_node_view.head.as_ref().unwrap().clone();
            let mut current_node_perm = current_locked_node.acquire_lock();
            // Indent so that the view is dropped before the loop
            // We want a fresh view every loop.
            {
                let mut current_node_view = current_locked_node.cell.borrow(Tracked(current_node_perm.borrow_mut()));
                let current_node_data = current_locked_node.data_view.get();
                // Check if we already have this node:
                if (insert_data == current_node_data) {
                    linked_list.release_lock(dummy_node_perm);
                    current_locked_node.release_lock(current_node_perm);
                    return None;
                }

                // Check if we need to insert inbetween dummy and first node:
                if (insert_data < current_node_data) {
                    // Insert inbetween dummy and normal.
                    let temp_dummy_node = DummyNode {
                        head: None,
                        map_token: None
                    };

                    let mut dummy_node = linked_list.cell.replace(Tracked(dummy_node_perm.borrow_mut()), temp_dummy_node);
                    let old_dummy_node_token = dummy_node.map_token.unwrap();

                    let tracked tuple;
                    let tracked updated_dummy_node_token;
                    let tracked new_node_token;
                    let tracked new_node_witness;

                    proof {
                        tuple = linked_list.instance.borrow().insert_node_inbetween_dummy_and_normal(current_node_data, insert_data, old_dummy_node_token.get());
                        updated_dummy_node_token = tuple.0.get();
                        new_node_token = tuple.1.get();
                        new_node_witness = tuple.2.get();
                    }

                    let new_locked_node = LockedNode::new(
                        insert_data, 
                        Tracked(new_node_token), 
                        Some(current_locked_node.clone()), 
                        current_locked_node.instance.clone()
                    );

                    let new_dummy_node = DummyNode {
                        head: Some(Arc::new(new_locked_node)),
                        map_token: Some(Tracked(updated_dummy_node_token))
                    };

                    linked_list.cell.replace(Tracked(dummy_node_perm.borrow_mut()), new_dummy_node);


                    linked_list.release_lock(dummy_node_perm);
                    current_locked_node.release_lock(current_node_perm);
                    return Some(Tracked(new_node_witness));
                }

                // And release the dummy node lock
                linked_list.release_lock(dummy_node_perm);
            }
            // Now we begin our traversal.
            let mut current_node_data = current_locked_node.data_view.get();
            loop 
                invariant
                    linked_list.wf(),
                    current_locked_node.wf(),
                    current_locked_node.instance == linked_list.instance,
                    current_node_perm.id() == current_locked_node.cell.id(),
                    NodeData::Node(current_node_perm.value().data) == current_locked_node.data_view,
                    current_node_perm.value().map_token.is_some(),
                    current_node_perm.value().map_token.unwrap()@.instance_id() == current_locked_node.instance@.id(),
                    current_node_perm.value().map_token.unwrap()@.key() == NodeData::Node(current_node_perm.value().data),
                    (current_node_perm.value().map_token.unwrap()@.value().is_none() <==> current_node_perm.value().next_node.is_none()), 
                    (current_node_perm.value().map_token.unwrap()@.value().is_some() ==> 
                        (
                            current_node_perm.value().next_node.unwrap().wf() &&
                            current_node_perm.value().next_node.unwrap().instance == current_locked_node.instance &&
                            NodeData::Node(current_node_perm.value().data) < current_node_perm.value().next_node.unwrap().data_view &&
                            current_node_perm.value().next_node.unwrap().data_view == current_node_perm.value().map_token.unwrap()@.value().unwrap()
                        )
                    ),
                    current_node_data == current_node_perm.value().data,
                    current_node_data < insert_data

            {
                let mut current_node_view = current_locked_node.cell.borrow(Tracked(current_node_perm.borrow_mut()));
                // Traversal loop:
                if (current_node_view.next_node.is_none()) {
                    // Insert at end.

                    let temp_tail_node = Node {
                        data: 0,
                        next_node: None,
                        map_token: None
                    };

                    let mut old_tail_node = current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), temp_tail_node);
                    let old_tail_node_token = old_tail_node.map_token.unwrap();

                    let tracked tuple;
                    let tracked updated_tail_node_token;
                    let tracked new_tail_node_token;
                    let tracked new_node_witness;

                    proof {
                        tuple = current_locked_node.instance.borrow().add_to_node_tail(current_node_data, insert_data, old_tail_node_token.get());
                        updated_tail_node_token = tuple.0.get();
                        new_tail_node_token = tuple.1.get();
                        new_node_witness = tuple.2.get();
                    }

                    let new_tail_node = LockedNode::new(
                        insert_data, 
                        Tracked(new_tail_node_token), 
                        None::<Arc<LockedNode>>, 
                        current_locked_node.instance.clone()
                    );

                    old_tail_node.next_node = Some(Arc::new(new_tail_node));
                    old_tail_node.map_token = Some(Tracked(updated_tail_node_token));

                    current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), old_tail_node);
                    current_locked_node.release_lock(current_node_perm);
                    return Some(Tracked(new_node_witness));
                } 
                
                else {
                    let mut next_locked_node = current_node_view.next_node.as_ref().unwrap().clone();
                    let mut next_node_perm = next_locked_node.acquire_lock();
                    let next_node_view = next_locked_node.cell.borrow(Tracked(next_node_perm.borrow_mut()));
                    let next_node_data = next_locked_node.data_view.get();

                    // Check if we already have the node:
                    if (insert_data == next_node_data) {
                        current_locked_node.release_lock(current_node_perm);
                        next_locked_node.release_lock(next_node_perm);
                        return None;
                    } 

                    // Check if we need to insert here
                    if (insert_data < next_node_data) {
                        // Insert inbetween two normals.
                        let temp_lower_node = Node {
                            data: 0,
                            next_node: None,
                            map_token: None
                        };

                        let mut lower_node = current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), temp_lower_node);
                        let old_lower_node_token = lower_node.map_token.unwrap();

                        let tracked tuple;
                        let tracked updated_lower_node_token;
                        let tracked new_node_token;
                        let tracked new_node_witness;

                        proof {
                            tuple = current_locked_node.instance.borrow().insert_node_inbetween_normal_and_normal(current_node_data, next_node_data, insert_data, old_lower_node_token.get());
                            updated_lower_node_token = tuple.0.get();
                            new_node_token = tuple.1.get();
                            new_node_witness = tuple.2.get();
                        }

                        let new_locked_node = LockedNode::new(
                            insert_data, 
                            Tracked(new_node_token), 
                            Some(next_locked_node.clone()), 
                            current_locked_node.instance.clone()
                        );

                        lower_node.next_node = Some(Arc::new(new_locked_node));
                        lower_node.map_token = Some(Tracked(updated_lower_node_token));

                        current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), lower_node);


                        current_locked_node.release_lock(current_node_perm);
                        next_locked_node.release_lock(next_node_perm);
                        return Some(Tracked(new_node_witness));
                    } 

                    // Otherwise, we give up the previous lock, and loop again!
                    current_locked_node.release_lock(current_node_perm);

                    current_locked_node = next_locked_node;
                    current_node_perm = next_node_perm;
                    current_node_data = current_locked_node.data_view.get();
                }
            }
        }
    }
}

fn main() {
    let tracked (
        Tracked(instance),
        Tracked(nodes),
        Tracked(node_witnesses),
        Tracked(initialized),
    ) = machine::Instance::initialize();

    let linked_list = LinkedList::new();

    // assert(linked_list.not_contains(NodeData::Node(6)));
    // assert(linked_list.not_contains(NodeData::Node(7)));

    // assert(linked_list.contains(NodeData::Dummy));

    // insert(linked_list.clone(), &[5, 2, 4, 3, 1]);

    // assert(linked_list.contains(NodeData::Node(5)));
    // assert(linked_list.contains(NodeData::Node(4)));
    // assert(linked_list.contains(NodeData::Node(3)));
    // assert(linked_list.contains(NodeData::Node(2)));
    // assert(linked_list.contains(NodeData::Node(1)));
}
}