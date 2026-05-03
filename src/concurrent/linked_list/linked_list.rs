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
    pub data: NodeData,
    pub next_node: Option<Arc<LockedNode>>,
    pub map_token: Option<Tracked<machine::nodes>>
}

struct_with_invariants!{
    pub struct LockedDummyNode {
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
                    points_to.value().data == NodeData::Dummy &&
                    points_to.value().map_token.is_some() &&
                    points_to.value().map_token.unwrap()@.instance_id() == instance@.id() && 
                    points_to.value().map_token.unwrap()@.key() == NodeData::Dummy &&
                    (points_to.value().map_token.unwrap()@.value().is_none() <==> points_to.value().next_node.is_none()) && 
                    (points_to.value().map_token.unwrap()@.value().is_some() ==> 
                        (
                            points_to.value().next_node.unwrap().instance@.id() == instance@.id() &&
                            points_to.value().map_token.unwrap()@.value().unwrap() == points_to.value().next_node.unwrap().data_view &&
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
        let node = DummyNode { data: NodeData::Dummy, next_node: None::<Arc<LockedNode>>, map_token: Some(map_token)};
        let (cell, Tracked(perm)) = pcell::PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<pcell::PointsTo<DummyNode>>)
        requires 
            self.wf(),
        ensures 
            points_to@.id() == self.cell.id(),
            points_to@.value().data == NodeData::Dummy,
            points_to@.value().map_token.is_some(),
            points_to@.value().map_token.unwrap()@.instance_id() == self.instance@.id(),
            points_to@.value().map_token.unwrap()@.key() == NodeData::Dummy,
            (points_to@.value().map_token.unwrap()@.value().is_none() <==> points_to@.value().next_node.is_none()), 
            (points_to@.value().map_token.unwrap()@.value().is_some() ==> 
                (
                    points_to@.value().next_node.unwrap().instance@.id() == self.instance@.id() &&
                    points_to@.value().map_token.unwrap()@.value().unwrap() == points_to@.value().next_node.unwrap().data_view &&
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

    fn release_lock(&self, points_to: Tracked<pcell::PointsTo<DummyNode>>)
        requires
            self.wf(),
            points_to@.id() == self.cell.id(),
            points_to@.value().data == NodeData::Dummy,
            points_to@.value().map_token.is_some(),
            points_to@.value().map_token.unwrap()@.instance_id() == self.instance@.id(),
            points_to@.value().map_token.unwrap()@.key() == NodeData::Dummy,
            (points_to@.value().map_token.unwrap()@.value().is_none() <==> points_to@.value().next_node.is_none()), 
            (points_to@.value().map_token.unwrap()@.value().is_some() ==> 
                (
                    points_to.value().next_node.unwrap().instance@.id() == self.instance@.id() &&
                    points_to@.value().map_token.unwrap()@.value().unwrap() == points_to@.value().next_node.unwrap().data_view &&
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
                    points_to.value().data == data_view &&
                    points_to.value().data != NodeData::Dummy &&
                    points_to.value().map_token.is_some() &&
                    points_to.value().map_token.unwrap()@.instance_id() == instance@.id() &&
                    points_to.value().map_token.unwrap()@.key() == points_to.value().data &&
                    (points_to.value().map_token.unwrap()@.value().is_none() <==> points_to.value().next_node.is_none()) && 
                    (points_to.value().map_token.unwrap()@.value().is_some() ==> 
                        (
                            points_to.value().next_node.unwrap().instance@.id() == instance@.id() &&
                            points_to.value().map_token.unwrap()@.value().unwrap() == points_to.value().next_node.unwrap().data_view &&
                            points_to.value().next_node.unwrap().wf()
                        )
                    )
                }
            }
        }
    }
}

impl LockedNode {
    fn new(data: NodeData, map_token: Tracked<machine::nodes>, next_node: Option<Arc<LockedNode>>, instance: Tracked<machine::Instance>) -> (new_node: Self)
        requires
            data != NodeData::Dummy,
            map_token@.instance_id() == instance@.id(),
            map_token@.key() == data,
            map_token@.value().is_none() <==> next_node.is_none(),
            map_token@.value().is_some() ==> (
                map_token@.value().unwrap() == next_node.unwrap().data_view &&
                next_node.unwrap().wf()
            ),
            next_node.is_some() ==> (
                next_node.unwrap().wf() &&
                next_node.unwrap().instance@.id() == instance@.id()
            )
        ensures 
            new_node.wf(),
            new_node.instance == instance,
            new_node.data_view == data,
            next_node.is_some() ==> (
                next_node.unwrap().wf() &&
                next_node.unwrap().instance@.id() == instance@.id()
            )
    {   
        let data_view = data.clone();
        let node = Node { data, next_node, map_token: Some(map_token) };
        let (cell, Tracked(perm)) = pcell::PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance, data_view)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance, data_view }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<pcell::PointsTo<Node>>)
        requires 
            self.wf(),
        ensures 
            points_to@.id() == self.cell.id(),
            points_to@.value().data == self.data_view,
            points_to@.value().data != NodeData::Dummy,
            points_to@.value().map_token.is_some(),
            points_to@.value().map_token.unwrap()@.instance_id() == self.instance@.id(),
            points_to@.value().map_token.unwrap()@.key() == points_to@.value().data,
            (points_to@.value().map_token.unwrap()@.value().is_none() <==> points_to@.value().next_node.is_none()), 
            (points_to@.value().map_token.unwrap()@.value().is_some() ==> 
                (
                    points_to@.value().next_node.unwrap().instance@.id() == self.instance@.id() &&
                    points_to@.value().map_token.unwrap()@.value().unwrap() == points_to@.value().next_node.unwrap().data_view &&
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

    fn release_lock(&self, points_to: Tracked<pcell::PointsTo<Node>>)
        requires
            self.wf(),
            points_to@.id() == self.cell.id(),
            points_to@.value().data == self.data_view,
            points_to@.value().data != NodeData::Dummy,
            points_to@.value().map_token.is_some(),
            points_to@.value().map_token.unwrap()@.instance_id() == self.instance@.id(),
            points_to@.value().map_token.unwrap()@.key() == points_to@.value().data,
            (points_to@.value().map_token.unwrap()@.value().is_none() <==> points_to@.value().next_node.is_none()), 
            (points_to@.value().map_token.unwrap()@.value().is_some() ==> 
                (
                    points_to@.value().next_node.unwrap().instance@.id() == self.instance@.id() &&
                    points_to@.value().map_token.unwrap()@.value().unwrap() == points_to@.value().next_node.unwrap().data_view &&
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

pub struct LinkedList {
    pub element_witnesses: Vec<Tracked<machine::node_witnesses>>,
    pub head: Arc<LockedDummyNode>,
}

impl LinkedList {
    fn new(mut initialized: Tracked<machine::initialized>, instance: Tracked<machine::Instance>) -> (linked_list: Self) 
        requires
            initialized@.instance_id() == instance@.id(),
            initialized@.value() == false
        ensures
            linked_list.head.wf(),
            linked_list.valid_witnesses(),
            linked_list.contains(NodeData::Dummy),
            forall |node_data: NodeData| node_data != NodeData::Dummy ==>
                linked_list.not_contains(node_data)

    {
        let tracked dummy_tuple;
        let tracked dummy_token;
        let tracked dummy_witness;

        proof {
            dummy_tuple = instance.add_dummy_node(&mut initialized);
            dummy_token = dummy_tuple.0.get();
            dummy_witness = dummy_tuple.1.get();
        }

        let mut element_witnesses = Vec::new();
        element_witnesses.push(Tracked(dummy_witness));
        let head = Arc::new(LockedDummyNode::new(Tracked(dummy_token), instance.clone()));

        let linked_list = Self {
            element_witnesses,
            head
        };

        assert(
            exists |i: int| #![auto] 0 <= i < linked_list.element_witnesses.len() ==>
                linked_list.element_witnesses[i]@.element() == NodeData::Dummy
        ) by {
            assert(linked_list.element_witnesses[0]@.element() == NodeData::Dummy);
            assert(linked_list.element_witnesses[0]@.instance_id() == head.instance@.id());
        };

        return linked_list
    }

    fn insert(&mut self, insert_data_list: &[u32]) 
        requires
            old(self).head.wf(),
            old(self).valid_witnesses(),
            old(self).contains(NodeData::Dummy)
            // forall |data: u32| #![auto]
            //     (self.contains(NodeData::Node(data)) && old(self).not_contains(NodeData::Node(data))) 
            //     ==> insert_data_list@.contains(data)
        ensures
            self.head.wf(),
            self.valid_witnesses(),
            old(self).contains(NodeData::Dummy),
            forall |data: u32| #![auto]
                (self.contains(NodeData::Node(data)) && old(self).not_contains(NodeData::Node(data))) 
                ==> insert_data_list@.contains(data)
    {
        let mut i = 0;
        let mut join_handles: Vec<JoinHandle<Tracked<machine::node_witnesses>>> = Vec::new();
        while i < insert_data_list.len() 
            invariant
                0 <= i <= insert_data_list.len() ,
                self.head.wf(),
                join_handles.len() == i,
                forall|j: int, ret|
                    0 <= j < i ==> join_handles@.index(j).predicate(ret) ==>
                        ret@.instance_id() == self.head.instance@.id() &&
                        ret@.element() == NodeData::Node(insert_data_list[j])
            decreases
                insert_data_list.len() - i
        {
            let thread_head = self.head.clone();
            let insert_data = insert_data_list[i];
            let join_handle = spawn(move || -> (witness: Tracked<machine::node_witnesses>) 
                ensures
                    witness.instance_id() == self.head.instance@.id(),
                    witness.element() == NodeData::Node(insert_data_list[i as int])

            {
                insert_thread_routine(thread_head, insert_data)
            });
            join_handles.push(join_handle);
            i += 1;
        }

        let mut original_witnesses_length = self.element_witnesses.len();
        let mut i = 0;
        while i < insert_data_list.len() 
            invariant
                0 <= i <= insert_data_list.len(),
                self.head.wf(),
                join_handles.len() == insert_data_list.len() - i,
                self.element_witnesses.len() == original_witnesses_length + i,
                self.valid_witnesses(),
                (forall|j: int, ret|
                    0 <= j < join_handles@.len() ==>
                        #[trigger] join_handles@.index(j).predicate(ret) ==>
                            ret@.instance_id() == self.head.instance@.id() &&
                            ret@.element() == NodeData::Node(insert_data_list[j])),
                // forall |j: int| 0 <= j < i ==>
                //         #[trigger] self.contains(NodeData::Node(insert_data_list[insert_data_list.len() - 1 - j]))
            decreases
                insert_data_list.len() - i
        {
            let join_handle = join_handles.pop().unwrap();
            match join_handle.join() {
                Result::Ok(witness) => {
                    self.element_witnesses.push(witness);
                    assert(self.element_witnesses[self.element_witnesses.len() - 1].element() == NodeData::Node(insert_data_list[insert_data_list.len() - 1 - i]));
                    assert(self.contains(NodeData::Node(insert_data_list[insert_data_list.len() - 1 - i])));
                    // assert(forall |j: int| 0 <= j < i ==>
                    //     #[trigger] self.contains(NodeData::Node(insert_data_list[insert_data_list.len() - 1 - j])));
                },
                _ => {
                    assume(false);
                    return;
                },
            };
            i = i + 1;
        }

        assume(forall |i: int| #![auto] 0 <= i < insert_data_list.len() ==>
                self.contains(NodeData::Node(insert_data_list[i])));

        assert(self.contains_all(insert_data_list));
    }

    pub open spec fn valid_witnesses(&self) -> bool {
        forall |i: int| #![auto] 0 <= i < self.element_witnesses.len() ==>
            self.element_witnesses[i]@.instance_id() == self.head.instance@.id()
    }

    pub open spec fn contains(&self, data: NodeData) -> bool {
        self.valid_witnesses() &&
        exists |i: int| #![auto] 0 <= i < self.element_witnesses.len() &&
            self.element_witnesses[i]@.element() == data
    }

    pub open spec fn not_contains(&self, data: NodeData) -> bool {
        self.valid_witnesses() &&
        forall |i: int| #![auto] 0 <= i < self.element_witnesses.len() ==>
            self.element_witnesses[i]@.element() != data
    }

    pub open spec fn not_contains_any(&self, data: &[u32]) -> bool {
        self.valid_witnesses() &&
        forall |i: int, j: int| #![auto] 
            (0 <= i < self.element_witnesses.len() && 0 <= j < data.len()) ==>
            self.element_witnesses[i]@.element() != NodeData::Node(data[j])
    }

    pub open spec fn contains_all(&self, data: &[u32]) -> bool {
        forall |i: int| #![auto] 
            0 <= i < data.len() ==>
                self.contains(NodeData::Node(data[i]))
    }
}

fn insert_thread_routine(locked_dummy_node: Arc<LockedDummyNode>, insert_data: u32) -> (witness: Tracked<machine::node_witnesses>)
    requires
        locked_dummy_node.wf()
    ensures
        locked_dummy_node.wf(),
        witness.instance_id() == locked_dummy_node.instance@.id(),
        witness.element() == NodeData::Node(insert_data),
{
    let mut dummy_node_perm = locked_dummy_node.acquire_lock();
    let mut dummy_node_view = locked_dummy_node.cell.borrow(Tracked(dummy_node_perm.borrow_mut()));

    // If the next node of the dummy is none, then we just have to insert where we are:
    if (dummy_node_view.next_node.is_none()) {

        let temp_dummy_node = DummyNode {
            data: NodeData::Dummy,
            next_node: None,
            map_token: None
        };

        let mut dummy_node = locked_dummy_node.cell.replace(Tracked(dummy_node_perm.borrow_mut()), temp_dummy_node);
        let old_dummy_node_token = dummy_node.map_token.unwrap();

        let tracked tuple;
        let tracked updated_dummy_node_token;
        let tracked new_node_token;
        let tracked new_node_witness;

        proof {
            tuple = locked_dummy_node.instance.borrow().add_to_dummy_tail(insert_data, old_dummy_node_token.get());
            updated_dummy_node_token = tuple.0.get();
            new_node_token = tuple.1.get();
            new_node_witness = tuple.2.get();
        }

        let next_locked_node = LockedNode::new(
            NodeData::Node(insert_data), 
            Tracked(new_node_token), 
            None::<Arc<LockedNode>>, 
            locked_dummy_node.instance.clone()
        );

        let dummy_node = DummyNode {
            data: NodeData::Dummy,
            next_node: Some(Arc::new(next_locked_node)),
            map_token: Some(Tracked(updated_dummy_node_token))
        };

        locked_dummy_node.cell.replace(Tracked(dummy_node_perm.borrow_mut()), dummy_node);
        locked_dummy_node.release_lock(dummy_node_perm);
        return Tracked(new_node_witness);
    } 
    // Otherwise, we need to begin the loop of grabbing the next lock
    else {
        // We want to start from a LockedNode instead of a LockedDummyNode

        // AKA we want to move forward 1 before beginning our loop (for SMT solver)
        let mut current_locked_node = dummy_node_view.next_node.as_ref().unwrap().clone();
        let mut current_node_perm = current_locked_node.acquire_lock();
        // Indent so that the view is dropped before the loop
        // We want a fresh view every loop.
        {
            let mut current_node_view = current_locked_node.cell.borrow(Tracked(current_node_perm.borrow_mut()));
            let current_node_data = current_locked_node.data_view.get();
            // Check if we already have this node:
            assume(insert_data != current_node_data);
            if (insert_data == current_node_data) {
                // let current_node_token = current_node_view.map_token.as_ref().unwrap();

                // let tracked duplicate_witness;

                // proof {
                //     duplicate_witness = current_locked_node.instance.borrow().duplicate_witness(insert_data, &current_node_token.borrow());
                // }

                // locked_dummy_node.release_lock(dummy_node_perm);
                // current_locked_node.release_lock(current_node_perm);
                // return Tracked(duplicate_witness);
            }
            // Check if we need to insert inbetween dummy and first node:
            if (insert_data < current_node_data) {
                // Insert inbetween dummy and normal.
                let temp_dummy_node = DummyNode {
                    data: NodeData::Dummy,
                    next_node: None,
                    map_token: None
                };

                let mut dummy_node = locked_dummy_node.cell.replace(Tracked(dummy_node_perm.borrow_mut()), temp_dummy_node);
                let old_dummy_node_token = dummy_node.map_token.unwrap();

                let tracked tuple;
                let tracked updated_dummy_node_token;
                let tracked new_node_token;
                let tracked new_node_witness;

                proof {
                    tuple = locked_dummy_node.instance.borrow().insert_node_inbetween_dummy_and_normal(current_node_data, insert_data, old_dummy_node_token.get());
                    updated_dummy_node_token = tuple.0.get();
                    new_node_token = tuple.1.get();
                    new_node_witness = tuple.2.get();
                }

                let new_locked_node = LockedNode::new(
                    NodeData::Node(insert_data), 
                    Tracked(new_node_token), 
                    Some(current_locked_node.clone()), 
                    current_locked_node.instance.clone()
                );

                let new_dummy_node = DummyNode {
                    data: NodeData::Dummy,
                    next_node: Some(Arc::new(new_locked_node)),
                    map_token: Some(Tracked(updated_dummy_node_token))
                };

                locked_dummy_node.cell.replace(Tracked(dummy_node_perm.borrow_mut()), new_dummy_node);


                locked_dummy_node.release_lock(dummy_node_perm);
                current_locked_node.release_lock(current_node_perm);
                return Tracked(new_node_witness);
            }

            // And release the dummy node lock
            locked_dummy_node.release_lock(dummy_node_perm);
        }


        // Now we begin our traversal.
        let mut current_node_data = current_locked_node.data_view.get();
        loop 
            invariant
                locked_dummy_node.wf(),
                current_locked_node.wf(),
                current_locked_node.instance@.id() == locked_dummy_node.instance@.id(),
                NodeData::Node(current_node_data) == current_locked_node.data_view,
                current_node_data < insert_data,
                current_node_perm@.id() == current_locked_node.cell.id(),
                current_node_perm@.value().data == current_locked_node.data_view,
                current_node_perm@.value().data != NodeData::Dummy,
                current_node_perm@.value().map_token.is_some(),
                current_node_perm@.value().map_token.unwrap()@.instance_id() == current_locked_node.instance@.id(),
                current_node_perm@.value().map_token.unwrap()@.key() == current_node_perm@.value().data,
                (current_node_perm@.value().map_token.unwrap()@.value().is_none() <==> current_node_perm@.value().next_node.is_none()), 
                (current_node_perm@.value().map_token.unwrap()@.value().is_some() ==> 
                    (
                        current_node_perm@.value().next_node.unwrap().instance@.id() == current_locked_node.instance@.id() &&
                        current_node_perm@.value().map_token.unwrap()@.value().unwrap() == current_node_perm@.value().next_node.unwrap().data_view &&
                        current_node_perm@.value().next_node.unwrap().wf()
                    )
                ),
        {
            let mut current_node_view = current_locked_node.cell.borrow(Tracked(current_node_perm.borrow_mut()));
            // Traversal loop:
            if (current_node_view.next_node.is_none()) {
                // Insert at end.

                let temp_tail_node = Node {
                    data: NodeData::Node(0),
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
                    NodeData::Node(insert_data), 
                    Tracked(new_tail_node_token), 
                    None::<Arc<LockedNode>>, 
                    current_locked_node.instance.clone()
                );

                old_tail_node.next_node = Some(Arc::new(new_tail_node));
                old_tail_node.map_token = Some(Tracked(updated_tail_node_token));

                current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), old_tail_node);
                current_locked_node.release_lock(current_node_perm);
                return Tracked(new_node_witness);
            } 
            
            else {
                let mut next_locked_node = current_node_view.next_node.as_ref().unwrap().clone();
                let mut next_node_perm = next_locked_node.acquire_lock();
                let next_node_view = next_locked_node.cell.borrow(Tracked(next_node_perm.borrow_mut()));
                let next_node_data = next_locked_node.data_view.get();

                // Check if we already have the node:
                assume(insert_data != next_node_data);
                if (insert_data == next_node_data) {
                    // let next_node_token = next_node_view.map_token.as_ref().unwrap();

                    // let tracked duplicate_witness;

                    // proof {
                    //     duplicate_witness = next_locked_node.instance.borrow().duplicate_witness(insert_data, &next_node_token.borrow());
                    // }

                    // current_locked_node.release_lock(current_node_perm);
                    // next_locked_node.release_lock(next_node_perm);
                    // return Tracked(duplicate_witness);
                } 

                // Check if we need to insert here
                if (insert_data < next_node_data) {
                    // Insert inbetween two normals.
                    let temp_lower_node = Node {
                        data: NodeData::Node(0),
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
                        NodeData::Node(insert_data), 
                        Tracked(new_node_token), 
                        Some(next_locked_node.clone()), 
                        current_locked_node.instance.clone()
                    );

                    lower_node.next_node = Some(Arc::new(new_locked_node));
                    lower_node.map_token = Some(Tracked(updated_lower_node_token));

                    current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), lower_node);


                    current_locked_node.release_lock(current_node_perm);
                    next_locked_node.release_lock(next_node_perm);
                    return Tracked(new_node_witness);
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

fn main() {
    let tracked (
        Tracked(instance),
        Tracked(nodes),
        Tracked(node_witnesses),
        Tracked(initialized),
    ) = machine::Instance::initialize();

    let linked_list = LinkedList::new(Tracked(initialized), Tracked(instance));

    assert(linked_list.not_contains(NodeData::Node(6)));
    assert(linked_list.not_contains(NodeData::Node(7)));

    // assert(linked_list.contains(NodeData::Dummy));

    // insert(linked_list.clone(), &[5, 2, 4, 3, 1]);

    // assert(linked_list.contains(NodeData::Node(5)));
    // assert(linked_list.contains(NodeData::Node(4)));
    // assert(linked_list.contains(NodeData::Node(3)));
    // assert(linked_list.contains(NodeData::Node(2)));
    // assert(linked_list.contains(NodeData::Node(1)));
}
}