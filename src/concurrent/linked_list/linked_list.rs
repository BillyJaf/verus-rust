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

                        // No two nodes point to the same data:
                        (
                            forall |i: u32, j: u32| #![auto] 
                                (
                                    self.nodes.dom().contains(NodeData::Node(i)) &&
                                    self.nodes.dom().contains(NodeData::Node(j)) &&
                                    self.nodes[NodeData::Node(i)] == self.nodes[NodeData::Node(j)]
                                ) ==>
                                (
                                    i == j
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
            (self.initialized <==> self.node_witnesses.contains(NodeData::Dummy)) &&

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

        transition!{
            delete_tail_after_dummy_node(delete_node: u32)
            {   
                remove nodes -= [NodeData::Dummy => Some(NodeData::Node(delete_node))];
                remove nodes -= [NodeData::Node(delete_node) => None];
                remove node_witnesses -= set {NodeData::Node(delete_node)};
                add nodes += [NodeData::Dummy => None];
            }
        }

        transition!{
            delete_tail_node_after_normal_node(delete_node: u32, lower_node: u32)
            {   
                remove nodes -= [NodeData::Node(lower_node) => Some(NodeData::Node(delete_node))];
                remove nodes -= [NodeData::Node(delete_node) => None];
                remove node_witnesses -= set {NodeData::Node(delete_node)};
                add nodes += [NodeData::Node(lower_node) => None];
            }
        }

        transition!{
            delete_inbetween_dummy_and_normal(delete_node: u32, upper_node: u32)
            {   
                remove nodes -= [NodeData::Dummy => Some(NodeData::Node(delete_node))];
                remove nodes -= [NodeData::Node(delete_node) => Some(NodeData::Node(upper_node))];
                add nodes += [NodeData::Dummy => Some(NodeData::Node(upper_node))];
                remove node_witnesses -= set {NodeData::Node(delete_node)};
            }
        }

        transition!{
            delete_inbetween_normal_and_normal(delete_node: u32, lower_node: u32, upper_node: u32)
            {   
                remove nodes -= [NodeData::Node(lower_node) => Some(NodeData::Node(delete_node))];
                remove nodes -= [NodeData::Node(delete_node) => Some(NodeData::Node(upper_node))];
                add nodes += [NodeData::Node(lower_node) => Some(NodeData::Node(upper_node))];

                remove node_witnesses -= set {NodeData::Node(delete_node)};
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

        #[inductive(delete_tail_after_dummy_node)]
        fn delete_tail_after_dummy_node_inductive(pre: Self, post: Self, delete_node: u32) {                     
            assert(post.nodes =~= Map::empty().insert(NodeData::Dummy, None::<NodeData>)) by {
                
                assert(forall |i: u32| #![auto] 
                    !post.nodes.dom().contains(NodeData::Node(i)));

                assert forall |node_data: NodeData| post.nodes.dom().contains(node_data) 
                    implies node_data == NodeData::Dummy by {
                        match node_data {
                            NodeData::Dummy => {}
                            NodeData::Node(i) => {
                                assert(!post.nodes.dom().contains(NodeData::Node(i)))
                            }
                        }
                    }
            
                assert(post.nodes[NodeData::Dummy] == None::<NodeData>);
            };
        }

        #[inductive(delete_tail_node_after_normal_node)]
        fn delete_tail_node_after_normal_node_inductive(pre: Self, post: Self, delete_node: u32, lower_node: u32) { 
        }

        #[inductive(delete_inbetween_dummy_and_normal)]
        fn delete_inbetween_dummy_and_normal_inductive(pre: Self, post: Self, delete_node: u32, upper_node: u32) {
        }

        #[inductive(delete_inbetween_normal_and_normal)]
        fn delete_inbetween_normal_and_normal_inductive(pre: Self, post: Self, delete_node: u32, lower_node: u32, upper_node: u32) {
        }

        property!{
            no_token_exists(first_node_data: u32) {
                have nodes >= [NodeData::Dummy => Some(NodeData::Node(first_node_data))];
                birds_eye let n = pre.nodes;

                assert(
                    forall |data: u32| #![auto]
                        data < first_node_data ==>
                            !n.dom().contains(NodeData::Node(data))
                );
            }
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
                    // points_to.value().map_token.unwrap().value().is_none() ==> (
                    //     !(
                    //         exists |ln: LockedNode| #![auto]
                    //             ln.wf() && data_view < ln.data_view && ln.instance == instance
                    //     )
                    // )
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

pub struct DataWitness {
    data: u32,
    witness: Tracked<machine::node_witnesses>
}

// A -> B
// B -> C
// C -> D

impl LinkedList {
    fn insert(self: Arc<Self>, insert_data: u32) -> (data_witness: Option<DataWitness>)
        requires
            self.wf()
        ensures
            self.wf(),
            data_witness.is_some() ==> (
                data_witness.unwrap().witness.instance_id() == self.instance@.id() &&
                data_witness.unwrap().witness.element() == NodeData::Node(insert_data) &&
                data_witness.unwrap().data == insert_data &&
                exists |locked_node: LockedNode| #![auto]
                    locked_node.wf() && 
                    locked_node.instance@.id() == data_witness.unwrap().witness.instance_id() &&
                    locked_node.data_view == data_witness.unwrap().witness.element()
            ),
            data_witness.is_none() ==> (
                (
                    exists |locked_node: LockedNode| #![auto]
                        locked_node.wf() && 
                        locked_node.instance == self.instance &&
                        locked_node.data_view == NodeData::Node(insert_data)
                )
            )
    {
        let mut dummy_node_perm = self.acquire_lock();
        let mut dummy_node_view = self.cell.borrow(Tracked(dummy_node_perm.borrow_mut()));

        // If the next node of the dummy is none, then we just have to insert where we are:
        if (dummy_node_view.head.is_none()) {

            let temp_dummy_node = DummyNode {
                head: None,
                map_token: None
            };

            let mut dummy_node = self.cell.replace(Tracked(dummy_node_perm.borrow_mut()), temp_dummy_node);
            let old_dummy_node_token = dummy_node.map_token.unwrap();

            let tracked tuple;
            let tracked updated_dummy_node_token;
            let tracked new_node_token;
            let tracked new_node_witness;

            proof {
                tuple = self.instance.borrow().add_to_dummy_tail(insert_data, old_dummy_node_token.get());
                updated_dummy_node_token = tuple.0.get();
                new_node_token = tuple.1.get();
                new_node_witness = tuple.2.get();
            }

            let next_locked_node = LockedNode::new(
                insert_data, 
                Tracked(new_node_token), 
                None::<Arc<LockedNode>>, 
                self.instance.clone()
            );

            let dummy_node = DummyNode {
                head: Some(Arc::new(next_locked_node)),
                map_token: Some(Tracked(updated_dummy_node_token))
            };

            self.cell.replace(Tracked(dummy_node_perm.borrow_mut()), dummy_node);
            self.release_lock(dummy_node_perm);

            return Some(DataWitness {
                data: insert_data,
                witness: Tracked(new_node_witness)
            });
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
                    self.release_lock(dummy_node_perm);
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

                    let mut dummy_node = self.cell.replace(Tracked(dummy_node_perm.borrow_mut()), temp_dummy_node);
                    let old_dummy_node_token = dummy_node.map_token.unwrap();

                    let tracked tuple;
                    let tracked updated_dummy_node_token;
                    let tracked new_node_token;
                    let tracked new_node_witness;

                    proof {
                        tuple = self.instance.borrow().insert_node_inbetween_dummy_and_normal(current_node_data, insert_data, old_dummy_node_token.get());
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

                    self.cell.replace(Tracked(dummy_node_perm.borrow_mut()), new_dummy_node);


                    self.release_lock(dummy_node_perm);
                    current_locked_node.release_lock(current_node_perm);
                    return Some(DataWitness {
                        data: insert_data,
                        witness: Tracked(new_node_witness)
                    });
                }

                // And release the dummy node lock
                self.release_lock(dummy_node_perm);
            }
            // Now we begin our traversal.
            let mut current_node_data = current_locked_node.data_view.get();
            loop 
                invariant
                    self.wf(),
                    current_locked_node.wf(),
                    current_locked_node.instance == self.instance,
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
                    return Some(DataWitness {
                        data: insert_data,
                        witness: Tracked(new_node_witness)
                    });
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
                        return Some(DataWitness {
                            data: insert_data,
                            witness: Tracked(new_node_witness)
                        });
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

    fn delete(self: Arc<Self>, data_witness: DataWitness)
        requires
            self.wf(),
            data_witness.witness.element() == NodeData::Node(data_witness.data),
            data_witness.witness.instance_id() == self.instance.id(),
        ensures
            self.wf()
    {
        let witness = data_witness.witness;
        let delete_data = data_witness.data;
        let mut dummy_node_perm = self.acquire_lock();
        let mut dummy_node_view = self.cell.borrow(Tracked(dummy_node_perm.borrow_mut()));

        if (dummy_node_view.head.is_none()) {
            // This is not possible if we have a witness for a node:
            return;
        }

        let mut current_locked_node = dummy_node_view.head.as_ref().unwrap().clone();
        let mut current_node_perm = current_locked_node.acquire_lock();
        let mut current_node_data = current_locked_node.data_view.get();
        {
            let mut current_node_view = current_locked_node.cell.borrow(Tracked(current_node_perm.borrow_mut()));

            // Check if we are deleting the first node:
            if (delete_data == current_locked_node.data_view.get()) {
                // Check if this is the tail:
                if (current_node_view.next_node.is_none()) {
                    let temp_dummy_node = DummyNode {
                        head: None,
                        map_token: None
                    };

                    let mut old_dummy_node = self.cell.replace(Tracked(dummy_node_perm.borrow_mut()), temp_dummy_node);
                    let old_dummy_node_token = old_dummy_node.map_token.unwrap();

                    let temp_tail_node = Node {
                        data: 0,
                        next_node: None,
                        map_token: None
                    };

                    let mut deleted_tail_node = current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), temp_tail_node);
                    let deleted_tail_token = deleted_tail_node.map_token.unwrap();
                    

                    let tracked new_dummy_token;

                    proof {
                        new_dummy_token = current_locked_node.instance.borrow().delete_tail_after_dummy_node(delete_data, old_dummy_node_token.get(), deleted_tail_token.get(), witness.get());
                    }

                    old_dummy_node.map_token = Some(Tracked(new_dummy_token));
                    old_dummy_node.head = None;
                    self.cell.replace(Tracked(dummy_node_perm.borrow_mut()), old_dummy_node);

                    self.release_lock(dummy_node_perm);
                    return;
                }

                // Otherwise we are deleting between dummy and normal
                else {
                    let temp_dummy_node = DummyNode {
                        head: None,
                        map_token: None
                    };

                    let mut old_dummy_node = self.cell.replace(Tracked(dummy_node_perm.borrow_mut()), temp_dummy_node);
                    let old_dummy_node_token = old_dummy_node.map_token.unwrap();

                    let temp_current_node = Node {
                        data: 0,
                        next_node: None,
                        map_token: None
                    };

                    let mut deleted_current_node = current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), temp_current_node);
                    let deleted_current_token = deleted_current_node.map_token.unwrap();
                    

                    let tracked new_dummy_token;
                    let next_node_data = deleted_current_node.next_node.as_ref().unwrap().data_view.get();

                    proof {
                        new_dummy_token = current_locked_node.instance.borrow().delete_inbetween_dummy_and_normal(delete_data, next_node_data, old_dummy_node_token.get(), deleted_current_token.get(), witness.get());
                    }

                    old_dummy_node.map_token = Some(Tracked(new_dummy_token));
                    old_dummy_node.head = deleted_current_node.next_node;
                    self.cell.replace(Tracked(dummy_node_perm.borrow_mut()), old_dummy_node);

                    self.release_lock(dummy_node_perm);
                    return;
                }
            }
            
            // We do not want to delete the first node.
            // It is not possible for there to be no more nodes - we have a witness
            if (current_node_view.next_node.as_ref().is_none()) {
                return;
            }
            // We also know that the node we want to delete must be
            // larger than the node we are currently on
            if (current_node_data > delete_data) {
                return;
            }
        }
        // We can release the dummy node lock.
        self.release_lock(dummy_node_perm);
        // and begin our traversal:
        loop 
            invariant
                self.wf(),
                current_locked_node.wf(),
                current_locked_node.instance == self.instance,
                current_node_perm.id() == current_locked_node.cell.id(),
                NodeData::Node(current_node_perm.value().data) == current_locked_node.data_view,
                current_node_perm.value().map_token.is_some(),
                current_node_perm.value().map_token.unwrap()@.instance_id() == current_locked_node.instance@.id(),
                current_node_perm.value().map_token.unwrap()@.key() == NodeData::Node(current_node_perm.value().data),
                current_node_perm.value().next_node.is_some(),
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
                current_node_data < delete_data,
                witness.element() == NodeData::Node(delete_data),
                witness.instance_id() == self.instance.id()
        {
            let mut current_node_view = current_locked_node.cell.borrow(Tracked(current_node_perm.borrow_mut()));

            let mut next_locked_node = current_node_view.next_node.as_ref().unwrap().clone();
            let mut next_node_perm = next_locked_node.acquire_lock();
            let next_node_view = next_locked_node.cell.borrow(Tracked(next_node_perm.borrow_mut()));
            let next_node_data = next_locked_node.data_view.get();

            // delete the next node
            if (next_node_data == delete_data) {
                // The next node is a tail
                if (next_node_view.next_node.is_none()) {

                    let temp_current_node = Node {
                        data: 0,
                        next_node: None,
                        map_token: None
                    };

                    let mut old_current_node = current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), temp_current_node);
                    let old_current_node_token = old_current_node.map_token.unwrap();
                    // let current_node_data = old_current_node.next_node.as_ref().unwrap().data_view.get();

                    let temp_tail_node = Node {
                        data: 0,
                        next_node: None,
                        map_token: None
                    };

                    let mut deleted_tail_node = next_locked_node.cell.replace(Tracked(next_node_perm.borrow_mut()), temp_tail_node);
                    let deleted_tail_token = deleted_tail_node.map_token.unwrap();
                    

                    let tracked new_tail_token;

                    proof {
                        new_tail_token = current_locked_node.instance.borrow().delete_tail_node_after_normal_node(delete_data, old_current_node.data , old_current_node_token.get(), deleted_tail_token.get(), witness.get());
                    }

                    old_current_node.map_token = Some(Tracked(new_tail_token));
                    old_current_node.next_node = None;
                    current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), old_current_node);

                    current_locked_node.release_lock(current_node_perm);
                    return;
                }

                // The next node has a successor
                else {
                    let temp_current_node = Node {
                        data: 0,
                        next_node: None,
                        map_token: None
                    };

                    let mut old_current_node = current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), temp_current_node);
                    let old_current_node_token = old_current_node.map_token.unwrap();
                    // let current_node_data = old_current_node.next_node.as_ref().unwrap().data_view.get();

                    let temp_deleted_node = Node {
                        data: 0,
                        next_node: None,
                        map_token: None
                    };

                    let mut deleted_node = next_locked_node.cell.replace(Tracked(next_node_perm.borrow_mut()), temp_deleted_node);
                    let delted_token = deleted_node.map_token.unwrap();
                    

                    let tracked new_tail_token;
                    let successor_data = deleted_node.next_node.as_ref().unwrap().data_view.get();

                    proof {
                        new_tail_token = current_locked_node.instance.borrow().delete_inbetween_normal_and_normal(delete_data, old_current_node.data, successor_data, old_current_node_token.get(), delted_token.get(), witness.get());
                    }

                    old_current_node.map_token = Some(Tracked(new_tail_token));
                    old_current_node.next_node = deleted_node.next_node;
                    current_locked_node.cell.replace(Tracked(current_node_perm.borrow_mut()), old_current_node);

                    current_locked_node.release_lock(current_node_perm);
                    return;
                }
            }

            else if (delete_data < next_node_data) {
                // This is not reachable as we would have
                // current_node_data < delete_data < next_node_data
                // Which implies we are trying to delete a node that doesn't exist
                // but we have a witness.
                return;
            }

            // otherwise we need to traverse:
            else {
                if (next_node_view.next_node.is_none()) {
                    // if next_node has no successor, then we have reached the end without deleting
                    // this is impossible as we have a witness
                    return;
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

// proof fn no_node_exists(data: NodeData, token: &machine::nodes, instance: machine::Instance) 
//     requires
//         token.instance_id() == instance.id(),
//         token.value().is_some(),
//         data != NodeData::Dummy,
//         token.key() < data,
//         data < token.value().unwrap(),
//     ensures
//         forall |locked_node: LockedNode| #![auto] 
//             (locked_node.wf() && locked_node.instance == instance)
//                 ==> locked_node.data_view != data
// {
// }

// proof fn no_token_exists(data: NodeData, token: &machine::nodes, instance: machine::Instance) 
//     requires
//         token.instance_id() == instance.id(),
//         token.value().is_some(),
//         data != NodeData::Dummy,
//         token.key() < data,
//         data < token.value().unwrap(),
//     ensures
//         !(exists |token: machine::nodes| token.key() == data)
// {
// }

fn main() {
    let linked_list = Arc::new(LinkedList::new());

    let elements = [7,3,8,9,4,2,1,15,13,2,12,5,5,5,5,5];
    let mut join_handles: Vec<JoinHandle<Option<DataWitness>>> = Vec::new();

    let mut i = 0;
    while i < elements.len()
        invariant
            0 <= i <= elements.len(),
            join_handles.len() == i,
            linked_list.wf(),
            forall|j: int, ret|
                0 <= j < i ==> join_handles@.index(j).predicate(ret) ==>
                    (
                        (
                            ret.is_some() ==> (
                                ret.unwrap().witness.instance_id() == linked_list.instance@.id() &&
                                ret.unwrap().witness.element() == NodeData::Node(elements[j]) &&
                                ret.unwrap().data == elements[j] &&
                                exists |locked_node: LockedNode| #![auto]
                                    locked_node.wf() && 
                                    locked_node.instance@.id() == ret.unwrap().witness.instance_id() &&
                                    locked_node.data_view == ret.unwrap().witness.element()
                            )
                        ) &&
                        (
                            ret.is_none() ==> 
                                exists |locked_node: LockedNode| #![auto]
                                    locked_node.wf() && 
                                    locked_node.instance == linked_list.instance &&
                                    locked_node.data_view == NodeData::Node(elements[j])
                        )
                    )
        decreases
            elements.len() - i
    {

        // Insertion
        let linked_list_clone = linked_list.clone();
        let insert_data = elements[i];
        let join_handle = spawn(
            (move || -> (data_witness: Option<DataWitness>)
                requires
                    linked_list_clone.wf()
                ensures
                    linked_list_clone.wf(),
                    data_witness.is_some() ==> (
                        data_witness.unwrap().witness.instance_id() == linked_list_clone.instance@.id() &&
                        data_witness.unwrap().witness.element() == NodeData::Node(insert_data) &&
                        data_witness.unwrap().data == insert_data &&
                        exists |locked_node: LockedNode| #![auto]
                            locked_node.wf() && 
                            locked_node.instance@.id() == data_witness.unwrap().witness.instance_id() &&
                            locked_node.data_view == data_witness.unwrap().witness.element()
                    ),
                    data_witness.is_none() ==> (
                        (
                            exists |locked_node: LockedNode| #![auto]
                                locked_node.wf() && 
                                locked_node.instance == linked_list_clone.instance &&
                                locked_node.data_view == NodeData::Node(insert_data)
                        )
                    )
                {
                    linked_list_clone.insert(elements[i])
                }
            )
        );
        join_handles.push(join_handle);
        i = i + 1;
    }

    let mut data_witnesses: Vec<DataWitness> = Vec::new();
    let mut i = 0;
    while i < elements.len()
        invariant
            0 <= i <= elements.len(),
            join_handles.len() == elements.len() - i,
            linked_list.wf(),
            forall|j: int, ret|
                0 <= j < join_handles.len() ==> join_handles@.index(j).predicate(ret) ==>
                    (
                        (
                            ret.is_some() ==> (
                                ret.unwrap().witness.instance_id() == linked_list.instance@.id() &&
                                ret.unwrap().witness.element() == NodeData::Node(elements[j]) &&
                                ret.unwrap().data == elements[j] &&
                                exists |locked_node: LockedNode| #![auto]
                                    locked_node.wf() && 
                                    locked_node.instance@.id() == ret.unwrap().witness.instance_id() &&
                                    locked_node.data_view == ret.unwrap().witness.element()
                            )
                        ) &&
                        (
                            ret.is_none() ==> 
                                exists |locked_node: LockedNode| #![auto]
                                    locked_node.wf() && 
                                    locked_node.instance == linked_list.instance &&
                                    locked_node.data_view == NodeData::Node(elements[j])
                        )
                    ),
            forall |j: int| #![auto]
                0 <= j < data_witnesses.len() ==> (
                    data_witnesses[j].witness.element() == NodeData::Node(data_witnesses[j].data) &&
                    data_witnesses[j].witness.instance_id() == linked_list.instance.id()
                )
                    
        decreases
            elements.len() - i
    {
        let join_handle = join_handles.pop().unwrap();
        match join_handle.join() {
            Result::Ok(token) => {
                if token.is_some() {
                    data_witnesses.push(token.unwrap())
                }
            },
            _ => {
                return ;
            },
        };
        i = i + 1;
    }


    // Deletion
    let original_data_witnesses_len = data_witnesses.len();
    let mut join_handles: Vec<JoinHandle<()>> = Vec::new();

    while 0 < data_witnesses.len()
        invariant
            linked_list.wf(),
            join_handles.len() == original_data_witnesses_len - data_witnesses.len(),
            forall |j: int| #![auto]
                0 <= j < data_witnesses.len() ==> (
                    data_witnesses[j].witness.element() == NodeData::Node(data_witnesses[j].data) &&
                    data_witnesses[j].witness.instance_id() == linked_list.instance.id()
                )
        decreases
            data_witnesses.len()
    {
        let linked_list_clone = linked_list.clone();
        let data_witness = data_witnesses.pop().unwrap();

        let join_handle = spawn(
            (move ||
                requires
                    linked_list_clone.wf(),
                    data_witness.witness.element() == NodeData::Node(data_witness.data),
                    data_witness.witness.instance_id() == linked_list_clone.instance.id(),
                ensures
                    linked_list_clone.wf()
                {
                    linked_list_clone.delete(data_witness)
                }
            )
        );

        join_handles.push(join_handle);
    }

    while 0 < join_handles.len()
        invariant
            linked_list.wf(),             
        decreases
            join_handles.len()
    {
        let join_handle = join_handles.pop().unwrap();
        match join_handle.join() {
            Result::Ok(token) => {},
            _ => {
                return ;
            },
        };
    }
}
}