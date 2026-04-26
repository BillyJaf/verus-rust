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

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { 
        }
    }
}

pub struct LockedNodePredicate;

impl AtomicInvariantPredicate<
    (PCell<Node>, machine::Instance, NodeData),
    bool,
    Option<cell::PointsTo<Node>>,
> for LockedNodePredicate {
    open spec fn atomic_inv(
        k: (PCell<Node>, machine::Instance, NodeData),
        v: bool,
        g: Option<cell::PointsTo<Node>>,
    ) -> bool {
        node_invariant(k.0, k.1, k.2, v, g)
    }
}

pub open spec fn node_invariant(
    cell: PCell<Node>,
    instance: machine::Instance,
    data_view: NodeData,
    v: bool,
    g: Option<cell::PointsTo<Node>>
) -> bool {
    match g {
        None => v == true,
        Some(points_to) => {
            v == false &&
            points_to.id() == cell.id() &&
            points_to.is_init() &&
            points_to.value().data == data_view &&
            points_to.value().data != NodeData::Dummy &&
            points_to.value().map_token@.instance_id() == instance.id() &&
            points_to.value().map_token@.key() == points_to.value().data &&
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

pub struct LockedNode {
    pub atomic: AtomicBool<
        (PCell<Node>, machine::Instance, NodeData), 
        Option<cell::PointsTo<Node>>, 
        LockedNodePredicate
    >,
    pub cell: PCell<Node>,
    pub instance: Tracked<machine::Instance>,
    pub data_view: NodeData,
}

impl LockedNode {
    pub open spec fn wf(&self) -> bool {
        self.atomic.constant() == (self.cell, self.instance@, self.data_view)
    }
}

pub struct Node {
    pub data: NodeData,
    pub next_node: Option<Box<LockedNode>>,
    pub map_token: Tracked<machine::nodes>
}

fn main() {
    let tracked (
        Tracked(instance),
        Tracked(nodes),
        Tracked(initialized),
    ) = machine::Instance::initialize();
}
}