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
use vstd::simple_pptr::*;

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

pub struct NodeContent {
    pub data: NodeData,
    pub next_node: Option<PPtr<LockedNode>>,
    pub map_token: Tracked<machine::nodes>
}

pub type NodeGhost = Option<(cell::PointsTo<NodeContent>, Option<simple_pptr::PointsTo<LockedNode>>)>;

pub struct LockedNodePredicate;

impl AtomicInvariantPredicate<
    (PCell<NodeContent>, machine::Instance, NodeData, nat),
    bool,
    NodeGhost,
> for LockedNodePredicate {
    open spec fn atomic_inv(
        k: (PCell<NodeContent>, machine::Instance, NodeData, nat),
        v: bool,
        g: NodeGhost,
    ) -> bool {
        node_invariant(k.0, k.1, k.2, k.3, v, g)
    }
}

pub open spec fn node_invariant(
    cell: PCell<NodeContent>,
    instance: machine::Instance,
    data_view: NodeData,
    node_id: nat,
    v: bool,
    g: NodeGhost
) -> bool 
    decreases node_id
{
    match g {
        None => v == true,
        Some((content_perm, next_perm)) => {
            v == false &&
            content_perm.id() == cell.id() &&
            content_perm.is_init() &&
            content_perm.value().data == data_view &&
            content_perm.value().data != NodeData::Dummy &&
            content_perm.value().map_token@.instance_id() == instance.id() &&
            content_perm.value().map_token@.key() == content_perm.value().data &&


            (content_perm.value().next_node.is_none() <==> next_perm.is_none()) && 


            (next_perm.is_some() ==> {
                let next_locked_node = content_perm.value().next_node.unwrap().view(next_perm.unwrap());
                node_id > 0 &&
                next_locked_node.node_id < node_id &&
                next_locked_node.wf()
            })
        }
    }
}

pub struct LockedNode {
    pub atomic: AtomicBool<
        (PCell<NodeContent>, machine::Instance, NodeData, nat), 
        Option<cell::PointsTo<NodeContent>>, 
        LockedNodePredicate
    >,
    pub cell: PCell<NodeContent>,
    pub instance: Tracked<machine::Instance>,
    pub data_view: NodeData,
    pub ghost node_id: nat,
}

impl LockedNode {
    pub open spec fn wf(&self) -> bool {
        self.atomic.constant() == (self.cell, self.instance@, self.data_view, self.node_id)
    }
}

fn main() {
    let tracked (
        Tracked(instance),
        Tracked(nodes),
        Tracked(initialized),
    ) = machine::Instance::initialize();
}
}