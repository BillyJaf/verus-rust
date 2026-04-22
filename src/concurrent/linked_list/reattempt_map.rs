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

            #[sharding(variable)]
            pub initialized: bool,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            // Invariant ensures that:
            // 1. The list is sorted by the data each node stores (dummy node is minimum)
            // 
            //
            // If the map is uninitialised, then it doesn't contain anything, not even the dummy node (and vice versa)
            (!self.initialized <==> self.nodes.is_empty()) &&

            // If the map is initialised, then it must at least have the dummy node:
            // This case looks redundant, but I believe it will help the SMT solver.
            (self.initialized <==> self.nodes.dom().contains(NodeData::Dummy)) &&

            // If the map contains [NodeData::Dummy => None], then it can't contain anything else
            ((self.initialized && self.nodes[NodeData::Dummy] == None::<NodeData>) <==> self.nodes.dom().len() == 1) &&

            // The remaining conditions are checked if the map contains real data:

            (
                // If the map is initialised
                (self.initialized && self.nodes[NodeData::Dummy] != None::<NodeData>) ==> 
                    (
                        // The dummy node points to the smallest element in the list:
                        (
                            exists |i: u32| #![auto] 
                                self.nodes[NodeData::Dummy] == Some(NodeData::Node(i)) &&
                                forall |j: u32| #![auto] self.nodes.dom().contains(NodeData::Node(j)) ==> i <= j
                        
                        ) &&

                        // There is a node that points to None (this is the tail of the list).
                        // This node must be the largest element in the list:
                        (
                            exists |i: u32| #![auto]
                                self.nodes.dom().contains(NodeData::Node(i)) && 
                                self.nodes[NodeData::Node(i)] == None::<NodeData> &&
                                forall |j: u32| #![auto] self.nodes.dom().contains(NodeData::Node(j)) ==> j <= i
                        ) &&

                        // Everything else in the list is sorted (smallest to largest).
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

                        // The following points could be included in the above statements.
                        // I decided to separate them because of how important they are.
                        // We must assert that for any mapping [a => c], there are no entries in the map
                        // with key b such that a < b < c. Also, if there is a map with [a => None],
                        // then there are no entires in the map with key b and a < b. Similarly, the map
                        // [Dummy => a] implies that there are no keys smaller than a.
                        // Case [Dummy => a]:
                        (
                            exists |i: u32| #![auto] 
                                self.nodes[NodeData::Dummy] == Some(NodeData::Node(i)) ==> 
                                (forall |j: u32| #![auto] j < i ==> !self.nodes.dom().contains(NodeData::Node(j)))
                        
                        ) &&
                        // Case [a => None]
                        (
                            exists |i: u32| #![auto]
                                (
                                    self.nodes.dom().contains(NodeData::Node(i)) && 
                                    self.nodes[NodeData::Node(i)] == None::<NodeData>
                                ) ==> (
                                    forall |j: u32| #![auto] i < j ==> !self.nodes.dom().contains(NodeData::Node(j))
                                )
                        ) &&
                        // Every inbetween:
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
            // // If the map is initialised
            // (self.initialized ==> 
            //     (
            //         self.nodes.dom().contains(NodeData::Dummy)
            //     &&  self.nodes[NodeData::Dummy] == None::<NodeData> || 
            //         (
            //             exists |i: u32| #![auto] 
            //                 self.nodes[NodeData::Dummy] == Some(NodeData::Node(i)) &&
            //                 forall |j: u32| #![auto] self.nodes.dom().contains(NodeData::Node(j)) ==> i <= j
                        
            //         )
            //     // Everything else is sorted with unique data
            //     &&  (
            //             forall |i: u32| #![auto] self.nodes.dom().contains(NodeData::Node(i)) ==> 
            //                 (
            //                     self.nodes[NodeData::Node(i)] == None::<NodeData> ||
            //                     (exists |j: u32| #![auto] self.nodes[NodeData::Node(i)] == Some(NodeData::Node(j)) && i < j)
            //                 )
            //         )
            //     // Every map entry (except for the dummy) is pointed to by another entry
            //     &&  (forall |i: u32| #![auto] self.nodes.dom().contains(NodeData::Node(i)) ==>
            //             (
            //                 self.nodes[NodeData::Dummy] == Some(NodeData::Node(i)) ||
            //                 (exists |j: u32| #![auto] self.nodes[NodeData::Node(j)] == Some(NodeData::Node(i)) && j < i)
            //             )
            //         )
            //     )
            // )
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

        // transition!{
        //     add_to_tail()
        //     {   
        //         require(!pre.initialized);
        //         update initialized = true;
        //         add nodes += [NodeData::Dummy => None];
        //     }
        // }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { 
        }

        #[inductive(add_dummy_node)]
        fn add_dummy_node_inductive(pre: Self, post: Self) { 
        }
    }
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
}
}