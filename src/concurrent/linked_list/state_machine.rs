use verus_state_machines_macros::tokenized_state_machine;
use verus_builtin::*;
use verus_builtin_macros::*;
use std::sync::Arc;
use std::cmp::Ordering;
use vstd::{
    atomic_ghost::*,
    modes::*,
    prelude::*,
    thread::*,
    pervasive::*, 
    prelude::*, 
    cell::pcell_maybe_uninit::{
        PCell,
        PointsTo
    },
    seq_lib::*,
};

verus! {

pub enum NodeData {
    Nil,
    CAR(u32)
}

impl NodeData {
    pub fn clone(&self) -> (cloned: Self) 
        ensures
            *self == cloned
    {
        match self {
            NodeData::Nil => NodeData::Nil,
            NodeData::CAR(i) => NodeData::CAR(*i),
        }
    }

    pub fn get(&self) -> (value: u32) 
        requires
            *self != NodeData::Nil
        ensures
            *self == NodeData::CAR(value)
    {
        match self {
            NodeData::CAR(i) => *i,
            _ => 0
        }
    }

    pub open spec fn spec_lt(self, other: Self) -> bool {
        match (self, other) {
            (NodeData::Nil, NodeData::Nil) => false,
            (NodeData::Nil, _) => true,
            (_, NodeData::Nil) => false,
            (NodeData::CAR(a), NodeData::CAR(b)) => a < b,
        }
    }

    pub open spec fn spec_le(self, other: Self) -> bool {
        match (self, other) {
            (NodeData::Nil, NodeData::Nil) => true,
            (NodeData::Nil, _) => true,
            (_, NodeData::Nil) => false,
            (NodeData::CAR(a), NodeData::CAR(b)) => a <= b,
        }
    }

    pub open spec fn spec_gt(self, other: Self) -> bool {
        match (self, other) {
            (NodeData::Nil, NodeData::Nil) => false,
            (NodeData::Nil, _) => false,
            (_, NodeData::Nil) => true,
            (NodeData::CAR(a), NodeData::CAR(b)) => a > b,
        }
    }

    pub open spec fn spec_ge(self, other: Self) -> bool {
        match (self, other) {
            (NodeData::Nil, NodeData::Nil) => true,
            (NodeData::Nil, _) => false,
            (_, NodeData::Nil) => true,
            (NodeData::CAR(a), NodeData::CAR(b)) => a >= b,
        }
    }
}

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(map)]
            pub data_map: Map<NodeData, Option<NodeData>>,
            
            #[sharding(variable)]
            pub initialized: bool,
        }

        #[invariant]
        pub fn unique_inv(&self) -> bool {   
            forall |i: NodeData, j: NodeData| #![auto] 
                (
                    self.data_map.dom().contains(i) &&
                    self.data_map.dom().contains(j) &&
                    self.data_map[i] == self.data_map[j]
                ) ==>
                (
                    i == j
                )      
        }

        #[invariant]
        pub fn sorted_inv(&self) -> bool {
            (
                // If the map is initialised with real data
                (self.initialized && self.data_map[NodeData::Nil].is_some()) ==> 
                    (
                        // Nil is the smallest CAR:
                        // We don't need to prove that everything is larger than Nil
                        // Since this is done in the spec_gt and spec_ge functions
                        (
                            forall |i: NodeData| #![auto] 
                                (
                                    i < self.data_map[NodeData::Nil].unwrap() &&
                                    i != NodeData::Nil
                                ) ==> ( 
                                    !self.data_map.dom().contains(i)
                                )
                        
                        ) &&
                        (
                            forall |i: NodeData| #![auto] 
                                (
                                    self.data_map.dom().contains(i) &&
                                    i != NodeData::Nil
                                ) ==> ( 
                                    self.data_map[NodeData::Nil].unwrap() <= i
                                )
                        
                        ) &&

                        // Nothing larger than the tail CAR is in the list:
                        // The domain containment is used for transitions
                        // showing key absence
                        (
                            forall |i: NodeData| #![auto]
                                (
                                    self.data_map.dom().contains(i) && 
                                    self.data_map[i] == None::<NodeData>
                                ) ==> (
                                    (
                                        forall |j: NodeData| #![auto] 
                                            i < j ==> !self.data_map.dom().contains(j)
                                    ) && (
                                        forall |j: NodeData| #![auto] 
                                            self.data_map.dom().contains(j) ==> j <= i
                                    )
                                )
                        ) &&

                        // Everything in the list is sorted (smallest to largest).
                        // Nodes either point to something strictly larger, or to None
                        (
                            forall |i: NodeData| #![auto] 
                                (
                                    self.data_map.dom().contains(i) && 
                                    self.data_map[i] != None::<NodeData>
                                ) ==> (
                                    i < self.data_map[i].unwrap() &&
                                    self.data_map.dom().contains(self.data_map[i].unwrap())
                                )
                        ) &&

                        // // We must assert that for any mapping [a => c], there are no entries in the map
                        // // with key b such that a < b < c. 
                        (
                            forall |i: NodeData| #![auto] 
                                (
                                    self.data_map.dom().contains(i) && 
                                    self.data_map[i] != None::<NodeData>
                                ) ==> (
                                    forall |j: NodeData| #![auto] 
                                        (
                                            i < j && 
                                            j < self.data_map[i].unwrap()
                                        ) ==> (
                                            !self.data_map.dom().contains(j)
                                        )
                                )
                        )
                    )
            )
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            // If the map is uninitialised, then it doesn't contain anything, not even the nil node (and vice versa)
            (!self.initialized <==> self.data_map.is_empty()) &&

            // If the map is initialised, then it must at least have the nil node:
            // This case looks redundant, but I believe it will help the SMT solver.
            (self.initialized <==> self.data_map.dom().contains(NodeData::Nil)) &&

            // If the map contains [NodeData::Nil => None], then it can't contain anything else
            (
                (self.initialized && self.data_map[NodeData::Nil] == None::<NodeData>) <==> 
                (self.data_map =~= Map::empty().insert(NodeData::Nil, None::<NodeData>))
            )
        }

        init!{
            initialize()
            {
                init data_map = Map::empty();
                init initialized = false;
            }
        }

        transition!{
            create_nil()
            {   
                require(!pre.initialized);
                update initialized = true;
                add data_map += [NodeData::Nil => None];
            }
        }

        transition!{
            insert_at_tail(current_tail: NodeData, new_tail: NodeData)
            {   
                require(pre.initialized);
                require(current_tail < new_tail);
                remove data_map -= [current_tail => None];
                add data_map += [current_tail => Some(new_tail)];
                add data_map += [new_tail => None];
            }
        }

        transition!{
            insert_inbetween(lower_car: NodeData, insert_car: NodeData, upper_car: NodeData)
            {   
                require(pre.initialized);
                require(lower_car < insert_car);
                require(insert_car < upper_car);
                remove data_map -= [lower_car => Some(upper_car)];
                add data_map += [lower_car => Some(insert_car)];
                add data_map += [insert_car => Some(upper_car)];
            }
        }

        transition!{
            delete_at_tail(lower_car: NodeData, delete_car: NodeData)
            {   
                require(pre.initialized);
                require(delete_car != NodeData::Nil);
                remove data_map -= [lower_car => Some(delete_car)];
                remove data_map -= [delete_car => None];
                add data_map += [lower_car => None];
            }
        }

        transition!{
            delete_inbetween(lower_car: NodeData, delete_car: NodeData, upper_car: NodeData)
            {   
                require(pre.initialized);
                require(delete_car != NodeData::Nil);
                remove data_map -= [lower_car => Some(delete_car)];
                remove data_map -= [delete_car => Some(upper_car)];
                add data_map += [lower_car => Some(upper_car)];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {
            assert(post.data_map.is_empty());
        }

        #[inductive(create_nil)]
        fn create_nil_inductive(pre: Self, post: Self) { 
        }

        #[inductive(insert_at_tail)]
        fn insert_at_tail_inductive(pre: Self, post: Self, current_tail: NodeData, new_tail: NodeData) {            
            assert 
                forall |i: NodeData|
                    #[trigger] (new_tail < i)
                implies
                    !pre.data_map.dom().contains(i)
            by {
                assert(current_tail < i);

                assert(
                    current_tail < i
                    ==> !pre.data_map.dom().contains(i)
                );

                assert(!pre.data_map.dom().contains(i));
            }

            assert
                forall |i: NodeData| #![auto] 
                    pre.data_map.dom().contains(i) 
                implies 
                    #[trigger] (i < new_tail)
            by {
                assert(i <= current_tail);
                assert(current_tail < new_tail);
            };

            assert
                forall |i: NodeData| 
                    post.data_map.dom().contains(i)
                implies
                    #[trigger] (i <= new_tail)
            by {
                assert(pre.data_map.dom().contains(i) || i == new_tail);
                assert(i < new_tail || i == new_tail);
            }
        }

        #[inductive(insert_inbetween)]
        fn insert_inbetween_inductive(pre: Self, post: Self, lower_car: NodeData, insert_car: NodeData, upper_car: NodeData) {             
            assert
                forall |i: NodeData|
                    (
                        #[trigger] post.data_map.dom().contains(i) && 
                        post.data_map[i] == None::<NodeData>
                    ) 
                implies 
                    (
                        forall |j: NodeData| #![auto] 
                            i < j ==> !post.data_map.dom().contains(j)
                    ) && (
                        forall |j: NodeData| #![auto] 
                            post.data_map.dom().contains(j) ==> j <= i
                    )
            by {
                assert(insert_car < upper_car);
                assert(upper_car <= i);
            };    

            assert
                forall |i: NodeData| #![auto] 
                    (
                        #[trigger] post.data_map.dom().contains(i) && 
                        post.data_map[i] != None::<NodeData>
                    )
                implies
                    forall |j: NodeData| #![auto] 
                        (
                            i < j && 
                            j < post.data_map[i].unwrap()
                        ) ==> (
                            !post.data_map.dom().contains(j)
                        )
            by {
                if (i == lower_car) {
                    assert(post.data_map[i] == Some(insert_car));
                } else if (i == insert_car) {
                    assert(post.data_map[i] == Some(upper_car));
                    // Removing this fails verification - I believe it is because of triggers
                    assert(
                        forall |j: NodeData| #![auto] 
                            (
                                lower_car < j && 
                                j < upper_car
                            ) ==> (
                                !pre.data_map.dom().contains(j)
                            )
                        );
                } else if (i < lower_car) {
                    assert(pre.data_map[i].unwrap() < insert_car);
                } else {
                    assert(lower_car < i);
                }
            }
        }

        #[inductive(delete_at_tail)]
        fn delete_at_tail_inductive(pre: Self, post: Self, lower_car: NodeData, delete_car: NodeData) {
            assert(post.data_map.dom().contains(NodeData::Nil));

            if (lower_car == NodeData::Nil) {
                assert forall |i: NodeData|
                    #[trigger] pre.data_map.dom().contains(i)
                implies
                    i == lower_car || i == delete_car
                by {
                    if i == lower_car {
                    } else {
                        assert(
                            forall |j: NodeData| #![auto] 
                                pre.data_map.dom().contains(j) ==> j <= delete_car
                        );

                        assert(i <= delete_car);

                        assert(
                            forall |j: NodeData| #![auto]
                                (
                                    lower_car < j &&
                                    j < delete_car
                                ) ==> (
                                    !pre.data_map.dom().contains(j)
                                )
                        );

                        assert(i == delete_car);
                    }
                }
            }

            assert forall |i: NodeData|
                #[trigger] pre.data_map.dom().contains(i)
            implies
                (i <= lower_car) || i == delete_car
            by {
                assert(i <= delete_car);

                if i == delete_car {
                } else {
                    assert(i < delete_car);

                    assert(
                        forall |j: NodeData| #![auto]
                            (
                                lower_car < j &&
                                j < delete_car
                            ) ==> (
                                !pre.data_map.dom().contains(j)
                            )
                    );
                }
            }
        }

        #[inductive(delete_inbetween)]
        fn delete_inbetween_inductive(pre: Self, post: Self, lower_car: NodeData, delete_car: NodeData, upper_car: NodeData) {

            if (lower_car == NodeData::Nil) {
                assert
                    forall |i: NodeData|
                        #[trigger] post.data_map.dom().contains(i)
                    implies
                        (
                            i >= post.data_map[NodeData::Nil].unwrap() ||
                            i == NodeData::Nil
                        )
                by {
                    if (i == NodeData::Nil) {
                    } else {
                        assert(lower_car < i);

                        assert(
                            forall |j: NodeData| #![auto]
                                (
                                    lower_car < j &&
                                    j < delete_car
                                ) ==> (
                                    !post.data_map.dom().contains(j)
                                )
                        );

                        assert(
                            forall |j: NodeData| #![auto]
                                (
                                    delete_car < j &&
                                    j < upper_car
                                ) ==> (
                                    !post.data_map.dom().contains(j)
                                )
                        );

                        assert(
                            forall |j: NodeData| #![auto]
                                (
                                    lower_car < j &&
                                    j < upper_car
                                ) ==> (
                                    !post.data_map.dom().contains(j)
                                )
                        );
                    }
                }
            }
 
            assert
                forall |i: NodeData| #![auto] 
                    (
                        post.data_map.dom().contains(i) && 
                        #[trigger] post.data_map[i] != None::<NodeData>
                    ) 
                implies
                    forall |j: NodeData| #![auto] 
                        (
                            i < j && 
                            j < post.data_map[i].unwrap()
                        ) ==> (
                            !post.data_map.dom().contains(j)
                        )
            by {
                assert(
                    forall |j: NodeData| #![auto]
                        (
                            lower_car < j &&
                            j < delete_car
                        ) ==> (
                            !pre.data_map.dom().contains(j)
                        )
                );
                    
                assert(
                    forall |j: NodeData| #![auto]
                        (
                            delete_car < j &&
                            j < upper_car
                        ) ==> (
                            !pre.data_map.dom().contains(j)
                        )
                );
            }
        }
    }
}
}