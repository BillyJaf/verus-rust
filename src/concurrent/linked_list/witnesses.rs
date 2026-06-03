#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use verus_state_machines_macros::tokenized_state_machine;
use verus_builtin::*;
use verus_builtin_macros::*;
use std::sync::Arc;
use vstd::{
    atomic_ghost::*,
    modes::*,
    prelude::*,
    thread::*,
    pervasive::*, 
    cell::pcell_maybe_uninit::{
        PCell,
        PointsTo
    },
    seq_lib::*,
};

verus! {

pub enum Operation {
    CreateNil,
    Insert(NodeData),
    InsertFail(NodeData),
    Delete(NodeData),
    DeleteFail(NodeData)
}

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

pub open spec fn count_inserts_up_to(
    operation_index: nat,
    insert_value: NodeData,
    history: Map<nat, Operation>,
) -> nat
decreases operation_index
{
    if operation_index == 0 {
        0nat
    } else {
        let possible_insert = if history[operation_index] == Operation::Insert(insert_value) { 1nat } else { 0nat };

        possible_insert + count_inserts_up_to((operation_index - 1) as nat, insert_value, history)
    }
}

pub open spec fn count_deletes_up_to(
    operation_index: nat,
    insert_value: NodeData,
    history: Map<nat, Operation>,
) -> nat
decreases operation_index
{
    if operation_index == 0 {
        0nat
    } else {
        let possible_insert = if history[operation_index] == Operation::Delete(insert_value) { 1nat } else { 0nat };

        possible_insert + count_deletes_up_to((operation_index - 1) as nat, insert_value, history)
    }
}

pub proof fn stable_counts(
    data: NodeData,
    up_to_index: nat,
    pre_history: Map<nat, Operation>,
    post_history: Map<nat, Operation>,
)
requires
    up_to_index < pre_history.dom().len(),
    pre_history =~= post_history.remove(pre_history.len()),
ensures
    count_inserts_up_to(up_to_index, data, pre_history) == count_inserts_up_to(up_to_index, data, post_history),
    count_deletes_up_to(up_to_index, data, pre_history) == count_deletes_up_to(up_to_index, data, post_history)
decreases
    up_to_index
{
    if up_to_index == 0 {}
    else {
        stable_counts(data, (up_to_index - 1) as nat, pre_history, post_history);
    }
}
    


tokenized_state_machine!{
    machine {
        fields {
            #[sharding(map)]
            pub data_map: Map<NodeData, Option<NodeData>>,
            
            #[sharding(variable)]
            pub initialized: bool,

            #[sharding(map)]
            pub operation_history: Map<nat, Operation>,
        }

        #[invariant]
        pub fn uninitialised_operation_inv(&self) -> bool {
            (self.operation_history.is_empty() <==> !self.initialized) &&
            (self.initialized ==> (self.operation_history[0] == Operation::CreateNil)) &&
            (forall |i: nat, j: nat| #![auto]
                (
                    self.operation_history.dom().contains(i) && 
                    self.operation_history[i] == Operation::CreateNil && 
                    self.operation_history.dom().contains(j) &&
                    self.operation_history[j] == Operation::CreateNil 
                ) ==> i == j
            )
        }

        #[invariant]
        pub fn more_inserts_than_deletes_inv(&self) -> bool {
            forall |i: nat, data: NodeData| #![auto] 
                (
                    i < self.operation_history.dom().len() &&
                    self.operation_history[i] == Operation::Insert(data)
                ) ==> (
                    count_inserts_up_to(i, data, self.operation_history) == count_deletes_up_to(i, data, self.operation_history) ||
                    count_inserts_up_to(i, data, self.operation_history) == count_deletes_up_to(i, data, self.operation_history) + 1
                )
        }

        #[invariant]
        pub fn insert_count_equals_delete_count_implies_not_in_list_inv(&self) -> bool {
            forall |data: NodeData| #![auto]
                !self.data_map.dom().contains(data) ==> (
                forall |i: nat| #![auto] 
                    (
                        i < self.operation_history.dom().len() &&
                        self.operation_history[i] == Operation::Insert(data)
                    ) ==> 
                    count_inserts_up_to(i, data, self.operation_history) == count_deletes_up_to(i, data, self.operation_history)
                )
        }

        #[invariant]
        pub fn insert_count_larger_than_delete_count_implies_in_list_inv(&self) -> bool {
            forall |data: NodeData| #![auto]
                self.data_map.dom().contains(data) ==> (
                forall |i: nat| #![auto] 
                    (
                        i < self.operation_history.dom().len() &&
                        self.operation_history[i] == Operation::Insert(data)
                    ) ==> 
                    count_inserts_up_to(i, data, self.operation_history) == count_deletes_up_to(i, data, self.operation_history) + 1
                )
        }

        #[invariant]
        pub fn main_operation_inv(&self) -> bool {
            self.operation_history.dom().finite() &&
            (forall |i: nat| i < self.operation_history.dom().len() <==> self.operation_history.dom().contains(i))
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
                init operation_history = Map::empty();
            }
        }

        transition!{
            create_nil()
            {   
                require(!pre.initialized);
                update initialized = true;
                add data_map += [NodeData::Nil => None];

                add operation_history += [0 => Operation::CreateNil]; 
            }
        }

        transition!{
            insert(lower_car: NodeData, insert_car: NodeData, upper_car: Option<NodeData>)
            {   
                require(lower_car < insert_car);
                require(upper_car.is_some() ==> insert_car < upper_car.unwrap());
                remove data_map -= [lower_car => upper_car];
                add data_map += [lower_car => Some(insert_car)];
                add data_map += [insert_car => upper_car];

                birds_eye let next_operation_index = pre.operation_history.dom().len();
                add operation_history += [next_operation_index => Operation::Insert(insert_car)];
            }
        }

        transition!{
            delete(lower_car: NodeData, delete_car: NodeData, upper_car: Option<NodeData>)
            {   
                require(lower_car < delete_car);
                require(upper_car.is_some() ==> delete_car < upper_car.unwrap());
                remove data_map -= [lower_car => Some(delete_car)];
                remove data_map -= [delete_car => upper_car];
                add data_map += [lower_car => upper_car];

                birds_eye let next_operation_index = pre.operation_history.dom().len();
                add operation_history += [next_operation_index => Operation::Delete(delete_car)];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {
            assert(post.data_map.is_empty());
        }

        #[inductive(create_nil)]
        fn create_nil_inductive(pre: Self, post: Self) { 
        }

        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, lower_car: NodeData, insert_car: NodeData, upper_car: Option<NodeData>) {  
            if (upper_car.is_some()) { 
                let upper_car = upper_car.unwrap();      
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
            } else {
                assert 
                    forall |i: NodeData|
                        #[trigger] (insert_car < i)
                    implies
                        !pre.data_map.dom().contains(i)
                by {
                    assert(lower_car < i);
                }

                assert
                    forall |i: NodeData| 
                        post.data_map.dom().contains(i)
                    implies
                        #[trigger] (i <= insert_car)
                by {
                    assert
                        forall |i: NodeData| #![auto] 
                            pre.data_map.dom().contains(i) 
                        implies 
                            #[trigger] (i < insert_car)
                    by {
                        assert(i <= lower_car);
                        assert(lower_car < insert_car);
                    };

                    assert(pre.data_map.dom().contains(i) || i == insert_car);
                    assert(i < insert_car || i == insert_car);
                }
            }

            assert(
                forall |data: NodeData| #![auto]
                    !pre.data_map.dom().contains(data) ==> (
                    forall |i: nat| #![auto] 
                        (
                            i < pre.operation_history.dom().len() &&
                            pre.operation_history[i] == Operation::Insert(data)
                        ) ==> 
                        count_inserts_up_to(i, data, pre.operation_history) == count_deletes_up_to(i, data, pre.operation_history)
                    )
            );

            assert(!pre.data_map.dom().contains(insert_car));

            assert(
                forall |i: nat| #![auto] 
                    (
                        i < pre.operation_history.dom().len() &&
                        pre.operation_history[i] == Operation::Insert(insert_car)
                    ) ==> 
                    count_inserts_up_to(i, insert_car, pre.operation_history) == count_deletes_up_to(i, insert_car, pre.operation_history)
            );

            assert(pre.operation_history.insert(pre.operation_history.len(), Operation::Insert(insert_car)) =~= post.operation_history);

            assert(post.data_map.dom().contains(insert_car));

            assert(
                forall |data: NodeData| #![auto]
                    !post.data_map.dom().contains(data) ==> !pre.data_map.dom().contains(data)
            );

            assert(
                forall |data: NodeData| #![auto]
                    !post.data_map.dom().contains(data) ==> (
                        forall |i: nat| #![auto] 
                            (
                                i < pre.operation_history.dom().len() &&
                                pre.operation_history[i] == Operation::Insert(insert_car)
                            ) ==> 
                            count_inserts_up_to(i, insert_car, pre.operation_history) == count_deletes_up_to(i, insert_car, pre.operation_history)
                    )
            );


            assert
                forall |data: NodeData| #![auto]
                    !post.data_map.dom().contains(data) 
            implies 
                (
                    forall |i: nat| #![auto]
                        i < pre.operation_history.dom().len() ==>
                            count_inserts_up_to(i, data, pre.operation_history) == count_inserts_up_to(i, data, post.operation_history) &&
                            count_deletes_up_to(i, data, pre.operation_history) == count_deletes_up_to(i, data, post.operation_history)
                )
            by {
                assert forall |i: nat|
                    i < pre.operation_history.dom().len()
                implies
                    count_inserts_up_to(i, data, pre.operation_history) == count_inserts_up_to(i, data, post.operation_history) &&
                    count_deletes_up_to(i, data, pre.operation_history) == count_deletes_up_to(i, data, post.operation_history)
                by {
                    stable_counts(data, i, pre.operation_history, post.operation_history);
                };
            };

            assert(
                forall |data: NodeData| #![auto]
                    !post.data_map.dom().contains(data) ==> (
                    forall |i: nat| #![auto] 
                        (
                            i < post.operation_history.dom().len() &&
                            post.operation_history[i] == Operation::Insert(data)
                        ) ==> 
                        ((count_inserts_up_to(i, data, post.operation_history) == count_inserts_up_to(i, data, pre.operation_history) && count_deletes_up_to(i, data, post.operation_history) == count_deletes_up_to(i, data, pre.operation_history)) || i == pre.operation_history.dom().len())
                    )
                );

            assert(
                forall |data: NodeData| #![auto]
                    !post.data_map.dom().contains(data) ==> (
                    forall |i: nat| #![auto] 
                        (
                            i < post.operation_history.dom().len() &&
                            post.operation_history[i] == Operation::Insert(data)
                        ) ==> 
                        (count_inserts_up_to(i, data, pre.operation_history) == count_deletes_up_to(i, data, pre.operation_history) || i == pre.operation_history.dom().len())
                    )
                );

                assert(
                forall |data: NodeData| #![auto]
                    !post.data_map.dom().contains(data) ==> (
                    forall |i: nat| #![auto] 
                        (
                            i < post.operation_history.dom().len() &&
                            post.operation_history[i] == Operation::Insert(data)
                        ) ==> 
                        (count_inserts_up_to(i, data, post.operation_history) == count_deletes_up_to(i, data, post.operation_history) || i == pre.operation_history.dom().len())
                    )
                );



            // assert(
            //     forall |data: NodeData| #![auto]
            //         !post.data_map.dom().contains(data) ==> (
            //         forall |i: nat| #![auto] 
            //             (
            //                 i < post.operation_history.dom().len() &&
            //                 post.operation_history[i] == Operation::Insert(data)
            //             ) ==> 
            //             count_inserts_up_to(i, data, post.operation_history) == count_deletes_up_to(i, data, post.operation_history)
            //         )
            //     );


            // assert(
            //     forall |i: nat, data: NodeData| #![auto] 
            //         (
            //             i < pre.operation_history.dom().len() &&
            //             pre.operation_history[i] == Operation::Insert(data)
            //         ) ==> (
            //             count_inserts_up_to(i, data, pre.operation_history) == count_deletes_up_to(i, data, pre.operation_history) ||
            //             count_inserts_up_to(i, data, pre.operation_history) == count_deletes_up_to(i, data, pre.operation_history) + 1
            //         )
            //     );
            // assert(pre.operation_history.insert(pre.operation_history.len(), Operation::Insert(insert_car)) =~= post.operation_history);
        }

        #[inductive(delete)]
        fn delete_inductive(pre: Self, post: Self, lower_car: NodeData, delete_car: NodeData, upper_car: Option<NodeData>) {
            if (upper_car.is_some()) {
                let upper_car = upper_car.unwrap();
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
            } else {
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
        }

        property!{
            delete_successful_empty_list(delete_car: NodeData) {
                require(NodeData::Nil < delete_car);
                have data_map >= [NodeData::Nil => None::<NodeData>];
                birds_eye let map = pre.data_map;

                assert(
                    !map.dom().contains(delete_car)
                );
            }
        }

        property!{
            delete_successful_car_not_in_list(lower_car: NodeData, delete_car: NodeData, upper_car: Option<NodeData>) {
                require(lower_car < delete_car);
                require(upper_car.is_some() ==> delete_car < upper_car.unwrap());
                have data_map >= [lower_car => upper_car];
                birds_eye let map = pre.data_map;

                assert(
                    !map.dom().contains(delete_car)
                );
            }
        }
    }
}

pub struct Nil {
    pub cdr: Option<Arc<LockedCons>>,
    pub map_token: Tracked<machine::data_map>
}

struct_with_invariants!{
    pub struct LockedNil {
        atomic: AtomicBool<_, Option<PointsTo<Nil>>, _>,
        cell: PCell<Nil>,
        instance: Tracked<machine::Instance>,
    }

    spec fn wf(&self) -> bool 
    {
        invariant on atomic with (cell, instance) is (v: bool, g: Option<PointsTo<Nil>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.is_init() &&
                    points_to.id() == cell.id() &&
                    points_to.value().map_token@.instance_id() == instance@.id() && 
                    points_to.value().map_token@.key() == NodeData::Nil &&
                    (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()) && 
                    (points_to.value().map_token@.value().is_some() ==> 
                        (
                            points_to.value().cdr.unwrap().wf() &&
                            points_to.value().cdr.unwrap().view_instance() == instance &&
                            points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
                        )
                    )
                }
            }
        }
    }
}

impl LockedNil {
    fn new() -> (locked_nil: Self)
        ensures 
            locked_nil.wf(),
    {
        let tracked (
            Tracked(instance),
            Tracked(data_map),
            Tracked(initialized),
            Tracked(operation_history)
        ) = machine::Instance::initialize();

        let tracked tuple;
        let tracked map_token;
        let tracked witness_token;
        proof {
            tuple = instance.create_nil(&mut initialized);
            map_token = tuple.0.get();
            witness_token = tuple.1.get();
        };

        let node = Nil { cdr: None::<Arc<LockedCons>>, map_token: Tracked(map_token) };
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, Tracked(instance))), false, Tracked(Some(perm)));
        Self { 
            atomic, 
            cell, 
            instance: Tracked(instance)
        }
    }

    pub open spec fn view_car(&self) -> NodeData {
        NodeData::Nil
    }

    fn acquire_lock(&self) -> (points_to: Tracked<PointsTo<Nil>>)
        requires 
            self.wf(),
        ensures 
            points_to.is_init(),
            points_to.id() == self.cell.id(),
            points_to.value().map_token@.instance_id() == self.instance@.id(), 
            points_to.value().map_token@.key() == NodeData::Nil,
            (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()), 
            (points_to.value().map_token@.value().is_some() ==> 
                (
                    points_to.value().cdr.unwrap().wf() &&
                    points_to.value().cdr.unwrap().view_instance() == self.instance &&
                    points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
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

    fn release_lock(&self, points_to: Tracked<PointsTo<Nil>>)
        requires
            self.wf(),
            points_to.is_init(),
            points_to.id() == self.cell.id(),
            points_to.value().map_token@.instance_id() == self.instance@.id(), 
            points_to.value().map_token@.key() == NodeData::Nil,
            (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()), 
            (points_to.value().map_token@.value().is_some() ==> 
                (
                    points_to.value().cdr.unwrap().wf() &&
                    points_to.value().cdr.unwrap().view_instance() == self.instance &&
                    points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
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

    fn insert(self: Arc<Self>, insert_car_raw: u32)
        requires
            self.wf()
        ensures
            self.wf()
    {
        // Acquire the lock for the nil node, and view the data inside (without taking)
        let mut nil_perm = self.acquire_lock();
        let nil_view = self.cell.borrow(Tracked(nil_perm.borrow_mut()));
        let insert_car = NodeData::CAR(insert_car_raw);

        // If the nil cdr is none, then we must insert here - at the tail
        if (nil_view.cdr.is_none()) {

            let mut nil = self.cell.take(Tracked(nil_perm.borrow_mut()));

            let tracked token_tuple;
            let tracked updated_nil_token;
            let tracked cons_token;

            proof {
                token_tuple = self.instance.borrow().insert(
                    self.view_car(), 
                    insert_car, 
                    nil.map_token.value(), 
                    nil.map_token.get()
                );
                updated_nil_token = token_tuple.0.get();
                cons_token = token_tuple.1.get();
            }

            let locked_cons = LockedCons::new(
                insert_car_raw, 
                Tracked(cons_token), 
                None::<Arc<LockedCons>>, 
                self.instance.clone()
            );

            nil.cdr = Some(Arc::new(locked_cons));
            nil.map_token = Tracked(updated_nil_token);
            self.cell.put(Tracked(nil_perm.borrow_mut()), nil);
            self.release_lock(nil_perm);
            return;
        } 
        else {
            // We check if we need to insert inbetween Nil and the first Cons
            let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
            let mut first_cons_perm = first_locked_cons.acquire_lock();
            let first_cons_view = first_locked_cons.cell.borrow(Tracked(first_cons_perm.borrow_mut()));

            // If a Cons with this value already exists:
            if (insert_car_raw == first_cons_view.car) {
                // Return early and do nothing - the Cons exists.
                self.release_lock(nil_perm);
                first_locked_cons.release_lock(first_cons_perm);
                return;
            }

            // If the first Cons cdr is larger than the insert cdr:
            if (insert_car_raw < first_cons_view.car) {

                // Then we insert inbetween Nil and first Cons
                let mut nil = self.cell.take(Tracked(nil_perm.borrow_mut()));

                let tracked token_tuple;
                let tracked updated_nil_token;
                let tracked cons_token;

                proof {
                    token_tuple = self.instance.borrow().insert(
                        self.view_car(), 
                        insert_car, 
                        nil.map_token.value(), 
                        nil.map_token.get()
                    );
                    updated_nil_token = token_tuple.0.get();
                    cons_token = token_tuple.1.get();
                }

                let locked_cons = LockedCons::new(
                    insert_car_raw, 
                    Tracked(cons_token), 
                    Some(first_locked_cons.clone()), 
                    self.instance.clone()
                );

                nil.cdr = Some(Arc::new(locked_cons));
                nil.map_token = Tracked(updated_nil_token);

                self.cell.put(Tracked(nil_perm.borrow_mut()), nil);

                self.release_lock(nil_perm);
                first_locked_cons.release_lock(first_cons_perm);
                return;
            }

            // If we have reached here, we may release the nil lock:
            self.release_lock(nil_perm);

            // Any insert from here onwards will not involve nil - 
            // we may delegate the insert to a chain of LockedCons
            first_locked_cons.insert(first_cons_perm, insert_car_raw);
        }
    }

    fn delete(self: Arc<Self>, delete_car_raw: u32)
        requires
            self.wf()
        ensures
            self.wf()
    {
        let delete_car = NodeData::CAR(delete_car_raw);
        // Acquire the lock for the nil node, and view the data inside (without taking)
        let mut nil_perm = self.acquire_lock();
        let nil_view = self.cell.borrow(Tracked(nil_perm.borrow_mut()));

        // If the nil cdr is none, then we are done - no tokens exist ==> no nodes exist
        if (nil_view.cdr.is_none()) {
            proof {
                self.instance.delete_successful_empty_list(delete_car, nil_view.map_token.borrow());
            }
            self.release_lock(nil_perm);
            return;
        }

        // We check if we need to delete the first Cons (hence lower is LockedNil)
        let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
        let mut first_cons_perm = first_locked_cons.acquire_lock();
        let first_cons_view = first_locked_cons.cell.borrow(Tracked(first_cons_perm.borrow_mut()));

        // If the first car is larger than our delete, then we are done - no tokens exist ==> no nodes exist
        if (delete_car_raw < first_cons_view.car) {
            proof {
                self.instance.delete_successful_car_not_in_list(
                    self.view_car(), 
                    delete_car, 
                    nil_view.map_token.value(), 
                    nil_view.map_token.borrow()
                );
            }
            self.release_lock(nil_perm);
            first_locked_cons.release_lock(first_cons_perm);
            return;
        }

        // Check if we are deleting the first LockedCons:
        if (delete_car_raw == first_cons_view.car) {
            let mut nil = self.cell.take(Tracked(nil_perm.borrow_mut()));
            let mut first_cons = first_locked_cons.cell.take(Tracked(first_cons_perm.borrow_mut()));

            let tracked tuple;
            let tracked updated_nil_token;
            let tracked witness_token;

            proof {
                tuple = self.instance.borrow().delete(
                    self.view_car(), 
                    delete_car, 
                    first_cons.map_token.value(), 
                    nil.map_token.get(),
                    first_cons.map_token.get()
                );

                updated_nil_token = tuple.0.get();
                witness_token = tuple.2.get();
            }

            nil.map_token = Tracked(updated_nil_token);
            nil.cdr = first_cons.cdr;

            proof {
                self.instance.delete_successful_car_not_in_list(
                    self.view_car(), 
                    delete_car, 
                    nil.map_token.value(), 
                    nil.map_token.borrow()
                );
            }

            self.cell.put(Tracked(nil_perm.borrow_mut()), nil);
            self.release_lock(nil_perm);

            return;
        }
        
        // We can release the dummy node lock.
        self.release_lock(nil_perm);
        // and begin our traversal:
        first_locked_cons.delete(first_cons_perm, delete_car_raw);
    }
}

pub struct Cons {
    pub car: u32,
    pub cdr: Option<Arc<LockedCons>>,
    pub map_token: Tracked<machine::data_map>
}

struct_with_invariants!{
    pub struct LockedCons {
        atomic: AtomicBool<_, Option<PointsTo<Cons>>, _>,
        cell: PCell<Cons>,
        instance: Tracked<machine::Instance>,
        view_car: Ghost<NodeData>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant on atomic with (cell, instance, view_car) is (v: bool, g: Option<PointsTo<Cons>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.is_init() &&
                    points_to.id() == cell.id() &&
                    NodeData::CAR(points_to.value().car) == view_car &&
                    points_to.value().map_token@.instance_id() == instance@.id() &&
                    points_to.value().map_token@.key() == NodeData::CAR(points_to.value().car) &&
                    (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()) && 
                    (points_to.value().map_token@.value().is_some() ==> 
                        (
                            points_to.value().cdr.unwrap().wf() &&
                            points_to.value().cdr.unwrap().view_instance() == instance &&
                            points_to.value().cdr.unwrap().view_car() > NodeData::CAR(points_to.value().car) &&
                            points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
                        )
                    )
                }
            }
        }
    }
}

impl LockedCons {
    fn new(car: u32, map_token: Tracked<machine::data_map>, cdr: Option<Arc<LockedCons>>, instance: Tracked<machine::Instance>) -> (new_cons: Self)
        requires
            map_token@.instance_id() == instance@.id(),
            map_token@.key() == NodeData::CAR(car),
            map_token@.value().is_none() <==> cdr.is_none(),
            map_token@.value().is_some() ==> (
                cdr.unwrap().wf() &&
                cdr.unwrap().view_instance() == instance &&
                cdr.unwrap().view_car() > NodeData::CAR(car) &&
                cdr.unwrap().view_car() == map_token@.value().unwrap()
            ),
        ensures 
            new_cons.wf(),
            new_cons.instance == instance,
            new_cons.view_car == NodeData::CAR(car),
    {   
        let view_car = Ghost(NodeData::CAR(car));
        let node = Cons { car, cdr, map_token: map_token };
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance, view_car)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance, view_car }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<PointsTo<Cons>>)
        requires 
            self.wf(),
        ensures 
            points_to.is_init(),
            points_to.id() == self.cell.id(),
            NodeData::CAR(points_to.value().car) == self.view_car,
            points_to.value().map_token@.instance_id() == self.instance@.id(),
            points_to.value().map_token@.key() == NodeData::CAR(points_to.value().car),
            (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()), 
            (points_to.value().map_token@.value().is_some() ==> 
                (
                    points_to.value().cdr.unwrap().wf() &&
                    points_to.value().cdr.unwrap().view_instance() == self.instance &&
                    points_to.value().cdr.unwrap().view_car() > NodeData::CAR(points_to.value().car) &&
                    points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
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

    fn release_lock(&self, points_to: Tracked<PointsTo<Cons>>)
        requires
            self.wf(),
            points_to.is_init(),
            points_to.id() == self.cell.id(),
            NodeData::CAR(points_to.value().car) == self.view_car,
            points_to.value().map_token@.instance_id() == self.instance@.id(),
            points_to.value().map_token@.key() == NodeData::CAR(points_to.value().car),
            (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()), 
            (points_to.value().map_token@.value().is_some() ==> 
                (
                    points_to.value().cdr.unwrap().wf() &&
                    points_to.value().cdr.unwrap().view_instance() == self.instance &&
                    points_to.value().cdr.unwrap().view_car() > NodeData::CAR(points_to.value().car) &&
                    points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
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

    pub closed spec fn view_car(&self) -> (view_car: NodeData)
    {
        self.view_car@
    }

    pub closed spec fn view_instance(&self) -> (instance: machine::Instance)
    {
        self.instance@
    }

    fn insert(self: Arc<Self>, mut current_cons_perm: Tracked<PointsTo<Cons>>, insert_car_raw: u32)
        requires
            self.wf(),
            current_cons_perm.is_init(),
            current_cons_perm.id() == self.cell.id(),
            NodeData::CAR(current_cons_perm.value().car) == self.view_car,
            current_cons_perm.value().map_token@.instance_id() == self.instance@.id(),
            current_cons_perm.value().map_token@.key() == NodeData::CAR(current_cons_perm.value().car),
            (current_cons_perm.value().map_token@.value().is_none() <==> current_cons_perm.value().cdr.is_none()), 
            (current_cons_perm.value().map_token@.value().is_some() ==> 
                (
                    current_cons_perm.value().cdr.unwrap().wf() &&
                    current_cons_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    current_cons_perm.value().cdr.unwrap().view_car() > NodeData::CAR(current_cons_perm.value().car) &&
                    current_cons_perm.value().cdr.unwrap().view_car() == current_cons_perm.value().map_token@.value().unwrap()
                )
            ),
            current_cons_perm.value().car < insert_car_raw
        ensures
            self.wf()
    {
        let insert_car = NodeData::CAR(insert_car_raw);
        let mut current_locked_cons = self;
        loop 
            invariant
                self.wf(),
                current_locked_cons.wf(),
                current_cons_perm.is_init(),
                current_cons_perm.id() == current_locked_cons.cell.id(),
                NodeData::CAR(current_cons_perm.value().car) == current_locked_cons.view_car,
                current_cons_perm.value().map_token@.instance_id() == current_locked_cons.instance@.id(),
                current_cons_perm.value().map_token@.key() == NodeData::CAR(current_cons_perm.value().car),
                (current_cons_perm.value().map_token@.value().is_none() <==> current_cons_perm.value().cdr.is_none()), 
                (current_cons_perm.value().map_token@.value().is_some() ==> 
                    (
                        current_cons_perm.value().cdr.unwrap().wf() &&
                        current_cons_perm.value().cdr.unwrap().view_instance() == current_locked_cons.instance &&
                        current_cons_perm.value().cdr.unwrap().view_car() > NodeData::CAR(current_cons_perm.value().car) &&
                        current_cons_perm.value().cdr.unwrap().view_car() == current_cons_perm.value().map_token@.value().unwrap()
                    )
                ),
                current_cons_perm.value().car < insert_car_raw,
                insert_car == NodeData::CAR(insert_car_raw)
            decreases
                insert_car_raw - current_cons_perm.value().car
        {
            let mut current_cons_view = current_locked_cons.cell.borrow(Tracked(current_cons_perm.borrow_mut()));

            // If there is no next LockedCons, then we must insert at the tail after a Cons
            if (current_cons_view.cdr.is_none()) {

                let mut old_tail_cons = current_locked_cons.cell.take(Tracked(current_cons_perm.borrow_mut()));

                let tracked token_tuple;
                let tracked updated_old_tail_cons_token;
                let tracked new_tail_cons_token;

                proof {
                    token_tuple = current_locked_cons.instance.borrow().insert(
                        current_locked_cons.view_car(), 
                        insert_car, 
                        old_tail_cons.map_token.value(), 
                        old_tail_cons.map_token.get()
                    );
                    updated_old_tail_cons_token = token_tuple.0.get();
                    new_tail_cons_token = token_tuple.1.get();
                }

                let locked_cons = LockedCons::new(
                    insert_car_raw, 
                    Tracked(new_tail_cons_token), 
                    None::<Arc<LockedCons>>, 
                    current_locked_cons.instance.clone()
                );

                old_tail_cons.cdr = Some(Arc::new(locked_cons));
                old_tail_cons.map_token = Tracked(updated_old_tail_cons_token);

                current_locked_cons.cell.put(Tracked(current_cons_perm.borrow_mut()), old_tail_cons);
                current_locked_cons.release_lock(current_cons_perm);

                return;
            } 
            // Otherwise, there is another LockedCons
            else {
                // Acquire the permissions to access the Cons:
                let next_locked_cons = current_cons_view.cdr.as_ref().unwrap().clone();
                let mut next_cons_perm = next_locked_cons.acquire_lock();
                let next_cons_view = next_locked_cons.cell.borrow(Tracked(next_cons_perm.borrow_mut()));

                // If a Cons with this value already exists:
                if (insert_car_raw == next_cons_view.car) {
                    // Return early and do nothing - the Cons exists.
                    current_locked_cons.release_lock(current_cons_perm);
                    next_locked_cons.release_lock(next_cons_perm);
                    return;
                }

                // If the next Cons cdr is larger than the insert cdr:
                if (insert_car_raw < next_cons_view.car) {

                    // Then we insert inbetween Cons and Cons
                    let mut current_cons = current_locked_cons.cell.take(Tracked(current_cons_perm.borrow_mut()));

                    let tracked token_tuple;
                    let tracked updated_cons_token;
                    let tracked new_cons_token;

                    proof {
                        token_tuple = current_locked_cons.instance.borrow().insert(
                            current_locked_cons.view_car(), 
                            insert_car, 
                            current_cons.map_token.value(), 
                            current_cons.map_token.get()
                        );
                        updated_cons_token = token_tuple.0.get();
                        new_cons_token = token_tuple.1.get();
                    }

                    let locked_cons = LockedCons::new(
                        insert_car_raw, 
                        Tracked(new_cons_token), 
                        Some(next_locked_cons.clone()), 
                        current_locked_cons.instance.clone()
                    );

                    current_cons.cdr = Some(Arc::new(locked_cons));
                    current_cons.map_token = Tracked(updated_cons_token);

                    current_locked_cons.cell.put(Tracked(current_cons_perm.borrow_mut()), current_cons);

                    current_locked_cons.release_lock(current_cons_perm);
                    next_locked_cons.release_lock(next_cons_perm);
                    return;
                }

                // Otherwise, we give up the previous lock, and loop again
                current_locked_cons.release_lock(current_cons_perm);

                current_locked_cons = next_locked_cons;
                current_cons_perm = next_cons_perm;
            }
        }
    }

    fn delete(self: Arc<Self>, mut current_cons_perm: Tracked<PointsTo<Cons>>, delete_car_raw: u32)
        requires
            self.wf(),
            current_cons_perm.is_init(),
            current_cons_perm.id() == self.cell.id(),
            NodeData::CAR(current_cons_perm.value().car) == self.view_car,
            current_cons_perm.value().map_token@.instance_id() == self.instance@.id(),
            current_cons_perm.value().map_token@.key() == NodeData::CAR(current_cons_perm.value().car),
            (current_cons_perm.value().map_token@.value().is_none() <==> current_cons_perm.value().cdr.is_none()), 
            (current_cons_perm.value().map_token@.value().is_some() ==> 
                (
                    current_cons_perm.value().cdr.unwrap().wf() &&
                    current_cons_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    current_cons_perm.value().cdr.unwrap().view_car() > NodeData::CAR(current_cons_perm.value().car) &&
                    current_cons_perm.value().cdr.unwrap().view_car() == current_cons_perm.value().map_token@.value().unwrap()
                )
            ),
            current_cons_perm.value().car < delete_car_raw
        ensures
            self.wf()
    {
        let delete_car = NodeData::CAR(delete_car_raw);
        let mut current_locked_cons = self;
        loop 
            invariant
                self.wf(),
                current_locked_cons.wf(),
                current_cons_perm.is_init(),
                current_cons_perm.id() == current_locked_cons.cell.id(),
                NodeData::CAR(current_cons_perm.value().car) == current_locked_cons.view_car,
                current_cons_perm.value().map_token@.instance_id() == current_locked_cons.instance@.id(),
                current_cons_perm.value().map_token@.key() == NodeData::CAR(current_cons_perm.value().car),
                (current_cons_perm.value().map_token@.value().is_none() <==> current_cons_perm.value().cdr.is_none()), 
                (current_cons_perm.value().map_token@.value().is_some() ==> 
                    (
                        current_cons_perm.value().cdr.unwrap().wf() &&
                        current_cons_perm.value().cdr.unwrap().view_instance() == current_locked_cons.instance &&
                        current_cons_perm.value().cdr.unwrap().view_car() > NodeData::CAR(current_cons_perm.value().car) &&
                        current_cons_perm.value().cdr.unwrap().view_car() == current_cons_perm.value().map_token@.value().unwrap()
                    )
                ),
                current_cons_perm.value().car < delete_car_raw,
                delete_car == NodeData::CAR(delete_car_raw)
            decreases
                delete_car_raw - current_cons_perm.value().car
        {
            let mut current_cons_view = current_locked_cons.cell.borrow(Tracked(current_cons_perm.borrow_mut()));

            // If there is no next LockedCons, then we have reached the tail.
            // If we have not deleted by now, then we are done - no tokens exist ==> no nodes exist
            if (current_cons_view.cdr.is_none()) {
                proof {
                    current_locked_cons.instance.delete_successful_car_not_in_list(
                        current_locked_cons.view_car(), 
                        delete_car, 
                        current_cons_view.map_token.value(), 
                        current_cons_view.map_token.borrow()
                    );
                }
                current_locked_cons.release_lock(current_cons_perm);
                return;
            } 
            // Otherwise, there is another LockedCons
            else {
                // Acquire the permissions to access the Cons:
                let next_locked_cons = current_cons_view.cdr.as_ref().unwrap().clone();
                let mut next_cons_perm = next_locked_cons.acquire_lock();
                let next_cons_view = next_locked_cons.cell.borrow(Tracked(next_cons_perm.borrow_mut()));

                // If the next car is larger than our delete, then we have:
                // lower_car < delete_car < upper_car
                // Which means that no node exist with value delete_car.
                // We are done - no tokens exist ==> no nodes exist
                if (delete_car_raw < next_cons_view.car) {
                    proof {
                        current_locked_cons.instance.delete_successful_car_not_in_list(
                            current_locked_cons.view_car(), 
                            delete_car, 
                            current_cons_view.map_token.value(), 
                            current_cons_view.map_token.borrow()
                        );
                    }
                    current_locked_cons.release_lock(current_cons_perm);
                    next_locked_cons.release_lock(next_cons_perm);
                    return;
                }

                // Check if we are deleting the first LockedCons:
                if (delete_car_raw == next_cons_view.car) {
                    let mut current_cons = current_locked_cons.cell.take(Tracked(current_cons_perm.borrow_mut()));
                    let mut next_cons = next_locked_cons.cell.take(Tracked(next_cons_perm.borrow_mut()));

                    let tracked tuple;
                    let tracked updated_current_cons_token;
                    let tracked witness_token;

                    proof {
                        tuple = current_locked_cons.instance.borrow().delete(
                            current_locked_cons.view_car(), 
                            delete_car, 
                            next_cons.map_token.value(), 
                            current_cons.map_token.get(),
                            next_cons.map_token.get()
                        );

                        updated_current_cons_token = tuple.0.get();
                        witness_token = tuple.2.get();
                    }

                    current_cons.map_token = Tracked(updated_current_cons_token);
                    current_cons.cdr = next_cons.cdr;

                    proof {
                        current_locked_cons.instance.delete_successful_car_not_in_list(
                            current_locked_cons.view_car(), 
                            delete_car, 
                            current_cons.map_token.value(), 
                            current_cons.map_token.borrow()
                        );
                    }

                    current_locked_cons.cell.put(Tracked(current_cons_perm.borrow_mut()), current_cons);
                    current_locked_cons.release_lock(current_cons_perm);
                    return;
                }

                // Otherwise, we give up the previous lock, and loop again
                current_locked_cons.release_lock(current_cons_perm);
                current_locked_cons = next_locked_cons;
                current_cons_perm = next_cons_perm;
            }
        }
    }
}

pub struct LinkedList {
    pub locked_nil: Arc<LockedNil>,
}

impl LinkedList {
    pub closed spec fn wf(&self) -> bool
    {
        self.locked_nil.wf()
    }

    pub fn new() -> (linked_list: Self)
        ensures
            linked_list.wf()
    {
        Self { locked_nil: Arc::new(LockedNil::new()) }
    }

    pub fn insert(self, data: u32) 
        requires
            self.wf()
        ensures
            self.wf()
    {
        self.locked_nil.insert(data);
    }

    pub fn delete(self, data: u32) 
        requires
            self.wf()
        ensures
            self.wf()
    {
        self.locked_nil.delete(data);
    }
}

fn main() {
    let linked_list = Arc::new(LinkedList::new());
}
}