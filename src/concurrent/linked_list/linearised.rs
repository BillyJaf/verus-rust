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
    Insert(u32),
    Delete(u32)
}

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(map)]
            pub operation_history: Map<nat, Operation>,

            // #[sharding(map)]
            // pub list_representation: Map<u32, Option<u32>>,
        }

        #[invariant]
        pub fn operation_inv(&self) -> bool {
            self.operation_history.dom().finite() &&
            (forall |i: nat| i < self.operation_history.dom().len() <==> self.operation_history.dom().contains(i))
        }

        transition!{
            insert(lower: u32, insert: u32, upper: Option<u32>)
            {   
                require(lower < insert);
                require(upper.is_some() ==> insert < upper.unwrap());

                // remove list_representation -= [lower => upper];
                // add list_representation += [lower => Some(insert)];
                // add list_representation += [insert => upper];

                birds_eye let next_operation_index = pre.operation_history.dom().len();
                add operation_history += [next_operation_index => Operation::Insert(insert)];
            }
        }

        transition!{
            delete(lower: u32, delete: u32, upper: Option<u32>)
            {   
                require(lower < delete);
                require(upper.is_some() ==> delete < upper.unwrap());

                // remove list_representation -= [lower => upper];
                // add list_representation += [lower => Some(delete)];
                // add list_representation += [delete => upper];

                birds_eye let next_operation_index = pre.operation_history.dom().len();
                add operation_history += [next_operation_index => Operation::Delete(delete)];
            }
        }

        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, lower: u32, insert: u32, upper: Option<u32>) {}

        #[inductive(delete)]
        fn delete_inductive(pre: Self, post: Self, lower: u32, delete: u32, upper: Option<u32>) {}
    }
}

fn main() {
}
}