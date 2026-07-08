#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use verus_state_machines_macros::tokenized_state_machine;
use verus_builtin::*;
use verus_builtin_macros::*;
use std::sync::Arc;
use vstd::{
    atomic_ghost::*,
    modes::*,
    prelude::*,
    pervasive::*, 
    seq_lib::*,
    atomic::*,
    simple_pptr::*,
};

verus! {
fn main() {
    let (test, Tracked(test_perm)) = PPtr::<u32>::new(5);
    let test_address = test.addr();
    let reconstructed_pptr = PPtr::<u32>::from_addr(test_address);

    let reconstructed_u32 = reconstructed_pptr.read(Tracked(&test_perm));
    assert(reconstructed_u32 == 5);
}
}