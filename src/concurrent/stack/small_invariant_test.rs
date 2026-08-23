#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use std::sync::Arc;
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{atomic_ghost::*, pervasive::*, prelude::*, simple_pptr::*};

verus! {

struct_with_invariants!{
    pub struct NumberHolder {
        pub number: u32,
        pub atomic_size: AtomicUsize<_, (), _>,
    }

    pub open spec fn wf(self) -> bool {
        invariant on atomic_size with (number) is (size: usize, nothing: ()) {
            true
        }
    }
}

pub fn main() {
    let ghost_k: Ghost<u32> = Ghost(5);
    let size: usize = 0;
    let tracked_g: Tracked<()> = Tracked(());

    let atomic_size = AtomicUsize::new(
        ghost_k,
        size,
        tracked_g,
    );

    let number_holder = NumberHolder { number: 5, atomic_size };
    assert(number_holder.wf());
}

} // verus!
