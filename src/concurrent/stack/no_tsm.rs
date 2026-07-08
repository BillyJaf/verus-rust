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

#[derive(Copy, Clone)]
pub struct StackCell {
    pub elem: u32,
    pub next: usize,
}

struct_with_invariants!{
    pub struct TreiberStack {
        pub head: AtomicUsize<_, Seq<usize>, _>,
    }

    pub open spec fn wf(self) -> bool {
        invariant on head is (head_address: usize, pointers: Seq<usize>) {
            (head_address == 0 <==> pointers.len() == 0)
        }
    }
}

impl TreiberStack {
    fn new() -> (treiber_stack: Self)
        ensures treiber_stack.wf()
    {
        //let tracked pointer_seq = Seq::empty();

        let head = AtomicUsize::new(Ghost(()), 0, Tracked(Seq::empty()));

        TreiberStack { head }
    }

    pub fn pop(self: Arc<Self>) -> (elem: Option<u32>)
        requires
            self.wf()
        ensures
            self.wf()
    {
        loop 
            invariant
                self.wf()
        {
            let mut popped_value = None;
            let tracked a;

            let mut head_stack_cell_address = atomic_with_ghost!{
                self.head => load();
                returning ret;

                ghost points_to_inv => {
                    if ret != 0 {
                        // Then this is a real address, lets get the next address:
                        a = points_to_inv.last();
                    }
                }
            };

            if head_stack_cell_address == 0 {
                return popped_value;
            }

            return Some(1); // just to satisfy compiler, will remove later
        }
    }
}

fn main() {
    let shared_stack = Arc::new(TreiberStack::new());
}

}