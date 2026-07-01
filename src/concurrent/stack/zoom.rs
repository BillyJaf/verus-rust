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
};

verus! {

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(variable)]
            pub stack: PermissionUsize
        }

        #[invariant]
        pub fn complete_stack_inv(&self) -> bool {
            self.stack.dom().finite() &&
            (forall |i: nat| i < self.stack.dom().len() <==> self.stack.dom().contains(i))
        }

        init!{
            initialize()
            {
                init stack = Map::empty();
            }
        }

        transition!{
            push(new_stack_elem_perm: PermissionUsize)
            {   
                birds_eye let new_stack_elem_index = pre.stack.dom().len();
                deposit stack += [new_stack_elem_index => new_stack_elem_perm];
            }
        }

        transition!{
            pop()
            {   
                birds_eye let top_of_stack_index = pre.stack.dom().len() - 1;
                require(top_of_stack_index >= 0);
                withdraw stack -= [top_of_stack_index => let _];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {}

        #[inductive(push)]
        fn push_inductive(pre: Self, post: Self, new_stack_elem_perm: PermissionUsize) {}

        #[inductive(pop)]
        fn pop_inductive(pre: Self, post: Self) {}
    }
}

pub struct TreiberStack {
    pub head: PAtomicUsize
}

pub struct StackCell {
    pub elem: u32,
    pub next: Option<PAtomicUsize>
}
}