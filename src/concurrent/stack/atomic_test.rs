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
            #[sharding(storage_map)]
            pub stack: Map<usize, PermissionUsize>,

            // #[sharding(variable)]
            // pub stack_addresses: Seq<usize>,

            #[sharding(variable)]
            pub stack_values: Seq<u32>, // Where u32 is the value we are storing

            #[sharding(variable)]
            pub head: usize,

            // #[sharding(persistent_map)]
            // pub cells: Map<usize, StackCell>, // address, cell
        }

        // #[invariant]
        // pub fn complete_stack_inv(&self) -> bool {
        //     self.stack.dom().finite() &&
        //     (forall |i: nat| i < self.stack.dom().len() <==> self.stack.dom().contains(i))
        // }

        init!{
            initialize()
            {
                init stack = Map::empty();
                init stack_addresses = Seq::empty();
                init stack_values = Seq::empty();
            }
        }

        // transition!{
        //     push(new_stack_elem_perm: PAtomicUsize)
        //     {   
        //         birds_eye let new_stack_elem_index = pre.stack.dom().len();
        //         deposit stack += [new_stack_elem_index => new_stack_elem_perm];
        //     }
        // }

        transition!{
            pop()
            {   
                update stack_values = pre.stack_values.drop_first();
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {}
    }
}

pub struct TreiberStack {
    pub head: PAtomicUsize
}

pub struct StackCell {
    pub elem: u32,
    pub next: Option<PAtomicUsize>
}

pub fn pop(stack: Arc<TreiberStack>) {
    
}

fn main() {
    
    let tracked a: vstd::map::Map<usize, vstd::atomic::PermissionUsize> = Map::empty();

    let tracked (
        Tracked(instance),
        // Tracked(stack),
        Tracked(stack_addresses),
        Tracked(stack_values)
    ) = machine::Instance::initialize(a);
}
}