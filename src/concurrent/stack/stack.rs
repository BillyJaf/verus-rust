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
};

verus! {

pub assume_specification<T> 
[std::boxed::Box::<T>::into_raw] 
(_0: std::boxed::Box<T>) -> *mut T
    where
    T: std::marker::MetaSized + ?Sized,;

pub assume_specification<T>
[std::boxed::Box::<T>::from_raw]
(ptr: *mut T) -> std::boxed::Box<T>
where
    T: std::marker::MetaSized;

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(variable)]
            pub head_address: usize,
        }

        init!{
            initialize()
            {
                init initialised = false;
                init head_address = 0;
            }
        }

        // transition!{
        //     create_empty_stack()
        //     {

        //         update head_address = new_head_address;
        //     }
        // }

        transition!{
            push(new_head_address: usize)
            {
                update head_address = new_head_address;
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {}

        #[inductive(push)]
        fn initialize_push(pre: Self, post: Self, new_head_address: usize) {}
    }
}

pub struct StackCell {
    pub elem: u32,
    pub next: usize,
}

struct_with_invariants!{
    pub struct TreiberStack {
        pub head: AtomicUsize<_, machine::head_address, _>,
        pub instance: Tracked<machine::Instance>,
    }

    pub open spec fn wf(self) -> bool {
        invariant on head with (instance) is (v: usize, g: machine::head_address) {
            g.instance_id() == instance@.id()
            && g.value() == v as int
        }
    }
}

impl TreiberStack {
    fn new() -> (s: Self)
        ensures s.wf()
    {
        let tracked (Tracked(instance), Tracked(head_address)) = machine::Instance::initialize();
        let head = AtomicUsize::new(Ghost(Tracked(instance)), 0, Tracked(head_address));
        TreiberStack { head, instance: Tracked(instance) }
    }

    pub fn push(self: Arc<Self>, elem: u32)
        requires
            self.wf()
        ensures
            self.wf()
    {
        loop 
            invariant
                self.wf()
        {
            let loaded_head = self.head.load();
            let stack_cell = StackCell { elem, next: loaded_head };

            let _ = atomic_with_ghost!(
                self.head => compare_exchange(self.head.load(), loaded_head);
                update prev -> next;
                returning previous_head_result;

                ghost points_to_inv => {
                    if let Ok(previous_head) = previous_head_result {
                        self.instance.push(loaded_head, &mut points_to_inv);
                    }
                }
            );
        }
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
            let old_head_address = self.head.load();
            if old_head_address == 0 {
                return None;
            }

            let new_head = *usize_to_stackcell_ptr(old_head_address);
        }
    }
}

fn main() {
    let shared_stack = Arc::new(TreiberStack::new());
}

}