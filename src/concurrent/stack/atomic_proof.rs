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
            pub head_address: usize,
        }

        init!{
            initialize()
            {
                init head_address = 0;
            }
        }

        transition!{
            add_one()
            {

                update head_address = (pre.head_address + 1) as usize;
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {}

        #[inductive(add_one)]
        fn initialize_add_one(pre: Self, post: Self) {}
    }
}

pub struct StackCell {
    pub elem: u32,
    pub next: Option<PAtomicUsize>
}

pub fn pop(stack: Arc<TreiberStack>) {

}

struct_with_invariants!{
    pub struct TreiberStack {
        pub head: AtomicUsize<_, machine::head_address, _>,
        pub instance: Tracked<machine::Instance>,
    }
    spec fn wf(self) -> bool {
        invariant on head with (instance) is (v: usize, g: machine::head_address) {
            g.instance_id() == instance@.id()
            && g.value() == v as int
        }
    }
}

impl TreiberStack {
    fn new() -> (s: Self) ensures s.wf() {
        let tracked (Tracked(instance), Tracked(head_address)) = machine::Instance::initialize();
        let head = AtomicUsize::new(Ghost(Tracked(instance)), 0, Tracked(head_address));
        TreiberStack { head, instance: Tracked(instance) }
    }
}

fn main() {
    let shared_stack = Arc::new(TreiberStack::new());

    for i in 0..2
        invariant shared_stack.wf(),
    {
        let thread_local_stack = shared_stack.clone();
        let _ = vstd::thread::spawn(move || {
            let current_usize = thread_local_stack.head.load();
            assume(current_usize < usize::MAX - 1);
            let x = atomic_with_ghost!(
                thread_local_stack.head => compare_exchange(current_usize, current_usize + 2);
                returning result_previous_usize;
                ghost points_to_inv => {
                    if let Ok(previous_usize) = result_previous_usize {
                        thread_local_stack.instance.add_one(&mut points_to_inv);
                        thread_local_stack.instance.add_one(&mut points_to_inv);
                    }
                }
            );
        });
    }
}

}