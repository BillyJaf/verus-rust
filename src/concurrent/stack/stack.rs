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

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {}
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
}

// AtomicUsize<Tracked<Instance>, head_address, InvariantPredicate_auto_TreiberStack_head>
// AtomicUsize<Instance,head_address, _>