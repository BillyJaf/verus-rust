use verus_state_machines_macros::tokenized_state_machine;
use verus_builtin::*;
use verus_builtin_macros::*;
use std::sync::Arc;
use vstd::{
    atomic_ghost::*,
    prelude::*,
    simple_pptr::*,
};

verus! {

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(map)]
            pub bad_map: Map<PointsTo<GuardedObject>, nat>,
        }

        init!{
            initialize()
            {
                init bad_map = Map::empty();
            }
        }
    }
}

pub struct GuardedObject {
    option_holder: Option<InvariantStruct>
}

struct_with_invariants!{
    pub struct InvariantStruct {
        atomic: AtomicBool<_, (), _>,
        instance: Tracked<Option<machine::Instance>>,
    }

    spec fn wf(&self) -> bool 
    {
        invariant on atomic with (instance) is (b: bool, nothing: ()) {
            true
        }
    }
}

pub fn main() {
    let tracked (
        Tracked(instance),
        Tracked(bad_map)
    ) = machine::Instance::initialize();

    let atomic = AtomicBool::new(Ghost(Tracked(Some(instance))), true, Tracked(()));
    let invariant_struct = InvariantStruct { atomic, instance: Tracked(Some(instance)) };
}
}