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
            pub initialized: bool,

            #[sharding(set)]
            pub head_address: Set<PointsTo<StackCell>>,
        }

        #[invariant]
        pub fn uninitialised_inv(&self) -> bool {
            !self.initialized <==> self.head_address.is_empty()
        }

        init!{
            initialize()
            {
                init initialized = false;
                init head_address = Set::empty();
            }
        }

        transition!{
            create_empty_stack(points_to: PointsTo<StackCell>)
            {
                require(!pre.initialized);
                update initialized = true;

                add head_address += set { points_to };
            }
        }

        // transition!{
        //     push(new_head_address: usize)
        //     {
        //         update head_address = new_head_address;
        //     }
        // }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {}

        #[inductive(create_empty_stack)]
        fn create_empty_stack_inductive(pre: Self, post: Self, points_to: PointsTo<StackCell>) { }

        // #[inductive(push)]
        // fn initialize_push(pre: Self, post: Self, new_head_address: usize) {}
    }
}

pub struct TokenPermAndPointer {
    pub token: Tracked<machine::head_address>,
    pub pointer: PPtr<StackCell>
}

pub struct StackCell {
    pub elem: u32,
    pub next: Option<PPtr<StackCell>>,
}

struct_with_invariants!{
    pub struct TreiberStack {
        pub head: AtomicUsize<_, Vec<TokenPermAndPointer>, _>,
        pub instance: Tracked<machine::Instance>,
    }

    pub open spec fn wf(self) -> bool {
        invariant on head with (instance) is (v: usize, tpaps: Vec<TokenPermAndPointer>) {
            // We always have the null pointer in the stack and it is at the base
            tpaps.len() > 0 && 
            tpaps[0].token@.element().is_uninit() &&

            // Each token is from the correct TSM
            // Each token has the correct perm for the correspnding pointer
            // The null pointer is the only uninit pointer (at the base)
            forall |i: int| #![auto] 0 <= i < tpaps.len() ==> (
                tpaps[i].token.instance_id() == instance.id() &&
                tpaps[i].token@.element().pptr() == tpaps[i].pointer &&
                (tpaps[i].token@.element().is_uninit() <==> i == 0)
            ) &&

            // The last pair in the list is the current head value
            tpaps[tpaps.len() - 1].token@.element().addr() == v
        }
    }
}

impl TreiberStack {
    fn new() -> (s: Self)
        ensures s.wf()
    {
        let (empty_stack, Tracked(empty_stack_perm)) = PPtr::<StackCell>::empty();
        let tracked (
            Tracked(instance), 
            Tracked(initialized),
            Tracked(head_address_tuple)
        ) = machine::Instance::initialize();

        let tracked head_token;
        proof {
            head_token = instance.create_empty_stack(empty_stack_perm, &mut initialized);
        };

        let address = empty_stack.addr();
        let tpap = TokenPermAndPointer { token: Tracked(head_token), pointer: empty_stack };
        let mut tpaps = Vec::new();
        tpaps.push(tpap);


        let head = AtomicUsize::new(Ghost(Tracked(instance)), address, Tracked(tpaps));


        TreiberStack { head, instance: Tracked(instance) }
    }

    // pub fn push(self: Arc<Self>, elem: u32)
    //     requires
    //         self.wf()
    //     ensures
    //         self.wf()
    // {
    //     loop 
    //         invariant
    //             self.wf()
    //     {
    //         let loaded_head = self.head.load();
    //         let stack_cell = StackCell { elem, next: loaded_head };

    //         let _ = atomic_with_ghost!(
    //             self.head => compare_exchange(self.head.load(), loaded_head);
    //             update prev -> next;
    //             returning previous_head_result;

    //             ghost points_to_inv => {
    //                 if let Ok(previous_head) = previous_head_result {
    //                     self.instance.push(loaded_head, &mut points_to_inv.0);
    //                 }
    //             }
    //         );
    //     }
    // }

    // pub fn pop(self: Arc<Self>) -> (elem: Option<u32>)
    //     requires
    //         self.wf()
    //     ensures
    //         self.wf()
    // {
    //     // loop 
    //     //     invariant
    //     //         self.wf()
    //     // {
    //     //     let old_head_address = self.head.load();
    //     //     if old_head_address == 0 {
    //     //         return None;
    //     //     }

    //     //     let new_head = *usize_to_stackcell_ptr(old_head_address);
    //     // }
    //     Some(4)
    // }
}

fn main() {
    let shared_stack = Arc::new(TreiberStack::new());
}

}