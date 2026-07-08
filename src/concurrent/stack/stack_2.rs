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

enum Operation {
    Pop(u32),
    Push(u32)
}

tokenized_state_machine!{
    machine {
        fields {
            // #[sharding(variable)]
            // pub head_address: Seq<usize>,

            // #[sharding(map)]
            // pub active_stack_cells: Map<usize, PointsTo<StackCell>>,

            // #[sharding(storage_map)]
            // pub popped_stack_cells: Map<usize, StackCell>,

            #[sharding(map)]
            pub every_cell_ever: Map<usize, PointsTo<StackCell>>,

            #[sharding(map)]
            pub linearised_history: Map<int, Operation>,
        }

        init!{
            initialize()
            {
                init head_address = Seq::empty();
            }
        }

        transition!{
            push(points_to: PointsTo<StackCell>)
            {
                update head_address = pre.head_address.push(points_to);
            }
        }

        transition!{
            pop()
            {
                update head_address = pre.head_address.drop_last();
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {}

        #[inductive(push)]
        fn push_inductive(pre: Self, post: Self, points_to: PointsTo<StackCell>) { }

        #[inductive(pop)]
        fn pop_inductive(pre: Self, post: Self) { }
    }
}

pub struct TokenPermAndPointers {
    pub token: Tracked<machine::head_address>,
    pub pointers: Ghost<Seq<PPtr<StackCell>>>
}

#[derive(Copy, Clone)]
pub struct StackCell {
    pub elem: u32,
    pub next: usize,
}

struct_with_invariants!{
    pub struct TreiberStack {
        pub head: AtomicUsize<_, TokenPermAndPointers, _>,
        pub instance: Tracked<machine::Instance>,
    }

    pub open spec fn wf(self) -> bool {
        invariant on head with (instance) is (v: usize, tpaps: TokenPermAndPointers) {
            // The token is from the correct TSM
            tpaps.token@.instance_id() == instance.id() &&

            // We always have the null pointer in the stack and it is at the base
            tpaps.pointers.len() > 0  &&
            tpaps.token@.value().len() == tpaps.pointers.len() &&
            tpaps.token@.value()[0].is_uninit() &&

            // Each token has the correct perm for the correspnding pointer
            // The null pointer is the only uninit pointer (at the base)
            (forall |i: int| #![auto] 0 <= i < tpaps.token@.value().len() ==> (
                tpaps.token@.value()[i].pptr() == tpaps.pointers[i] &&
                (tpaps.token@.value()[i].is_uninit() <==> i == 0)
            )) &&

            // If we only have the base, then we set v to 0 to represent the nullptr
            (tpaps.token@.value().len() == 1 <==> v == 0) &&

            // Otherwise, v should represent the address of the head
            (tpaps.token@.value().len() > 1 ==> tpaps.token@.value().last().addr() == v)

            // // The tokens all point to disjoints regions of memory:
            // forall |i: int, j: int| #![auto] 0 <= i < j < tpaps.token@.value().len() ==> (
            //     tpaps.token@.value()[i].is_disjoint(&tpaps.token@.value()[j])
            // )
        }
    }
}

impl TreiberStack {
    fn new() -> (treiber_stack: Self)
        ensures treiber_stack.wf()
    {
        let (base, Tracked(base_perm)) = PPtr::<StackCell>::empty();
        let tracked (
            Tracked(instance), 
            Tracked(stack_token)
        ) = machine::Instance::initialize();

        proof {
            instance.push(base_perm, &mut stack_token);
        }

        let base_address = base.addr();
  
        let ghost pointer_seq = Seq::empty().push(base);

        let tpaps = TokenPermAndPointers { token: Tracked(stack_token), pointers: Ghost(pointer_seq) };

        let head = AtomicUsize::new(Ghost(Tracked(instance)), 0, Tracked(tpaps));

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
            let stack_cell = StackCell { elem, next: self.head.load() };
            let (permissioned_stack_cell, Tracked(stack_cell_perm)) = PPtr::new(stack_cell);
            
            proof {
                stack_cell_perm.is_nonnull()
            }

            let mut push_result = atomic_with_ghost!(
                self.head => compare_exchange(
                    permissioned_stack_cell.read(Tracked(&stack_cell_perm)).next, 
                    permissioned_stack_cell.addr()
                );
                returning previous_head_result;

                ghost points_to_inv => {
                    if let Ok(previous_head) = previous_head_result {

                        self.instance.push(stack_cell_perm, &mut points_to_inv.token);
                        points_to_inv.pointers = Ghost(points_to_inv.pointers@.push(permissioned_stack_cell));
                    }
                }
            );

            if let Ok(_) = push_result {
                return;
            }
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
            let mut popped_value = None;
            let ghost 

            let mut head_stack_cell_address = atomic_with_ghost!{
                self.head => load();
                returning ret;

                ghost points_to_inv => {
                    if ret == 0 {
                        // Then the top node is the base. i.e. we can't pop it:
                    } else {
                        // Then this is a real value:
                        assert(points_to_inv.token@.value().last().addr() == ret);
                        assert(points_to_inv.pointers@.last().addr() == ret);
                        
                    }
                }
            };

            if head_stack_cell_address == 0 {
                return popped_value;
            }

            // usize
            let permissioned_pointer = PPtr::from_addr(head_stack_cell_address);
            let head_clone = permissioned_pointer.read(Tracked(&IDK));

            let mut possible_pop = atomic_with_ghost!{
                self.head => compare_exchange(
                    permissioned_pointer.addr(), 
                    head_clone.next()
                );

                returning ret;

                ghost points_to_inv => {
                    self.instance.pop(&mut points_to_inv.token);
                    points_to_inv.pointers = Ghost(points_to_inv.pointers@.drop_last());
                }
            };

            if let Ok(result) = possible_pop {
                return Some(head_clone.elem);
            }
        }
    }
}

fn main() {
    let shared_stack = Arc::new(TreiberStack::new());
}

}