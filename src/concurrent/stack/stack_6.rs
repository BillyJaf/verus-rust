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
    set_lib::*,
    map_lib::*,
};

verus! {

pub enum Operation {
    Pop(u32),
    Push(u32),
    CreateBase
}

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(constant)]
            pub base_address: usize,

            #[sharding(variable)]
            pub permission_guard: Set<PointsTo<StackCell>>,

            #[sharding(persistent_map)]
            pub address_permissions_witnesses: Map<usize, PointsTo<StackCell>>,

            #[sharding(storage_map)]
            pub address_permissions: Map<usize, PointsTo<StackCell>>,

            #[sharding(persistent_map)]
            pub linearised_history: Map<int, Operation>,
        }

        #[invariant]
        pub fn permission_guards_correctly_represent_permissions_inv(&self) -> bool {
            (self.permission_guard == self.address_permissions.values()) && (
            forall |points_to: PointsTo<StackCell>| #![auto]
                self.permission_guard.contains(points_to) <==>
                    self.address_permissions.dom().contains(points_to.addr())
            )
        }

        #[invariant]
        pub fn permission_guards_correctly_represent_witnesses_inv(&self) -> bool {
            (self.permission_guard == self.address_permissions_witnesses.values()) && (
            forall |points_to: PointsTo<StackCell>| #![auto]
                self.permission_guard.contains(points_to) <==>
                    self.address_permissions_witnesses.dom().contains(points_to.addr())
            )
        }

        #[invariant]
        pub fn witness_equals_storage_inv(&self) -> bool {
            self.address_permissions_witnesses == self.address_permissions
        }

        #[invariant]
        pub fn correct_address_for_permissions_inv(&self) -> bool {
            forall |addr: usize| #![auto]
                self.address_permissions.dom().contains(addr) ==>
                    self.address_permissions.index(addr).addr() == addr
        }

        #[invariant]
        pub fn correct_address_for_witnesses_inv(&self) -> bool {
            forall |addr: usize| #![auto]
                self.address_permissions_witnesses.dom().contains(addr) ==>
                    self.address_permissions_witnesses.index(addr).addr() == addr
        }

        init!{
            initialize(base_address: usize)
            {
                init base_address = base_address;
                init permission_guard = Set::empty();
                init address_permissions_witnesses = Map::empty();
                init address_permissions = Map::empty();
                init linearised_history = Map::empty();
            }
        }

        transition!{
            create_base(points_to: PointsTo<StackCell>)
            {
                require(points_to.addr() == pre.base_address);
                require(pre.permission_guard.is_empty());
                require(!pre.permission_guard.contains(points_to));

                update permission_guard = pre.permission_guard.insert(points_to);
                deposit address_permissions += [points_to.addr() => points_to];
                add address_permissions_witnesses (union)= [points_to.addr() => points_to];
            }
        }

        transition!{
            push(points_to: PointsTo<StackCell>)
            {
                // require(points_to.addr() != pre.base_address);
                require(!pre.permission_guard.contains(points_to));

                update permission_guard = pre.permission_guard.insert(points_to);
                deposit address_permissions += [points_to.addr() => points_to];
                add address_permissions_witnesses (union)= [points_to.addr() => points_to];
            }
        }

        // transition!{
        //     pop()
        //     {
        //         update head_address = pre.head_address.drop_last();
        //     }
        // }

        property!{
            get_permission_reference(addr: usize, permission: PointsTo<StackCell>) {
                have address_permissions_witnesses >= [addr => permission];
                guard address_permissions >= [addr => permission];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, base_address: usize) {
            assert(post.permission_guard == post.address_permissions_witnesses.values());
        }

        #[inductive(create_base)]
        fn create_base_inductive(pre: Self, post: Self, points_to: PointsTo<StackCell>) {
            broadcast use group_set_properties;
            broadcast use group_map_properties;
            // assert();
            assume(post.permission_guard == post.address_permissions.values());
            // assume(post.permission_guard == post.address_permissions_witnesses.values());

            assert(
                forall |points_to: PointsTo<StackCell>| #![auto]
                    post.permission_guard.contains(points_to) ==>
                        post.address_permissions.dom().contains(points_to.addr())
            );

            // assume(
            //     forall |points_to: PointsTo<StackCell>| #![auto]
            //         post.address_permissions.dom().contains(points_to.addr()) ==>
            //             post.permission_guard.contains(points_to)
            // );
            assert(post.address_permissions.dom().contains(points_to.addr()));
            assert(post.permission_guard.contains(points_to));

            // assert(
            //     forall |points_to: PointsTo<StackCell>| #![auto]
            //         post.address_permissions.dom().contains(points_to.addr()) ==>
            //             post.permission_guard.contains(points_to)
            // );

            assert
                forall |perm: PointsTo<StackCell>|
                    post.address_permissions.dom().contains(perm.addr())
                implies
                    #[trigger] post.permission_guard.contains(perm)
            by {
                broadcast use group_set_properties;

                // assert(
                //     forall |perm: PointsTo<StackCell>| #![auto]
                //         pre.address_permissions.dom().contains(perm.addr()) <==>
                //             pre.permission_guard.contains(perm)
                // );

                // assert(
                //     forall |perm: PointsTo<StackCell>| #![auto]
                //         pre.address_permissions.dom().contains(perm.addr()) ==>
                //             post.address_permissions.dom().contains(perm.addr())
                // );
                assert(pre.address_permissions.dom().contains(perm.addr()) ==> pre.permission_guard.contains(perm));
                assert(pre.address_permissions.dom().insert(points_to.addr()) == post.address_permissions.dom());
                assert(pre.permission_guard.insert(points_to) == post.permission_guard);

                if (perm == points_to) {
                    assume(false);
                } else {
                    // assert(post.address_permissions.dom() == pre.address_permissions.dom().insert(points_to.addr()));
                    assert(post.address_permissions.dom() == pre.address_permissions.dom().insert(points_to.addr()));
                    assert(perm != points_to);
                    // proof {
                    //     perm.is_distinct(&points_to);
                    // }
                    PointsTo::is_disjoint(&mut perm, &points_to);
                    
                    assert(perm.addr() != points_to.addr());
                    assert(post.address_permissions.dom().contains(perm.addr()) ==> pre.address_permissions.dom().contains(perm.addr()));

                    assert(post.address_permissions.dom().contains(perm.addr()) ==> post.permission_guard.contains(perm));
                }


                // assert(
                //     forall |perm2: PointsTo<StackCell>| #![auto]
                //         ((post.address_permissions.dom().contains(perm2.addr())) ==>
                //             pre.address_permissions.dom().contains(perm2.addr())) || perm2 == points_to
                // );

                // assert(pre.permission_guard.insert(points_to) == post.permission_guard);
            };   
        }

        #[inductive(push)]
        fn push_inductive(pre: Self, post: Self, points_to: PointsTo<StackCell>) {
            assert(pre.permission_guard == pre.address_permissions_witnesses.values());
            assert(!pre.permission_guard.contains(points_to));
            assert(!pre.address_permissions.dom().contains(points_to.addr()));
            assume(post.permission_guard == post.address_permissions_witnesses.values());

            assume(false);
        }

        // #[inductive(pop)]
        // fn pop_inductive(pre: Self, post: Self) { }
    }
}

pub struct AtomicTokens {
    pub cell_witnesses: Tracked<Map<usize, machine::address_permissions_witnesses>>,
    pub permission_guard: Tracked<machine::permission_guard>
}

#[derive(Copy, Clone)]
pub struct StackCell {
    pub elem: u32,
    pub next: usize,
}

struct_with_invariants!{
    pub struct TreiberStack {
        pub base_address: usize,
        pub head: AtomicUsize<_, AtomicTokens, _>,
        pub instance: Tracked<machine::Instance>,
    }

    pub open spec fn wf(self) -> bool {
        invariant on head with (base_address, instance) is (addr: usize, atomic_tokens: AtomicTokens) {
            (
                base_address == instance.base_address()
            ) &&
            (
                atomic_tokens.permission_guard.instance_id() == instance.id()
            ) &&
            (
                forall |map_key: usize| #![auto]
                    atomic_tokens.cell_witnesses.dom().contains(map_key) ==>
                        atomic_tokens.cell_witnesses.index(map_key).instance_id() == instance.id()
            ) &&
            (
                atomic_tokens.cell_witnesses.dom().contains(addr)
            ) &&
            (
                forall |map_key: usize| #![auto]
                    (atomic_tokens.cell_witnesses.dom().contains(map_key) && map_key != instance.base_address()) ==>
                        atomic_tokens.cell_witnesses.index(map_key).value().is_init()
            ) &&
            (
                forall |map_key: usize| #![auto]
                    atomic_tokens.cell_witnesses.dom().contains(map_key) ==>
                        atomic_tokens.cell_witnesses.index(map_key).key() == map_key
            ) &&
            (
                forall |map_key: usize| #![auto]
                    (atomic_tokens.cell_witnesses.dom().contains(map_key)) ==>
                        atomic_tokens.cell_witnesses.index(map_key).value().addr() == map_key
            )
        }
    }
}

impl TreiberStack {
    fn new() -> (treiber_stack: Self)
        ensures treiber_stack.wf()
    {
        let (base, Tracked(base_perm)) = PPtr::<StackCell>::empty();
        let base_address = base.addr();

        let tracked (
            Tracked(instance), 
            Tracked(permission_guard),
            Tracked(address_permissions_witnesses),
            Tracked(linearised_history)
        ) = machine::Instance::initialize(base_address, Map::tracked_empty());

        let tracked witness_tokens = Map::tracked_empty();

        proof {
            let tracked base_witness = instance.create_base(base_perm, &mut permission_guard, base_perm);
            witness_tokens.tracked_insert(base_address, base_witness);
        }

        let atomic_tokens = AtomicTokens {
            cell_witnesses: Tracked(witness_tokens),
            permission_guard: Tracked(permission_guard)
        };

        let head = AtomicUsize::new(Ghost((base_address, Tracked(instance))), base_address, Tracked(atomic_tokens));

        TreiberStack { base_address, head, instance: Tracked(instance) }
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

            let mut push_result = atomic_with_ghost!(
                self.head => compare_exchange(
                    permissioned_stack_cell.read(Tracked(&stack_cell_perm)).next, 
                    permissioned_stack_cell.addr()
                );
                returning previous_head_result;

                ghost points_to_inv => {
                    if let Ok(previous_head) = previous_head_result {
                        assume(!points_to_inv.permission_guard.value().contains(stack_cell_perm));
                        let tracked witness_token = self.instance.push(stack_cell_perm, &mut points_to_inv.permission_guard, stack_cell_perm);
                        points_to_inv.cell_witnesses.tracked_insert(witness_token.key(), witness_token);
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
            let tracked witness_token;
            let tracked token_ref; 

            let mut head_stack_cell_address = atomic_with_ghost!{
                self.head => load();
                returning addr;

                ghost points_to_inv => {
                    witness_token = points_to_inv.cell_witnesses.tracked_remove(addr);
                    points_to_inv.cell_witnesses.tracked_insert(addr, witness_token);

                }
            };

            if head_stack_cell_address == self.base_address {
                return popped_value;
            }

            proof {
                token_ref = self.instance.get_permission_reference(witness_token.key(), witness_token.value(), &witness_token);
            }

            let permissioned_pointer = PPtr::<StackCell>::from_addr(head_stack_cell_address);
            let head_read = permissioned_pointer.read(Tracked(token_ref));

            let mut possible_new_head_address = atomic_with_ghost!{
                self.head => compare_exchange(
                    head_stack_cell_address, 
                    head_read.next
                );
                update current_head_address -> new_head_address;
                returning possible_new_head_address;

                ghost points_to_inv => {
                    if let Ok(_) = possible_new_head_address {
                        assume(points_to_inv.cell_witnesses.dom().contains(new_head_address));
                    }
                }
            };

            if let Ok(new_head_address) = possible_new_head_address {
                return Some(head_read.elem);
            }
        }
    }
}

fn main() {
    let shared_stack = Arc::new(TreiberStack::new());
}

}