#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use std::sync::Arc;
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{
    atomic_ghost::*, 
    prelude::*, 
    pervasive::*,
    simple_pptr::*,
};

verus! {

global layout StackCell is size == 16;

type StackCellAddress = usize;

pub enum StackCellContents {
    Elem(u32),
    Base,
}

pub enum Operation {
    Pop(Option<u32>),
    Push(u32),
    InitBase,
}

impl Operation {
    pub open spec fn is_empty_pop(&self) -> bool {
        match self {
            Operation::Pop(None) => true,
            _ => false,
        }
    }
}

tokenized_state_machine!{
    machine {
        fields {
            // Book Keeping

            #[sharding(constant)]
            pub base_address: StackCellAddress,

            // Witnesses and Permissions

            #[sharding(variable)]
            pub addresses: Set<StackCellAddress>,

            #[sharding(persistent_map)]
            pub witnesses: Map<StackCellAddress, PointsTo<StackCell>>,

            #[sharding(storage_map)]
            pub permissions: Map<StackCellAddress, PointsTo<StackCell>>,
        }

        // Witnesses and Permissions Invariants

        #[invariant]
        pub fn permissions_domain_equals_addresses_inv(&self) -> bool {
            self.permissions.dom() == self.addresses
        }

        #[invariant]
        pub fn permissions_equals_witnesses_inv(&self) -> bool {
            self.permissions == self.witnesses
        }

        #[invariant]
        pub fn base_address_witness_always_exists_inv(&self) -> bool {
            self.witnesses.dom().contains(self.base_address)
        }

        #[invariant]
        pub fn permissions_and_permissions_domains_are_correct_inv(&self) -> bool {
            forall |addr: StackCellAddress| #![auto]
                (
                    self.witnesses.dom().contains(addr) ==>
                        self.witnesses.index(addr).addr() == addr
                ) && (
                    self.permissions.dom().contains(addr) ==>
                        self.permissions.index(addr).addr() == addr
                )
        }

        #[invariant]
        pub fn witnesses_contains_next_witness_inv(&self) -> bool {
            forall |addr: StackCellAddress| #![auto]
                (
                    self.witnesses.dom().contains(addr) &&
                    addr != self.base_address
                ) ==>
                self.witnesses.dom().contains(
                    self.witnesses.index(addr).value().next
                )
        }

        #[invariant]
        pub fn witnesses_are_init_except_base_witness_inv(&self) -> bool {
            forall |addr: StackCellAddress| #![auto]
                self.witnesses.dom().contains(addr) ==> (
                    addr != self.base_address <==> self.witnesses.index(addr).is_init()
                )
        }

        init!{
            initialize(base_permission: PointsTo<StackCell>)
            {
                require(base_permission.is_uninit());
                init base_address = base_permission.addr();
                init addresses = Set::empty().insert(base_permission.addr());
                init witnesses = Map::empty().insert(base_permission.addr(), base_permission);
                init permissions = Map::empty().insert(base_permission.addr(), base_permission);
            }
        }

        transition!{
            push(new_stack_cell_permission: PointsTo<StackCell>)
            {
                require(new_stack_cell_permission.is_init());
                require(pre.addresses.contains(new_stack_cell_permission.value().next));

                require(!pre.addresses.contains(new_stack_cell_permission.addr()));

                update addresses = pre.addresses.insert(new_stack_cell_permission.addr());
                deposit permissions += [new_stack_cell_permission.addr() => new_stack_cell_permission];
                add witnesses (union)= [new_stack_cell_permission.addr() => new_stack_cell_permission];
            }
        }

        transition!{
            pop(new_head_stack_cell_permission: PointsTo<StackCell>, current_head_stack_cell_permission: PointsTo<StackCell>)
            {
                require(current_head_stack_cell_permission.addr() != pre.base_address);

                require(current_head_stack_cell_permission.value().next == new_head_stack_cell_permission.addr());

                have witnesses >= [current_head_stack_cell_permission.addr() => current_head_stack_cell_permission];
            }
        }

        transition!{
            empty_stack_pop(base_stack_cell_permission: PointsTo<StackCell>)
            {
                require(base_stack_cell_permission.addr() == pre.base_address);

                have witnesses >= [base_stack_cell_permission.addr() => base_stack_cell_permission];
            }
        }

        property!{
            get_permission_reference(stack_cell_address: StackCellAddress, stack_cell_permission: PointsTo<StackCell>) {
                have witnesses >= [stack_cell_address => stack_cell_permission];
                guard permissions >= [stack_cell_address => stack_cell_permission];
            }
        }

        property!{
            have_witness_after_pop(stack_cell_address: StackCellAddress, stack_cell_permission: PointsTo<StackCell>) {
                require(stack_cell_address != pre.base_address);
                have witnesses >= [stack_cell_address => stack_cell_permission];
                assert(pre.addresses.contains(stack_cell_permission.value().next));
            }
        }

        property!{
            same_address_implies_same_permission(stack_cell_address_1: StackCellAddress, stack_cell_permission_1: PointsTo<StackCell>, stack_cell_address_2: StackCellAddress, stack_cell_permission_2: PointsTo<StackCell>) {
                require(stack_cell_address_1 == stack_cell_address_2);
                have witnesses >= [stack_cell_address_1 => stack_cell_permission_1];
                have witnesses >= [stack_cell_address_2 => stack_cell_permission_2];
                assert(stack_cell_permission_1 == stack_cell_permission_2);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, base_permission: PointsTo<StackCell>) {
            assert(post.witnesses.index(post.base_address).is_uninit());
        }

        #[inductive(push)]
        fn push_inductive(pre: Self, post: Self, new_stack_cell_permission: PointsTo<StackCell>) {
        }

        #[inductive(pop)]
        fn pop_inductive(pre: Self, post: Self, new_head_stack_cell_permission: PointsTo<StackCell>, current_head_stack_cell_permission: PointsTo<StackCell>) {
        }

        #[inductive(empty_stack_pop)]
        fn empty_stack_pop_inductive(pre: Self, post: Self, base_stack_cell_permission: PointsTo<StackCell>) {
        }
    }
}

pub struct AtomicTokens {
    pub witnesses: Tracked<
        Map<StackCellAddress, machine::witnesses>,
    >,
    pub addresses: Tracked<machine::addresses>,
}

#[derive(Copy, Clone)]
pub struct StackCell {
    pub elem: u32,
    pub next: StackCellAddress,
}

struct_with_invariants!{
    pub struct TreiberStack {
        pub base_address: StackCellAddress,
        pub head_stack_cell_address: AtomicUsize<_, AtomicTokens, _>,
        pub instance: Tracked<machine::Instance>,
    }

    pub open spec fn wf(self) -> bool {
        invariant on head_stack_cell_address with (base_address, instance) is (head_stack_cell_address: usize, atomic_tokens: AtomicTokens) {
            // The base address must reflect the TSM base address:
            &&& base_address == instance.base_address()

            // All tokens must come from the correct TSM:
            &&& atomic_tokens.addresses.instance_id() == instance.id()
            &&& (forall |addr: StackCellAddress| #![auto]
                    atomic_tokens.witnesses.dom().contains(addr) ==>
                        atomic_tokens.witnesses.index(addr).instance_id() == instance.id())

            // The base address is always present even before the first push:
            &&& atomic_tokens.witnesses.dom().contains(base_address)
            &&& atomic_tokens.addresses.value().contains(base_address)

            // The top address is always tracked:
            &&& atomic_tokens.witnesses.dom().contains(head_stack_cell_address)

            // The set of cell addresses should equal the domain of the witness tokens:
            &&& atomic_tokens.addresses.value() == atomic_tokens.witnesses.dom()

            // Every witness token's permission points to initialised memory except for the witness of the base address:
            &&& (forall |addr: StackCellAddress| #![auto]
                    atomic_tokens.witnesses.dom().contains(addr) ==> (
                        addr != base_address <==> atomic_tokens.witnesses.index(addr).value().is_init()
                    ))

            // Each individual map entry must agree internally at the address it is referencing (map structure):
            &&& (forall |addr: StackCellAddress| #![auto]
                    atomic_tokens.witnesses.dom().contains(addr) ==> (
                        atomic_tokens.witnesses.index(addr).key() == addr &&
                        atomic_tokens.witnesses.index(addr).value().addr() == addr
                    ))
        }
    }
}

impl TreiberStack {
    pub fn new() -> (treiber_stack: Self)
        ensures
            treiber_stack.wf(),
    {
        let (base, Tracked(base_perm)) = PPtr::<StackCell>::empty();
        let base_address = base.addr();

        let tracked permissions = Map::tracked_empty();
        proof {
            permissions.tracked_insert(base_address, base_perm);
        }

        let tracked (
            Tracked(instance),
            Tracked(addresses),
            Tracked(witnesses),
        ) = machine::Instance::initialize(base_perm, permissions);

        let tracked witness_tokens = witnesses.into_map();

        let atomic_tokens = AtomicTokens {
            witnesses: Tracked(witness_tokens),
            addresses: Tracked(addresses),
        };

        let head_stack_cell_address = AtomicUsize::new(
            Ghost((base_address, Tracked(instance))),
            base_address,
            Tracked(atomic_tokens),
        );

        TreiberStack { base_address, head_stack_cell_address, instance: Tracked(instance) }
    }

    pub fn push(&self, elem: u32)
        requires
            self.wf(),
        ensures
            self.wf()
    {
        loop
            invariant
                self.wf(),
        {
            let new_stack_cell = StackCell { elem, next: self.head_stack_cell_address.load() };
            let (permission_guarded_new_stack_cell, Tracked(new_stack_cell_permission)) = PPtr::new(
                new_stack_cell,
            );

            let mut push_result =
                atomic_with_ghost!(
                self.head_stack_cell_address => compare_exchange(
                    permission_guarded_new_stack_cell.read(Tracked(&new_stack_cell_permission)).next,
                    permission_guarded_new_stack_cell.addr()
                );
                returning previous_head_address_result;

                ghost points_to_inv => {
                    if let Ok(_) = previous_head_address_result {

                        // Proving that there does not already exist a permission for the cell in the TSM (or our tokens by extension):
                        if points_to_inv.witnesses@.dom().contains(new_stack_cell_permission.addr()) {
                            let tracked witness_token = points_to_inv.witnesses.tracked_borrow(new_stack_cell_permission.addr());
                            let tracked stack_cell_permission_reference = self.instance.get_permission_reference(witness_token.key(), witness_token.value(), &witness_token);
                            new_stack_cell_permission.is_distinct(stack_cell_permission_reference);
                            assert(false);
                        }

                        let tracked witness_token = self.instance.push(
                            new_stack_cell_permission,
                            &mut points_to_inv.addresses,
                            new_stack_cell_permission
                        );

                        // Insert the witness token for the new stack cell into our map:
                        points_to_inv.witnesses.tracked_insert(witness_token.key(), witness_token);
                    }
                }
            );

            if let Ok(_) = push_result {
                return;
            }
        }
    }

    pub fn pop(&self) -> (elem: Option<u32>)
        requires
            self.wf(),
        ensures
            self.wf()
    {
        loop
            invariant
                self.wf(),
        {
            let tracked stack_head_witness;
            let tracked stack_cell_permission_reference;

            let mut head_stack_cell_address =
                atomic_with_ghost!{
                self.head_stack_cell_address => load();
                returning addr;

                ghost points_to_inv => {
                    stack_head_witness = points_to_inv.witnesses.tracked_remove(addr);
                    points_to_inv.witnesses.tracked_insert(addr, stack_head_witness.clone());
                    if addr == self.base_address {
                        self.instance.empty_stack_pop(
                            stack_head_witness.value(),
                            &stack_head_witness
                        )
                    }
                }
            };

            if head_stack_cell_address == self.base_address {
                return None;
            }
            proof {
                stack_cell_permission_reference =
                self.instance.get_permission_reference(
                    stack_head_witness.key(),
                    stack_head_witness.value(),
                    &stack_head_witness,
                );
            }

            let permissioned_pointer = PPtr::<StackCell>::from_addr(head_stack_cell_address);
            let head_read = permissioned_pointer.read(Tracked(stack_cell_permission_reference));

            let mut new_stack_head_address_result =
                atomic_with_ghost!{
                self.head_stack_cell_address => compare_exchange(
                    head_stack_cell_address,
                    head_read.next
                );
                update current_stack_head_address -> new_stack_head_address;
                returning previous_head_address_result;

                ghost points_to_inv => {
                    if let Ok(_) = previous_head_address_result {
                        // There is a witness token for new_stack_head_address:
                        self.instance.have_witness_after_pop(
                            stack_head_witness.key(),
                            stack_head_witness.value(),
                            &points_to_inv.addresses,
                            &stack_head_witness
                        );
                        let tracked new_stack_head_witness = points_to_inv.witnesses.tracked_borrow(new_stack_head_address);

                        // Assert that the witness token for the current stack head, has next == new_stack_head_address:
                        let tracked possible_second_old_stack_head_witness = points_to_inv.witnesses.tracked_borrow(current_stack_head_address);
                        self.instance.same_address_implies_same_permission(
                            stack_head_witness.key(),
                            stack_head_witness.value(),
                            possible_second_old_stack_head_witness.key(),
                            possible_second_old_stack_head_witness.value(),
                            &stack_head_witness,
                            &possible_second_old_stack_head_witness
                        );
                        assert(possible_second_old_stack_head_witness.value() == stack_head_witness.value());
                        assert(stack_head_witness.value().value().next == new_stack_head_address);
                        
                        self.instance.pop(
                            new_stack_head_witness.value(),
                            stack_head_witness.value(),
                            &stack_head_witness
                        );
                    }
                }
            };

            if let Ok(new_stack_head_address) = new_stack_head_address_result {
                return Some(head_read.elem);
            }
        }
    }
}

pub fn main() {}
} // verus!