#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use std::sync::Arc;
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{atomic_ghost::*, pervasive::*, prelude::*, simple_pptr::*};

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

            // Stack Representation

            #[sharding(variable)]
            pub current_stack_addresses: Seq<StackCellAddress>,

            #[sharding(variable)]
            pub popped_addresses: Set<StackCellAddress>,

            // Witnesses and Permissions

            #[sharding(variable)]
            pub addresses: Set<StackCellAddress>,

            #[sharding(persistent_map)]
            pub witnesses: Map<StackCellAddress, PointsTo<StackCell>>,

            #[sharding(storage_map)]
            pub permissions: Map<StackCellAddress, PointsTo<StackCell>>,
        }

        // Current Stack Representation Invariants

        #[invariant]
        pub fn no_duplicates_inv(&self) -> bool {
            self.current_stack_addresses.no_duplicates()
        }

        #[invariant]
        pub fn current_stack_disjoint_popped_inv(&self) -> bool {
            self.current_stack_addresses.to_set().disjoint(self.popped_addresses)
        }

        #[invariant]
        pub fn current_stack_union_popped_inv(&self) -> bool {
            self.current_stack_addresses.to_set().union(self.popped_addresses) == self.addresses
        }

        #[invariant]
        pub fn current_stack_contains_base_address_inv(&self) -> bool {
            &&& self.current_stack_addresses.contains(self.base_address)
            &&& self.current_stack_addresses.first() == self.base_address
        }

        #[invariant]
        pub fn current_stack_has_witnesses_inv(&self) -> bool {
            self.current_stack_addresses.to_set().subset_of(self.witnesses.dom())
        }

        // Witnesses and Permissions Invariants

        #[invariant]
        pub fn addresses_reflect_permissions_inv(&self) -> bool {
            self.permissions.dom() == self.addresses
        }

        #[invariant]
        pub fn witnesses_reflect_permissions_inv(&self) -> bool {
            self.permissions == self.witnesses
        }

        #[invariant]
        pub fn base_address_witness_exists_inv(&self) -> bool {
            self.witnesses.dom().contains(self.base_address)
        }

        #[invariant]
        pub fn maps_are_correct_inv(&self) -> bool {
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
                    self.witnesses.index(addr).value().next_address
                )
        }

        #[invariant]
        pub fn permissions_are_init_except_base_inv(&self) -> bool {
            forall |addr: StackCellAddress| #![auto]
                self.permissions.dom().contains(addr) ==> (
                    addr != self.base_address <==> self.permissions.index(addr).is_init()
                )
        }

        init!{
            initialize(base_permission: PointsTo<StackCell>)
            {
                require(base_permission.is_uninit());
                init base_address = base_permission.addr();
                init current_stack_addresses = Seq::empty().push(base_permission.addr());
                init popped_addresses = Set::empty();
                init addresses = Set::empty().insert(base_permission.addr());
                init witnesses = Map::empty().insert(base_permission.addr(), base_permission);
                init permissions = Map::empty().insert(base_permission.addr(), base_permission);
            }
        }

        transition!{
            push(new_stack_cell_permission: PointsTo<StackCell>)
            {
                require(new_stack_cell_permission.is_init());
                require(pre.current_stack_addresses.last() == new_stack_cell_permission.value().next_address);
                require(!pre.addresses.contains(new_stack_cell_permission.addr()));

                update addresses = pre.addresses.insert(new_stack_cell_permission.addr());
                update current_stack_addresses = pre.current_stack_addresses.push(new_stack_cell_permission.addr());

                deposit permissions += [new_stack_cell_permission.addr() => new_stack_cell_permission];
                add witnesses (union)= [new_stack_cell_permission.addr() => new_stack_cell_permission];
            }
        }

        transition!{
            pop(current_head_stack_cell_permission: PointsTo<StackCell>)
            {
                require(current_head_stack_cell_permission.addr() != pre.base_address);
                require(pre.current_stack_addresses.last() == current_head_stack_cell_permission.addr());
                have witnesses >= [current_head_stack_cell_permission.addr() => current_head_stack_cell_permission];
                update popped_addresses = pre.popped_addresses.insert(pre.current_stack_addresses.last());
                update current_stack_addresses = pre.current_stack_addresses.drop_last();
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
                assert(pre.addresses.contains(stack_cell_permission.value().next_address));
            }
        }

        property!{
            same_address_implies_same_permission(stack_cell_permission_1: PointsTo<StackCell>, stack_cell_permission_2: PointsTo<StackCell>) {
                require(stack_cell_permission_1.addr() == stack_cell_permission_2.addr());
                have witnesses >= [stack_cell_permission_1.addr() => stack_cell_permission_1];
                have witnesses >= [stack_cell_permission_2.addr() => stack_cell_permission_2];
                assert(stack_cell_permission_1 == stack_cell_permission_2);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, base_permission: PointsTo<StackCell>) {
            assert(post.current_stack_addresses.first() == post.base_address);
            assert(post.current_stack_addresses.to_set().union(post.popped_addresses) == post.addresses);
            assert(post.witnesses.index(post.base_address).is_uninit());
        }

        #[inductive(push)]
        fn push_inductive(pre: Self, post: Self, new_stack_cell_permission: PointsTo<StackCell>) {
            assert(pre.current_stack_addresses == post.current_stack_addresses.drop_last());
            assert(post.current_stack_addresses.last() == (new_stack_cell_permission.addr()));
            assert(post.current_stack_addresses.to_set().union(post.popped_addresses) == post.addresses);
        }

        #[inductive(pop)]
        fn pop_inductive(pre: Self, post: Self, current_head_stack_cell_permission: PointsTo<StackCell>) {
            pre.current_stack_addresses.lemma_add_last_back();
            assert(post.current_stack_addresses.to_set().union(post.popped_addresses) == post.addresses);
        }
    }
}

pub tracked struct AtomicTokens {
    pub current_stack_addresses: machine::current_stack_addresses,
    pub popped_addresses: machine::popped_addresses,
    pub witnesses: Map<StackCellAddress, machine::witnesses>,
    pub addresses: machine::addresses,
}

#[derive(Copy, Clone)]
pub struct StackCell {
    pub elem: u32,
    pub next_address: StackCellAddress,
}

struct_with_invariants!{
    pub struct TreiberStack {
        pub base_address: StackCellAddress,
        pub top_address: AtomicUsize<_, AtomicTokens, _>,
        pub instance: Tracked<machine::Instance>
    }

    pub open spec fn wf(self) -> bool {
        invariant on top_address with (base_address, instance) is (top_addr: usize, atomic_tokens: AtomicTokens) {
            // The base address must reflect the TSM base address:
            &&& base_address == instance.base_address()

            // All tokens must come from the correct TSM:
            &&& atomic_tokens.current_stack_addresses.instance_id() == instance.id()
            &&& atomic_tokens.popped_addresses.instance_id() == instance.id()
            &&& atomic_tokens.addresses.instance_id() == instance.id()
            &&& forall |addr: StackCellAddress| #![auto]
                    atomic_tokens.witnesses.dom().contains(addr) ==>
                        atomic_tokens.witnesses.index(addr).instance_id() == instance.id()

            // The base address is always present even before the first push:
            &&& atomic_tokens.witnesses.dom().contains(base_address)
            &&& atomic_tokens.current_stack_addresses.value().contains(base_address)
            &&& atomic_tokens.current_stack_addresses.value().first() == base_address

            // The top address is always tracked:
            &&& atomic_tokens.witnesses.dom().contains(top_addr)
            &&& atomic_tokens.current_stack_addresses.value().contains(top_addr)
            &&& atomic_tokens.current_stack_addresses.value().last() == top_addr

            // If the top is the base, then our stack is empty (we only have the base):
            &&& top_addr == base_address <==> atomic_tokens.current_stack_addresses.value().len() == 1

            // There are no duplicate addresses in our stack
            &&& atomic_tokens.current_stack_addresses.value().no_duplicates()

            // The current stack cell addresses is disjoint from the set of all popped stack cell addresses:
            // However, their union should be the domain of the set of all witnesses
            &&& atomic_tokens.current_stack_addresses.value().to_set().disjoint(atomic_tokens.popped_addresses.value())
            &&& atomic_tokens.witnesses.dom() =~= atomic_tokens.current_stack_addresses.value().to_set().union(atomic_tokens.popped_addresses.value())
            &&& atomic_tokens.current_stack_addresses.value().to_set().subset_of(atomic_tokens.witnesses.dom())

            // The set of cell addresses should equal the domain of the witness tokens:
            &&& atomic_tokens.addresses.value() == atomic_tokens.witnesses.dom()

            // Every witness token's permission points to initialised memory except for the witness of the base address:
            &&& forall |addr: StackCellAddress| #![auto]
                    atomic_tokens.witnesses.dom().contains(addr) ==> (
                        addr != base_address <==> atomic_tokens.witnesses.index(addr).value().is_init()
                    )

            // Each individual map entry must agree internally at the address it is referencing (map structure):
            &&& forall |addr: StackCellAddress| #![auto]
                    atomic_tokens.witnesses.dom().contains(addr) ==> (
                        atomic_tokens.witnesses.index(addr).key() == addr &&
                        atomic_tokens.witnesses.index(addr).value().addr() == addr
                    )

            // There exists a witness for the next stack cell of every current stack cell (except base):
            &&& forall |addr: StackCellAddress| #![auto]
                    (
                        atomic_tokens.witnesses.dom().contains(addr) &&
                        addr != base_address
                    ) ==>
                    atomic_tokens.witnesses.dom().contains(
                        atomic_tokens.witnesses.index(addr).value().value().next_address
                    )

            &&& forall |i: int| #![auto]
                    0 < i < atomic_tokens.current_stack_addresses.value().len() ==> (
                        atomic_tokens.current_stack_addresses.value()[i-1] ==
                        atomic_tokens.witnesses.index(atomic_tokens.current_stack_addresses.value()[i]).value().value().next_address
                    )
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
            Tracked(current_stack_addresses),
            Tracked(popped_addresses),
            Tracked(addresses),
            Tracked(witnesses),
        ) = machine::Instance::initialize(base_perm, permissions);

        let tracked witnesses = witnesses.into_map();

        let tracked atomic_tokens = AtomicTokens {
            current_stack_addresses,
            popped_addresses,
            witnesses,
            addresses
        };

        assert(current_stack_addresses.value().first() == base_address);

        let top_address = AtomicUsize::new(
            Ghost((base_address, Tracked(instance))),
            base_address,
            Tracked(atomic_tokens),
        );

        TreiberStack { base_address, top_address, instance: Tracked(instance) }
    }

    pub fn push(&self, elem: u32)
        requires
            self.wf(),
        ensures
            self.wf(),
    {
        loop
            invariant
                self.wf(),
        {
            let new_stack_cell = StackCell { elem, next_address: self.top_address.load() };
            let (permission_guarded_new_stack_cell, Tracked(new_stack_cell_permission)) = PPtr::new(
                new_stack_cell,
            );

            let mut push_result =
                atomic_with_ghost!(
                self.top_address => compare_exchange(
                    permission_guarded_new_stack_cell.read(Tracked(&new_stack_cell_permission)).next_address,
                    permission_guarded_new_stack_cell.addr()
                );
                returning previous_head_address_result;

                ghost atomic_tokens => {
                    if let Ok(_) = previous_head_address_result {

                        // Proving that there does not already exist a permission for the cell in the TSM (or our tokens by extension):
                        if atomic_tokens.witnesses.dom().contains(new_stack_cell_permission.addr()) {
                            let tracked witness_token = atomic_tokens.witnesses.tracked_borrow(new_stack_cell_permission.addr());
                            let tracked stack_cell_permission_reference = self.instance.get_permission_reference(witness_token.key(), witness_token.value(), &witness_token);
                            new_stack_cell_permission.is_distinct(stack_cell_permission_reference);
                            assert(false);
                        }

                        let ghost pre_current_stack_addresses = Ghost(atomic_tokens.current_stack_addresses.value());

                        let tracked witness_token = self.instance.push(
                            new_stack_cell_permission,
                            &mut atomic_tokens.current_stack_addresses,
                            &mut atomic_tokens.addresses,
                            new_stack_cell_permission
                        );

                        assert(pre_current_stack_addresses@ =~= pre_current_stack_addresses.push(witness_token.value().addr()).drop_last());

                        // Insert the witness token for the new stack cell into our map:
                        atomic_tokens.witnesses.tracked_insert(witness_token.key(), witness_token);

                        // The push correctly updated our view of the stack:
                        assert(atomic_tokens.current_stack_addresses.value().last() == witness_token.key());
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
            self.wf(),
    {
        loop
            invariant
                self.wf(),
        {
            let tracked stack_head_witness;
            let tracked stack_cell_permission_reference;

            let mut top_address =
                atomic_with_ghost!{
                self.top_address => load();
                returning addr;

                ghost atomic_tokens => {
                    stack_head_witness = *atomic_tokens.witnesses.tracked_borrow(addr);
                }
            };

            if top_address == self.base_address {
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

            let permissioned_pointer = PPtr::<StackCell>::from_addr(top_address);
            let head_read = permissioned_pointer.read(Tracked(stack_cell_permission_reference));

            let mut new_stack_head_address_result =
                atomic_with_ghost!{
                self.top_address => compare_exchange(
                    top_address,
                    head_read.next_address
                );
                update current_stack_head_address -> new_stack_head_address;
                returning previous_head_address_result;

                ghost atomic_tokens => {
                    if let Ok(_) = previous_head_address_result {
                        // There is a witness token for new_stack_head_address:
                        self.instance.have_witness_after_pop(
                            stack_head_witness.key(),
                            stack_head_witness.value(),
                            &atomic_tokens.addresses,
                            &stack_head_witness
                        );

                        // Assert that the witness token for the current stack head, has next_address == new_stack_head_address:
                        let tracked possible_second_old_stack_head_witness = atomic_tokens.witnesses.tracked_borrow(current_stack_head_address);
                        self.instance.same_address_implies_same_permission(
                            stack_head_witness.value(),
                            possible_second_old_stack_head_witness.value(),
                            &stack_head_witness,
                            &possible_second_old_stack_head_witness
                        );

                        // This assert is are trivial, but we need to disharge them:
                        assert(atomic_tokens.current_stack_addresses.value() =~= atomic_tokens.current_stack_addresses.value().drop_last().push(stack_head_witness.value().addr()));

                        self.instance.pop(
                            stack_head_witness.value(),
                            &mut atomic_tokens.current_stack_addresses,
                            &mut atomic_tokens.popped_addresses,
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

pub fn main() {
}

} // verus!
