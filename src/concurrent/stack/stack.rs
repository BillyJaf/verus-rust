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

global layout StackCell is size == 16;

pub enum Operation {
    Pop(Option<u32>),
    Push(u32),
    Init
}

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(constant)]
            pub base_address: usize,

            #[sharding(variable)]
            pub cell_addresses: Set<usize>,

            #[sharding(persistent_map)]
            pub address_permissions_witnesses: Map<usize, PointsTo<StackCell>>,

            #[sharding(storage_map)]
            pub address_permissions: Map<usize, PointsTo<StackCell>>,

            #[sharding(map)]
            pub linearised_history: Map<nat, Operation>,
        }

        #[invariant]
        pub fn complete_linearised_history_inv(&self) -> bool {
            &&& self.linearised_history.dom().finite()
            &&& forall |i: nat| i < self.linearised_history.dom().len() <==> 
                    self.linearised_history.dom().contains(i)
        }

        #[invariant]
        pub fn uninitialised_operation_inv(&self) -> bool {
            self.address_permissions.dom() == self.cell_addresses
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

        #[invariant]
        pub fn stack_has_valid_witnesses(&self) -> bool {
            forall |addr: usize| #![auto]
                (self.address_permissions_witnesses.dom().contains(addr) && addr != self.base_address) ==>
                    self.address_permissions_witnesses.dom().contains(self.address_permissions_witnesses.index(addr).value().next)
        }

        init!{
            initialize(base_permission: PointsTo<StackCell>)
            {
                init base_address                  = base_permission.addr();
                init cell_addresses                = Set::empty().insert(base_permission.addr());
                init address_permissions_witnesses = Map::empty().insert(base_permission.addr(), base_permission);
                init address_permissions           = Map::empty().insert(base_permission.addr(), base_permission);
                init linearised_history            = Map::empty().insert(0, Operation::Init);
            }
        }

        transition!{
            push(points_to: PointsTo<StackCell>)
            {
                require(!pre.cell_addresses.contains(points_to.addr()));
                require(pre.cell_addresses.contains(points_to.value().next));

                update cell_addresses                    = pre.cell_addresses.insert(points_to.addr());
                deposit address_permissions             += [points_to.addr() => points_to];
                add address_permissions_witnesses (union)= [points_to.addr() => points_to];

                birds_eye let next_operation_index       = pre.linearised_history.dom().len();
                add linearised_history                  += [next_operation_index => Operation::Push(points_to.value().elem)];
            }
        }

        transition!{
            pop(points_to: PointsTo<StackCell>)
            {
                require(points_to.addr() != pre.base_address);

                have address_permissions_witnesses >= [points_to.addr() => points_to];

                birds_eye let next_operation_index  = pre.linearised_history.dom().len();
                add linearised_history             += [next_operation_index => Operation::Pop(Some(points_to.value().elem))];
            }
        }

        transition!{
            empty_stack_pop(points_to: PointsTo<StackCell>)
            {
                require(points_to.addr() == pre.base_address);

                have address_permissions_witnesses >= [points_to.addr() => points_to];

                birds_eye let next_operation_index  = pre.linearised_history.dom().len();
                add linearised_history             += [next_operation_index => Operation::Pop(None)];
            }
        }

        property!{
            get_permission_reference(addr: usize, permission: PointsTo<StackCell>) {
                have address_permissions_witnesses >= [addr => permission];
                guard address_permissions          >= [addr => permission];
            }
        }

        property!{
            have_stack_witness(addr: usize, permission: PointsTo<StackCell>) {
                have address_permissions_witnesses >= [addr => permission];
                require(addr != pre.base_address);
                assert(pre.cell_addresses.contains(permission.value().next));
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, base_permission: PointsTo<StackCell>) { }

        #[inductive(push)]
        fn push_inductive(pre: Self, post: Self, points_to: PointsTo<StackCell>) { }

        #[inductive(pop)]
        fn pop_inductive(pre: Self, post: Self, points_to: PointsTo<StackCell>) { }

        #[inductive(empty_stack_pop)]
        fn empty_stack_pop_inductive(pre: Self, post: Self, points_to: PointsTo<StackCell>) { }
    }
}

pub struct AtomicTokens {
    pub cell_witnesses: Tracked<Map<usize, machine::address_permissions_witnesses>>,
    pub cell_addresses: Tracked<machine::cell_addresses>
}

#[derive(Copy, Clone)]
pub struct StackCell {
    pub elem: u32,
    pub next: usize,
}

struct_with_invariants!{
    pub struct TreiberStack {
        pub base_address: usize,
        pub top_address: AtomicUsize<_, AtomicTokens, _>,
        pub instance: Tracked<machine::Instance>,
    }

    pub open spec fn wf(self) -> bool {
        invariant on top_address with (base_address, instance) is (top_address: usize, atomic_tokens: AtomicTokens) {
            // The base address must reflect the TSM base address:
            &&& base_address == instance.base_address()

            // The base address is always present even before the first push:
            &&& atomic_tokens.cell_addresses.value().contains(base_address)

            // All tokens must come from the correct TSM:
            &&& atomic_tokens.cell_addresses.instance_id() == instance.id()
            &&& forall |address: usize| #![auto]
                    atomic_tokens.cell_witnesses.dom().contains(address) ==>
                        atomic_tokens.cell_witnesses.index(address).instance_id() == instance.id()
            
            // There is a witness token for the current address:
            &&& atomic_tokens.cell_witnesses.dom().contains(top_address)

            // The set of cell addresses should equal the domain of the witness tokens:
            &&&  atomic_tokens.cell_addresses.value() == atomic_tokens.cell_witnesses.dom()

            // Every witness token's permission points to initialised memory except for the witness of the base address:
            &&& forall |address: usize| #![auto]
                    atomic_tokens.cell_witnesses.dom().contains(address) ==> (
                        address != base_address <==> atomic_tokens.cell_witnesses.index(address).value().is_init()
                    )

            // Each individual map entry must agree internally at the address it is referencing
            &&& forall |address: usize| #![auto]
                    atomic_tokens.cell_witnesses.dom().contains(address) ==> (
                        atomic_tokens.cell_witnesses.index(address).key() == address &&
                        atomic_tokens.cell_witnesses.index(address).value().addr() == address
                    )
        }
    }
}

pub struct PoppedElemAndWitness {
        pub elem: Option<u32>,
        pub witness: Tracked<machine::linearised_history>
    }

impl TreiberStack {
    fn new() -> (treiber_stack: Self)
        ensures treiber_stack.wf()
    {
        let (base, Tracked(base_perm)) = PPtr::<StackCell>::empty();
        let base_address = base.addr();

        let tracked address_permissions = Map::tracked_empty();
        proof {
            address_permissions.tracked_insert(base_address, base_perm);
        }

        let tracked (
            Tracked(instance), 
            Tracked(cell_addresses),
            Tracked(address_permissions_witnesses),
            Tracked(linearised_history)
        ) = machine::Instance::initialize(base_perm, address_permissions);

        let tracked witness_tokens = address_permissions_witnesses.into_map();

        let atomic_tokens = AtomicTokens {
            cell_witnesses: Tracked(witness_tokens),
            cell_addresses: Tracked(cell_addresses)
        };

        let top_address = AtomicUsize::new(Ghost((base_address, Tracked(instance))), base_address, Tracked(atomic_tokens));

        TreiberStack { base_address, top_address, instance: Tracked(instance) }
    }

    pub fn push(self: Arc<Self>, elem: u32) -> (push_witness: Tracked<machine::linearised_history>)
        requires
            self.wf()
        ensures
            self.wf(),
            push_witness.value() == Operation::Push(elem)
    {
        loop 
            invariant
                self.wf()
        {
            let stack_cell = StackCell { elem, next: self.top_address.load() };
            let (permissioned_stack_cell, Tracked(stack_cell_perm)) = PPtr::new(stack_cell);

            let tracked push_witness = None;

            let mut push_result = atomic_with_ghost!(
                self.top_address => compare_exchange(
                    permissioned_stack_cell.read(Tracked(&stack_cell_perm)).next, 
                    permissioned_stack_cell.addr()
                );
                returning previous_head_result;

                ghost points_to_inv => {
                    if let Ok(previous_head) = previous_head_result {

                        if points_to_inv.cell_witnesses@.dom().contains(stack_cell_perm.addr()) {
                            let tracked witness_token = points_to_inv.cell_witnesses.tracked_borrow(stack_cell_perm.addr()); 
                            let tracked token_ref = self.instance.get_permission_reference(witness_token.key(), witness_token.value(), &witness_token);
                            stack_cell_perm.is_distinct(token_ref);
                            assert(false);
                        }

                        let tracked tuple = self.instance.push(stack_cell_perm, &mut points_to_inv.cell_addresses, stack_cell_perm);
                        let tracked witness_token = tuple.0.get();
                        push_witness = Some(tuple.2.get());

                        points_to_inv.cell_witnesses.tracked_insert(witness_token.key(), witness_token);
                    }
                }
            );

            if let Ok(_) = push_result {
                return Tracked(push_witness.tracked_unwrap());
            }
        }
    }

    pub fn pop(self: Arc<Self>) -> (popped_elem_and_witness: PoppedElemAndWitness)
        requires
            self.wf()
        ensures
            self.wf(),
            popped_elem_and_witness.witness.value() == Operation::Pop(popped_elem_and_witness.elem)
    {
        loop 
            invariant
                self.wf()
        {
            let tracked witness_token;
            let tracked token_ref;
            let tracked pop_witness = None;

            let mut head_stack_cell_address = atomic_with_ghost!{
                self.top_address => load();
                returning addr;

                ghost points_to_inv => {
                    witness_token = points_to_inv.cell_witnesses.tracked_borrow(addr).clone();
                    if addr == self.base_address {
                        pop_witness = Some(self.instance.empty_stack_pop(witness_token.value(), &witness_token).1.get());
                    }
                }
            };

            if head_stack_cell_address == self.base_address {
                return PoppedElemAndWitness { elem: None, witness: Tracked(pop_witness.tracked_unwrap()) };
            }

            proof {
                token_ref = self.instance.get_permission_reference(witness_token.key(), witness_token.value(), &witness_token);
            }

            let permissioned_pointer = PPtr::<StackCell>::from_addr(head_stack_cell_address);
            let head_read = permissioned_pointer.read(Tracked(token_ref));

            let mut possible_new_head_address = atomic_with_ghost!{
                self.top_address => compare_exchange(
                    head_stack_cell_address, 
                    head_read.next
                );
                update current_head_address -> new_head_address;
                returning possible_new_head_address;

                ghost points_to_inv => {
                    if let Ok(_) = possible_new_head_address {
                        self.instance.have_stack_witness(witness_token.key(), witness_token.value(), &points_to_inv.cell_addresses, &witness_token);
                        pop_witness = Some(self.instance.pop(witness_token.value(), &witness_token).1.get());
                    }
                }
            };

            if let Ok(new_head_address) = possible_new_head_address {
                return PoppedElemAndWitness { elem: Some(head_read.elem), witness: Tracked(pop_witness.tracked_unwrap()) };
            }
        }
    }
}

fn main() {
    let shared_stack = Arc::new(TreiberStack::new());
}
}