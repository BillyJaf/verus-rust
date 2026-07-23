#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use std::sync::Arc;
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{
    atomic_ghost::*, 
    prelude::*, 
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

pub open spec fn replay_history(
    operation_index: nat,
    linearised_history: Map<nat, Operation>,
    current_stack: Seq<StackCellContents>,
) -> Seq<StackCellContents>
    decreases linearised_history.len() - operation_index,
{
    if operation_index >= linearised_history.len() {
        current_stack
    } else {
        replay_history(
            (operation_index + 1) as nat,
            linearised_history,
            apply_operation(linearised_history[operation_index], current_stack),
        )
    }
}

pub open spec fn apply_operation(
    operation: Operation,
    current_stack: Seq<StackCellContents>,
) -> Seq<StackCellContents> {
    match operation {
        Operation::InitBase => current_stack.push(StackCellContents::Base),
        Operation::Push(elem) => current_stack.push(StackCellContents::Elem(elem)),
        Operation::Pop(Some(_)) => current_stack.drop_last(),
        Operation::Pop(None) => current_stack,
    }
}

pub proof fn interchange_apply_and_replay(
    operation_index: nat,
    linearised_history: Map<nat, Operation>,
    current_stack: Seq<StackCellContents>,
    appended_operation: Operation,
)
    requires
        forall|i: nat|
            #![auto]
            i < linearised_history.len() <==> linearised_history.dom().contains(i),
        operation_index <= linearised_history.len(),
        linearised_history.dom().finite(),
    ensures
        replay_history(
            operation_index,
            linearised_history.insert(linearised_history.len(), appended_operation),
            current_stack,
        ) == apply_operation(
            appended_operation,
            replay_history(operation_index, linearised_history, current_stack),
        ),
    decreases linearised_history.len() - operation_index,
{
    let extended = linearised_history.insert(linearised_history.len(), appended_operation);

    if operation_index == linearised_history.len() {
        assert(apply_operation(
            appended_operation,
            replay_history(operation_index, linearised_history, current_stack),
        ) == apply_operation(appended_operation, current_stack));

        assert(apply_operation(appended_operation, current_stack) == replay_history(
            (operation_index + 1) as nat,
            extended,
            apply_operation(appended_operation, current_stack),
        ));
    } else {
        interchange_apply_and_replay(
            (operation_index + 1) as nat,
            linearised_history,
            apply_operation(linearised_history[operation_index], current_stack),
            appended_operation,
        )
    }
}

pub proof fn replay_history_lemma(
    pre_linearised_history: Map<nat, Operation>,
    post_linearised_history: Map<nat, Operation>,
    operation: Operation,
)
    requires
        forall|i: nat|
            #![auto]
            i < pre_linearised_history.len() <==> pre_linearised_history.dom().contains(i),
        pre_linearised_history.insert(pre_linearised_history.len(), operation)
            == post_linearised_history,
        operation != Operation::InitBase,
        pre_linearised_history.dom().finite(),
    ensures
        match operation {
            Operation::Push(elem) => replay_history(
                0nat,
                pre_linearised_history,
                Seq::empty(),
            ).push(StackCellContents::Elem(elem)) == replay_history(
                0nat,
                post_linearised_history,
                Seq::empty(),
            ),
            Operation::Pop(Some(_)) => replay_history(
                0nat,
                pre_linearised_history,
                Seq::empty(),
            ).drop_last() == replay_history(0nat, post_linearised_history, Seq::empty()),
            Operation::Pop(None) => replay_history(0nat, pre_linearised_history, Seq::empty())
                == replay_history(0nat, post_linearised_history, Seq::empty()),
            Operation::InitBase => true,
        },
{
    interchange_apply_and_replay(0, pre_linearised_history, Seq::empty(), operation)
}

pub open spec fn count_pushes_up_to(
    operation_index: nat,
    linearised_history: Map<nat, Operation>,
) -> nat
    decreases operation_index,
{
    if operation_index == 0 {
        0nat
    } else {
        let possible_push = if let Operation::Push(_) = linearised_history[operation_index] {
            1nat
        } else {
            0nat
        };

        possible_push + count_pushes_up_to((operation_index - 1) as nat, linearised_history)
    }
}

pub open spec fn count_successful_pops_up_to(
    operation_index: nat,
    linearised_history: Map<nat, Operation>,
) -> nat
    decreases operation_index,
{
    if operation_index == 0 {
        0nat
    } else {
        let possible_push = if let Operation::Pop(Some(_)) = linearised_history[operation_index] {
            1nat
        } else {
            0nat
        };

        possible_push + count_pushes_up_to((operation_index - 1) as nat, linearised_history)
    }
}

pub proof fn stable_counts(
    up_to_index: nat,
    pre_linearised_history: Map<nat, Operation>,
    post_linearised_history: Map<nat, Operation>,
)
    requires
        up_to_index < pre_linearised_history.dom().len(),
        pre_linearised_history =~= post_linearised_history.remove(pre_linearised_history.len()),
    ensures
        count_pushes_up_to(up_to_index, pre_linearised_history) == count_pushes_up_to(
            up_to_index,
            post_linearised_history,
        ),
        count_successful_pops_up_to(up_to_index, pre_linearised_history)
            == count_successful_pops_up_to(up_to_index, post_linearised_history),
    decreases up_to_index,
{
    if up_to_index == 0 {
    } else {
        stable_counts((up_to_index - 1) as nat, pre_linearised_history, post_linearised_history);
    }
}

tokenized_state_machine!{
    machine {
        fields {
            // Book Keeping

            #[sharding(constant)]
            pub base_address: StackCellAddress,

            #[sharding(map)]
            pub linearised_history: Map<nat, Operation>,

            // Stack Representation

            #[sharding(variable)]
            pub current_stack_cell_elements: Seq<StackCellContents>,

            #[sharding(variable)]
            pub current_stack_cell_addresses: Seq<StackCellAddress>,

            #[sharding(variable)]
            pub popped_stack_cell_addresses: Set<StackCellAddress>,

            // Witnesses and Permissions

            #[sharding(variable)]
            pub all_stack_cell_addresses: Set<StackCellAddress>,

            #[sharding(persistent_map)]
            pub all_stack_cell_permissions_witnesses: Map<StackCellAddress, PointsTo<StackCell>>,

            #[sharding(storage_map)]
            pub all_stack_cell_address_permissions: Map<StackCellAddress, PointsTo<StackCell>>,
        }

        // Linearised History Invariants

        #[invariant]
        pub fn linearised_history_is_complete_inv(&self) -> bool {
            &&& self.linearised_history.dom().finite()
            &&& forall |i: nat| i < self.linearised_history.dom().len() <==>
                    self.linearised_history.dom().contains(i)
        }

        #[invariant]
        pub fn linearised_history_reflects_stack(&self) -> bool {
            replay_history(0nat, self.linearised_history, Seq::empty()) == self.current_stack_cell_elements
        }

        #[invariant]
        pub fn linearised_history_empty_pop_implies_empty_stack(&self) -> bool {
            forall |i: nat| #![auto]
                (i < self.linearised_history.len() && self.linearised_history[i].is_empty_pop()) ==> (
                    count_pushes_up_to(i, self.linearised_history) == count_successful_pops_up_to(i, self.linearised_history)
                )
        }

        // Current Stack Representation Invariants

        #[invariant]
        pub fn current_stack_cell_addresses_no_duplicates_inv(&self) -> bool {
            self.current_stack_cell_addresses.no_duplicates()
        }

        #[invariant]
        pub fn current_stack_cell_addresses_and_popped_stack_cell_addresses_are_disjoint_inv(&self) -> bool {
            self.current_stack_cell_addresses.to_set().disjoint(self.popped_stack_cell_addresses)
        }

        #[invariant]
        pub fn current_stack_cell_addresses_union_popped_stack_cell_addresses_are_all_addresses_inv(&self) -> bool {
            self.current_stack_cell_addresses.to_set().union(self.popped_stack_cell_addresses) == self.all_stack_cell_addresses
        }

        #[invariant]
        pub fn current_stack_cell_addresses_contains_base_address_inv(&self) -> bool {
            &&& self.current_stack_cell_addresses.contains(self.base_address)
            &&& self.current_stack_cell_addresses.first() == self.base_address
        }

        #[invariant]
        pub fn every_current_stack_cell_address_has_a_permission_witness_inv(&self) -> bool {
            forall |i: int| #![auto]
                0 <= i < self.current_stack_cell_addresses.len() ==>
                    self.all_stack_cell_permissions_witnesses.dom().contains(self.current_stack_cell_addresses[i])
        }

        #[invariant]
        pub fn current_stack_cell_addresses_reflects_current_stack_cell_elements_inv(&self) -> bool {
            &&& self.current_stack_cell_addresses.len() == self.current_stack_cell_elements.len()
            &&& self.current_stack_cell_elements[0] == StackCellContents::Base
            &&& forall |i: int| #![auto]
                    0 < i < self.current_stack_cell_addresses.len() ==>
                        self.current_stack_cell_elements[i] == StackCellContents::Elem(self.all_stack_cell_permissions_witnesses.index(self.current_stack_cell_addresses[i]).value().elem)
        }

        #[invariant]
        pub fn current_stack_cell_addresses_point_to_next_correctly_inv(&self) -> bool {
            forall |addr: StackCellAddress, i: int|
                (
                    #[trigger] self.current_stack_cell_addresses.contains(addr) &&
                    0 < i < self.current_stack_cell_addresses.len() &&
                    #[trigger] self.current_stack_cell_addresses[i] == addr
                ) ==>
                self.current_stack_cell_addresses[i-1] == self.all_stack_cell_permissions_witnesses.index(addr).value().next
        }

        // Witnesses and Permissions Invariants

        #[invariant]
        pub fn all_stack_cell_address_permissions_domain_equals_all_stack_cell_addresses_inv(&self) -> bool {
            self.all_stack_cell_address_permissions.dom() == self.all_stack_cell_addresses
        }

        #[invariant]
        pub fn all_stack_cell_address_permissions_equals_all_stack_cell_permissions_witnesses_inv(&self) -> bool {
            self.all_stack_cell_address_permissions == self.all_stack_cell_permissions_witnesses
        }

        #[invariant]
        pub fn base_address_witness_always_exists_inv(&self) -> bool {
            self.all_stack_cell_permissions_witnesses.dom().contains(self.base_address)
        }

        #[invariant]
        pub fn all_stack_cell_address_permissions_and_all_stack_cell_address_permissions_domains_are_correct_inv(&self) -> bool {
            forall |addr: StackCellAddress| #![auto]
                (
                    self.all_stack_cell_permissions_witnesses.dom().contains(addr) ==>
                        self.all_stack_cell_permissions_witnesses.index(addr).addr() == addr
                ) && (
                    self.all_stack_cell_address_permissions.dom().contains(addr) ==>
                        self.all_stack_cell_address_permissions.index(addr).addr() == addr
                )
        }

        #[invariant]
        pub fn all_stack_cell_permissions_witnesses_contains_next_witness_inv(&self) -> bool {
            forall |addr: StackCellAddress| #![auto]
                (
                    self.all_stack_cell_permissions_witnesses.dom().contains(addr) &&
                    addr != self.base_address
                ) ==>
                self.all_stack_cell_permissions_witnesses.dom().contains(
                    self.all_stack_cell_permissions_witnesses.index(addr).value().next
                )
        }

        #[invariant]
        pub fn all_stack_cell_permissions_witnesses_are_init_except_base_witness_inv(&self) -> bool {
            forall |addr: StackCellAddress| #![auto]
                self.all_stack_cell_permissions_witnesses.dom().contains(addr) ==> (
                    addr != self.base_address <==> self.all_stack_cell_permissions_witnesses.index(addr).is_init()
                )
        }

        init!{
            initialize(base_permission: PointsTo<StackCell>)
            {
                require(base_permission.is_uninit());
                init base_address = base_permission.addr();
                init linearised_history = Map::empty().insert(0, Operation::InitBase);
                init current_stack_cell_addresses = Seq::empty().push(base_permission.addr());
                init current_stack_cell_elements = Seq::empty().push(StackCellContents::Base);
                init popped_stack_cell_addresses = Set::empty();
                init all_stack_cell_addresses = Set::empty().insert(base_permission.addr());
                init all_stack_cell_permissions_witnesses = Map::empty().insert(base_permission.addr(), base_permission);
                init all_stack_cell_address_permissions = Map::empty().insert(base_permission.addr(), base_permission);
            }
        }

        transition!{
            push(new_stack_cell_permission: PointsTo<StackCell>)
            {
                require(new_stack_cell_permission.is_init());
                require(pre.all_stack_cell_addresses.contains(new_stack_cell_permission.value().next));
                require(pre.current_stack_cell_addresses.last() == new_stack_cell_permission.value().next);

                require(!pre.all_stack_cell_addresses.contains(new_stack_cell_permission.addr()));
                require(!pre.popped_stack_cell_addresses.contains(new_stack_cell_permission.addr()));

                update all_stack_cell_addresses                = pre.all_stack_cell_addresses.insert(new_stack_cell_permission.addr());
                update current_stack_cell_addresses      = pre.current_stack_cell_addresses.push(new_stack_cell_permission.addr());
                update current_stack_cell_elements      = pre.current_stack_cell_elements.push(StackCellContents::Elem(new_stack_cell_permission.value().elem));
                deposit all_stack_cell_address_permissions             += [new_stack_cell_permission.addr() => new_stack_cell_permission];
                add all_stack_cell_permissions_witnesses (union)= [new_stack_cell_permission.addr() => new_stack_cell_permission];

                birds_eye let next_operation_index       = pre.linearised_history.dom().len();
                add linearised_history                  += [next_operation_index => Operation::Push(new_stack_cell_permission.value().elem)];
            }
        }

        transition!{
            pop(new_head_stack_cell_permission: PointsTo<StackCell>, current_head_stack_cell_permission: PointsTo<StackCell>)
            {
                require(current_head_stack_cell_permission.addr() != pre.base_address);
                require(pre.current_stack_cell_addresses.len() > 1);

                require(pre.current_stack_cell_addresses.last() == current_head_stack_cell_permission.addr());
                require(current_head_stack_cell_permission.value().next == new_head_stack_cell_permission.addr());

                have all_stack_cell_permissions_witnesses >= [current_head_stack_cell_permission.addr() => current_head_stack_cell_permission];

                birds_eye let next_operation_index  = pre.linearised_history.dom().len();
                add linearised_history             += [next_operation_index => Operation::Pop(Some(current_head_stack_cell_permission.value().elem))];

                update popped_stack_cell_addresses = pre.popped_stack_cell_addresses.insert(pre.current_stack_cell_addresses.last());
                update current_stack_cell_addresses       = pre.current_stack_cell_addresses.drop_last();
                update current_stack_cell_elements      = pre.current_stack_cell_elements.drop_last();
            }
        }

        transition!{
            empty_stack_pop(base_stack_cell_permission: PointsTo<StackCell>)
            {
                require(base_stack_cell_permission.addr() == pre.base_address);
                require(pre.current_stack_cell_addresses.len() == 1);

                have all_stack_cell_permissions_witnesses >= [base_stack_cell_permission.addr() => base_stack_cell_permission];

                birds_eye let next_operation_index = pre.linearised_history.dom().len();
                add linearised_history += [next_operation_index => Operation::Pop(None)];
            }
        }

        property!{
            get_permission_reference(stack_cell_address: StackCellAddress, stack_cell_permission: PointsTo<StackCell>) {
                have all_stack_cell_permissions_witnesses >= [stack_cell_address => stack_cell_permission];
                guard all_stack_cell_address_permissions >= [stack_cell_address => stack_cell_permission];
            }
        }

        property!{
            have_witness_after_pop(stack_cell_address: StackCellAddress, stack_cell_permission: PointsTo<StackCell>) {
                require(stack_cell_address != pre.base_address);
                have all_stack_cell_permissions_witnesses >= [stack_cell_address => stack_cell_permission];
                assert(pre.all_stack_cell_addresses.contains(stack_cell_permission.value().next));
            }
        }

        property!{
            same_address_implies_same_permission(stack_cell_address_1: StackCellAddress, stack_cell_permission_1: PointsTo<StackCell>, stack_cell_address_2: StackCellAddress, stack_cell_permission_2: PointsTo<StackCell>) {
                require(stack_cell_address_1 == stack_cell_address_2);
                have all_stack_cell_permissions_witnesses >= [stack_cell_address_1 => stack_cell_permission_1];
                have all_stack_cell_permissions_witnesses >= [stack_cell_address_2 => stack_cell_permission_2];
                assert(stack_cell_permission_1 == stack_cell_permission_2);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, base_permission: PointsTo<StackCell>) {
            assert(post.current_stack_cell_addresses.first() == post.base_address);
            assert(post.current_stack_cell_addresses.to_set().union(post.popped_stack_cell_addresses) == post.all_stack_cell_addresses);
            assert(post.all_stack_cell_permissions_witnesses.index(post.base_address).is_uninit());

            reveal_with_fuel(replay_history, 2);
            assert(replay_history(0nat, post.linearised_history, Seq::empty()) == Seq::empty().push(StackCellContents::Base));
            assert(replay_history(0nat, post.linearised_history, Seq::empty()) == post.current_stack_cell_elements);
        }

        #[inductive(push)]
        fn push_inductive(pre: Self, post: Self, new_stack_cell_permission: PointsTo<StackCell>) {
            assert(pre.current_stack_cell_addresses == post.current_stack_cell_addresses.drop_last());
            assert(post.current_stack_cell_addresses.last() == (new_stack_cell_permission.addr()));
            assert(post.current_stack_cell_addresses.to_set().union(post.popped_stack_cell_addresses) == post.all_stack_cell_addresses);

            assert
                forall |i: nat| #![auto]
                    i < pre.linearised_history.len()
                implies
                    count_pushes_up_to(i, pre.linearised_history) == count_pushes_up_to(i, post.linearised_history) &&
                    count_successful_pops_up_to(i, pre.linearised_history) == count_successful_pops_up_to(i, post.linearised_history)
            by {
                stable_counts(i, pre.linearised_history, post.linearised_history);
            };

            assert(replay_history(0nat, post.linearised_history, Seq::empty()) == post.current_stack_cell_elements) by {
                replay_history_lemma(pre.linearised_history, post.linearised_history, Operation::Push(new_stack_cell_permission.value().elem));
            };
        }

        #[inductive(pop)]
        fn pop_inductive(pre: Self, post: Self, new_head_stack_cell_permission: PointsTo<StackCell>, current_head_stack_cell_permission: PointsTo<StackCell>) {
            assert(post.current_stack_cell_addresses.first() == post.base_address);
            assert(pre.current_stack_cell_addresses.drop_last() == post.current_stack_cell_addresses);

            pre.current_stack_cell_addresses.lemma_add_last_back();
            assert(post.current_stack_cell_addresses.to_set().union(post.popped_stack_cell_addresses) == post.all_stack_cell_addresses);

            assert
                forall |i: nat| #![auto]
                    i < pre.linearised_history.len()
                implies
                    count_pushes_up_to(i, pre.linearised_history) == count_pushes_up_to(i, post.linearised_history) &&
                    count_successful_pops_up_to(i, pre.linearised_history) == count_successful_pops_up_to(i, post.linearised_history)
            by {
                stable_counts(i, pre.linearised_history, post.linearised_history);
            };

            assert(replay_history(0nat, post.linearised_history, Seq::empty()) == post.current_stack_cell_elements) by {
                replay_history_lemma(pre.linearised_history, post.linearised_history, Operation::Pop(Some(current_head_stack_cell_permission.value().elem)));
            };
        }

        #[inductive(empty_stack_pop)]
        fn empty_stack_pop_inductive(pre: Self, post: Self, base_stack_cell_permission: PointsTo<StackCell>) {
            assert(replay_history(0nat, post.linearised_history, Seq::empty()) == post.current_stack_cell_elements) by {
                replay_history_lemma(pre.linearised_history, post.linearised_history, Operation::Pop(None));
            };
        }
    }
}

pub struct AtomicTokens {
    pub current_stack_cell_addresses: Tracked<machine::current_stack_cell_addresses>,
    pub current_stack_cell_elements: Tracked<machine::current_stack_cell_elements>,
    pub popped_stack_cell_addresses: Tracked<machine::popped_stack_cell_addresses>,
    pub all_stack_cell_permissions_witnesses: Tracked<
        Map<StackCellAddress, machine::all_stack_cell_permissions_witnesses>,
    >,
    pub all_stack_cell_addresses: Tracked<machine::all_stack_cell_addresses>,
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
            &&& atomic_tokens.current_stack_cell_addresses.instance_id() == instance.id()
            &&& atomic_tokens.popped_stack_cell_addresses.instance_id() == instance.id()
            &&& atomic_tokens.current_stack_cell_elements.instance_id() == instance.id()
            &&& atomic_tokens.all_stack_cell_addresses.instance_id() == instance.id()
            &&& (forall |addr: StackCellAddress| #![auto]
                    atomic_tokens.all_stack_cell_permissions_witnesses.dom().contains(addr) ==>
                        atomic_tokens.all_stack_cell_permissions_witnesses.index(addr).instance_id() == instance.id())

            // The base address is always present even before the first push:
            &&& atomic_tokens.all_stack_cell_permissions_witnesses.dom().contains(base_address)
            &&& atomic_tokens.all_stack_cell_addresses.value().contains(base_address)
            &&& atomic_tokens.current_stack_cell_addresses.value().contains(base_address)
            &&& atomic_tokens.current_stack_cell_addresses.value().first() == base_address

            // The top address is always tracked:
            &&& atomic_tokens.all_stack_cell_permissions_witnesses.dom().contains(head_stack_cell_address)
            &&& atomic_tokens.current_stack_cell_addresses.value().contains(head_stack_cell_address)
            &&& atomic_tokens.current_stack_cell_addresses.value().last() == head_stack_cell_address

            // If the head is the base, then our stack is empty (we only have the base):
            &&& head_stack_cell_address == base_address <==> atomic_tokens.current_stack_cell_addresses.value().len() == 1

            // There are no duplicate addresses in our stack
            &&& atomic_tokens.current_stack_cell_addresses.value().no_duplicates()

            // The current stack cell addresses is disjoint from the set of all popped stack cell addresses:
            // However, their union should be the domain of the set of all witnesses
            &&& atomic_tokens.current_stack_cell_addresses.value().to_set().disjoint(atomic_tokens.popped_stack_cell_addresses.value())
            &&& atomic_tokens.all_stack_cell_permissions_witnesses.dom() =~= atomic_tokens.current_stack_cell_addresses.value().to_set().union(atomic_tokens.popped_stack_cell_addresses.value())

            // The set of cell addresses should equal the domain of the witness tokens:
            &&& atomic_tokens.all_stack_cell_addresses.value() == atomic_tokens.all_stack_cell_permissions_witnesses.dom()

            // Every witness token's permission points to initialised memory except for the witness of the base address:
            &&& (forall |addr: StackCellAddress| #![auto]
                    atomic_tokens.all_stack_cell_permissions_witnesses.dom().contains(addr) ==> (
                        addr != base_address <==> atomic_tokens.all_stack_cell_permissions_witnesses.index(addr).value().is_init()
                    ))

            // Each individual map entry must agree internally at the address it is referencing (map structure):
            &&& (forall |addr: StackCellAddress| #![auto]
                    atomic_tokens.all_stack_cell_permissions_witnesses.dom().contains(addr) ==> (
                        atomic_tokens.all_stack_cell_permissions_witnesses.index(addr).key() == addr &&
                        atomic_tokens.all_stack_cell_permissions_witnesses.index(addr).value().addr() == addr
                    ))

            // There exists a witness for the next stack cell of every current stack cell (except base):
            &&& forall |addr: StackCellAddress, i: int|
                (
                    #[trigger] atomic_tokens.current_stack_cell_addresses.value().contains(addr) &&
                    0 < i < atomic_tokens.current_stack_cell_addresses.value().len() &&
                    #[trigger] atomic_tokens.current_stack_cell_addresses.value()[i] == addr
                ) ==>
                atomic_tokens.current_stack_cell_addresses.value()[i-1] == atomic_tokens.all_stack_cell_permissions_witnesses.index(addr).value().value().next
        }
    }
}

pub struct PoppedElemAndWitness {
    pub elem: Option<u32>,
    pub witness: Tracked<machine::linearised_history>,
}

impl TreiberStack {
    fn new() -> (treiber_stack: Self)
        ensures
            treiber_stack.wf(),
    {
        let (base, Tracked(base_perm)) = PPtr::<StackCell>::empty();
        let base_address = base.addr();

        let tracked all_stack_cell_address_permissions = Map::tracked_empty();
        proof {
            all_stack_cell_address_permissions.tracked_insert(base_address, base_perm);
        }

        let tracked (
            Tracked(instance),
            Tracked(linearised_history),
            Tracked(current_stack_cell_elements),
            Tracked(current_stack_cell_addresses),
            Tracked(popped_stack_cell_addresses),
            Tracked(all_stack_cell_addresses),
            Tracked(all_stack_cell_permissions_witnesses),
        ) = machine::Instance::initialize(base_perm, all_stack_cell_address_permissions);

        let tracked witness_tokens = all_stack_cell_permissions_witnesses.into_map();

        let atomic_tokens = AtomicTokens {
            current_stack_cell_elements: Tracked(current_stack_cell_elements),
            current_stack_cell_addresses: Tracked(current_stack_cell_addresses),
            popped_stack_cell_addresses: Tracked(popped_stack_cell_addresses),
            all_stack_cell_permissions_witnesses: Tracked(witness_tokens),
            all_stack_cell_addresses: Tracked(all_stack_cell_addresses),
        };

        assert(current_stack_cell_addresses.value().first() == base_address);

        let head_stack_cell_address = AtomicUsize::new(
            Ghost((base_address, Tracked(instance))),
            base_address,
            Tracked(atomic_tokens),
        );

        TreiberStack { base_address, head_stack_cell_address, instance: Tracked(instance) }
    }

    pub fn push(self: Arc<Self>, elem: u32) -> (linearised_push_witness: Tracked<
        machine::linearised_history,
    >)
        requires
            self.wf(),
        ensures
            self.wf(),
            linearised_push_witness.value() == Operation::Push(elem),
    {
        loop
            invariant
                self.wf(),
        {
            let new_stack_cell = StackCell { elem, next: self.head_stack_cell_address.load() };
            let (permission_guarded_new_stack_cell, Tracked(new_stack_cell_permission)) = PPtr::new(
                new_stack_cell,
            );

            let tracked linearised_push_witness = None;

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
                        if points_to_inv.all_stack_cell_permissions_witnesses@.dom().contains(new_stack_cell_permission.addr()) {
                            let tracked witness_token = points_to_inv.all_stack_cell_permissions_witnesses.tracked_borrow(new_stack_cell_permission.addr());
                            let tracked stack_cell_permission_reference = self.instance.get_permission_reference(witness_token.key(), witness_token.value(), &witness_token);
                            new_stack_cell_permission.is_distinct(stack_cell_permission_reference);
                            assert(false);
                        }

                        let ghost pre_current_stack_cell_addresses = Ghost(points_to_inv.current_stack_cell_addresses@.value());

                        let tracked tuple = self.instance.push(
                            new_stack_cell_permission,
                            &mut points_to_inv.current_stack_cell_elements,
                            &mut points_to_inv.current_stack_cell_addresses,
                            &mut points_to_inv.popped_stack_cell_addresses,
                            &mut points_to_inv.all_stack_cell_addresses,
                            new_stack_cell_permission
                        );

                        let tracked witness_token = tuple.2.get();
                        linearised_push_witness = Some(tuple.1.get());


                        assert(pre_current_stack_cell_addresses@ =~= pre_current_stack_cell_addresses.push(witness_token.value().addr()).drop_last());

                        // Insert the witness token for the new stack cell into our map:
                        points_to_inv.all_stack_cell_permissions_witnesses.tracked_insert(witness_token.key(), witness_token);

                        // The push correctly updated our view of the stack:
                        assert(points_to_inv.current_stack_cell_addresses.value().last() == witness_token.key());

                        // There exists a witness for the next stack cell of every current stack cell (except base):
                        assert(
                            forall |addr: StackCellAddress|
                                #[trigger] points_to_inv.current_stack_cell_addresses.value().contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < points_to_inv.current_stack_cell_addresses.value().len() - 1 && #[trigger] points_to_inv.current_stack_cell_addresses.value()[i] == addr) ==> (
                                            points_to_inv.current_stack_cell_addresses.value()[i-1] == points_to_inv.all_stack_cell_permissions_witnesses.index(addr).value().value().next
                                        )
                                )
                        ) by {
                            assert(
                                forall |addr: StackCellAddress|
                                    (#[trigger] points_to_inv.current_stack_cell_addresses.value().contains(addr) && addr != points_to_inv.current_stack_cell_addresses.value().last()) ==>
                                        points_to_inv.current_stack_cell_addresses.value().drop_last().contains(addr)
                            );

                            assert(
                                forall |addr: StackCellAddress|
                                    #[trigger] points_to_inv.current_stack_cell_addresses.value().drop_last().contains(addr) ==> (
                                        forall |i: int|
                                            (0 < i < points_to_inv.current_stack_cell_addresses.value().len() - 1 && #[trigger] points_to_inv.current_stack_cell_addresses.value()[i] == addr) ==> (
                                                points_to_inv.current_stack_cell_addresses.value()[i-1] == points_to_inv.all_stack_cell_permissions_witnesses.index(addr).value().value().next
                                            )
                                    )
                            );

                            assert(points_to_inv.current_stack_cell_addresses.value().last() == witness_token.key());
                            assert(points_to_inv.current_stack_cell_addresses.value().drop_last().last() == points_to_inv.all_stack_cell_permissions_witnesses.index(witness_token.key()).value().value().next);
                        };

                    }
                }
            );

            if let Ok(_) = push_result {
                return Tracked(linearised_push_witness.tracked_unwrap());
            }
        }
    }

    pub fn pop(self: Arc<Self>) -> (popped_elem_and_witness: PoppedElemAndWitness)
        requires
            self.wf(),
        ensures
            self.wf(),
            popped_elem_and_witness.witness.value() == Operation::Pop(popped_elem_and_witness.elem),
    {
        loop
            invariant
                self.wf(),
        {
            let tracked stack_head_witness;
            let tracked stack_cell_permission_reference;
            let tracked linearised_pop_witness = None;

            let mut head_stack_cell_address =
                atomic_with_ghost!{
                self.head_stack_cell_address => load();
                returning addr;

                ghost points_to_inv => {
                    stack_head_witness = points_to_inv.all_stack_cell_permissions_witnesses.tracked_remove(addr);
                    points_to_inv.all_stack_cell_permissions_witnesses.tracked_insert(addr, stack_head_witness.clone());
                    if addr == self.base_address {
                        linearised_pop_witness = Some(
                            self.instance.empty_stack_pop(
                                stack_head_witness.value(),
                                &mut points_to_inv.current_stack_cell_addresses,
                                &stack_head_witness
                            ).1.get()
                        );
                    }
                }
            };

            if head_stack_cell_address == self.base_address {
                return PoppedElemAndWitness {
                    elem: None,
                    witness: Tracked(linearised_pop_witness.tracked_unwrap()),
                };
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
                            &points_to_inv.all_stack_cell_addresses,
                            &stack_head_witness
                        );
                        let tracked new_stack_head_witness = points_to_inv.all_stack_cell_permissions_witnesses.tracked_borrow(new_stack_head_address);

                        // Assert that the witness token for the current stack head, has next == new_stack_head_address:
                        let tracked possible_second_old_stack_head_witness = points_to_inv.all_stack_cell_permissions_witnesses.tracked_borrow(current_stack_head_address);
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


                        let ghost pre_current_stack_cell_addresses = Ghost(points_to_inv.current_stack_cell_addresses@.value());

                        // This is a pointless assert - the fact is trivial but verus needs to discharge it
                        assert(
                            forall |addr: StackCellAddress|
                                #[trigger] pre_current_stack_cell_addresses.subrange(0, pre_current_stack_cell_addresses.len() - 1).contains(addr) ==>
                                    pre_current_stack_cell_addresses.contains(addr)
                        );




                        linearised_pop_witness = Some(
                            self.instance.pop(
                                new_stack_head_witness.value(),
                                stack_head_witness.value(),
                                &mut points_to_inv.current_stack_cell_elements,
                                &mut points_to_inv.current_stack_cell_addresses,
                                &mut points_to_inv.popped_stack_cell_addresses,
                                &stack_head_witness
                            ).1.get()
                        );

                        // Same here - this is a trivial fact, but we need to discharge it:
                        assert(pre_current_stack_cell_addresses@ =~= pre_current_stack_cell_addresses@.drop_last().push(stack_head_witness.value().addr()));
                        pre_current_stack_cell_addresses@.drop_last().lemma_push_to_set_commute(stack_head_witness.value().addr());
                    }
                }
            };

            if let Ok(new_stack_head_address) = new_stack_head_address_result {
                return PoppedElemAndWitness {
                    elem: Some(head_read.elem),
                    witness: Tracked(linearised_pop_witness.tracked_unwrap()),
                };
            }
        }
    }
}
} // verus!
