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
    map_lib::*,
    set_lib::*,
};

verus! {

global layout StackCell is size == 16;

pub enum Operation {
    Pop(Option<u32>),
    Push(u32),
    InitBase
}

impl Operation {
    pub fn get_push(&self) -> (value: u32) 
        requires
            match self {
                Operation::Push(_) => true,
                _ => false
            }
        ensures
            *self == Operation::Push(value)
    {
        match self {
            Operation::Push(i) => *i,
            _ => 0
        }
    }

    pub fn get_pop(&self) -> (value: Option<u32>) 
        requires
            match self {
                Operation::Pop(_) => true,
                _ => false
            }
        ensures
            *self == Operation::Pop(value)
    {
        match self {
            Operation::Pop(i) => *i,
            _ => None
        }
    }

    pub open spec fn is_empty_pop(&self) -> bool
    {
        match self {
                Operation::Pop(None) => true,
                _ => false
            }
    }
}

pub enum CellRepresentation {
    Elem(u32),
    Base
}

pub open spec fn replay_history(
    operation_index: nat,
    linearised_history: Map<nat, Operation>,
    current_stack: Seq<CellRepresentation>
) -> Seq<CellRepresentation>
decreases linearised_history.len() - operation_index
{
    if operation_index >= linearised_history.len() {
        current_stack
    } else {
        replay_history((operation_index + 1) as nat, linearised_history, apply_operation(linearised_history[operation_index], current_stack))
    }
}

pub open spec fn apply_operation(
    operation: Operation,
    current_stack: Seq<CellRepresentation>
) -> Seq<CellRepresentation>
{
    match operation {
        Operation::InitBase => current_stack.push(CellRepresentation::Base),
        Operation::Push(elem) => current_stack.push(CellRepresentation::Elem(elem)),
        Operation::Pop(Some(_)) => current_stack.drop_last(),
        Operation::Pop(None) => current_stack
    }
}

pub proof fn interchange_apply_and_replay(
    operation_index: nat,
    linearised_history: Map<nat, Operation>,
    current_stack: Seq<CellRepresentation>,
    appended_operation: Operation,
)
    requires
        forall |i: nat| #![auto]
            i < linearised_history.len() <==> linearised_history.dom().contains(i),
        operation_index <= linearised_history.len(),
        linearised_history.dom().finite()
    ensures
        replay_history(operation_index, linearised_history.insert(linearised_history.len(), appended_operation), current_stack) ==
            apply_operation(appended_operation, replay_history(operation_index, linearised_history, current_stack))
    decreases
        linearised_history.len() - operation_index
{
    let extended = linearised_history.insert(linearised_history.len(), appended_operation);

    if operation_index == linearised_history.len() {
        
        assert(replay_history(operation_index, extended, current_stack) == replay_history((operation_index + 1) as nat, extended, apply_operation(appended_operation, current_stack)));
    }
    else {
        interchange_apply_and_replay((operation_index + 1) as nat, linearised_history, apply_operation(linearised_history[operation_index], current_stack), appended_operation)
    }
}

pub proof fn replay_history_lemma(
    pre_linearised_history: Map<nat, Operation>,
    post_linearised_history: Map<nat, Operation>,
    operation: Operation,
)
requires
    forall |i: nat| #![auto]
        i < pre_linearised_history.len() <==> pre_linearised_history.dom().contains(i),
    pre_linearised_history.insert(pre_linearised_history.len(), operation) == post_linearised_history,
    operation != Operation::InitBase,
    pre_linearised_history.dom().finite()
ensures
    match operation {
        Operation::Push(elem) => replay_history(0nat, pre_linearised_history, Seq::empty()).push(CellRepresentation::Elem(elem)) == replay_history(0nat, post_linearised_history, Seq::empty()),
        Operation::Pop(Some(_)) => replay_history(0nat, pre_linearised_history, Seq::empty()).drop_last() == replay_history(0nat, post_linearised_history, Seq::empty()),
        Operation::Pop(None) => replay_history(0nat, pre_linearised_history, Seq::empty()) == replay_history(0nat, post_linearised_history, Seq::empty()),
        Operation::InitBase => true
    }
{
    interchange_apply_and_replay(0, pre_linearised_history, Seq::empty(), operation)
}

pub open spec fn count_pushes_up_to(
    operation_index: nat,
    linearised_history: Map<nat, Operation>,
) -> nat
decreases operation_index
{
    if operation_index == 0 {
        0nat
    } else {
        let possible_push = if let Operation::Push(_) = linearised_history[operation_index] { 1nat } else { 0nat };

        possible_push + count_pushes_up_to((operation_index - 1) as nat, linearised_history)
    }
}

pub open spec fn count_successful_pops_up_to(
    operation_index: nat,
    linearised_history: Map<nat, Operation>,
) -> nat
decreases operation_index
{
    if operation_index == 0 {
        0nat
    } else {
        let possible_push = if let Operation::Pop(Some(_)) = linearised_history[operation_index] { 1nat } else { 0nat };

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
    count_pushes_up_to(up_to_index, pre_linearised_history) == count_pushes_up_to(up_to_index, post_linearised_history),
    count_successful_pops_up_to(up_to_index, pre_linearised_history) == count_successful_pops_up_to(up_to_index, post_linearised_history)
decreases
    up_to_index
{
    if up_to_index == 0 {}
    else {
        stable_counts((up_to_index - 1) as nat, pre_linearised_history, post_linearised_history);
    }
}

tokenized_state_machine!{
    machine {
        fields {
            // Book Keeping

            #[sharding(constant)]
            pub base_address: usize,

            #[sharding(map)]
            pub linearised_history: Map<nat, Operation>,

            // Stack Representation

            #[sharding(variable)]
            pub current_stack_representation_addresses: Seq<usize>,

            #[sharding(variable)]
            pub current_stack_representation_elements: Seq<CellRepresentation>,

            #[sharding(variable)]
            pub popped_cells: Set<usize>,

            // Witnesses and Permissions

            #[sharding(variable)]
            pub all_cell_addresses: Set<usize>,

            #[sharding(persistent_map)]
            pub all_permission_witnesses: Map<usize, PointsTo<StackCell>>,

            #[sharding(storage_map)]
            pub all_address_permissions: Map<usize, PointsTo<StackCell>>,
        }

        #[invariant]
        pub fn complete_linearised_history_inv(&self) -> bool {
            &&& self.linearised_history.dom().finite()
            &&& forall |i: nat| i < self.linearised_history.dom().len() <==> 
                    self.linearised_history.dom().contains(i)
        }

        #[invariant]
        pub fn current_stack_representation_addresses_no_duplicates_inv(&self) -> bool {
            self.current_stack_representation_addresses.no_duplicates()
        }

        #[invariant]
        pub fn current_stack_representation_addresses_reflects_current_stack_representation_elements_inv(&self) -> bool {
            &&& self.current_stack_representation_addresses.len() == self.current_stack_representation_elements.len()
            &&& self.current_stack_representation_addresses.first() == self.base_address
            &&& self.current_stack_representation_elements[0] == CellRepresentation::Base
            &&& forall |i: int| #![auto]
                    0 < i < self.current_stack_representation_addresses.len() ==> (
                        self.all_permission_witnesses.dom().contains(self.current_stack_representation_addresses[i]) &&
                        CellRepresentation::Elem(self.all_permission_witnesses.index(self.current_stack_representation_addresses[i]).value().elem) == self.current_stack_representation_elements[i]
                    )
        }

        #[invariant]
        pub fn current_stack_representation_addresses_and_popped_cells_are_disjoint_inv(&self) -> bool {
            self.popped_cells.disjoint(self.current_stack_representation_addresses.to_set())
        }

        #[invariant]
        pub fn current_stack_representation_addresses_union_popped_cells_are_all_addresses_inv(&self) -> bool {
            self.current_stack_representation_addresses.to_set().union(self.popped_cells) == self.all_cell_addresses
        }

        #[invariant]
        pub fn current_stack_representation_addresses_contains_base_address_inv(&self) -> bool {
            &&& self.current_stack_representation_addresses.contains(self.base_address)
            &&& self.current_stack_representation_addresses.first() == self.base_address
        }

        #[invariant]
        pub fn current_stack_representation_addresses_point_to_next_correctly_inv(&self) -> bool {
            forall |addr: usize|
                #[trigger] self.current_stack_representation_addresses.contains(addr) ==> (
                    forall |i: int|
                        (0 < i < self.current_stack_representation_addresses.len() && #[trigger] self.current_stack_representation_addresses[i] == addr) ==> (
                            self.current_stack_representation_addresses[i-1] == self.all_permission_witnesses.index(addr).value().next
                        )
                )
        }

        #[invariant]
        pub fn adress_permissions_domain_is_all_addresses_inv(&self) -> bool {
            self.all_address_permissions.dom() == self.all_cell_addresses
        }

        #[invariant]
        pub fn witness_equals_storage_inv(&self) -> bool {
            self.all_permission_witnesses == self.all_address_permissions
        }

        #[invariant]
        pub fn base_witness_always_exists_inv(&self) -> bool {
            self.all_permission_witnesses.dom().contains(self.base_address)
        }

        #[invariant]
        pub fn correct_address_for_permissions_inv(&self) -> bool {
            forall |addr: usize| #![auto]
                self.all_address_permissions.dom().contains(addr) ==>
                    self.all_address_permissions.index(addr).addr() == addr
        }

        #[invariant]
        pub fn correct_address_for_witnesses_inv(&self) -> bool {
            forall |addr: usize| #![auto]
                self.all_permission_witnesses.dom().contains(addr) ==>
                    self.all_permission_witnesses.index(addr).addr() == addr
        }

        #[invariant]
        pub fn stack_has_valid_witnesses_one(&self) -> bool {
            forall |addr: usize| #![auto]
                (self.all_permission_witnesses.dom().contains(addr) && addr != self.base_address) ==>
                    self.all_permission_witnesses.dom().contains(self.all_permission_witnesses.index(addr).value().next)
        }

        #[invariant]
        pub fn stack_has_valid_witnesses_two(&self) -> bool {
            forall |addr: usize| #![auto]
                self.all_permission_witnesses.dom().contains(addr) ==> (
                    addr != self.base_address <==> self.all_permission_witnesses.index(addr).is_init()
                )       
        }

        #[invariant]
        pub fn empty_pop_implies_empty_stack(&self) -> bool {
            forall |i: nat| #![auto]
                (i < self.linearised_history.len() && self.linearised_history[i].is_empty_pop()) ==> (
                    count_pushes_up_to(i, self.linearised_history) == count_successful_pops_up_to(i, self.linearised_history)
                )
        }

        #[invariant]
        pub fn linearised_history_reflects_stack(&self) -> bool {
            replay_history(0nat, self.linearised_history, Seq::empty()) == self.current_stack_representation_elements
        }

        init!{
            initialize(base_permission: PointsTo<StackCell>)
            {
                require(base_permission.is_uninit());
                init base_address                  = base_permission.addr();
                init linearised_history            = Map::empty().insert(0, Operation::InitBase);
                init current_stack_representation_addresses  = Seq::empty().push(base_permission.addr());
                init current_stack_representation_elements = Seq::empty().push(CellRepresentation::Base);
                init popped_cells                  = Set::empty();
                init all_cell_addresses            = Set::empty().insert(base_permission.addr());
                init all_permission_witnesses      = Map::empty().insert(base_permission.addr(), base_permission);
                init all_address_permissions       = Map::empty().insert(base_permission.addr(), base_permission);
            }
        }

        transition!{
            push(points_to: PointsTo<StackCell>)
            {
                require(points_to.is_init());

                require(!pre.all_cell_addresses.contains(points_to.addr()));
                require(pre.all_cell_addresses.contains(points_to.value().next));

                require(pre.current_stack_representation_addresses.last() == points_to.value().next);

                update all_cell_addresses                = pre.all_cell_addresses.insert(points_to.addr());
                update current_stack_representation_addresses      = pre.current_stack_representation_addresses.push(points_to.addr());
                update current_stack_representation_elements      = pre.current_stack_representation_elements.push(CellRepresentation::Elem(points_to.value().elem));
                deposit all_address_permissions             += [points_to.addr() => points_to];
                add all_permission_witnesses (union)= [points_to.addr() => points_to];

                birds_eye let next_operation_index       = pre.linearised_history.dom().len();
                add linearised_history                  += [next_operation_index => Operation::Push(points_to.value().elem)];
            }
        }

        transition!{
            pop(second_top_points_to: PointsTo<StackCell>, top_points_to: PointsTo<StackCell>)
            {
                require(top_points_to.addr() != pre.base_address);
                require(pre.current_stack_representation_addresses.len() > 1);
                require(pre.current_stack_representation_addresses.last() == top_points_to.addr());
                require(top_points_to.value().next == second_top_points_to.addr());

                have all_permission_witnesses >= [top_points_to.addr() => top_points_to];

                birds_eye let next_operation_index  = pre.linearised_history.dom().len();
                add linearised_history             += [next_operation_index => Operation::Pop(Some(top_points_to.value().elem))];

                update popped_cells = pre.popped_cells.insert(pre.current_stack_representation_addresses.last());
                update current_stack_representation_addresses       = pre.current_stack_representation_addresses.drop_last();
                update current_stack_representation_elements      = pre.current_stack_representation_elements.drop_last();
            }
        }

        transition!{
            empty_stack_pop(points_to: PointsTo<StackCell>)
            {
                require(points_to.addr() == pre.base_address);
                require(pre.current_stack_representation_addresses.len() == 1);

                have all_permission_witnesses >= [points_to.addr() => points_to];

                birds_eye let next_operation_index  = pre.linearised_history.dom().len();
                add linearised_history             += [next_operation_index => Operation::Pop(None)];
            }
        }

        property!{
            get_permission_reference(addr: usize, permission: PointsTo<StackCell>) {
                have all_permission_witnesses >= [addr => permission];
                guard all_address_permissions          >= [addr => permission];
            }
        }

        property!{
            have_witness_after_pop(addr: usize, permission: PointsTo<StackCell>) {
                have all_permission_witnesses >= [addr => permission];
                require(addr != pre.base_address);
                assert(pre.all_cell_addresses.contains(permission.value().next));
            }
        }

        property!{
            same_address_implies_same_permission(addr1: usize, permission1: PointsTo<StackCell>, addr2: usize, permission2: PointsTo<StackCell>) {
                require(addr1 == addr2);
                have all_permission_witnesses >= [addr1 => permission1];
                have all_permission_witnesses >= [addr2 => permission2];
                assert(permission1 == permission2);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, base_permission: PointsTo<StackCell>) {
            assert(post.current_stack_representation_addresses.first() == post.base_address);
            assert(post.current_stack_representation_addresses.to_set().union(post.popped_cells) == post.all_cell_addresses);
            assert(post.all_permission_witnesses.index(post.base_address).is_uninit());

            reveal_with_fuel(replay_history, 2);
            assert(replay_history(0nat, post.linearised_history, Seq::empty()) == Seq::empty().push(CellRepresentation::Base));
            assert(replay_history(0nat, post.linearised_history, Seq::empty()) == post.current_stack_representation_elements);
        }

        #[inductive(push)]
        fn push_inductive(pre: Self, post: Self, points_to: PointsTo<StackCell>) {
            assert(post.current_stack_representation_addresses.first() == post.base_address);
            assert(post.current_stack_representation_addresses.contains(post.base_address));

            assert(
                forall |addr: usize|
                    #[trigger] pre.current_stack_representation_addresses.contains(addr) ==> (
                        forall |i: int|
                            (0 < i < pre.current_stack_representation_addresses.len() && #[trigger] pre.current_stack_representation_addresses[i] == addr) ==> (
                                pre.current_stack_representation_addresses[i-1] == pre.all_permission_witnesses.index(addr).value().next
                            )
                    )
            );

            assert(pre.current_stack_representation_addresses == post.current_stack_representation_addresses.subrange(0, post.current_stack_representation_addresses.len() - 1));

            assert(
                forall |addr: usize|
                    #[trigger] post.current_stack_representation_addresses.subrange(0, post.current_stack_representation_addresses.len() - 1).contains(addr) ==> (
                        forall |i: int|
                            (0 < i < post.current_stack_representation_addresses.subrange(0, post.current_stack_representation_addresses.len() - 1).len() && #[trigger] post.current_stack_representation_addresses.subrange(0, post.current_stack_representation_addresses.len() - 1)[i] == addr) ==> (
                                post.current_stack_representation_addresses.subrange(0, post.current_stack_representation_addresses.len() - 1)[i-1] == post.all_permission_witnesses.index(addr).value().next
                            )
                    )
            );

            assert(
                forall |addr: usize|
                    #[trigger] post.current_stack_representation_addresses.subrange(0, post.current_stack_representation_addresses.len() - 1).contains(addr) ==> (
                        forall |i: int|
                            (0 < i < post.current_stack_representation_addresses.len() && #[trigger] post.current_stack_representation_addresses[i] == addr) ==> (
                                post.current_stack_representation_addresses[i-1] == post.all_permission_witnesses.index(addr).value().next
                            )
                    )
            );

            assert(pre.current_stack_representation_addresses.push(points_to.addr()) == post.current_stack_representation_addresses);
            assert(post.all_permission_witnesses.contains_key(points_to.addr()));
                        
            assert(post.current_stack_representation_addresses.last() == (points_to.addr()));
            assert(post.current_stack_representation_addresses.contains(points_to.addr()));

            assert(
                forall |addr: usize|
                    (#[trigger] post.current_stack_representation_addresses.contains(addr) && addr != post.current_stack_representation_addresses.last()) ==>
                        (post.current_stack_representation_addresses.subrange(0, post.current_stack_representation_addresses.len() - 1).contains(addr))
            );


            assert(pre.current_stack_representation_addresses.to_set().union(pre.popped_cells) == pre.all_cell_addresses);
            assert(post.current_stack_representation_addresses.to_set().union(post.popped_cells) == post.all_cell_addresses);

            assert
                forall |i: nat| #![auto] 
                    i < pre.linearised_history.len()
                implies
                    count_pushes_up_to(i, pre.linearised_history) == count_pushes_up_to(i, post.linearised_history) &&
                    count_successful_pops_up_to(i, pre.linearised_history) == count_successful_pops_up_to(i, post.linearised_history)
            by {
                stable_counts(i, pre.linearised_history, post.linearised_history);
            };

            assert(pre.linearised_history.insert(pre.linearised_history.len(), Operation::Push(points_to.value().elem)) == post.linearised_history);

            assert(replay_history(0nat, post.linearised_history, Seq::empty()) == post.current_stack_representation_elements) by {
                replay_history_lemma(pre.linearised_history, post.linearised_history, Operation::Push(points_to.value().elem));
            };
        }

        #[inductive(pop)]
        fn pop_inductive(pre: Self, post: Self, second_top_points_to: PointsTo<StackCell>, top_points_to: PointsTo<StackCell>) {
            assert(pre.current_stack_representation_addresses.first() == post.base_address);
            assert(post.current_stack_representation_addresses.first() == post.base_address);

            assert(
                forall |addr: usize|
                    #[trigger] pre.current_stack_representation_addresses.contains(addr) ==> (
                        forall |i: int|
                            (0 < i < pre.current_stack_representation_addresses.drop_last().len() && #[trigger] pre.current_stack_representation_addresses.drop_last()[i] == addr) ==> (
                                pre.current_stack_representation_addresses.drop_last()[i-1] == pre.all_permission_witnesses.index(addr).value().next
                            )
                    )
            );

            assert(pre.current_stack_representation_addresses.drop_last() == post.current_stack_representation_addresses);
            assert(
                forall |addr: usize|
                    #[trigger] pre.current_stack_representation_addresses.drop_last().contains(addr) ==>
                        pre.current_stack_representation_addresses.contains(addr)
            );

            assert(pre.all_cell_addresses == post.all_cell_addresses);
            assert(pre.current_stack_representation_addresses.to_set().union(pre.popped_cells) == pre.all_cell_addresses);

            assert(post.current_stack_representation_addresses == pre.current_stack_representation_addresses.drop_last());
            assert(post.popped_cells == pre.popped_cells.insert(pre.current_stack_representation_addresses.last()));

            pre.current_stack_representation_addresses.lemma_add_last_back();

            assert(post.current_stack_representation_addresses.to_set().union(post.popped_cells) == post.all_cell_addresses);

            assert
                forall |i: nat| #![auto] 
                    i < pre.linearised_history.len()
                implies
                    count_pushes_up_to(i, pre.linearised_history) == count_pushes_up_to(i, post.linearised_history) &&
                    count_successful_pops_up_to(i, pre.linearised_history) == count_successful_pops_up_to(i, post.linearised_history)
            by {
                stable_counts(i, pre.linearised_history, post.linearised_history);
            };


            assert(pre.linearised_history.insert(pre.linearised_history.len(), Operation::Pop(Some(top_points_to.value().elem))) == post.linearised_history);

            assert(replay_history(0nat, post.linearised_history, Seq::empty()) == post.current_stack_representation_elements) by {
                replay_history_lemma(pre.linearised_history, post.linearised_history, Operation::Pop(Some(top_points_to.value().elem)));
            };
        }

        #[inductive(empty_stack_pop)]
        fn empty_stack_pop_inductive(pre: Self, post: Self, points_to: PointsTo<StackCell>) {
            assert(replay_history(0nat, pre.linearised_history, Seq::empty()) == pre.current_stack_representation_elements);
            assert(pre.linearised_history.insert(pre.linearised_history.len(), Operation::Pop(None)) == post.linearised_history);

            assert(replay_history(0nat, post.linearised_history, Seq::empty()) == post.current_stack_representation_elements) by {
                replay_history_lemma(pre.linearised_history, post.linearised_history, Operation::Pop(None));
            };
            // pre_linearised_history.insert(pre_linearised_history.len(), operation) == post_linearised_history
        }
    }
}

pub struct AtomicTokens {
    pub current_stack_representation_addresses: Tracked<machine::current_stack_representation_addresses>,
    pub current_stack_representation_elements: Tracked<machine::current_stack_representation_elements>,
    pub popped_cells: Tracked<machine::popped_cells>,
    pub cell_witnesses: Tracked<Map<usize, machine::all_permission_witnesses>>,
    pub all_cell_addresses: Tracked<machine::all_cell_addresses>,
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
            &&& atomic_tokens.cell_witnesses.dom().contains(base_address)
            &&& atomic_tokens.all_cell_addresses.value().contains(base_address)
            &&& atomic_tokens.current_stack_representation_addresses.value().contains(base_address)
            &&& atomic_tokens.current_stack_representation_addresses.value().first() == base_address

            // All tokens must come from the correct TSM:
            &&& atomic_tokens.current_stack_representation_addresses.instance_id() == instance.id()
            &&& atomic_tokens.popped_cells.instance_id() == instance.id()
            &&& atomic_tokens.current_stack_representation_elements.instance_id() == instance.id()
            &&& atomic_tokens.all_cell_addresses.instance_id() == instance.id()
            &&& (forall |address: usize| #![auto]
                    atomic_tokens.cell_witnesses.dom().contains(address) ==>
                        atomic_tokens.cell_witnesses.index(address).instance_id() == instance.id())
            
            // The top address is always tracked:
            &&& atomic_tokens.cell_witnesses.dom().contains(top_address)
            &&& atomic_tokens.current_stack_representation_addresses.value().contains(top_address)
            &&& atomic_tokens.current_stack_representation_addresses.value().last() == top_address

            // The set of cell addresses should equal the domain of the witness tokens:
            &&&  atomic_tokens.all_cell_addresses.value() == atomic_tokens.cell_witnesses.dom()

            // Every witness token's permission points to initialised memory except for the witness of the base address:
            &&& (forall |address: usize| #![auto]
                    atomic_tokens.cell_witnesses.dom().contains(address) ==> (
                        address != base_address <==> atomic_tokens.cell_witnesses.index(address).value().is_init()
                    ))

            // Each individual map entry must agree internally at the address it is referencing
            &&& (forall |address: usize| #![auto]
                    atomic_tokens.cell_witnesses.dom().contains(address) ==> (
                        atomic_tokens.cell_witnesses.index(address).key() == address &&
                        atomic_tokens.cell_witnesses.index(address).value().addr() == address
                    ))

            // TESTING:
            &&& atomic_tokens.current_stack_representation_addresses.value().to_set().subset_of(atomic_tokens.all_cell_addresses.value())
            &&& atomic_tokens.current_stack_representation_addresses.value().no_duplicates()
            &&& forall |addr: usize|
                    #[trigger] atomic_tokens.current_stack_representation_addresses.value().contains(addr) ==> (
                        forall |i: int|
                            (0 < i < atomic_tokens.current_stack_representation_addresses.value().len() && #[trigger] atomic_tokens.current_stack_representation_addresses.value()[i] == addr) ==> (
                                atomic_tokens.current_stack_representation_addresses.value()[i-1] == atomic_tokens.cell_witnesses.index(addr).value().value().next
                            )
                    )
            &&& top_address == base_address <==> atomic_tokens.current_stack_representation_addresses.value().len() == 1
            // &&& atomic_tokens.current_stack_representation_addresses.value().len() == 1 ==> atomic_tokens.current_stack_representation_addresses.value().first() == atomic_tokens.current_stack_representation_addresses.value().last()
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

        let tracked all_address_permissions = Map::tracked_empty();
        proof {
            all_address_permissions.tracked_insert(base_address, base_perm);
        }

        let tracked (
            Tracked(instance), 
            Tracked(linearised_history),
            Tracked(current_stack_representation_addresses),
            Tracked(current_stack_representation_elements),
            Tracked(popped_cells),
            Tracked(all_cell_addresses),
            Tracked(all_permission_witnesses),
        ) = machine::Instance::initialize(base_perm, all_address_permissions);

        let tracked witness_tokens = all_permission_witnesses.into_map();

        let atomic_tokens = AtomicTokens {
            current_stack_representation_addresses: Tracked(current_stack_representation_addresses),
            current_stack_representation_elements: Tracked(current_stack_representation_elements),
            popped_cells: Tracked(popped_cells),
            cell_witnesses: Tracked(witness_tokens),
            all_cell_addresses: Tracked(all_cell_addresses),
        };

        assert(current_stack_representation_addresses.value().first() == base_address);

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
                update prev -> next;
                returning previous_head_result;

                ghost points_to_inv => {
                    if let Ok(previous_head) = previous_head_result {

                        if points_to_inv.cell_witnesses@.dom().contains(stack_cell_perm.addr()) {
                            let tracked witness_token = points_to_inv.cell_witnesses.tracked_borrow(stack_cell_perm.addr()); 
                            let tracked token_ref = self.instance.get_permission_reference(witness_token.key(), witness_token.value(), &witness_token);
                            stack_cell_perm.is_distinct(token_ref);
                            assert(false);
                        }

                        assert(points_to_inv.current_stack_representation_addresses.value().first() == self.base_address);

                        assert(
                            forall |addr: usize|
                                #[trigger] points_to_inv.current_stack_representation_addresses.value().contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < points_to_inv.current_stack_representation_addresses.value().len() && #[trigger] points_to_inv.current_stack_representation_addresses.value()[i] == addr) ==> (
                                            points_to_inv.current_stack_representation_addresses.value()[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        let ghost pre_current_stack_representation_addresses = Ghost(points_to_inv.current_stack_representation_addresses@.value());

                        let tracked tuple = self.instance.push(stack_cell_perm, &mut points_to_inv.current_stack_representation_addresses, &mut points_to_inv.current_stack_representation_elements, &mut points_to_inv.all_cell_addresses, stack_cell_perm);

                        assert(points_to_inv.current_stack_representation_addresses.value().first() == self.instance.base_address());
                        assert(points_to_inv.current_stack_representation_addresses.value().last() == next);


                        let tracked witness_token = tuple.2.get();
                        push_witness = Some(tuple.1.get());


                        assert(points_to_inv.current_stack_representation_addresses.value() == pre_current_stack_representation_addresses.push(witness_token.value().addr()));
                        assert(points_to_inv.current_stack_representation_addresses.value().drop_last() == pre_current_stack_representation_addresses.push(witness_token.value().addr()).drop_last());
                        assert(pre_current_stack_representation_addresses@ =~= pre_current_stack_representation_addresses.push(witness_token.value().addr()).drop_last());
                        assert(points_to_inv.current_stack_representation_addresses.value().drop_last() == pre_current_stack_representation_addresses);

                        assert(
                            forall |addr: usize|
                                #[trigger] pre_current_stack_representation_addresses.contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < pre_current_stack_representation_addresses.len() && #[trigger] pre_current_stack_representation_addresses[i] == addr) ==> (
                                            pre_current_stack_representation_addresses[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        assert(points_to_inv.current_stack_representation_addresses.value().last() == witness_token.key());
                        assert(points_to_inv.current_stack_representation_addresses.value()[points_to_inv.current_stack_representation_addresses.value().len() - 2] == witness_token.value().value().next);

                        points_to_inv.cell_witnesses.tracked_insert(witness_token.key(), witness_token);

                        assert(points_to_inv.current_stack_representation_addresses.value() == pre_current_stack_representation_addresses.push(witness_token.value().addr()));

                        assert(
                            forall |addr: usize|
                                #[trigger] pre_current_stack_representation_addresses.contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < pre_current_stack_representation_addresses.len() && #[trigger] pre_current_stack_representation_addresses[i] == addr) ==> (
                                            pre_current_stack_representation_addresses[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        assert(
                            forall |addr: usize|
                                #[trigger] pre_current_stack_representation_addresses.contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < pre_current_stack_representation_addresses.len() - 1 && #[trigger] pre_current_stack_representation_addresses[i] == addr) ==> (
                                            pre_current_stack_representation_addresses[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        assert(
                            forall |addr: usize|
                                #[trigger] points_to_inv.current_stack_representation_addresses.value().subrange(0, points_to_inv.current_stack_representation_addresses.value().len() - 1).contains(addr) ==>
                                    pre_current_stack_representation_addresses.contains(addr)
                        );

                        assert(pre_current_stack_representation_addresses.push(witness_token.value().addr()) == points_to_inv.current_stack_representation_addresses.value());
                        assert(pre_current_stack_representation_addresses == points_to_inv.current_stack_representation_addresses.value().subrange(0, points_to_inv.current_stack_representation_addresses.value().len() - 1));

                        assert(
                            forall |addr: usize|
                                #[trigger] points_to_inv.current_stack_representation_addresses.value().subrange(0, points_to_inv.current_stack_representation_addresses.value().len() - 1).contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < points_to_inv.current_stack_representation_addresses.value().subrange(0, points_to_inv.current_stack_representation_addresses.value().len() - 1).len() - 1 && #[trigger] points_to_inv.current_stack_representation_addresses.value().subrange(0, pre_current_stack_representation_addresses.len() - 1)[i] == addr) ==> (
                                            points_to_inv.current_stack_representation_addresses.value().subrange(0, points_to_inv.current_stack_representation_addresses.value().len() - 1)[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        assert(points_to_inv.cell_witnesses.contains_key(witness_token.key()));
                        // assert(points_to_inv.current_stack_representation_addresses.value().subrange(0, pre_current_stack_representation_addresses.len() - 1).push(witness_token.key()) =~= points_to_inv.current_stack_representation_addresses.value());

                        assert(points_to_inv.current_stack_representation_addresses.value().last() == witness_token.key());
                        assert(points_to_inv.current_stack_representation_addresses.value().contains(witness_token.key()));

                        assert(
                            forall |i: int|
                                (0 < i < points_to_inv.current_stack_representation_addresses.value().len() - 1 && #[trigger] points_to_inv.current_stack_representation_addresses.value()[i] == witness_token.key()) ==> (
                                    points_to_inv.current_stack_representation_addresses.value()[i-1] == points_to_inv.cell_witnesses.index(witness_token.key()).value().value().next
                                )
                        );

                        assert(
                            forall |addr: usize|
                                #[trigger] points_to_inv.current_stack_representation_addresses.value().subrange(0, points_to_inv.current_stack_representation_addresses.value().len() - 1).contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < points_to_inv.current_stack_representation_addresses.value().len() - 1 && #[trigger] points_to_inv.current_stack_representation_addresses.value()[i] == addr) ==> (
                                            points_to_inv.current_stack_representation_addresses.value()[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        assert(
                            forall |addr: usize|
                                (#[trigger] points_to_inv.current_stack_representation_addresses.value().contains(addr) && addr != points_to_inv.current_stack_representation_addresses.value().last()) ==>
                                    (points_to_inv.current_stack_representation_addresses.value().subrange(0, points_to_inv.current_stack_representation_addresses.value().len() - 1).contains(addr))
                        );

                        // assert(points_to_inv.current_stack_representation_addresses.value().len() > 1);

                        // assert(points_to_inv.current_stack_representation_addresses.value()[points_to_inv.current_stack_representation_addresses.value().len() - 1] == witness_token.key());
                        // assert(points_to_inv.current_stack_representation_addresses.value()[points_to_inv.current_stack_representation_addresses.value().len() - 2] == points_to_inv.cell_witnesses.index(witness_token.key()).value().value().next);

                        // // assert(pre_current_stack_representation_addresses@.drop_last() == post_current_stack_representation_addresses.value());

                        // assert(points_to_inv.current_stack_representation_addresses.value().last() == witness_token.key());

                        // assert(points_to_inv.current_stack_representation_addresses.value().first() == self.base_address);

                        // assert(
                        //     forall |addr: usize|
                        //         #[trigger] points_to_inv.current_stack_representation_addresses.value().contains(addr) ==> (
                        //             forall |i: int|
                        //                 (0 < i < points_to_inv.current_stack_representation_addresses.value().len() && #[trigger] points_to_inv.current_stack_representation_addresses.value()[i] == addr) ==> (
                        //                     points_to_inv.current_stack_representation_addresses.value()[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                        //                 )
                        //         )
                        // );




                        // assert(
                        //     forall |addr: usize|
                        //         #[trigger] points_to_inv.current_stack_representation_addresses.value().contains(addr) ==> (
                        //             forall |i: int|
                        //                 (0 < i < points_to_inv.current_stack_representation_addresses.value().len() && #[trigger] points_to_inv.current_stack_representation_addresses.value()[i] == addr) ==> (
                        //                     points_to_inv.current_stack_representation_addresses.value()[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                        //                 )
                        //         )
                        // );
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
            let tracked head_witness_token;
            let tracked token_ref;
            let tracked pop_witness = None;

            let mut head_stack_cell_address = atomic_with_ghost!{
                self.top_address => load();
                returning addr;

                ghost points_to_inv => {
                    head_witness_token = points_to_inv.cell_witnesses.tracked_remove(addr);
                    points_to_inv.cell_witnesses.tracked_insert(addr, head_witness_token.clone());
                    if addr == self.base_address {
                        pop_witness = Some(self.instance.empty_stack_pop(head_witness_token.value(), &mut points_to_inv.current_stack_representation_addresses, &head_witness_token).1.get());
                    }
                }
            };

            if head_stack_cell_address == self.base_address {
                return PoppedElemAndWitness { elem: None, witness: Tracked(pop_witness.tracked_unwrap()) };
            }

            proof {
                token_ref = self.instance.get_permission_reference(head_witness_token.key(), head_witness_token.value(), &head_witness_token);
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
                        assert(head_witness_token.value().value().next == new_head_address);

                        self.instance.have_witness_after_pop(head_witness_token.key(), head_witness_token.value(), &points_to_inv.all_cell_addresses, &head_witness_token);

                        let tracked new_top_witness = points_to_inv.cell_witnesses.tracked_borrow(new_head_address); 

                        assert(
                            forall |addr: usize|
                                #[trigger] points_to_inv.current_stack_representation_addresses.value().contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < points_to_inv.current_stack_representation_addresses.value().len() && #[trigger] points_to_inv.current_stack_representation_addresses.value()[i] == addr) ==> (
                                            points_to_inv.current_stack_representation_addresses.value()[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        assert(points_to_inv.current_stack_representation_addresses.value().last() == current_head_address);
                        assert(head_witness_token.value().addr() == current_head_address);
                        assert(head_witness_token.value().value().next == new_top_witness.value().addr());

                        assert(points_to_inv.current_stack_representation_addresses.value()[points_to_inv.current_stack_representation_addresses.value().len() - 1] == current_head_address);
                        assert(points_to_inv.current_stack_representation_addresses.value()[points_to_inv.current_stack_representation_addresses.value().len() - 2] == points_to_inv.cell_witnesses.index(current_head_address).value().value().next);

                        assert(head_witness_token.value().addr() == current_head_address);
                        assert(head_witness_token.key() == current_head_address);
                        assert(points_to_inv.cell_witnesses.dom().contains(current_head_address));

                        // Proving that the head_witness_token is still in the map:
                        let tracked possible_other_perm = points_to_inv.cell_witnesses.tracked_borrow(current_head_address);

                        self.instance.same_address_implies_same_permission(head_witness_token.key(), head_witness_token.value(), possible_other_perm.key(), possible_other_perm.value(), &head_witness_token, &possible_other_perm);
                        assert(possible_other_perm.value() == head_witness_token.value());

                        assert(head_witness_token.value().value().next == new_head_address);

                        assert(
                            forall |addr: usize|
                                #[trigger] points_to_inv.current_stack_representation_addresses.value().contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < points_to_inv.current_stack_representation_addresses.value().len() && #[trigger] points_to_inv.current_stack_representation_addresses.value()[i] == addr) ==> (
                                            points_to_inv.current_stack_representation_addresses.value()[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        let ghost pre_current_stack_representation_addresses = Ghost(points_to_inv.current_stack_representation_addresses@.value());

                        assert(
                            forall |addr: usize|
                                #[trigger] pre_current_stack_representation_addresses.contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < pre_current_stack_representation_addresses.len() && #[trigger] pre_current_stack_representation_addresses[i] == addr) ==> (
                                            pre_current_stack_representation_addresses[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        // assert(
                        //     forall |addr: usize|
                        //         #[trigger] pre_current_stack_representation_addresses.contains(addr) ==> (
                        //             forall |i: int|
                        //                 (0 < i < pre_current_stack_representation_addresses.len() - 1 && #[trigger] pre_current_stack_representation_addresses[i] == addr) ==> (
                        //                     pre_current_stack_representation_addresses[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                        //                 )
                        //         )
                        // );

                        let ghost post_current_stack_representation_addresses = Ghost(points_to_inv.current_stack_representation_addresses@.value().drop_last());
                        assert(post_current_stack_representation_addresses == pre_current_stack_representation_addresses.subrange(0, pre_current_stack_representation_addresses.len() - 1));

                        assert(
                            forall |addr: usize|
                                #[trigger] pre_current_stack_representation_addresses.contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < pre_current_stack_representation_addresses.subrange(0, pre_current_stack_representation_addresses.len() - 1).len() && #[trigger] pre_current_stack_representation_addresses.subrange(0, pre_current_stack_representation_addresses.len() - 1)[i] == addr) ==> (
                                            pre_current_stack_representation_addresses.subrange(0, pre_current_stack_representation_addresses.len() - 1)[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        assert(
                            forall |addr: usize|
                                #[trigger] pre_current_stack_representation_addresses.subrange(0, pre_current_stack_representation_addresses.len() - 1).contains(addr) ==>
                                pre_current_stack_representation_addresses.contains(addr)
                            );

                        assert(
                            forall |addr: usize|
                                #[trigger] pre_current_stack_representation_addresses.subrange(0, pre_current_stack_representation_addresses.len() - 1).contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < pre_current_stack_representation_addresses.subrange(0, pre_current_stack_representation_addresses.len() - 1).len() && #[trigger] pre_current_stack_representation_addresses.subrange(0, pre_current_stack_representation_addresses.len() - 1)[i] == addr) ==> (
                                            pre_current_stack_representation_addresses.subrange(0, pre_current_stack_representation_addresses.len() - 1)[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );

                        pop_witness = Some(self.instance.pop(new_top_witness.value(), head_witness_token.value(), &mut points_to_inv.current_stack_representation_addresses, &mut points_to_inv.current_stack_representation_elements, &mut points_to_inv.popped_cells, &head_witness_token).1.get());
                        
                        let ghost post_current_stack_representation_addresses = Ghost(points_to_inv.current_stack_representation_addresses);

                        assert(pre_current_stack_representation_addresses@.drop_last() == post_current_stack_representation_addresses.value());

                        assert(points_to_inv.current_stack_representation_addresses.value().last() == new_head_address);

                        assert(points_to_inv.current_stack_representation_addresses.value().first() == self.base_address);

                        assert(
                            forall |addr: usize|
                                #[trigger] points_to_inv.current_stack_representation_addresses.value().contains(addr) ==> (
                                    forall |i: int|
                                        (0 < i < points_to_inv.current_stack_representation_addresses.value().len() && #[trigger] points_to_inv.current_stack_representation_addresses.value()[i] == addr) ==> (
                                            points_to_inv.current_stack_representation_addresses.value()[i-1] == points_to_inv.cell_witnesses.index(addr).value().value().next
                                        )
                                )
                        );
                        
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