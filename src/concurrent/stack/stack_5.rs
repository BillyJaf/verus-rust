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

pub enum Operation {
    Pop(u32),
    Push(u32),
    CreateBase
}

pub struct PermAndNext {
    pub points_to: PointsTo<StackCell>,
    pub next_addr: Option<usize>,
}

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(constant)]
            pub base_address: usize,

            #[sharding(variable)]
            pub cell_addresses: Set<usize>,

            #[sharding(persistent_map)]
            pub address_permissions_witnesses: Map<usize, PermAndNext>,

            #[sharding(storage_map)]
            pub address_permissions: Map<usize, PermAndNext>,

            #[sharding(persistent_map)]
            pub linearised_history: Map<int, Operation>,
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
        pub fn no_next_address_only_on_base_inv(&self) -> bool {
            forall |addr: usize| #![auto]
                self.address_permissions.dom().contains(addr) ==> (
                    self.address_permissions.index(addr).next_addr.is_none() <==> addr == self.base_address
                )
        }

        #[invariant]
        pub fn correct_address_for_permissions_inv(&self) -> bool {
            forall |addr: usize| #![auto]
                self.address_permissions.dom().contains(addr) ==> (
                    self.address_permissions.index(addr).points_to.addr() == addr &&
                    (self.address_permissions.index(addr).next_addr.is_some() ==> self.address_permissions.dom().contains(self.address_permissions.index(addr).next_addr.unwrap()))
                )
        }

        #[invariant]
        pub fn correct_address_for_witnesses_inv(&self) -> bool {
            forall |addr: usize| #![auto]
                self.address_permissions_witnesses.dom().contains(addr) ==>
                    self.address_permissions_witnesses.index(addr).points_to.addr() == addr
        }

        init!{
            initialize(base_address: usize)
            {
                init base_address = base_address;
                init cell_addresses = Set::empty();
                init address_permissions_witnesses = Map::empty();
                init address_permissions = Map::empty();
                init linearised_history = Map::empty();
            }
        }

        transition!{
            create_base(addr: usize, perm_and_next: PermAndNext)
            {
                require(perm_and_next.next_addr == None::<usize>);
                require(perm_and_next.points_to.addr() == addr);
                require(addr == pre.base_address);
                require(pre.cell_addresses.is_empty());

                update cell_addresses = pre.cell_addresses.insert(addr);
                deposit address_permissions += [addr =>perm_and_next ];
                add address_permissions_witnesses (union)= [addr => perm_and_next];
            }
        }

        transition!{
            push(addr: usize, points_to: PointsTo<StackCell>, next_addr: usize)
            {
                require(addr == points_to.addr());
                require(!pre.cell_addresses.contains(addr));

                have address_permissions_witnesses >= [next_addr => let _];
                update cell_addresses = pre.cell_addresses.insert(addr);
                deposit address_permissions += [addr => PermAndNext{ points_to, next_addr: Some(next_addr) }];
                add address_permissions_witnesses (union)= [addr => PermAndNext{ points_to, next_addr: Some(next_addr) }];
            }
        }

        // transition!{
        //     pop()
        //     {
        //         update head_address = pre.head_address.drop_last();
        //     }
        // }

        property!{
            get_perm_and_next_reference(addr: usize, perm_and_next: PermAndNext) {
                have address_permissions_witnesses >= [addr => perm_and_next];
                guard address_permissions >= [addr => perm_and_next];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, base_address: usize) {}

        #[inductive(create_base)]
        fn create_base_inductive(pre: Self, post: Self, addr: usize, perm_and_next: PermAndNext) { }

        #[inductive(push)]
        fn push_inductive(pre: Self, post: Self, addr: usize, points_to: PointsTo<StackCell>, next_addr: usize) {
            assume(false);
        }

        // #[inductive(pop)]
        // fn pop_inductive(pre: Self, post: Self) { }
    }
}

#[derive(Copy, Clone)]
pub struct StackCell {
    pub elem: u32,
    pub next: usize,
}

struct_with_invariants!{
    pub struct TreiberStack {
        pub base_address: usize,
        pub head: AtomicUsize<_, Map<usize, machine::address_permissions_witnesses>, _>,
        pub instance: Tracked<machine::Instance>,
    }

    pub open spec fn wf(self) -> bool {
        invariant on head with (base_address, instance) is (addr: usize, address_permissions_witnesses_map: Map<usize, machine::address_permissions_witnesses>) {
            (
                base_address == instance.base_address()
            ) &&
            (
                forall |map_key: usize| #![auto]
                    address_permissions_witnesses_map.dom().contains(map_key) ==>
                        address_permissions_witnesses_map.index(map_key).instance_id() == instance.id()
            ) &&
            (
                address_permissions_witnesses_map.dom().contains(addr)
            ) &&
            (
                forall |map_key: usize| #![auto]
                    (address_permissions_witnesses_map.dom().contains(map_key) && map_key != instance.base_address()) ==>
                        address_permissions_witnesses_map.index(map_key).value().points_to.is_init()
            ) &&
            (
                forall |map_key: usize| #![auto]
                    address_permissions_witnesses_map.dom().contains(map_key) ==>
                        address_permissions_witnesses_map.index(map_key).key() == map_key
            ) &&
            (
                forall |map_key: usize| #![auto]
                    (address_permissions_witnesses_map.dom().contains(map_key)) ==>
                        address_permissions_witnesses_map.index(map_key).value().points_to.addr() == map_key
            ) &&
            (
                forall |map_key: usize| #![auto]
                    (
                        address_permissions_witnesses_map.dom().contains(map_key) &&
                        address_permissions_witnesses_map.index(map_key).value().next_addr.is_some()
                    ) ==>
                    address_permissions_witnesses_map.dom().contains(address_permissions_witnesses_map.index(map_key).value().next_addr.unwrap())
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
            Tracked(cell_addresses),
            Tracked(address_permissions_witnesses),
            Tracked(linearised_history)
        ) = machine::Instance::initialize(base_address, Map::tracked_empty());

        let tracked witness_tokens = Map::tracked_empty();

        proof {
            let tracked perm_and_next = PermAndNext { points_to: base_perm, next_addr: None };
            let tracked base_witness = instance.create_base(base_address, perm_and_next, &mut cell_addresses, perm_and_next);
            witness_tokens.tracked_insert(base_address, base_witness);
        }

        let head = AtomicUsize::new(Ghost((base_address, Tracked(instance))), base_address, Tracked(witness_tokens));

        TreiberStack { base_address, head, instance: Tracked(instance) }
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
                    witness_token = points_to_inv.tracked_remove(addr);
                    points_to_inv.tracked_insert(addr, witness_token);

                }
            };

            if head_stack_cell_address == self.base_address {
                return popped_value;
            }

            proof {
                token_ref = self.instance.get_perm_and_next_reference(witness_token.key(), witness_token.value(), &witness_token);
            }

            let permissioned_pointer = PPtr::<StackCell>::from_addr(head_stack_cell_address);
            let head_read = permissioned_pointer.read(Tracked(&token_ref.points_to));
            assume(token_ref.next_addr.is_some());
            

            let mut possible_new_head_address = atomic_with_ghost!{
                self.head => compare_exchange(
                    head_stack_cell_address, 
                    head_read.next
                );
                update current_head_address -> new_head_address;
                returning possible_new_head_address;

                ghost points_to_inv => {
                    if (token_ref.next_addr.is_some()) {
                        assert(points_to_inv.dom().contains(token_ref.next_addr.unwrap()));
                    }
                    if let Ok(_) = possible_new_head_address {
                        // assert(points_to_inv.dom().contains(token_ref.next_addr));

                        assert(points_to_inv.dom().contains(new_head_address));
                        // assume(points_to_inv.index(new_head_address).instance_id() == self.instance.id());

                        assert(points_to_inv.index(new_head_address).value().points_to.addr() == new_head_address);
                        // assert(points_to_inv.index(new_head_address).value().is_init());
                        assert(points_to_inv.index(new_head_address).key() == new_head_address);
                        // assume(false);
                    } else {
                        // assume(false)
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