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
            create_base(addr: usize, points_to: PointsTo<StackCell>)
            {
                require(addr == points_to.addr());
                require(pre.cell_addresses.is_empty());

                update cell_addresses = pre.cell_addresses.insert(addr);
                deposit address_permissions += [addr => points_to];
                add address_permissions_witnesses (union)= [addr => points_to];
            }
        }

        transition!{
            push(addr: usize, points_to: PointsTo<StackCell>)
            {
                require(addr == points_to.addr());
                require(!pre.cell_addresses.contains(addr));

                update cell_addresses = pre.cell_addresses.insert(addr);
                deposit address_permissions += [addr => points_to];
                add address_permissions_witnesses (union)= [addr => points_to];
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
        fn initialize_inductive(post: Self, base_address: usize) {}

        #[inductive(create_base)]
        fn create_base_inductive(pre: Self, post: Self, addr: usize, points_to: PointsTo<StackCell>) { }

        #[inductive(push)]
        fn push_inductive(pre: Self, post: Self, addr: usize, points_to: PointsTo<StackCell>) {
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
        pub head: AtomicUsize<_, machine::address_permissions_witnesses_map, _>,
        pub instance: Tracked<machine::Instance>,
    }

    pub open spec fn wf(self) -> bool {
        invariant on head with (instance) is (addr: usize, address_permissions_witnesses_map: machine::address_permissions_witnesses_map) {
            instance.id() == address_permissions_witnesses_map.instance_id() &&
            address_permissions_witnesses_map.map().dom().contains(addr)
            // forall |address_in_map: usize| #![auto]
            //     address_permissions_witnesses_map.map().dom().contains(address_in_map) ==>
            //         address_permissions_witnesses_map.map().index(address_in_map).addr() == addr
            // (address_permissions_witnesses_map.map().dom().contains(addr) || )
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

        proof {
            assert(address_permissions_witnesses.map().is_empty());
            instance.create_base(base_address, base_perm, &mut cell_addresses, base_perm);
            assert(!address_permissions_witnesses.map().is_empty());
        }

        let head = AtomicUsize::new(Ghost(Tracked(instance)), base_address, Tracked(address_permissions_witnesses));

        TreiberStack { head, instance: Tracked(instance) }
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
                    let tracked map_entry = points_to_inv.remove(addr);
                    witness_token = map_entry;
                    points_to_inv.insert(map_entry);
                }
            };

            if head_stack_cell_address == 0 {
                return popped_value;
            }


            proof {
                token_ref = self.instance.get_permission_reference(head_stack_cell_address, witness_token.value(), &witness_token);
            }

            let permissioned_pointer = PPtr::<StackCell>::from_addr(head_stack_cell_address);
            let head_clone = permissioned_pointer.read(Tracked(token_ref));

            // let mut possible_pop = atomic_with_ghost!{
            //     self.head => compare_exchange(
            //         permissioned_pointer.addr(), 
            //         head_clone.next()
            //     );

            //     returning ret;

            //     ghost points_to_inv => {
            //         self.instance.pop(&mut points_to_inv.token);
            //         points_to_inv.pointers = Ghost(points_to_inv.pointers@.drop_last());
            //     }
            // };

            // if let Ok(result) = possible_pop {
            //     return Some(head_clone.elem);
            // }
        }
    }
}

fn main() {
    let shared_stack = Arc::new(TreiberStack::new());
}

}