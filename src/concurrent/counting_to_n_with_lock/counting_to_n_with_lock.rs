#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use verus_state_machines_macros::tokenized_state_machine;
use verus_builtin::*;
use verus_builtin_macros::*;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::{pervasive::*, prelude::*, *};
use vstd::cell::PCell;

verus! {

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(constant)]
            pub num_threads: nat,

            #[sharding(variable)]
            pub counter: int,

            #[sharding(count)]
            pub unstamped_tickets: nat,

            #[sharding(count)]
            pub stamped_tickets: nat,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == self.stamped_tickets
            && self.stamped_tickets + self.unstamped_tickets == self.num_threads
        }

        init!{
            initialize(num_threads: nat) {
                init num_threads = num_threads;
                init counter = 0;
                init unstamped_tickets = num_threads;
                init stamped_tickets = 0;
            }
        }

        transition!{
            tr_inc() {
                // Equivalent to:
                //    require(pre.unstamped_tickets >= 1);
                //    update unstampted_tickets = pre.unstamped_tickets - 1
                // (In any `remove` statement, the `>=` condition is always implicit.)
                remove unstamped_tickets -= (1);

                // Equivalent to:
                //    update stamped_tickets = pre.stamped_tickets + 1
                add stamped_tickets += (1);

                // These still use ordinary 'update' syntax, because `pre.counter`
                // uses the `variable` sharding strategy.
                assert(pre.counter < pre.num_threads);
                update counter = pre.counter + 1;
            }
        }

        property!{
            finalize() {
                // Equivalent to:
                //    require(pre.unstamped_tickets >= pre.num_threads);
                have stamped_tickets >= (pre.num_threads);

                assert(pre.counter == pre.num_threads);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, num_threads: nat) { }

        #[inductive(tr_inc)]
        fn tr_inc_preserves(pre: Self, post: Self) {
        }
    }
}

pub struct CounterWithPerm {
    pub val: u32,
    pub ghost_token: Tracked<machine::counter>,
}

struct_with_invariants!{
    pub struct Global {
        pub atomic: AtomicBool<_, Option<cell::PointsTo<CounterWithPerm>>, _>,
        pub cell: PCell<CounterWithPerm>,
        pub instance: Tracked<machine::Instance>,
    }

    spec fn wf(&self) -> bool {
        invariant on atomic with (cell, instance) is (v: bool, g: Option<cell::PointsTo<CounterWithPerm>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    points_to.is_init() &&
                    points_to.value().ghost_token@.instance_id() == instance@.id() &&
                    points_to.value().ghost_token@.value() == points_to.value().val as int
                }
            }
        }

        predicate {
            self.instance@.num_threads() < 0x100000000
        }
    }
}

impl Global {
    fn new(cwp: CounterWithPerm, instance: Tracked<machine::Instance>) -> (global: Self)
        requires
            cwp.ghost_token@.instance_id() == instance@.id(),
            cwp.ghost_token@.value() == cwp.val as int,
            instance@.num_threads() < 0x100000000
        ensures 
            global.wf(),
            global.instance == instance,
    {
        let (cell, Tracked(perm)) = PCell::new(cwp);
        let atomic = AtomicBool::new(Ghost((cell, instance)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<cell::PointsTo<CounterWithPerm>>)
        requires 
            self.wf(),
        ensures 
            points_to@.id() == self.cell.id(), 
            points_to@.is_init(),
            points_to@.value().ghost_token@.instance_id() == self.instance@.id(),
            points_to@.value().ghost_token@.value() == points_to@.value().val as int,
            self.wf(),
    {
        loop
            invariant self.wf(),
        {
            let tracked mut points_to_opt = None;
            let res = atomic_with_ghost!(
                &self.atomic => compare_exchange(false, true);
                ghost points_to_inv => {
                    tracked_swap(&mut points_to_opt, &mut points_to_inv);
                }
            );
            if res.is_ok() {
                return Tracked(points_to_opt.tracked_unwrap());
            }
        }
    }

    fn release_lock(&self, points_to: Tracked<cell::PointsTo<CounterWithPerm>>)
        requires
            self.wf(),
            points_to@.id() == self.cell.id(), 
            points_to@.is_init(),
            points_to@.value().ghost_token@.instance_id() == self.instance@.id(),
            points_to@.value().ghost_token@.value() == points_to@.value().val as int,
        ensures
            self.wf()
    {
        atomic_with_ghost!(
            &self.atomic => store(false);
            ghost points_to_inv => {
                points_to_inv = Some(points_to.get());
            }
        );
    }
}

fn do_count(num_threads: u32) {
    // Initialize protocol
    let tracked (
        Tracked(instance),
        Tracked(counter_token),
        Tracked(unstamped_tokens),
        Tracked(stamped_tokens),
    ) = machine::Instance::initialize(num_threads as nat);
    // Initialize the counter
    let cwp = CounterWithPerm {
        val: 0,
        ghost_token: Tracked(counter_token),
    };

    let global = Global::new(cwp, Tracked(instance.clone()));
    let global_arc = Arc::new(global);

    // Spawn threads
    let mut join_handles: Vec<JoinHandle<Tracked<machine::stamped_tickets>>> = Vec::new();
    let mut i = 0;
    while i < num_threads
        invariant
            0 <= i,
            i <= num_threads,
            unstamped_tokens.count() + i == num_threads,
            unstamped_tokens.instance_id() == instance.id(),
            join_handles@.len() == i as int,
            forall|j: int, ret|
                0 <= j && j < i ==> join_handles@.index(j).predicate(ret) ==>
                    ret@.instance_id() == instance.id()
                    && ret@.count() == 1,
            (*global_arc).wf(),
            (*global_arc).instance@ === instance,
        decreases
            num_threads - i
    {
        let tracked unstamped_token;
        proof {
            unstamped_token = unstamped_tokens.split(1 as nat);
        }
        let global_arc = global_arc.clone();
        let join_handle = spawn(
            (move || -> (new_token: Tracked<machine::stamped_tickets>)
                ensures
                    new_token@.instance_id() == instance.id(),
                    new_token@.count() == 1,
                {
                    let tracked unstamped_token = unstamped_token;

                    let tracked stamped_token;

                    let mut perm = global_arc.acquire_lock();

                    let mut cwp = global_arc.cell.take(Tracked(perm.borrow_mut())); 
                    let val = cwp.val;
                    let mut ghost_token = cwp.ghost_token;
                    
                    proof {
                        stamped_token = global_arc.instance.borrow().tr_inc(ghost_token.borrow_mut(), unstamped_token);
                    }

                    global_arc.cell.put(Tracked(perm.borrow_mut()), CounterWithPerm {
                        val: val + 1,
                        ghost_token,
                    });

                    global_arc.release_lock(perm);

                    Tracked(stamped_token)
                }),
        );
        join_handles.push(join_handle);
        i = i + 1;
    }
    // Join threads

    let mut i = 0;
    while i < num_threads
        invariant
            0 <= i,
            i <= num_threads,
            stamped_tokens.count() == i,
            stamped_tokens.instance_id() == instance.id(),
            join_handles@.len() as int + i as int == num_threads,
            forall|j: int, ret|
                0 <= j && j < join_handles@.len() ==>
                    #[trigger] join_handles@.index(j).predicate(ret) ==>
                        ret@.instance_id() == instance.id()
                        && ret@.count() == 1,
            (*global_arc).wf(),
            (*global_arc).instance@ === instance,
        decreases
            num_threads - i
    {
        let join_handle = join_handles.pop().unwrap();
        match join_handle.join() {
            Result::Ok(token) => {
                proof {
                    stamped_tokens.join(token.get());
                }
            },
            _ => {
                return ;
            },
        };
        i = i + 1;
    }

    let mut perm = global_arc.acquire_lock();
    let mut cwp = global_arc.cell.borrow(Tracked(perm.borrow())); 
    let val = cwp.val;
    let ghost_token = &cwp.ghost_token;

    proof {
        global_arc.instance.borrow().finalize(ghost_token.borrow(), &stamped_tokens);
    }

    global_arc.release_lock(perm);
    assert(val == num_threads);
}

fn main() {
    do_count(20);
}

} // verus!