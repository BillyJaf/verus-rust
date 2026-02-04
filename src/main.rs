#![allow(non_snake_case)]

use verus_state_machines_macros::tokenized_state_machine;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::{pervasive::*, prelude::*, *};

include!("vec_remove_duplicates.rs");

verus! {

tokenized_state_machine!{
    X {
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

struct_with_invariants!{
    pub struct Global {
        pub atomic: AtomicU32<_, X::counter, _>,
        pub instance: Tracked<X::Instance>,
    }

    spec fn wf(&self) -> bool {
        invariant on atomic with (instance) is (v: u32, g: X::counter) {
            g.instance_id() == instance@.id()
            && g.value() == v as int
        }

        predicate {
            self.instance@.num_threads() < 0x100000000
        }
    }
}

fn do_count(num_threads: u32) {
    // Initialize protocol
    let tracked (
        Tracked(instance),
        Tracked(counter_token),
        Tracked(unstamped_tokens),
        Tracked(stamped_tokens),
    ) = X::Instance::initialize(num_threads as nat);
    // Initialize the counter
    let tracked_instance = Tracked(instance.clone());
    let atomic = AtomicU32::new(Ghost(tracked_instance), 0, Tracked(counter_token));
    let global = Global { atomic, instance: tracked_instance };
    let global_arc = Arc::new(global);

    // Spawn threads
    let mut join_handles: Vec<JoinHandle<Tracked<X::stamped_tickets>>> = Vec::new();
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
            decreases num_threads - i,
    {
        let tracked unstamped_token;
        proof {
            unstamped_token = unstamped_tokens.split(1 as nat);
        }
        let global_arc = global_arc.clone();
        let join_handle = spawn(
            (move || -> (new_token: Tracked<X::stamped_tickets>)
                ensures
                    new_token@.instance_id() == instance.id(),
                    new_token@.count() == 1,
                {
                    let tracked unstamped_token = unstamped_token;
                    let globals = &*global_arc;
                    let tracked stamped_token;
                    let _ =
                        atomic_with_ghost!(
                            &global_arc.atomic => fetch_add(1);
                            update prev -> next;
                            returning ret;
                            ghost c => {
                                stamped_token =
                                    global_arc.instance.borrow().tr_inc(&mut c, unstamped_token);
                            }
                        );
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
            decreases num_threads - i,
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

    let global = &*global_arc;
    let x =
        atomic_with_ghost!(&global.atomic => load();
        ghost c => {
            instance.finalize(&c, &stamped_tokens);
        }
    );
    assert(x == num_threads);
}

fn main() {
    do_count(20);
    let no_duplicates = vec_remove_duplicates(vec![1,2,3,4,5,5]);
}

} // verus!