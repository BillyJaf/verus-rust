#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use std::sync::Arc;
use vstd::atomic_ghost::*;
use vstd::modes::*;
use vstd::prelude::*;
use vstd::thread::*;
use vstd::{pervasive::*, *};
use vstd::cell::pcell;

verus! {

tokenized_state_machine!(
    machine {
        fields {
            #[sharding(variable)]
            pub counter: int,

            #[sharding(variable)]
            pub inc_a: bool,

            #[sharding(variable)]
            pub inc_b: bool,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            self.counter == (if self.inc_a { 1 as int } else { 0 }) + (if self.inc_b { 1 as int } else { 0 })
        }

        init!{
            initialize() {
                init counter = 0;
                init inc_a = false;
                init inc_b = false;
            }
        }

        transition!{
            tr_inc_a() {
                require(!pre.inc_a);
                update counter = pre.counter + 1;
                update inc_a = true;
            }
        }

        transition!{
            tr_inc_b() {
                require(!pre.inc_b);
                update counter = pre.counter + 1;
                update inc_b = true;
            }
        }

        property!{
            increment_will_not_overflow_u32() {
                assert 0 <= pre.counter < 0xffff_ffff;
            }
        }

        property!{
            finalize() {
                require(pre.inc_a);
                require(pre.inc_b);
                assert pre.counter == 2;
            }
        }

        #[inductive(tr_inc_a)]
        fn tr_inc_a_preserves(pre: Self, post: Self) {
        }

        #[inductive(tr_inc_b)]
        fn tr_inc_b_preserves(pre: Self, post: Self) {
        }

        #[inductive(initialize)]
        fn initialize_inv(post: Self) {
        }
    }
);

pub struct CounterWithPerm {
    pub val: u32,
    pub ghost_token: Option<Tracked<machine::counter>>,
}

struct_with_invariants!{
    pub struct Global {
        pub atomic: AtomicBool<_, Option<pcell::PointsTo<CounterWithPerm>>, _>,
        pub cell: pcell::PCell<CounterWithPerm>,
        pub instance: Tracked<machine::Instance>,
    }

    spec fn wf(&self) -> bool {
        invariant on atomic with (cell, instance) is (v: bool, g: Option<pcell::PointsTo<CounterWithPerm>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    points_to.value().ghost_token.is_some() &&
                    points_to.value().ghost_token.unwrap()@.instance_id() == instance@.id() &&
                    points_to.value().ghost_token.unwrap()@.value() == points_to.value().val as int
                }
            }
        }
    }
}

impl Global {
    fn new(cwp: CounterWithPerm, instance: Tracked<machine::Instance>) -> (global: Self)
        requires
            cwp.ghost_token.is_some() &&
            cwp.ghost_token.unwrap()@.instance_id() == instance@.id(),
            cwp.ghost_token.unwrap()@.value() == cwp.val as int
        ensures 
            global.wf(),
            global.instance == instance,
    {
        let (cell, Tracked(perm)) = pcell::PCell::new(cwp);
        let atomic = AtomicBool::new(Ghost((cell, instance)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<pcell::PointsTo<CounterWithPerm>>)
        requires 
            self.wf(),
        ensures 
            points_to@.id() == self.cell.id(), 
            points_to@.value().ghost_token.is_some(),
            points_to@.value().ghost_token.unwrap()@.instance_id() == self.instance@.id(),
            points_to@.value().ghost_token.unwrap()@.value() == points_to@.value().val as int,
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

    fn release_lock(&self, points_to: Tracked<pcell::PointsTo<CounterWithPerm>>)
        requires
            self.wf(),
            points_to@.id() == self.cell.id(), 
            points_to@.value().ghost_token.is_some(),
            points_to@.value().ghost_token.unwrap()@.instance_id() == self.instance@.id(),
            points_to@.value().ghost_token.unwrap()@.value() == points_to@.value().val as int,
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

fn main() {
    // Initialize protocol
    let tracked (
        Tracked(instance),
        Tracked(counter_token),
        Tracked(inc_a_token),
        Tracked(inc_b_token),
    ) = machine::Instance::initialize();

    let cwp = CounterWithPerm {
        val: 0,
        ghost_token: Some(Tracked(counter_token)),
    };

    let global = Global::new(cwp, Tracked(instance.clone()));
    let global_arc = Arc::new(global);

    // Spawn threads

    // Thread 1
    let global_arc_thread1 = global_arc.clone();
    
    let join_handle1 = spawn(
        (move || -> (new_token: Tracked<machine::inc_a>)
            ensures
                new_token@.instance_id() == instance.id(),
                new_token@.value() == true,
            {
                let tracked mut token = inc_a_token;

                let mut perm = global_arc_thread1.acquire_lock();

                let empty_cwp = CounterWithPerm { 
                    val: 0,
                    ghost_token: None
                };

                let mut cwp = global_arc_thread1.cell.replace(Tracked(perm.borrow_mut()), empty_cwp); 
                let val = cwp.val;
                let mut ghost_token = cwp.ghost_token.unwrap();
                
                proof {
                    global_arc_thread1.instance.borrow().increment_will_not_overflow_u32(ghost_token.borrow_mut());
                    global_arc_thread1.instance.borrow().tr_inc_a(ghost_token.borrow_mut(), &mut token);
                }

                global_arc_thread1.cell.replace(Tracked(perm.borrow_mut()), CounterWithPerm {
                    val: val + 1,
                    ghost_token: Some(ghost_token),
                });

                global_arc_thread1.release_lock(perm);
                Tracked(token)
            }),
    );

    // Thread 2
    let global_arc_thread2 = global_arc.clone();

    let join_handle2 = spawn(
        (move || -> (new_token: Tracked<machine::inc_b>)
            ensures
                new_token@.instance_id() == instance.id(),
                new_token@.value() == true,
            {
                let tracked mut token = inc_b_token;

                let mut perm = global_arc_thread2.acquire_lock();

                let empty_cwp = CounterWithPerm { 
                    val: 0,
                    ghost_token: None
                };

                let mut cwp = global_arc_thread2.cell.replace(Tracked(perm.borrow_mut()), empty_cwp); 
                let val = cwp.val;
                let mut ghost_token = cwp.ghost_token.unwrap();
                
                proof {
                    global_arc_thread2.instance.borrow().increment_will_not_overflow_u32(ghost_token.borrow_mut());
                    global_arc_thread2.instance.borrow().tr_inc_b(ghost_token.borrow_mut(), &mut token);
                }

                global_arc_thread2.cell.replace(Tracked(perm.borrow_mut()), CounterWithPerm {
                    val: val + 1,
                    ghost_token: Some(ghost_token),
                });

                global_arc_thread2.release_lock(perm);
                Tracked(token)
            }),
    );

    // Join threads
    let tracked inc_a_token;
    match join_handle1.join() {
        Result::Ok(token) => {
            proof {
                inc_a_token = token.get();
            }
        },
        _ => {
            return ;
        },
    };
    let tracked inc_b_token;
    match join_handle2.join() {
        Result::Ok(token) => {
            proof {
                inc_b_token = token.get();
            }
        },
        _ => {
            return ;
        },
    };

    // Join threads, load the atomic again
    let mut perm = global_arc.acquire_lock();
    let empty_cwp = CounterWithPerm { 
        val: 0,
        ghost_token: None
    };

    let mut cwp = global_arc.cell.replace(Tracked(perm.borrow_mut()), empty_cwp); 

    let val = cwp.val;
    let ghost_token_wrapped = cwp.ghost_token;
    let ghost_token = ghost_token_wrapped.unwrap();

    proof {
        global_arc.instance.borrow().finalize(ghost_token.borrow(), &inc_a_token, &inc_b_token);
    }

    global_arc.cell.replace(Tracked(perm.borrow_mut()), CounterWithPerm {
        val: val,
        ghost_token: Some(ghost_token),
    });

    global_arc.release_lock(perm);


    assert(val == 2);
}
}