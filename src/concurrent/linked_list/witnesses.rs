#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use verus_state_machines_macros::tokenized_state_machine;
use verus_builtin::*;
use verus_builtin_macros::*;
use std::sync::Arc;
use vstd::{
    atomic_ghost::*,
    modes::*,
    prelude::*,
    thread::*,
    pervasive::*, 
    cell::pcell_maybe_uninit::{
        PCell,
        PointsTo
    },
    seq_lib::*,
};

verus! {

pub enum Operation {
    Insert(u32),
    InsertFail(u32),
    Delete(u32),
    DeleteFail(u32)
}

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(map)]
            pub operation_history: Map<nat, Operation>,

            // #[sharding(map)]
            // pub list_representation: Map<u32, Option<u32>>,
        }

        #[invariant]
        pub fn operation_inv(&self) -> bool {
            self.operation_history.dom().finite() &&
            (forall |i: nat| i < self.operation_history.dom().len() <==> self.operation_history.dom().contains(i))
        }

        init!{
            initialize()
            {
                init operation_history = Map::empty();
            }
        }

        transition!{
            insert(lower: Option<u32>, insert: u32, upper: Option<u32>)
            {   
                require(lower.is_some() ==> lower.unwrap() < insert);
                require(upper.is_some() ==> insert < upper.unwrap());

                // remove list_representation -= [lower => upper];
                // add list_representation += [lower => Some(insert)];
                // add list_representation += [insert => upper];

                birds_eye let next_operation_index = pre.operation_history.dom().len();
                add operation_history += [next_operation_index => Operation::Insert(insert)];
            }
        }

        transition!{
            insert_fail(insert: u32, car: u32)
            {   
                require(insert == car);

                // remove list_representation -= [lower => upper];
                // add list_representation += [lower => Some(insert)];
                // add list_representation += [insert => upper];

                birds_eye let next_operation_index = pre.operation_history.dom().len();
                add operation_history += [next_operation_index => Operation::InsertFail(insert)];
            }
        }

        transition!{
            delete(lower_car: Option<u32>, delete_car: u32, upper_car: Option<u32>)
            {   
                require(lower_car.is_some() ==> lower_car.unwrap() < delete_car);
                require(upper_car.is_some() ==> delete_car < upper_car.unwrap());

                // remove list_representation -= [lower => upper];
                // add list_representation += [lower => Some(delete)];
                // add list_representation += [delete => upper];

                birds_eye let next_operation_index = pre.operation_history.dom().len();
                add operation_history += [next_operation_index => Operation::Delete(delete_car)];
            }
        }

        transition!{
            delete_fail(lower_car: Option<u32>, delete_car: u32, upper_car: Option<u32>)
            {   
                require(
                    // List is empty
                    (lower_car.is_none() && upper_car.is_none()) ||
                    // Desired delete is smaller than everything in the list
                    (lower_car.is_none() && upper_car.is_some() && delete_car < upper_car.unwrap()) ||
                    // Desired delete is larger than everything in the list
                    (lower_car.is_some() && upper_car.is_none() && lower_car.unwrap() < delete_car) ||
                    // Desired delete is not larger or smaller, but just not present:
                    (lower_car.is_some() && upper_car.is_some() && lower_car.unwrap() < delete_car && delete_car < upper_car.unwrap())
                );

                // remove list_representation -= [lower => upper];
                // add list_representation += [lower => Some(insert)];
                // add list_representation += [insert => upper];

                birds_eye let next_operation_index = pre.operation_history.dom().len();
                add operation_history += [next_operation_index => Operation::DeleteFail(delete_car)];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {}

        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, lower: Option<u32>, insert: u32, upper: Option<u32>) {}

        #[inductive(insert_fail)]
        fn insert_fail_inductive(pre: Self, post: Self, insert: u32, car: u32) {}

        #[inductive(delete)]
        fn delete_inductive(pre: Self, post: Self, lower_car: Option<u32>, delete_car: u32, upper_car: Option<u32>) {}

        #[inductive(delete_fail)]
        fn delete_fail_inductive(pre: Self, post: Self, lower_car: Option<u32>, delete_car: u32, upper_car: Option<u32>) {}
    }
}


pub struct Nil {
    pub cdr: Option<Arc<LockedCons>>,
}

struct_with_invariants!{
    struct LockedNil {
        atomic: AtomicBool<_, Option<PointsTo<Nil>>, _>,
        cell: PCell<Nil>,
        instance: Tracked<machine::Instance>,
    }

    spec fn wf(&self) -> bool 
    {
        invariant on atomic with (cell, instance) is (v: bool, g: Option<PointsTo<Nil>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.is_init() &&
                    points_to.id() == cell.id() &&
                    (points_to.value().cdr.is_some() ==> 
                        points_to.value().cdr.unwrap().wf() &&
                        points_to.value().cdr.unwrap().view_instance() == instance
                    )
                }
            }
        }
    }
}

impl LockedNil {
    fn new() -> (locked_nil: Self)
        ensures 
            locked_nil.wf(),
    {
        let tracked (
            Tracked(instance),
            Tracked(operation_history)
        ) = machine::Instance::initialize();

        let node = Nil { cdr: None::<Arc<LockedCons>> };
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, Tracked(instance))), false, Tracked(Some(perm)));
        Self { 
            atomic, 
            cell, 
            instance: Tracked(instance)
        }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<PointsTo<Nil>>)
        requires 
            self.wf(),
        ensures 
            points_to.is_init(),
            points_to.id() == self.cell.id(),
            (points_to.value().cdr.is_some() ==> 
                points_to.value().cdr.unwrap().wf() &&
                points_to.value().cdr.unwrap().instance == self.instance
            ),
            self.wf()
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

    fn release_lock(&self, points_to: Tracked<PointsTo<Nil>>)
        requires
            self.wf(),
            points_to.is_init(),
            points_to.id() == self.cell.id(),
            (points_to.value().cdr.is_some() ==> 
                points_to.value().cdr.unwrap().wf() &&
                points_to.value().cdr.unwrap().instance == self.instance
            ),
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

    fn insert_with_no_cdr(&self, mut nil_perm: Tracked<PointsTo<Nil>>, insert_car: u32) -> ((updated_nil_perm, new_cons_perm, witness_token): (Tracked<PointsTo<Nil>>, Tracked<PointsTo<Cons>>, Tracked<machine::operation_history>))
        requires
            self.wf(),
            nil_perm.is_init(),
            nil_perm.id() == self.cell.id(),
            nil_perm.value().cdr.is_none(),
        ensures
            self.wf(),
            updated_nil_perm.is_init(),
            new_cons_perm.is_init(),
            updated_nil_perm.id() == self.cell.id(),
            updated_nil_perm.value().cdr.is_some(),
            updated_nil_perm.value().cdr.unwrap().wf(),
            updated_nil_perm.value().cdr.unwrap().view_car == insert_car,
            updated_nil_perm.value().cdr.unwrap().instance == self.instance,
            new_cons_perm.id() == updated_nil_perm.value().cdr.unwrap().cell.id(),
            new_cons_perm.value().cdr.is_none(),
            new_cons_perm.value().car == insert_car,
            witness_token.instance_id() == self.instance.id(),
            witness_token.value() == Operation::Insert(insert_car)
    {
        let mut nil = self.cell.take(Tracked(nil_perm.borrow_mut()));
        let (locked_cons, locked_cons_perm) = LockedCons::new(
            insert_car, 
            None::<Arc<LockedCons>>,
            self.instance.clone()
        );

        let tracked witness_token;
        proof {
            witness_token = self.instance.borrow().insert(None, insert_car, None).1.get();
        }

        nil.cdr = Some(Arc::new(locked_cons));
        self.cell.put(Tracked(nil_perm.borrow_mut()), nil);
        return (nil_perm, locked_cons_perm, Tracked(witness_token))
    }

    fn insert_with_cdr(&self, mut nil_perm: Tracked<PointsTo<Nil>>, cons_perm: &Tracked<PointsTo<Cons>>, insert_car: u32) -> ((updated_nil_perm, new_cons_perm, witness_token): (Tracked<PointsTo<Nil>>, Tracked<PointsTo<Cons>>, Tracked<machine::operation_history>))
        requires
            self.wf(),
            nil_perm.is_init(),
            cons_perm.is_init(),
            nil_perm.id() == self.cell.id(),
            nil_perm.value().cdr.is_some(),
            nil_perm.value().cdr.unwrap().wf(),
            nil_perm.value().cdr.unwrap().view_car == cons_perm.value().car,
            nil_perm.value().cdr.unwrap().instance == self.instance,
            cons_perm.id() == nil_perm.value().cdr.unwrap().cell.id(),
            cons_perm.value().cdr.is_some() ==> (
                cons_perm.value().cdr.unwrap().wf() &&
                cons_perm.value().cdr.unwrap().instance == self.instance
            ),
            insert_car < cons_perm.value().car
        ensures
            self.wf(),
            updated_nil_perm.is_init(),
            new_cons_perm.is_init(),
            cons_perm.is_init(),
            updated_nil_perm.id() == self.cell.id(),
            updated_nil_perm.value().cdr.is_some(),
            updated_nil_perm.value().cdr.unwrap().wf(),
            updated_nil_perm.value().cdr.unwrap().view_car == insert_car,
            updated_nil_perm.value().cdr.unwrap().instance == self.instance,
            new_cons_perm.id() == updated_nil_perm.value().cdr.unwrap().cell.id(),
            new_cons_perm.value().car == insert_car,
            new_cons_perm.value().cdr.is_some(),
            new_cons_perm.value().cdr.unwrap().wf(),
            new_cons_perm.value().cdr.unwrap().view_car == cons_perm.value().car,
            new_cons_perm.value().cdr.unwrap().instance == self.instance,
            witness_token.instance_id() == self.instance.id(),
            witness_token.value() == Operation::Insert(insert_car)
    {
        let mut nil = self.cell.take(Tracked(nil_perm.borrow_mut()));

        let (locked_cons, locked_cons_perm) = LockedCons::new(
            insert_car, 
            Some(nil.cdr.as_ref().unwrap().clone()),
            self.instance.clone()
        );

        let tracked witness_token;
        proof {
            witness_token = self.instance.borrow().insert(None, insert_car, Some(cons_perm.value().car)).1.get();
        }

        nil.cdr = Some(Arc::new(locked_cons));
        self.cell.put(Tracked(nil_perm.borrow_mut()), nil);
        return (nil_perm, locked_cons_perm, Tracked(witness_token))
    }

    fn insert(self: Arc<Self>, insert_car: u32) -> (witness_token: Tracked<machine::operation_history>)
        requires
            self.wf()
        ensures
            self.wf(),
            witness_token.instance_id() == self.instance.id(),
            witness_token.value() == Operation::Insert(insert_car) || witness_token.value() == Operation::InsertFail(insert_car)
    {
        // Acquire the lock for the nil node, and view the data inside (without taking)
        let mut nil_perm = self.acquire_lock();
        let nil_view = self.cell.borrow(Tracked(nil_perm.borrow_mut()));

        // If the nil cdr is none, then we must insert here - at the tail
        if (nil_view.cdr.is_none()) {
            let (mut updated_nil_perm, new_cons_perm, witness_token) = self.insert_with_no_cdr(nil_perm, insert_car);
            let updated_nil_view = self.cell.borrow(Tracked(updated_nil_perm.borrow_mut()));
            let new_locked_cons = updated_nil_view.cdr.as_ref().unwrap().clone();

            self.release_lock(updated_nil_perm);
            new_locked_cons.release_lock(new_cons_perm);
            return witness_token;
        } 
        else {
            // We check if we need to insert inbetween Nil and the first Cons
            let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
            let mut first_cons_perm = first_locked_cons.acquire_lock();
            let first_cons_view = first_locked_cons.cell.borrow(Tracked(first_cons_perm.borrow_mut()));

            // If a Cons with this value already exists:
            if (insert_car == first_cons_view.car) {
                // Return early and do nothing - the Cons exists.
                let tracked witness_token;
                proof {
                    witness_token = self.instance.borrow().insert_fail(insert_car, first_cons_view.car).1.get();
                }
                self.release_lock(nil_perm);
                first_locked_cons.release_lock(first_cons_perm);
                return Tracked(witness_token);
            }

            // If the first Cons cdr is larger than the insert cdr:
            if (insert_car < first_cons_view.car) {

                let (mut updated_nil_perm, new_cons_perm, witness_token) = self.insert_with_cdr(nil_perm, &first_cons_perm, insert_car);
                let updated_nil_view = self.cell.borrow(Tracked(updated_nil_perm.borrow_mut()));
                let new_locked_cons = updated_nil_view.cdr.as_ref().unwrap().clone();

                self.release_lock(updated_nil_perm);
                new_locked_cons.release_lock(new_cons_perm);
                first_locked_cons.release_lock(first_cons_perm);
                return witness_token;
            }

            // If we have reached here, we may release the nil lock:
            self.release_lock(nil_perm);

            // Any insert from here onwards will not involve nil - 
            // we may delegate the insert to a chain of LockedCons
            return first_locked_cons.insert(first_cons_perm, insert_car);
        }
    }

    fn delete_first_cons(&self, mut nil_perm: Tracked<PointsTo<Nil>>, mut cons_perm: Tracked<PointsTo<Cons>>, delete_car: u32) -> ((updated_nil_perm, witness_token): (Tracked<PointsTo<Nil>>, Tracked<machine::operation_history>))
        requires
            self.wf(),
            nil_perm.is_init(),
            cons_perm.is_init(),
            nil_perm.id() == self.cell.id(),
            nil_perm.value().cdr.is_some(),
            nil_perm.value().cdr.unwrap().wf(),
            nil_perm.value().cdr.unwrap().view_car == cons_perm.value().car,
            nil_perm.value().cdr.unwrap().instance == self.instance,
            cons_perm.id() == nil_perm.value().cdr.unwrap().cell.id(),
            cons_perm.value().cdr.is_some() ==> (
                cons_perm.value().cdr.unwrap().wf() &&
                cons_perm.value().cdr.unwrap().view_car > delete_car &&
                cons_perm.value().cdr.unwrap().instance == self.instance
            ),
            delete_car == cons_perm.value().car,
        ensures
            self.wf(),
            updated_nil_perm.is_init(),
            updated_nil_perm.id() == self.cell.id(),
            updated_nil_perm.value().cdr == cons_perm.value().cdr,
            updated_nil_perm.value().cdr.is_some() ==> ( 
                updated_nil_perm.value().cdr.unwrap().wf() &&
                updated_nil_perm.value().cdr.unwrap().view_car > delete_car &&
                updated_nil_perm.value().cdr.unwrap().instance == self.instance
            ),
            witness_token.instance_id() == self.instance.id(),
            witness_token.value() == Operation::Delete(delete_car)
    {
        let mut nil = self.cell.take(Tracked(nil_perm.borrow_mut()));
        let delete_cons = nil.cdr.as_ref().unwrap().cell.take(Tracked(cons_perm.borrow_mut()));
        let upper = match delete_cons.cdr {
            Some(second_cons) => Some(second_cons.view_car()),
            _ => None,
        };
        nil.cdr = delete_cons.cdr;
        self.cell.put(Tracked(nil_perm.borrow_mut()), nil);

        let tracked witness_token;
        proof {
            witness_token = self.instance.borrow().delete(None, delete_car, upper).1.get()
        }

        return (nil_perm, Tracked(witness_token))
    }

    fn delete(self: Arc<Self>, delete_car: u32) -> (witness_token: Tracked<machine::operation_history>)
        requires
            self.wf()
        ensures
            self.wf(),
            witness_token.instance_id() == self.instance.id(),
            witness_token.value() == Operation::Delete(delete_car) || witness_token.value() == Operation::DeleteFail(delete_car)
    {
        // Acquire the lock for the nil node, and view the data inside (without taking)
        let mut nil_perm = self.acquire_lock();
        let nil_view = self.cell.borrow(Tracked(nil_perm.borrow_mut()));

        // If the nil cdr is none, then we are done, no nodes exist
        if (nil_view.cdr.is_none()) {
            let tracked witness_token;
            proof {
                witness_token = self.instance.borrow().delete_fail(None, delete_car, None).1.get();
            }

            self.release_lock(nil_perm);
            return Tracked(witness_token);
        }

        // We check if we need to delete the first Cons (hence lower is LockedNil)
        let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
        let mut first_cons_perm = first_locked_cons.acquire_lock();
        let first_cons_view = first_locked_cons.cell.borrow(Tracked(first_cons_perm.borrow_mut()));

        // If the first car is larger than our delete, then we are done, all nodes are larger
        if (delete_car < first_cons_view.car) {
            let tracked witness_token;
            proof {
                witness_token = self.instance.borrow().delete_fail(None, delete_car, Some(first_cons_view.car)).1.get();
            }
            self.release_lock(nil_perm);
            first_locked_cons.release_lock(first_cons_perm);
            return Tracked(witness_token);
        }

        // Check if we are deleting the first LockedCons:
        if (delete_car == first_cons_view.car) {
            let (updated_nil_perm, witness_token) = self.delete_first_cons(nil_perm, first_cons_perm, delete_car);
            self.release_lock(updated_nil_perm);
            return witness_token;
        }
        
        // We can release the dummy node lock.
        self.release_lock(nil_perm);
        // and begin our traversal:
        return first_locked_cons.delete(first_cons_perm, delete_car);
    }
}

pub struct Cons {
    pub car: u32,
    pub cdr: Option<Arc<LockedCons>>,
}

struct_with_invariants!{
    pub struct LockedCons {
        atomic: AtomicBool<_, Option<PointsTo<Cons>>, _>,
        cell: PCell<Cons>,
        instance: Tracked<machine::Instance>,
        view_car: Ghost<u32>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant on atomic with (cell, view_car, instance) is (v: bool, g: Option<PointsTo<Cons>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.is_init() &&
                    points_to.id() == cell.id() &&
                    points_to.value().car == view_car &&
                    (points_to.value().cdr.is_some() ==> 
                        (
                            points_to.value().cdr.unwrap().wf() &&
                            points_to.value().cdr.unwrap().view_car > points_to.value().car &&
                            points_to.value().cdr.unwrap().instance == instance
                        )
                    )
                }
            }
        }
    }
}

impl LockedCons {
    fn new(car: u32, cdr: Option<Arc<LockedCons>>, instance: Tracked<machine::Instance>) -> ((cons, cons_perm): (Self, Tracked<PointsTo<Cons>>))
        requires
            cdr.is_some() ==> (
                cdr.unwrap().wf() &&
                cdr.unwrap().view_car > car
            )
        ensures 
            cons.wf(),
            cons.view_car == car,
            cons.instance == instance,
            cons_perm.is_init(),
            cons_perm.id() == cons.cell.id(),
            cons_perm.value().car == car,
            cons_perm.value().cdr == cdr
    {   
        let view_car = Ghost(car);
        let node = Cons { car, cdr };
        let (cell, Tracked(perm)) = PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, view_car, instance)), true, Tracked(None));
        let cons = Self { atomic, cell, view_car, instance };
        return (cons, Tracked(perm));
    }

    fn acquire_lock(&self) -> (points_to: Tracked<PointsTo<Cons>>)
        requires 
            self.wf(),
        ensures 
            points_to.is_init(),
            points_to.id() == self.cell.id(),
            points_to.value().car == self.view_car,
            (points_to.value().cdr.is_some() ==> 
                (
                    points_to.value().cdr.unwrap().wf() &&
                    points_to.value().cdr.unwrap().view_car > points_to.value().car &&
                    points_to.value().cdr.unwrap().instance == self.instance
                )
            ),
            self.wf()
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

    fn release_lock(&self, points_to: Tracked<PointsTo<Cons>>)
        requires
            self.wf(),
            points_to.is_init(),
            points_to.id() == self.cell.id(),
            points_to.value().car == self.view_car,
            (points_to.value().cdr.is_some() ==> 
                (
                    points_to.value().cdr.unwrap().wf() &&
                    points_to.value().cdr.unwrap().view_car > points_to.value().car &&
                    points_to.value().cdr.unwrap().instance == self.instance
                )
            )
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

    pub closed spec fn view_instance(&self) -> (instance: machine::Instance)
    {
        self.instance@
    }

    pub fn view_car(&self) -> u32
    {
        self.view_car@
    }

    fn insert_with_cdr(&self, mut first_cons_perm: Tracked<PointsTo<Cons>>, second_cons_perm: &Tracked<PointsTo<Cons>>, insert_car: u32) -> ((updated_first_cons_perm, new_cons_perm, witness_token): (Tracked<PointsTo<Cons>>, Tracked<PointsTo<Cons>>, Tracked<machine::operation_history>))
        requires
            self.wf(),
            first_cons_perm.is_init(),
            second_cons_perm.is_init(),
            first_cons_perm.id() == self.cell.id(),
            first_cons_perm.value().car < insert_car,
            first_cons_perm.value().cdr.is_some(),
            first_cons_perm.value().cdr.unwrap().wf(),
            first_cons_perm.value().cdr.unwrap().view_car == second_cons_perm.value().car,
            first_cons_perm.value().cdr.unwrap().instance == self.instance,
            second_cons_perm.id() == first_cons_perm.value().cdr.unwrap().cell.id(),
            second_cons_perm.value().cdr.is_some() ==> (
                second_cons_perm.value().cdr.unwrap().wf() &&
                second_cons_perm.value().cdr.unwrap().instance == self.instance
            ),
            insert_car < second_cons_perm.value().car
        ensures
            self.wf(),
            updated_first_cons_perm.is_init(),
            new_cons_perm.is_init(),
            second_cons_perm.is_init(),
            updated_first_cons_perm.id() == self.cell.id(),
            updated_first_cons_perm.value().car == first_cons_perm.value().car,
            updated_first_cons_perm.value().cdr.is_some(),
            updated_first_cons_perm.value().cdr.unwrap().wf(),
            updated_first_cons_perm.value().cdr.unwrap().view_car == insert_car,
            updated_first_cons_perm.value().cdr.unwrap().instance == self.instance,
            new_cons_perm.id() == updated_first_cons_perm.value().cdr.unwrap().cell.id(),
            new_cons_perm.value().car == insert_car,
            new_cons_perm.value().cdr.is_some(),
            new_cons_perm.value().cdr.unwrap().wf(),
            new_cons_perm.value().cdr.unwrap().view_car == second_cons_perm.value().car,
            new_cons_perm.value().cdr.unwrap().instance == self.instance,
            second_cons_perm.id() == new_cons_perm.value().cdr.unwrap().cell.id(),
            second_cons_perm.value().cdr.is_some() ==> (
                second_cons_perm.value().cdr.unwrap().wf() &&
                second_cons_perm.value().cdr.unwrap().instance == self.instance
            ),
            insert_car < second_cons_perm.value().car,
            witness_token.instance_id() == self.instance.id(),
            witness_token.value() == Operation::Insert(insert_car)
    {
        let mut first_cons = self.cell.take(Tracked(first_cons_perm.borrow_mut()));

        let (new_locked_cons, new_locked_cons_perm) = LockedCons::new(
            insert_car, 
            Some(first_cons.cdr.as_ref().unwrap().clone()),
            self.instance.clone()
        );

        let tracked witness_token;
        proof {
            witness_token = self.instance.borrow().insert(Some(first_cons.car), insert_car, Some(second_cons_perm.value().car)).1.get();
        }

        first_cons.cdr = Some(Arc::new(new_locked_cons));
        self.cell.put(Tracked(first_cons_perm.borrow_mut()), first_cons);
        return (first_cons_perm, new_locked_cons_perm, Tracked(witness_token))
    }

    fn insert_with_no_cdr(&self, mut cons_perm: Tracked<PointsTo<Cons>>, insert_car: u32) -> ((updated_cons_perm, new_cons_perm, witness_token): (Tracked<PointsTo<Cons>>, Tracked<PointsTo<Cons>>, Tracked<machine::operation_history>))
        requires
            self.wf(),
            cons_perm.is_init(),
            cons_perm.id() == self.cell.id(),
            cons_perm.value().car < insert_car,
            cons_perm.value().cdr.is_none()
        ensures
            self.wf(),
            updated_cons_perm.is_init(),
            new_cons_perm.is_init(),
            updated_cons_perm.id() == self.cell.id(),
            updated_cons_perm.value().car == cons_perm.value().car,
            updated_cons_perm.value().cdr.is_some(),
            updated_cons_perm.value().cdr.unwrap().wf(),
            updated_cons_perm.value().cdr.unwrap().view_car == insert_car,
            updated_cons_perm.value().cdr.unwrap().instance == self.instance,
            new_cons_perm.id() == updated_cons_perm.value().cdr.unwrap().cell.id(),
            new_cons_perm.value().cdr.is_none(),
            new_cons_perm.value().car == insert_car,
            witness_token.instance_id() == self.instance.id(),
            witness_token.value() == Operation::Insert(insert_car)
    {
        let mut cons = self.cell.take(Tracked(cons_perm.borrow_mut()));
        let (new_locked_cons, new_locked_cons_perm) = LockedCons::new(
            insert_car, 
            None::<Arc<LockedCons>>,
            self.instance.clone()
        );

        let tracked witness_token;
        proof {
            witness_token = self.instance.borrow().insert(Some(cons.car), insert_car, None).1.get();
        }


        cons.cdr = Some(Arc::new(new_locked_cons));
        self.cell.put(Tracked(cons_perm.borrow_mut()), cons);
        return (cons_perm, new_locked_cons_perm, Tracked(witness_token))
    }

    fn insert(self: Arc<Self>, mut current_cons_perm: Tracked<PointsTo<Cons>>, insert_car: u32) -> (witness_token: Tracked<machine::operation_history>)
        requires
            self.wf(),
            current_cons_perm.is_init(),
            current_cons_perm.id() == self.cell.id(),
            current_cons_perm.value().car == self.view_car,
            current_cons_perm.value().cdr.is_some() ==> (
                    current_cons_perm.value().cdr.unwrap().wf() &&
                    current_cons_perm.value().cdr.unwrap().view_car > current_cons_perm.value().car &&
                    current_cons_perm.value().cdr.unwrap().instance == self.instance
            ),
            current_cons_perm.value().car < insert_car
        ensures
            self.wf(),
            witness_token.instance_id() == self.instance.id(),
            witness_token.value() == Operation::Insert(insert_car) || witness_token.value() == Operation::InsertFail(insert_car)
    {
        let mut current_locked_cons = self;
        loop 
            invariant
                self.wf(),
                current_locked_cons.instance == self.instance,
                current_locked_cons.wf(),
                current_cons_perm.is_init(),
                current_cons_perm.id() == current_locked_cons.cell.id(),
                current_cons_perm.value().car == current_locked_cons.view_car,
                current_cons_perm.value().cdr.is_some() ==> (
                        current_cons_perm.value().cdr.unwrap().wf() &&
                        current_cons_perm.value().cdr.unwrap().view_car > current_cons_perm.value().car &&
                        current_cons_perm.value().cdr.unwrap().instance == self.instance
                ),
                current_cons_perm.value().car < insert_car,
            decreases
                insert_car - current_cons_perm.value().car
        {
            let mut current_cons_view = current_locked_cons.cell.borrow(Tracked(current_cons_perm.borrow_mut()));

            // If there is no next LockedCons, then we must insert at the tail after a Cons
            if (current_cons_view.cdr.is_none()) {
                let (mut updated_current_cons_perm, new_cons_perm, witness_token) = current_locked_cons.insert_with_no_cdr(current_cons_perm, insert_car);
                let updated_current_cons_view = current_locked_cons.cell.borrow(Tracked(updated_current_cons_perm.borrow_mut()));
                let new_locked_cons = updated_current_cons_view.cdr.as_ref().unwrap().clone();

                current_locked_cons.release_lock(updated_current_cons_perm);
                new_locked_cons.release_lock(new_cons_perm);
                return witness_token;
            } 
            // Otherwise, there is another LockedCons
            else {
                // Acquire the permissions to access the Cons:
                let next_locked_cons = current_cons_view.cdr.as_ref().unwrap().clone();
                let mut next_cons_perm = next_locked_cons.acquire_lock();
                let next_cons_view = next_locked_cons.cell.borrow(Tracked(next_cons_perm.borrow_mut()));

                // If a Cons with this value already exists:
                if (insert_car == next_cons_view.car) {

                    let tracked witness_token;
                    proof {
                        witness_token = current_locked_cons.instance.borrow().insert_fail(insert_car, next_cons_view.car).1.get();
                    }
                    // Return early and do nothing - the Cons exists.
                    current_locked_cons.release_lock(current_cons_perm);
                    next_locked_cons.release_lock(next_cons_perm);
                    return Tracked(witness_token);
                }

                // If the next Cons cdr is larger than the insert cdr:
                if (insert_car < next_cons_view.car) {
                    // Then we insert inbetween Cons and Cons
                    let (mut updated_current_cons_perm, new_cons_perm, witness_token) = current_locked_cons.insert_with_cdr(current_cons_perm, &next_cons_perm, insert_car);
                    let updated_current_cons_view = current_locked_cons.cell.borrow(Tracked(updated_current_cons_perm.borrow_mut()));
                    let new_locked_cons = updated_current_cons_view.cdr.as_ref().unwrap().clone();

                    current_locked_cons.release_lock(updated_current_cons_perm);
                    new_locked_cons.release_lock(new_cons_perm);
                    next_locked_cons.release_lock(next_cons_perm);
                    return witness_token;
                }

                // Otherwise, we give up the previous lock, and loop again
                current_locked_cons.release_lock(current_cons_perm);

                current_locked_cons = next_locked_cons;
                current_cons_perm = next_cons_perm;
            }
        }
    }

    fn delete_cons(&self, mut first_cons_perm: Tracked<PointsTo<Cons>>, mut delete_cons_perm: Tracked<PointsTo<Cons>>, delete_car: u32) -> ((updated_first_cons_perm, witness_token): (Tracked<PointsTo<Cons>>, Tracked<machine::operation_history>))
        requires
            self.wf(),
            first_cons_perm.is_init(),
            delete_cons_perm.is_init(),
            first_cons_perm.id() == self.cell.id(),
            first_cons_perm.value().car == self.view_car,
            first_cons_perm.value().car < delete_car,
            first_cons_perm.value().cdr.is_some(),
            first_cons_perm.value().cdr.unwrap().wf(),
            first_cons_perm.value().cdr.unwrap().view_car == delete_cons_perm.value().car,
            first_cons_perm.value().cdr.unwrap().instance == self.instance,
            delete_cons_perm.id() == first_cons_perm.value().cdr.unwrap().cell.id(),
            delete_cons_perm.value().car == delete_car,
            delete_cons_perm.value().cdr.is_some() ==> (
                delete_cons_perm.value().cdr.unwrap().wf() &&
                delete_cons_perm.value().cdr.unwrap().view_car > delete_car &&
                delete_cons_perm.value().cdr.unwrap().instance == self.instance
            ),
        ensures
            self.wf(),
            updated_first_cons_perm.is_init(),
            updated_first_cons_perm.id() == self.cell.id(),
            self.view_car == updated_first_cons_perm.value().car,
            updated_first_cons_perm.value().cdr == delete_cons_perm.value().cdr,
            updated_first_cons_perm.value().cdr.is_some() ==> (
                updated_first_cons_perm.value().cdr.unwrap().wf() &&
                updated_first_cons_perm.value().cdr.unwrap().view_car > delete_car &&
                updated_first_cons_perm.value().cdr.unwrap().instance == self.instance
            ),
            witness_token.instance_id() == self.instance.id(),
            witness_token.value() == Operation::Delete(delete_car)
    {
        let mut first_cons = self.cell.take(Tracked(first_cons_perm.borrow_mut()));
        let delete_cons = first_cons.cdr.as_ref().unwrap().cell.take(Tracked(delete_cons_perm.borrow_mut()));
        let upper = match delete_cons.cdr {
            Some(second_cons) => Some(second_cons.view_car@),
            _ => None,
        };
        first_cons.cdr = delete_cons.cdr;

        let tracked witness_token;
        proof {
            witness_token = self.instance.borrow().delete(Some(first_cons.car), delete_car, upper).1.get();
        }

        self.cell.put(Tracked(first_cons_perm.borrow_mut()), first_cons);
        return (first_cons_perm, Tracked(witness_token))
    }

    fn delete(self: Arc<Self>, mut current_cons_perm: Tracked<PointsTo<Cons>>, delete_car: u32) -> (witness_token: Tracked<machine::operation_history>)
        requires
            self.wf(),
            current_cons_perm.is_init(),
            current_cons_perm.id() == self.cell.id(),
            current_cons_perm.value().car == self.view_car,
            current_cons_perm.value().cdr.is_some() ==> 
                (
                    current_cons_perm.value().cdr.unwrap().wf() &&
                    current_cons_perm.value().cdr.unwrap().view_car > current_cons_perm.value().car &&
                    current_cons_perm.value().cdr.unwrap().instance == self.instance
                ),
            current_cons_perm.value().car < delete_car
        ensures
            self.wf(),
            witness_token.instance_id() == self.instance.id(),
            witness_token.value() == Operation::Delete(delete_car) || witness_token.value() == Operation::DeleteFail(delete_car)
    {
        let mut current_locked_cons = self;
        loop 
            invariant
                self.wf(),
                current_locked_cons.wf(),
                current_locked_cons.instance == self.instance,
                current_cons_perm.is_init(),
                current_cons_perm.id() == current_locked_cons.cell.id(),
                current_cons_perm.value().car == current_locked_cons.view_car,
                current_cons_perm.value().cdr.is_some() ==> 
                    (
                        current_cons_perm.value().cdr.unwrap().wf() &&
                        current_cons_perm.value().cdr.unwrap().view_car > current_cons_perm.value().car &&
                        current_cons_perm.value().cdr.unwrap().instance == self.instance
                    ),
                current_cons_perm.value().car < delete_car,
            decreases
                delete_car - current_cons_perm.value().car
        {
            let mut current_cons_view = current_locked_cons.cell.borrow(Tracked(current_cons_perm.borrow_mut()));

            // If there is no next LockedCons, then we have reached the tail.
            // If we have not deleted by now, then we are done, no nodes exist
            if (current_cons_view.cdr.is_none()) {
                let tracked witness_token;
                proof {
                    witness_token = self.instance.borrow().delete_fail(Some(current_cons_view.car), delete_car, None).1.get();
                }
                current_locked_cons.release_lock(current_cons_perm);
                return Tracked(witness_token);
            } 
            // Otherwise, there is another LockedCons
            else {
                // Acquire the permissions to access the Cons:
                let next_locked_cons = current_cons_view.cdr.as_ref().unwrap().clone();
                let mut next_cons_perm = next_locked_cons.acquire_lock();
                let next_cons_view = next_locked_cons.cell.borrow(Tracked(next_cons_perm.borrow_mut()));

                // If the next car is larger than our delete, then we have:
                // lower_car < delete_car < upper_car
                // Which means that no node exist with value delete_car.
                // We are done, no nodes exist
                if (delete_car < next_cons_view.car) {
                    let tracked witness_token;
                    proof {
                        witness_token = self.instance.borrow().delete_fail(Some(current_cons_view.car), delete_car, Some(next_cons_view.car)).1.get();
                    }
                    current_locked_cons.release_lock(current_cons_perm);
                    next_locked_cons.release_lock(next_cons_perm);
                    return Tracked(witness_token);
                }

                // Check if we are deleting the next LockedCons:
                if (delete_car == next_cons_view.car) {
                    let (updated_current_cons_perm, witness_token) = current_locked_cons.delete_cons(current_cons_perm, next_cons_perm, delete_car);

                    current_locked_cons.release_lock(updated_current_cons_perm);
                    return witness_token;
                }

                // Otherwise, we give up the previous lock, and loop again
                current_locked_cons.release_lock(current_cons_perm);
                current_locked_cons = next_locked_cons;
                current_cons_perm = next_cons_perm;
            }
        }
    }
}

pub struct LinkedList {
    locked_nil: Arc<LockedNil>,
}

impl LinkedList {
    pub closed spec fn wf(&self) -> bool
    {
        self.locked_nil.wf()
    }

    pub fn new() -> (linked_list: Self)
        ensures
            linked_list.wf()
    {
        Self { locked_nil: Arc::new(LockedNil::new()) }
    }

    pub fn insert(self, data: u32) 
        requires
            self.wf()
        ensures
            self.wf()
    {
        self.locked_nil.insert(data);
    }

    pub fn delete(self, data: u32) 
        requires
            self.wf()
        ensures
            self.wf()
    {
        self.locked_nil.delete(data);
    }
}

fn main() {
    let linked_list = Arc::new(LinkedList::new());
}
}