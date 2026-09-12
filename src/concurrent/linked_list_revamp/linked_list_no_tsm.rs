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
    cell::pcell_maybe_uninit::*,
    seq_lib::*,
};

verus! {

pub struct Nil {
    pub cdr: Option<Arc<LockedCons>>
}

struct_with_invariants!{
    pub struct LockedNil {
        atomic: AtomicBool<_, Option<PointsTo<Nil>>, _>,
        nil_cell: PCell<Nil>
    }

    spec fn wf(&self) -> bool 
    {
        invariant on atomic with (nil_cell) is (v: bool, option_perm: Option<PointsTo<Nil>>) {
            match option_perm {
                None => v == true,
                Some(perm) => {
                    &&& v == false
                    &&& perm.is_init()
                    &&& perm.id() == nil_cell.id()
                    &&& (
                            perm.value().cdr.is_some() ==>
                                perm.value().cdr.unwrap().wf()
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
        let nil = Nil { cdr: None::<Arc<LockedCons>> };
        let (nil_cell, Tracked(nil_perm)) = PCell::new(nil);

        let atomic = AtomicBool::new(Ghost(nil_cell), false, Tracked(Some(nil_perm)));
        Self { 
            atomic, 
            nil_cell
        }
    }

    fn acquire_lock(&self) -> (perm: Tracked<PointsTo<Nil>>)
        requires 
            self.wf(),
        ensures 
            perm.is_init(),
            perm.id() == self.nil_cell.id(),
            (
                perm.value().cdr.is_some() ==>
                    perm.value().cdr.unwrap().wf()
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

    fn release_lock(&self, perm: Tracked<PointsTo<Nil>>)
        requires
            perm.is_init(),
            perm.id() == self.nil_cell.id(),
            (
                perm.value().cdr.is_some() ==>
                    perm.value().cdr.unwrap().wf()
            ),
            self.wf()
        ensures
            self.wf()
    {
        atomic_with_ghost!(
            &self.atomic => store(false);
            ghost points_to_inv => {
                points_to_inv = Some(perm.get());
            }
        );
    }

    fn insert(self: Arc<Self>, insert_car: u32)
        requires
            self.wf()
        ensures
            self.wf()
    {
        // Acquire the lock for the nil node, and view the data inside (without taking)
        let mut nil_perm = self.acquire_lock();
        let nil_view = self.nil_cell.borrow(Tracked(&mut nil_perm));

        // If the nil cdr is none, then we must insert here - at the tail
        if (nil_view.cdr.is_none()) {

            let locked_cons = LockedCons::new(
                insert_car,  
                None::<Arc<LockedCons>>
            );

            let arc_locked_cons = Arc::new(locked_cons);

            let mut nil = self.nil_cell.take(Tracked(&mut nil_perm));
            nil.cdr = Some(arc_locked_cons.clone());
            self.nil_cell.put(Tracked(&mut nil_perm), nil);

            self.release_lock(nil_perm);
            return;
        } 
        else {
            // We check if we need to insert inbetween Nil and the first Cons

            let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
            let mut cons_perm = first_locked_cons.acquire_lock();
            let first_cons_view = first_locked_cons.cons_cell.borrow(Tracked(&mut cons_perm));

            // If a Cons with this value already exists:
            if (insert_car == first_cons_view.car) {
                // Return early and do nothing - the Cons exists.
                self.release_lock(nil_perm);
                first_locked_cons.release_lock(cons_perm);
                return;
            }

            // If the first Cons cdr is larger than the insert cdr:
            if (insert_car < first_cons_view.car) {
                // Then we insert inbetween Nil and first Cons
                let locked_cons = LockedCons::new(
                    insert_car,  
                    Some(first_locked_cons.clone())
                );

                let arc_locked_cons = Arc::new(locked_cons);

                let mut nil = self.nil_cell.take(Tracked(&mut nil_perm));
                nil.cdr = Some(arc_locked_cons.clone());
                self.nil_cell.put(Tracked(&mut nil_perm), nil);

                self.release_lock(nil_perm);
                first_locked_cons.release_lock(cons_perm);
                return;
            }

            // If we have reached here, we may release the nil lock:
            self.release_lock(nil_perm);

            // Any insert from here onwards will not involve nil - 
            // we may delegate the insert to a chain of LockedCons
            first_locked_cons.insert(insert_car, cons_perm);
        }
    }

    fn delete(self: Arc<Self>, delete_car: u32)
        requires
            self.wf()
        ensures
            self.wf()
    {
        // Acquire the lock for the nil node, and view the data inside (without taking)
        let mut nil_perm = self.acquire_lock();
        let nil_view = self.nil_cell.borrow(Tracked(&mut nil_perm));

        // If the nil cdr is none, then we are done - no tokens exist ==> no nodes exist
        if (nil_view.cdr.is_none()) {
            self.release_lock(nil_perm);
            return;
        }

        // We check if we need to delete the first Cons (hence lower is LockedNil)
        let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
        let mut cons_perm = first_locked_cons.acquire_lock();
        let first_cons_view = first_locked_cons.cons_cell.borrow(Tracked(&mut cons_perm));

        // If the first car is larger than our delete, then we are done - no tokens exist ==> no nodes exist
        if (delete_car < first_cons_view.car) {
            self.release_lock(nil_perm);
            first_locked_cons.release_lock(cons_perm);
            return;
        }

        // Check if we are deleting the first LockedCons:
        if (delete_car == first_cons_view.car) {
            let mut nil = self.nil_cell.take(Tracked(&mut nil_perm));
            let mut first_cons = first_locked_cons.cons_cell.take(Tracked(&mut cons_perm));


            nil.cdr = first_cons.cdr;
            self.nil_cell.put(Tracked(&mut nil_perm), nil);

            self.release_lock(nil_perm);

            return;
        }
        
        // We can release the dummy node lock.
        self.release_lock(nil_perm);
        // // and begin our traversal:
        first_locked_cons.delete(delete_car, cons_perm);
    }
}

pub struct Cons {
    pub car: u32,
    pub cdr: Option<Arc<LockedCons>>,
}

struct_with_invariants!{
    pub struct LockedCons {
        atomic: AtomicBool<_, Option<PointsTo<Cons>>, _>,
        cons_cell: PCell<Cons>,
        ghost view_car: u32,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant on atomic with (cons_cell, view_car) is (v: bool, option_perm: Option<PointsTo<Cons>>) {
            match option_perm {
                None => v == true,
                Some(perm) => {
                    &&& v == false
                    &&& perm.is_init()
                    &&& perm.id() == cons_cell.id()
                    &&& perm.value().car == view_car
                    &&& (
                            perm.value().cdr.is_some() ==>
                                perm.value().cdr.unwrap().wf() &&
                                perm.value().car < perm.value().cdr.unwrap().view_car()
                        )
                }
            }
        }
    }
}

impl LockedCons {
    pub closed spec fn view_car(&self) -> (view_car: u32)
    {
        self.view_car@
    }

    fn new(car: u32, cdr: Option<Arc<LockedCons>>) -> (locked_cons: Self)
        requires
            (
               cdr.is_some() ==>
                    cdr.unwrap().wf() &&
                    car < cdr.unwrap().view_car()
            )
        ensures 
            locked_cons.wf(),
            locked_cons.view_car() == car
    {   
        let cons = Cons { car, cdr };
        let (cons_cell, Tracked(cons_perm)) = PCell::new(cons);
        let atomic = AtomicBool::new(Ghost((cons_cell, car)), false, Tracked(Some(cons_perm)));
        Self { atomic, cons_cell, view_car: car }
    }

    fn acquire_lock(&self) -> (perm: Tracked<PointsTo<Cons>>)
        requires 
            self.wf(),
        ensures 
            perm.is_init(),
            perm.id() == self.cons_cell.id(),
            perm.value().car == self.view_car,
            (
                perm.value().cdr.is_some() ==>
                    perm.value().cdr.unwrap().wf() &&
                    perm.value().car < perm.value().cdr.unwrap().view_car()
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

    fn release_lock(&self, perm: Tracked<PointsTo<Cons>>)
        requires
            self.wf(),
            perm.is_init(),
            perm.id() == self.cons_cell.id(),
            perm.value().car == self.view_car,
            (
                perm.value().cdr.is_some() ==>
                    perm.value().cdr.unwrap().wf() &&
                    perm.value().car < perm.value().cdr.unwrap().view_car()
            )
        ensures
            self.wf()
    {
        atomic_with_ghost!(
            &self.atomic => store(false);
            ghost points_to_inv => {
                points_to_inv = Some(perm.get());
            }
        );
    }

    fn insert(self: Arc<Self>, insert_car: u32, mut cons_perm: Tracked<PointsTo<Cons>>)
        requires
            self.wf(),
            cons_perm.is_init(),
            cons_perm.id() == self.cons_cell.id(),
            cons_perm.value().car == self.view_car,
            (
                cons_perm.value().cdr.is_some() ==>
                    cons_perm.value().cdr.unwrap().wf() &&
                    cons_perm.value().car < cons_perm.value().cdr.unwrap().view_car()
            ),
            cons_perm.value().car < insert_car
        ensures
            self.wf()
    {
        let mut current_locked_cons = self;
        loop 
            invariant
                self.wf(),
                current_locked_cons.wf(),
                cons_perm.is_init(),
                cons_perm.id() == current_locked_cons.cons_cell.id(),
                cons_perm.value().car == current_locked_cons.view_car(),
                (
                    cons_perm.value().cdr.is_some() ==>
                        cons_perm.value().cdr.unwrap().wf() &&
                        cons_perm.value().car < cons_perm.value().cdr.unwrap().view_car()
                ),
                cons_perm.value().car < insert_car
            decreases
                insert_car - cons_perm.value().car
        {
            let mut current_cons_view = current_locked_cons.cons_cell.borrow(Tracked(&mut cons_perm));

            // If there is no next LockedCons, then we must insert at the tail after a Cons
            if (current_cons_view.cdr.is_none()) {

                let mut old_tail_cons = current_locked_cons.cons_cell.take(Tracked(&mut cons_perm));

                let locked_cons = LockedCons::new(
                    insert_car, 
                    None::<Arc<LockedCons>>
                );

                old_tail_cons.cdr = Some(Arc::new(locked_cons));
                current_locked_cons.cons_cell.put(Tracked(&mut cons_perm), old_tail_cons);
                current_locked_cons.release_lock(cons_perm);

                return;
            } 
            // Otherwise, there is another LockedCons
            else {
                // Acquire the permissions to access the Cons:
                let next_locked_cons = current_cons_view.cdr.as_ref().unwrap().clone();
                let mut next_cons_perm = next_locked_cons.acquire_lock();
                let next_cons_view = next_locked_cons.cons_cell.borrow(Tracked(&mut next_cons_perm));

                // If a Cons with this value already exists:
                if (insert_car == next_cons_view.car) {
                    // Return early and do nothing - the Cons exists.
                    current_locked_cons.release_lock(cons_perm);
                    next_locked_cons.release_lock(next_cons_perm);
                    return;
                }

                // If the next Cons cdr is larger than the insert cdr:
                if (insert_car < next_cons_view.car) {

                    // Then we insert inbetween Cons and Cons
                    let mut current_cons = current_locked_cons.cons_cell.take(Tracked(&mut cons_perm));


                    let locked_cons = LockedCons::new(
                        insert_car, 
                        Some(next_locked_cons.clone())
                    );

                    current_cons.cdr = Some(Arc::new(locked_cons));

                    current_locked_cons.cons_cell.put(Tracked(&mut cons_perm), current_cons);

                    current_locked_cons.release_lock(cons_perm);
                    next_locked_cons.release_lock(next_cons_perm);
                    return;
                }

                // Otherwise, we give up the previous lock, and loop again
                current_locked_cons.release_lock(cons_perm);

                current_locked_cons = next_locked_cons;
                cons_perm = next_cons_perm;
            }
        }
    }

    fn delete(self: Arc<Self>, delete_car: u32, mut cons_perm: Tracked<PointsTo<Cons>>)
        requires
            self.wf(),
            cons_perm.is_init(),
            cons_perm.id() == self.cons_cell.id(),
            cons_perm.value().car == self.view_car,
            (
                cons_perm.value().cdr.is_some() ==>
                    cons_perm.value().cdr.unwrap().wf() &&
                    cons_perm.value().car < cons_perm.value().cdr.unwrap().view_car()
            ),
            cons_perm.value().car < delete_car
        ensures
            self.wf()
    {
        let mut current_locked_cons = self;
        loop 
            invariant
                self.wf(),
                current_locked_cons.wf(),
                cons_perm.is_init(),
                cons_perm.id() == current_locked_cons.cons_cell.id(),
                cons_perm.value().car == current_locked_cons.view_car(),
                (
                    cons_perm.value().cdr.is_some() ==>
                        cons_perm.value().cdr.unwrap().wf() &&
                        cons_perm.value().car < cons_perm.value().cdr.unwrap().view_car()
                ),
                cons_perm.value().car < delete_car
            // decreases
            //     delete_car_raw - current_cons_perm.value().car
        {
            let mut current_cons_view = current_locked_cons.cons_cell.borrow(Tracked(&mut cons_perm));

            // If there is no next LockedCons, then we have reached the tail.
            // If we have not deleted by now, then we are done - no tokens exist ==> no nodes exist
            if (current_cons_view.cdr.is_none()) {
                current_locked_cons.release_lock(cons_perm);
                return;
            } 
            // Otherwise, there is another LockedCons
            else {
                // Acquire the permissions to access the Cons:
                let next_locked_cons = current_cons_view.cdr.as_ref().unwrap().clone();
                let mut next_cons_perm = next_locked_cons.acquire_lock();
                let next_cons_view = next_locked_cons.cons_cell.borrow(Tracked(&mut next_cons_perm));

                // If the next car is larger than our delete, then we have:
                // lower_car < delete_car < upper_car
                // Which means that no node exist with value delete_car.
                // We are done - no tokens exist ==> no nodes exist
                if (delete_car < next_cons_view.car) {
                    current_locked_cons.release_lock(cons_perm);
                    next_locked_cons.release_lock(next_cons_perm);
                    return;
                }

                // Check if we are deleting this LockedCons:
                if (delete_car == next_cons_view.car) {
                    let mut current_cons = current_locked_cons.cons_cell.take(Tracked(&mut cons_perm));
                    let mut next_cons = next_locked_cons.cons_cell.take(Tracked(&mut next_cons_perm));


                    current_cons.cdr = next_cons.cdr;

                    current_locked_cons.cons_cell.put(Tracked(&mut cons_perm), current_cons);
                    current_locked_cons.release_lock(cons_perm);
                    return;
                }

                // Otherwise, we give up the previous lock, and loop again
                current_locked_cons.release_lock(cons_perm);
                current_locked_cons = next_locked_cons;
                cons_perm = next_cons_perm;
            }
        }
    }
}

fn main() {
}
}