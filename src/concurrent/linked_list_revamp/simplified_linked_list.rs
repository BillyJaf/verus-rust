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

pub struct ListHead {
    pub nil_perm: PointsTo<Nil>,
    pub cons_perm: Option<PointsTo<Cons>>
}

#[verifier::accept_recursive_types]
tokenized_state_machine!{
    machine {
        fields {
            #[sharding(variable)]
            pub list_head: ListHead,

            #[sharding(map)]
            pub list_representation: Map<PointsTo<Cons>, Option<PointsTo<Cons>>>,
        }

        init!{
            initialize(nil_perm: PointsTo<Nil>)
            {
                init list_head = ListHead { nil_perm, cons_perm: None };
                init list_representation = Map::empty();
            }
        }

        // Insert

        transition!{
            empty_list_insert(lower_car: PointsTo<Nil>, insert_car: PointsTo<Cons>)
            {   
                
            }
        }

        transition!{
            insert_at_head(lower_car: PointsTo<Nil>, insert_car: PointsTo<Cons>, upper_car: PointsTo<Cons>)
            {   
                
            }
        }

        transition!{
            insert(lower_car: PointsTo<Cons>, insert_car: PointsTo<Cons>, upper_car: PointsTo<Cons>)
            {   
                
            }
        }

        transition!{
            insert_at_tail(lower_car: PointsTo<Cons>, insert_car: PointsTo<Cons>)
            {   
                
            }
        }

        // Delete

        transition!{
            one_elem_delete(lower_car: PointsTo<Nil>, delete_car: PointsTo<Cons>)
            {   
                
            }
        }

        transition!{
            delete_at_head(lower_car: PointsTo<Nil>, delete_car: PointsTo<Cons>, upper_car: PointsTo<Cons>)
            {   
                
            }
        }

        transition!{
            delete(lower_car: PointsTo<Cons>, delete_car: PointsTo<Cons>, upper_car: PointsTo<Cons>)
            {   
                
            }
        }

        transition!{
            delete_at_tail(lower_car: PointsTo<Cons>, delete_car: PointsTo<Cons>)
            {   
                
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, nil_perm: PointsTo<Nil>) {
        }
    }
}

pub struct Nil {
    pub cdr: Option<Arc<LockedCons>>
}

pub tracked struct PermAndToken {
    pub perm: PointsTo<Nil>,
    pub map_token: machine::list_head
}

struct_with_invariants!{
    pub struct LockedNil {
        atomic: AtomicBool<_, Option<PermAndToken>, _>,
        cell: PCell<Nil>,
        instance: Tracked<machine::Instance>,
    }

    spec fn wf(&self) -> bool 
    {
        invariant on atomic with (cell, instance) is (v: bool, option_pat: Option<PermAndToken>) {
            match option_pat {
                None => v == true,
                Some(pat) => {
                    &&& v == false
                    &&& pat.perm.is_init()
                    &&& pat.perm.id() == cell.id()
                    &&& pat.map_token.instance_id() == instance.id()
                    &&& pat.map_token.value().nil_perm == pat.perm
                    &&& (pat.map_token.value().cons_perm.is_none() <==> pat.perm.value().cdr.is_none()) 
                    &&& (pat.map_token.value().cons_perm.is_some() ==> 
                            (
                                pat.perm.value().cdr.unwrap().wf() &&
                                // pat.perm.value().cdr.unwrap().view_instance() == instance &&
                                pat.perm.value().cdr.unwrap().view_car() == pat.map_token.value().cons_perm.unwrap().value().car
                            )
                        )
                }
            }
        }
    }
}

// impl LockedNil {
//     fn new() -> (locked_nil: Self)
//         ensures 
//             locked_nil.wf(),
//     {
//         let (cell, Tracked(perm)) = PCell::empty();

//         let tracked (
//             Tracked(instance),
//             Tracked(list_representation)
//         ) = machine::Instance::initialize();

//         let tracked map_token;
//         proof {
//             map_token = list_representation.remove(None);
//         }

//         let node = Nil { cdr: None::<Arc<LockedCons>>, map_token: Tracked(map_token) };
//         let (cell, Tracked(perm)) = PCell::new(node);


//         let atomic = AtomicBool::new(Ghost((cell, Tracked(instance))), false, Tracked(Some(perm)));
//         Self { 
//             atomic, 
//             cell, 
//             instance: Tracked(instance)
//         }
//     }

//     fn acquire_lock(&self) -> (points_to: Tracked<PointsTo<Nil>>)
//         requires 
//             self.wf(),
//         ensures 
//             points_to.is_init(),
//             points_to.id() == self.cell.id(),
//             points_to.value().map_token.instance_id() == self.instance.id(),
//             points_to.value().map_token.key() == None::<u32>,
//             (points_to.value().map_token.value().is_none() <==> points_to.value().cdr.is_none()),
//             (points_to.value().map_token.value().is_some() ==> 
//                 (
//                     points_to.value().cdr.unwrap().wf() &&
//                     points_to.value().cdr.unwrap().view_instance() == self.instance &&
//                     points_to.value().cdr.unwrap().view_car() == points_to.value().map_token.value().unwrap()
//                 )
//             ),
//             self.wf()
//     {
//         loop
//             invariant self.wf(),
//         {
//             let tracked mut points_to_opt = None;
//             let res = atomic_with_ghost!(
//                 &self.atomic => compare_exchange(false, true);
//                 ghost points_to_inv => {
//                     tracked_swap(&mut points_to_opt, &mut points_to_inv);
//                 }
//             );
//             if res.is_ok() {
//                 return Tracked(points_to_opt.tracked_unwrap());
//             }
//         }
//     }

    // fn release_lock(&self, points_to: Tracked<PointsTo<Nil>>)
    //     requires
    //         self.wf(),
    //         points_to.is_init(),
    //         points_to.id() == self.cell.id(),
    //         points_to.value().map_token.instance_id() == self.instance.id(),
    //         points_to.value().map_token.key() == None::<u32>,
    //         (points_to.value().map_token.value().is_none() <==> points_to.value().cdr.is_none()),
    //         (points_to.value().map_token.value().is_some() ==> 
    //             (
    //                 points_to.value().cdr.unwrap().wf() &&
    //                 points_to.value().cdr.unwrap().view_instance() == self.instance &&
    //                 points_to.value().cdr.unwrap().view_car() == points_to.value().map_token.value().unwrap()
    //             )
    //         )
    //     ensures
    //         self.wf()
    // {
    //     atomic_with_ghost!(
    //         &self.atomic => store(false);
    //         ghost points_to_inv => {
    //             points_to_inv = Some(points_to.get());
    //         }
    //     );
    // }
// }
//     fn insert(self: Arc<Self>, insert_car_raw: u32)
//         requires
//             self.wf()
//         ensures
//             self.wf()
//     {
//         // Acquire the lock for the nil node, and view the data inside (without taking)
//         let mut nil_perm = self.acquire_lock();
//         let nil_view = self.cell.borrow(Tracked(nil_perm.borrow_mut()));
//         let insert_car = NodeData::CAR(insert_car_raw);

//         // If the nil cdr is none, then we must insert here - at the tail
//         if (nil_view.cdr.is_none()) {

//             let mut nil = self.cell.take(Tracked(nil_perm.borrow_mut()));

//             let tracked token_tuple;
//             let tracked updated_nil_token;
//             let tracked cons_token;

//             proof {
//                 token_tuple = self.instance.borrow().insert(
//                     self.view_car(), 
//                     insert_car, 
//                     nil.map_token.value(), 
//                     nil.map_token.get()
//                 );
//                 updated_nil_token = token_tuple.0.get();
//                 cons_token = token_tuple.1.get();
//             }

//             let locked_cons = LockedCons::new(
//                 insert_car_raw, 
//                 Tracked(cons_token), 
//                 None::<Arc<LockedCons>>, 
//                 self.instance.clone()
//             );

//             nil.cdr = Some(Arc::new(locked_cons));
//             nil.map_token = Tracked(updated_nil_token);
//             self.cell.put(Tracked(nil_perm.borrow_mut()), nil);
//             self.release_lock(nil_perm);
//             return;
//         } 
//         else {
//             // We check if we need to insert inbetween Nil and the first Cons
//             let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
//             let mut first_cons_perm = first_locked_cons.acquire_lock();
//             let first_cons_view = first_locked_cons.cell.borrow(Tracked(first_cons_perm.borrow_mut()));

//             // If a Cons with this value already exists:
//             if (insert_car_raw == first_cons_view.car) {
//                 // Return early and do nothing - the Cons exists.
//                 self.release_lock(nil_perm);
//                 first_locked_cons.release_lock(first_cons_perm);
//                 return;
//             }

//             // If the first Cons cdr is larger than the insert cdr:
//             if (insert_car_raw < first_cons_view.car) {

//                 // Then we insert inbetween Nil and first Cons
//                 let mut nil = self.cell.take(Tracked(nil_perm.borrow_mut()));

//                 let tracked token_tuple;
//                 let tracked updated_nil_token;
//                 let tracked cons_token;

//                 proof {
//                     token_tuple = self.instance.borrow().insert(
//                         self.view_car(), 
//                         insert_car, 
//                         nil.map_token.value(), 
//                         nil.map_token.get()
//                     );
//                     updated_nil_token = token_tuple.0.get();
//                     cons_token = token_tuple.1.get();
//                 }

//                 let locked_cons = LockedCons::new(
//                     insert_car_raw, 
//                     Tracked(cons_token), 
//                     Some(first_locked_cons.clone()), 
//                     self.instance.clone()
//                 );

//                 nil.cdr = Some(Arc::new(locked_cons));
//                 nil.map_token = Tracked(updated_nil_token);

//                 self.cell.put(Tracked(nil_perm.borrow_mut()), nil);

//                 self.release_lock(nil_perm);
//                 first_locked_cons.release_lock(first_cons_perm);
//                 return;
//             }

//             // If we have reached here, we may release the nil lock:
//             self.release_lock(nil_perm);

//             // Any insert from here onwards will not involve nil - 
//             // we may delegate the insert to a chain of LockedCons
//             first_locked_cons.insert(first_cons_perm, insert_car_raw);
//         }
//     }

//     fn delete(self: Arc<Self>, delete_car_raw: u32)
//         requires
//             self.wf()
//         ensures
//             self.wf()
//     {
//         let delete_car = NodeData::CAR(delete_car_raw);
//         // Acquire the lock for the nil node, and view the data inside (without taking)
//         let mut nil_perm = self.acquire_lock();
//         let nil_view = self.cell.borrow(Tracked(nil_perm.borrow_mut()));

//         // If the nil cdr is none, then we are done - no tokens exist ==> no nodes exist
//         if (nil_view.cdr.is_none()) {
//             proof {
//                 self.instance.delete_successful_empty_list(delete_car, nil_view.map_token.borrow());
//             }
//             self.release_lock(nil_perm);
//             return;
//         }

//         // We check if we need to delete the first Cons (hence lower is LockedNil)
//         let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
//         let mut first_cons_perm = first_locked_cons.acquire_lock();
//         let first_cons_view = first_locked_cons.cell.borrow(Tracked(first_cons_perm.borrow_mut()));

//         // If the first car is larger than our delete, then we are done - no tokens exist ==> no nodes exist
//         if (delete_car_raw < first_cons_view.car) {
//             proof {
//                 self.instance.delete_successful_car_not_in_list(
//                     self.view_car(), 
//                     delete_car, 
//                     nil_view.map_token.value(), 
//                     nil_view.map_token.borrow()
//                 );
//             }
//             self.release_lock(nil_perm);
//             first_locked_cons.release_lock(first_cons_perm);
//             return;
//         }

//         // Check if we are deleting the first LockedCons:
//         if (delete_car_raw == first_cons_view.car) {
//             let mut nil = self.cell.take(Tracked(nil_perm.borrow_mut()));
//             let mut first_cons = first_locked_cons.cell.take(Tracked(first_cons_perm.borrow_mut()));

//             let tracked updated_nil_token;

//             proof {
//                 updated_nil_token = self.instance.borrow().delete(
//                     self.view_car(), 
//                     delete_car, 
//                     first_cons.map_token.value(), 
//                     nil.map_token.get(),
//                     first_cons.map_token.get()
//                 );
//             }

//             nil.map_token = Tracked(updated_nil_token);
//             nil.cdr = first_cons.cdr;

//             proof {
//                 self.instance.delete_successful_car_not_in_list(
//                     self.view_car(), 
//                     delete_car, 
//                     nil.map_token.value(), 
//                     nil.map_token.borrow()
//                 );
//             }

//             self.cell.put(Tracked(nil_perm.borrow_mut()), nil);
//             self.release_lock(nil_perm);

//             return;
//         }
        
//         // We can release the dummy node lock.
//         self.release_lock(nil_perm);
//         // and begin our traversal:
//         first_locked_cons.delete(first_cons_perm, delete_car_raw);
//     }
// }

pub struct Cons {
    pub car: u32,
    pub cdr: Option<Arc<LockedCons>>,
}

pub tracked struct PermAndToken2 {
    pub perm: PointsTo<Nil>
}

struct_with_invariants!{
    pub struct LockedCons {
        atomic: AtomicBool<_, Option<PermAndToken2>, _>,
        cell: PCell<Cons>,
        instance: Tracked<machine::Instance>,
        view_car: Ghost<u32>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant on atomic with (cell, instance, view_car) is (v: bool, g: Option<PermAndToken2>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    true
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

    // pub closed spec fn view_instance(&self) -> (instance: machine::Instance)
    // {
    //     self.instance@
    // }

    // fn new(car: u32, map_token: Tracked<machine::data_map>, cdr: Option<Arc<LockedCons>>, instance: Tracked<machine::Instance>) -> (new_cons: Self)
    //     requires
    //         map_token@.instance_id() == instance@.id(),
    //         map_token@.key() == NodeData::CAR(car),
    //         map_token@.value().is_none() <==> cdr.is_none(),
    //         map_token@.value().is_some() ==> (
    //             cdr.unwrap().wf() &&
    //             cdr.unwrap().view_instance() == instance &&
    //             cdr.unwrap().view_car() > NodeData::CAR(car) &&
    //             cdr.unwrap().view_car() == map_token@.value().unwrap()
    //         ),
    //     ensures 
    //         new_cons.wf(),
    //         new_cons.instance == instance,
    //         new_cons.view_car == NodeData::CAR(car),
    // {   
    //     let view_car = Ghost(NodeData::CAR(car));
    //     let node = Cons { car, cdr, map_token: map_token };
    //     let (cell, Tracked(perm)) = PCell::new(node);
    //     let atomic = AtomicBool::new(Ghost((cell, instance, view_car)), false, Tracked(Some(perm)));
    //     Self { atomic, cell, instance, view_car }
    // }

    // fn acquire_lock(&self) -> (points_to: Tracked<PointsTo<Cons>>)
    //     requires 
    //         self.wf(),
    //     ensures 
    //         points_to.is_init(),
    //         points_to.id() == self.cell.id(),
    //         NodeData::CAR(points_to.value().car) == self.view_car,
    //         points_to.value().map_token@.instance_id() == self.instance@.id(),
    //         points_to.value().map_token@.key() == NodeData::CAR(points_to.value().car),
    //         (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()), 
    //         (points_to.value().map_token@.value().is_some() ==> 
    //             (
    //                 points_to.value().cdr.unwrap().wf() &&
    //                 points_to.value().cdr.unwrap().view_instance() == self.instance &&
    //                 points_to.value().cdr.unwrap().view_car() > NodeData::CAR(points_to.value().car) &&
    //                 points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
    //             )
    //         ),
    //         self.wf()
    // {
    //     loop
    //         invariant self.wf(),
    //     {
    //         let tracked mut points_to_opt = None;
    //         let res = atomic_with_ghost!(
    //             &self.atomic => compare_exchange(false, true);
    //             ghost points_to_inv => {
    //                 tracked_swap(&mut points_to_opt, &mut points_to_inv);
    //             }
    //         );
    //         if res.is_ok() {
    //             return Tracked(points_to_opt.tracked_unwrap());
    //         }
    //     }
    // }

    // fn release_lock(&self, points_to: Tracked<PointsTo<Cons>>)
    //     requires
    //         self.wf(),
    //         points_to.is_init(),
    //         points_to.id() == self.cell.id(),
    //         NodeData::CAR(points_to.value().car) == self.view_car,
    //         points_to.value().map_token@.instance_id() == self.instance@.id(),
    //         points_to.value().map_token@.key() == NodeData::CAR(points_to.value().car),
    //         (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()), 
    //         (points_to.value().map_token@.value().is_some() ==> 
    //             (
    //                 points_to.value().cdr.unwrap().wf() &&
    //                 points_to.value().cdr.unwrap().view_instance() == self.instance &&
    //                 points_to.value().cdr.unwrap().view_car() > NodeData::CAR(points_to.value().car) &&
    //                 points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
    //             )
    //         ),
    //     ensures
    //         self.wf()
    // {
    //     atomic_with_ghost!(
    //         &self.atomic => store(false);
    //         ghost points_to_inv => {
    //             points_to_inv = Some(points_to.get());
    //         }
    //     );
    // }

    // fn insert(self: Arc<Self>, mut current_cons_perm: Tracked<PointsTo<Cons>>, insert_car_raw: u32)
    //     requires
    //         self.wf(),
    //         current_cons_perm.is_init(),
    //         current_cons_perm.id() == self.cell.id(),
    //         NodeData::CAR(current_cons_perm.value().car) == self.view_car,
    //         current_cons_perm.value().map_token@.instance_id() == self.instance@.id(),
    //         current_cons_perm.value().map_token@.key() == NodeData::CAR(current_cons_perm.value().car),
    //         (current_cons_perm.value().map_token@.value().is_none() <==> current_cons_perm.value().cdr.is_none()), 
    //         (current_cons_perm.value().map_token@.value().is_some() ==> 
    //             (
    //                 current_cons_perm.value().cdr.unwrap().wf() &&
    //                 current_cons_perm.value().cdr.unwrap().view_instance() == self.instance &&
    //                 current_cons_perm.value().cdr.unwrap().view_car() > NodeData::CAR(current_cons_perm.value().car) &&
    //                 current_cons_perm.value().cdr.unwrap().view_car() == current_cons_perm.value().map_token@.value().unwrap()
    //             )
    //         ),
    //         current_cons_perm.value().car < insert_car_raw
    //     ensures
    //         self.wf()
    // {
    //     let insert_car = NodeData::CAR(insert_car_raw);
    //     let mut current_locked_cons = self;
    //     loop 
    //         invariant
    //             self.wf(),
    //             current_locked_cons.wf(),
    //             current_cons_perm.is_init(),
    //             current_cons_perm.id() == current_locked_cons.cell.id(),
    //             NodeData::CAR(current_cons_perm.value().car) == current_locked_cons.view_car,
    //             current_cons_perm.value().map_token@.instance_id() == current_locked_cons.instance@.id(),
    //             current_cons_perm.value().map_token@.key() == NodeData::CAR(current_cons_perm.value().car),
    //             (current_cons_perm.value().map_token@.value().is_none() <==> current_cons_perm.value().cdr.is_none()), 
    //             (current_cons_perm.value().map_token@.value().is_some() ==> 
    //                 (
    //                     current_cons_perm.value().cdr.unwrap().wf() &&
    //                     current_cons_perm.value().cdr.unwrap().view_instance() == current_locked_cons.instance &&
    //                     current_cons_perm.value().cdr.unwrap().view_car() > NodeData::CAR(current_cons_perm.value().car) &&
    //                     current_cons_perm.value().cdr.unwrap().view_car() == current_cons_perm.value().map_token@.value().unwrap()
    //                 )
    //             ),
    //             current_cons_perm.value().car < insert_car_raw,
    //             insert_car == NodeData::CAR(insert_car_raw)
    //         decreases
    //             insert_car_raw - current_cons_perm.value().car
    //     {
    //         let mut current_cons_view = current_locked_cons.cell.borrow(Tracked(current_cons_perm.borrow_mut()));

    //         // If there is no next LockedCons, then we must insert at the tail after a Cons
    //         if (current_cons_view.cdr.is_none()) {

    //             let mut old_tail_cons = current_locked_cons.cell.take(Tracked(current_cons_perm.borrow_mut()));

    //             let tracked token_tuple;
    //             let tracked updated_old_tail_cons_token;
    //             let tracked new_tail_cons_token;

    //             proof {
    //                 token_tuple = current_locked_cons.instance.borrow().insert(
    //                     current_locked_cons.view_car(), 
    //                     insert_car, 
    //                     old_tail_cons.map_token.value(), 
    //                     old_tail_cons.map_token.get()
    //                 );
    //                 updated_old_tail_cons_token = token_tuple.0.get();
    //                 new_tail_cons_token = token_tuple.1.get();
    //             }

    //             let locked_cons = LockedCons::new(
    //                 insert_car_raw, 
    //                 Tracked(new_tail_cons_token), 
    //                 None::<Arc<LockedCons>>, 
    //                 current_locked_cons.instance.clone()
    //             );

    //             old_tail_cons.cdr = Some(Arc::new(locked_cons));
    //             old_tail_cons.map_token = Tracked(updated_old_tail_cons_token);

    //             current_locked_cons.cell.put(Tracked(current_cons_perm.borrow_mut()), old_tail_cons);
    //             current_locked_cons.release_lock(current_cons_perm);

    //             return;
    //         } 
    //         // Otherwise, there is another LockedCons
    //         else {
    //             // Acquire the permissions to access the Cons:
    //             let next_locked_cons = current_cons_view.cdr.as_ref().unwrap().clone();
    //             let mut next_cons_perm = next_locked_cons.acquire_lock();
    //             let next_cons_view = next_locked_cons.cell.borrow(Tracked(next_cons_perm.borrow_mut()));

    //             // If a Cons with this value already exists:
    //             if (insert_car_raw == next_cons_view.car) {
    //                 // Return early and do nothing - the Cons exists.
    //                 current_locked_cons.release_lock(current_cons_perm);
    //                 next_locked_cons.release_lock(next_cons_perm);
    //                 return;
    //             }

    //             // If the next Cons cdr is larger than the insert cdr:
    //             if (insert_car_raw < next_cons_view.car) {

    //                 // Then we insert inbetween Cons and Cons
    //                 let mut current_cons = current_locked_cons.cell.take(Tracked(current_cons_perm.borrow_mut()));

    //                 let tracked token_tuple;
    //                 let tracked updated_cons_token;
    //                 let tracked new_cons_token;

    //                 proof {
    //                     token_tuple = current_locked_cons.instance.borrow().insert(
    //                         current_locked_cons.view_car(), 
    //                         insert_car, 
    //                         current_cons.map_token.value(), 
    //                         current_cons.map_token.get()
    //                     );
    //                     updated_cons_token = token_tuple.0.get();
    //                     new_cons_token = token_tuple.1.get();
    //                 }

    //                 let locked_cons = LockedCons::new(
    //                     insert_car_raw, 
    //                     Tracked(new_cons_token), 
    //                     Some(next_locked_cons.clone()), 
    //                     current_locked_cons.instance.clone()
    //                 );

    //                 current_cons.cdr = Some(Arc::new(locked_cons));
    //                 current_cons.map_token = Tracked(updated_cons_token);

    //                 current_locked_cons.cell.put(Tracked(current_cons_perm.borrow_mut()), current_cons);

    //                 current_locked_cons.release_lock(current_cons_perm);
    //                 next_locked_cons.release_lock(next_cons_perm);
    //                 return;
    //             }

    //             // Otherwise, we give up the previous lock, and loop again
    //             current_locked_cons.release_lock(current_cons_perm);

    //             current_locked_cons = next_locked_cons;
    //             current_cons_perm = next_cons_perm;
    //         }
    //     }
    // }

    // fn delete(self: Arc<Self>, mut current_cons_perm: Tracked<PointsTo<Cons>>, delete_car_raw: u32)
    //     requires
    //         self.wf(),
    //         current_cons_perm.is_init(),
    //         current_cons_perm.id() == self.cell.id(),
    //         NodeData::CAR(current_cons_perm.value().car) == self.view_car,
    //         current_cons_perm.value().map_token@.instance_id() == self.instance@.id(),
    //         current_cons_perm.value().map_token@.key() == NodeData::CAR(current_cons_perm.value().car),
    //         (current_cons_perm.value().map_token@.value().is_none() <==> current_cons_perm.value().cdr.is_none()), 
    //         (current_cons_perm.value().map_token@.value().is_some() ==> 
    //             (
    //                 current_cons_perm.value().cdr.unwrap().wf() &&
    //                 current_cons_perm.value().cdr.unwrap().view_instance() == self.instance &&
    //                 current_cons_perm.value().cdr.unwrap().view_car() > NodeData::CAR(current_cons_perm.value().car) &&
    //                 current_cons_perm.value().cdr.unwrap().view_car() == current_cons_perm.value().map_token@.value().unwrap()
    //             )
    //         ),
    //         current_cons_perm.value().car < delete_car_raw
    //     ensures
    //         self.wf()
    // {
    //     let delete_car = NodeData::CAR(delete_car_raw);
    //     let mut current_locked_cons = self;
    //     loop 
    //         invariant
    //             self.wf(),
    //             current_locked_cons.wf(),
    //             current_cons_perm.is_init(),
    //             current_cons_perm.id() == current_locked_cons.cell.id(),
    //             NodeData::CAR(current_cons_perm.value().car) == current_locked_cons.view_car,
    //             current_cons_perm.value().map_token@.instance_id() == current_locked_cons.instance@.id(),
    //             current_cons_perm.value().map_token@.key() == NodeData::CAR(current_cons_perm.value().car),
    //             (current_cons_perm.value().map_token@.value().is_none() <==> current_cons_perm.value().cdr.is_none()), 
    //             (current_cons_perm.value().map_token@.value().is_some() ==> 
    //                 (
    //                     current_cons_perm.value().cdr.unwrap().wf() &&
    //                     current_cons_perm.value().cdr.unwrap().view_instance() == current_locked_cons.instance &&
    //                     current_cons_perm.value().cdr.unwrap().view_car() > NodeData::CAR(current_cons_perm.value().car) &&
    //                     current_cons_perm.value().cdr.unwrap().view_car() == current_cons_perm.value().map_token@.value().unwrap()
    //                 )
    //             ),
    //             current_cons_perm.value().car < delete_car_raw,
    //             delete_car == NodeData::CAR(delete_car_raw)
    //         decreases
    //             delete_car_raw - current_cons_perm.value().car
    //     {
    //         let mut current_cons_view = current_locked_cons.cell.borrow(Tracked(current_cons_perm.borrow_mut()));

    //         // If there is no next LockedCons, then we have reached the tail.
    //         // If we have not deleted by now, then we are done - no tokens exist ==> no nodes exist
    //         if (current_cons_view.cdr.is_none()) {
    //             proof {
    //                 current_locked_cons.instance.delete_successful_car_not_in_list(
    //                     current_locked_cons.view_car(), 
    //                     delete_car, 
    //                     current_cons_view.map_token.value(), 
    //                     current_cons_view.map_token.borrow()
    //                 );
    //             }
    //             current_locked_cons.release_lock(current_cons_perm);
    //             return;
    //         } 
    //         // Otherwise, there is another LockedCons
    //         else {
    //             // Acquire the permissions to access the Cons:
    //             let next_locked_cons = current_cons_view.cdr.as_ref().unwrap().clone();
    //             let mut next_cons_perm = next_locked_cons.acquire_lock();
    //             let next_cons_view = next_locked_cons.cell.borrow(Tracked(next_cons_perm.borrow_mut()));

    //             // If the next car is larger than our delete, then we have:
    //             // lower_car < delete_car < upper_car
    //             // Which means that no node exist with value delete_car.
    //             // We are done - no tokens exist ==> no nodes exist
    //             if (delete_car_raw < next_cons_view.car) {
    //                 proof {
    //                     current_locked_cons.instance.delete_successful_car_not_in_list(
    //                         current_locked_cons.view_car(), 
    //                         delete_car, 
    //                         current_cons_view.map_token.value(), 
    //                         current_cons_view.map_token.borrow()
    //                     );
    //                 }
    //                 current_locked_cons.release_lock(current_cons_perm);
    //                 next_locked_cons.release_lock(next_cons_perm);
    //                 return;
    //             }

    //             // Check if we are deleting the first LockedCons:
    //             if (delete_car_raw == next_cons_view.car) {
    //                 let mut current_cons = current_locked_cons.cell.take(Tracked(current_cons_perm.borrow_mut()));
    //                 let mut next_cons = next_locked_cons.cell.take(Tracked(next_cons_perm.borrow_mut()));

    //                 let tracked updated_current_cons_token;

    //                 proof {
    //                     updated_current_cons_token = current_locked_cons.instance.borrow().delete(
    //                         current_locked_cons.view_car(), 
    //                         delete_car, 
    //                         next_cons.map_token.value(), 
    //                         current_cons.map_token.get(),
    //                         next_cons.map_token.get()
    //                     );
    //                 }

    //                 current_cons.map_token = Tracked(updated_current_cons_token);
    //                 current_cons.cdr = next_cons.cdr;

    //                 proof {
    //                     current_locked_cons.instance.delete_successful_car_not_in_list(
    //                         current_locked_cons.view_car(), 
    //                         delete_car, 
    //                         current_cons.map_token.value(), 
    //                         current_cons.map_token.borrow()
    //                     );
    //                 }

    //                 current_locked_cons.cell.put(Tracked(current_cons_perm.borrow_mut()), current_cons);
    //                 current_locked_cons.release_lock(current_cons_perm);
    //                 return;
    //             }

    //             // Otherwise, we give up the previous lock, and loop again
    //             current_locked_cons.release_lock(current_cons_perm);
    //             current_locked_cons = next_locked_cons;
    //             current_cons_perm = next_cons_perm;
    //         }
    //     }
    // }
}

fn main() {
}
}