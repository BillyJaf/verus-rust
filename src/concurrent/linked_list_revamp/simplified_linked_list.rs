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

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(variable)]
            pub list_head: Option<u32>,

            #[sharding(map)]
            pub list_representation: Map<u32, Option<u32>>,
        }

        #[invariant]
        pub fn empty_list_inv(&self) -> bool {
            self.list_head.is_none() <==> self.list_representation.is_empty()
        }

        #[invariant]
        pub fn non_empty_list_inv(&self) -> bool {
            self.list_head.is_some() <==> self.list_representation.contains_key(self.list_head.unwrap())
        }

        #[invariant]
        pub fn ordered_key_value_pairs_inv(&self) -> bool {
            forall |elem_1: u32, elem_2: u32| #![auto]
                (
                    self.list_representation.contains_pair(elem_1, Some(elem_2))
                ) ==>
                elem_1 < elem_2
        }

        #[invariant]
        pub fn list_representation_map_is_complete(&self) -> bool {
            forall |elem_1: u32, elem_2: u32| #![auto]
                (
                    self.list_representation.contains_pair(elem_1, Some(elem_2))
                ) ==>
                self.list_representation.contains_key(elem_2)
        }

        #[invariant]
        pub fn largest_cons_points_to_none_inv(&self) -> bool {
            forall |elem_1: u32| #![auto]
                (
                    self.list_representation.contains_pair(elem_1, None)
                ) ==> (
                    forall |elem_2: u32| #![auto]
                        (
                            self.list_representation.contains_key(elem_2) &&
                            elem_2 != elem_1
                        ) ==> elem_1 > elem_2
                )
        }

        #[invariant]
        pub fn list_head_has_smallest_cons_inv(&self) -> bool {
            forall |elem: u32| #![auto]
            (
                self.list_head.is_some() &&
                self.list_representation.contains_key(elem) &&
                elem != self.list_head.unwrap()
            ) ==>
            self.list_head.unwrap() < elem
        }

        #[invariant]
        pub fn unique_values_inv(&self) -> bool {   
            forall |elem_1: u32, elem_2: u32, option_elem: Option<u32>| #![auto]
                (
                    self.list_representation.contains_pair(elem_1, option_elem) &&
                    self.list_representation.contains_pair(elem_2, option_elem)
                ) ==>
                (
                    elem_1 == elem_2
                )      
        }

        #[invariant]
        pub fn key_exclusion_inv(&self) -> bool {   
            forall |elem_1: u32, elem_2: u32| #![auto] 
                (
                    self.list_representation.contains_pair(elem_1, Some(elem_2))
                ) ==> (
                    forall |elem_3: u32| #![auto] 
                        (
                            elem_1 < elem_3 &&
                            elem_3 < elem_2
                        ) ==> !self.list_representation.contains_key(elem_3)
                )      
        }

        init!{
            initialize()
            {
                init list_head = None;
                init list_representation = Map::empty();
            }
        }

        // Insert

        transition!{
            empty_list_insert(insert_elem: u32)
            {   
                require(pre.list_head.is_none());
                
                update list_head = Some(insert_elem);
                add list_representation += [insert_elem => None];
            }
        }

        transition!{
            insert_at_head(insert_elem: u32, upper_elem: u32)
            {   
                require(pre.list_head == Some(upper_elem));
                require(insert_elem < upper_elem);
                
                update list_head = Some(insert_elem);
                add list_representation += [insert_elem => Some(upper_elem)];
            }
        }

        transition!{
            insert(lower_elem: u32, insert_elem: u32, upper_elem: u32)
            {   
                require(lower_elem < insert_elem);
                require(insert_elem < upper_elem);

                remove list_representation -= [lower_elem => Some(upper_elem)];
                add list_representation += [lower_elem => Some(insert_elem)];
                add list_representation += [insert_elem => Some(upper_elem)];
            }
        }

        transition!{
            insert_at_tail(lower_elem: u32, insert_elem: u32)
            {   
                require(lower_elem < insert_elem);
                
                remove list_representation -= [lower_elem => None];
                add list_representation += [lower_elem => Some(insert_elem)];
                add list_representation += [insert_elem => None];
            }
        }

        // Delete

        transition!{
            delete_at_head(delete_elem: u32)
            {   
                require(pre.list_head == Some(delete_elem));

                remove list_representation -= [delete_elem => let option_elem];
                update list_head = option_elem;
            }
        }

        transition!{
            delete(lower_elem: u32, delete_elem: u32)
            {   
                remove list_representation -= [delete_elem => let option_elem];
                remove list_representation -= [lower_elem => Some(delete_elem)];
                add list_representation += [lower_elem => option_elem];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }
       
        #[inductive(empty_list_insert)]
        fn empty_list_insert_inductive(pre: Self, post: Self, insert_elem: u32) { }
       
        #[inductive(insert_at_head)]
        fn insert_at_head_inductive(pre: Self, post: Self, insert_elem: u32, upper_elem: u32) {
            assume(false);
        }
       
        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, lower_elem: u32, insert_elem: u32, upper_elem: u32) {
            assume(false);
        }
       
        #[inductive(insert_at_tail)]
        fn insert_at_tail_inductive(pre: Self, post: Self, lower_elem: u32, insert_elem: u32) {
            assume(false);
        }
       
        #[inductive(delete_at_head)]
        fn delete_at_head_inductive(pre: Self, post: Self, delete_elem: u32) {
            assume(false);
        }
       
        #[inductive(delete)]
        fn delete_inductive(pre: Self, post: Self, lower_elem: u32, delete_elem: u32) {
            assume(false);
        }
    }
}

pub struct Nil {
    pub cdr: Option<Arc<LockedCons>>
}

pub tracked struct NilPermAndToken {
    pub nil_perm: PointsTo<Nil>,
    pub list_head: machine::list_head
}

struct_with_invariants!{
    pub struct LockedNil {
        atomic: AtomicBool<_, Option<NilPermAndToken>, _>,
        nil_cell: PCell<Nil>,
        instance: Tracked<machine::Instance>,
    }

    spec fn wf(&self) -> bool 
    {
        invariant on atomic with (nil_cell, instance) is (v: bool, option_pat: Option<NilPermAndToken>) {
            match option_pat {
                None => v == true,
                Some(npat) => {
                    &&& v == false
                    &&& npat.nil_perm.is_init()
                    &&& npat.nil_perm.id() == nil_cell.id()
                    &&& npat.list_head.instance_id() == instance.id()
                    &&& (npat.list_head.value().is_none() <==> npat.nil_perm.value().cdr.is_none()) 
                    &&& (npat.list_head.value().is_some() ==> 
                            (
                                npat.nil_perm.value().cdr.unwrap().wf() &&
                                npat.nil_perm.value().cdr.unwrap().view_instance() == instance &&
                                npat.nil_perm.value().cdr.unwrap().view_car() == npat.list_head.value().unwrap()
                            )
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

        let tracked (
            Tracked(instance),
            Tracked(list_head),
            Tracked(list_representation)
        ) = machine::Instance::initialize();

        let tracked pat = NilPermAndToken {
            nil_perm,
            list_head
        };

        let atomic = AtomicBool::new(Ghost((nil_cell, Tracked(instance))), false, Tracked(Some(pat)));
        Self { 
            atomic, 
            nil_cell, 
            instance: Tracked(instance)
        }
    }

    fn acquire_lock(&self) -> (npat: Tracked<NilPermAndToken>)
        requires 
            self.wf(),
        ensures 
            npat.nil_perm.is_init(),
            npat.nil_perm.id() == self.nil_cell.id(),
            npat.list_head.instance_id() == self.instance.id(),
            (npat.list_head.value().is_none() <==> npat.nil_perm.value().cdr.is_none()) ,
            (npat.list_head.value().is_some() ==> 
                (
                    npat.nil_perm.value().cdr.unwrap().wf() &&
                    npat.nil_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    npat.nil_perm.value().cdr.unwrap().view_car() == npat.list_head.value().unwrap()
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

    fn release_lock(&self, npat: Tracked<NilPermAndToken>)
        requires
            npat.nil_perm.is_init(),
            npat.nil_perm.id() == self.nil_cell.id(),
            npat.list_head.instance_id() == self.instance.id(),
            (npat.list_head.value().is_none() <==> npat.nil_perm.value().cdr.is_none()) ,
            (npat.list_head.value().is_some() ==> 
                (
                    npat.nil_perm.value().cdr.unwrap().wf() &&
                    npat.nil_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    npat.nil_perm.value().cdr.unwrap().view_car() == npat.list_head.value().unwrap()
                )
            ),
            self.wf()
        ensures
            self.wf()
    {
        atomic_with_ghost!(
            &self.atomic => store(false);
            ghost points_to_inv => {
                points_to_inv = Some(npat.get());
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
        let mut nil_perm_and_token = self.acquire_lock();
        let nil_view = self.nil_cell.borrow(Tracked(&mut nil_perm_and_token.nil_perm));

        // If the nil cdr is none, then we must insert here - at the tail
        if (nil_view.cdr.is_none()) {
            let tracked map_token;

            proof {
                map_token = self.instance.empty_list_insert(
                    insert_car,
                    &mut nil_perm_and_token.list_head
                );
            }

            let locked_cons = LockedCons::new(
                insert_car,  
                None::<Arc<LockedCons>>, 
                self.instance.clone(),
                Tracked(map_token)
            );

            let arc_locked_cons = Arc::new(locked_cons);

            let mut nil = self.nil_cell.take(Tracked(&mut nil_perm_and_token.nil_perm));
            nil.cdr = Some(arc_locked_cons.clone());
            self.nil_cell.put(Tracked(&mut nil_perm_and_token.nil_perm), nil);
            self.release_lock(nil_perm_and_token);
            return;
        } 
        else {
            // We check if we need to insert inbetween Nil and the first Cons

            let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
            let mut first_cons_perm_and_token = first_locked_cons.acquire_lock();
            let first_cons_view = first_locked_cons.cons_cell.borrow(Tracked(&mut first_cons_perm_and_token.cons_perm));

            // If a Cons with this value already exists:
            if (insert_car == first_cons_view.car) {
                // Return early and do nothing - the Cons exists.
                self.release_lock(nil_perm_and_token);
                first_locked_cons.release_lock(first_cons_perm_and_token);
                return;
            }

            // If the first Cons cdr is larger than the insert cdr:
            if (insert_car < first_cons_view.car) {
                // Then we insert inbetween Nil and first Cons
                let tracked map_token;

                proof {
                    map_token = self.instance.insert_at_head(
                        insert_car,
                        first_cons_view.car,
                        &mut nil_perm_and_token.list_head
                    );
                }

                let locked_cons = LockedCons::new(
                    insert_car,  
                    Some(first_locked_cons.clone()), 
                    self.instance.clone(),
                    Tracked(map_token)
                );

                let arc_locked_cons = Arc::new(locked_cons);

                let mut nil = self.nil_cell.take(Tracked(&mut nil_perm_and_token.nil_perm));
                nil.cdr = Some(arc_locked_cons.clone());
                self.nil_cell.put(Tracked(&mut nil_perm_and_token.nil_perm), nil);

                self.release_lock(nil_perm_and_token);
                first_locked_cons.release_lock(first_cons_perm_and_token);
                return;
            }

            // If we have reached here, we may release the nil lock:
            self.release_lock(nil_perm_and_token);

            // Any insert from here onwards will not involve nil - 
            // we may delegate the insert to a chain of LockedCons
            first_locked_cons.insert(insert_car, first_cons_perm_and_token);
        }
    }

    fn delete(self: Arc<Self>, delete_car: u32)
        requires
            self.wf()
        ensures
            self.wf()
    {
        // Acquire the lock for the nil node, and view the data inside (without taking)
        let mut nil_perm_and_token = self.acquire_lock();
        let nil_view = self.nil_cell.borrow(Tracked(&mut nil_perm_and_token.nil_perm));

        // If the nil cdr is none, then we are done - no tokens exist ==> no nodes exist
        if (nil_view.cdr.is_none()) {
            self.release_lock(nil_perm_and_token);
            return;
        }

        // We check if we need to delete the first Cons (hence lower is LockedNil)
        let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
        let mut first_cons_perm_and_token = first_locked_cons.acquire_lock();
        let tracked ConsPermAndToken { cons_perm, map_token } = first_cons_perm_and_token.get();

        let first_cons_view = first_locked_cons.cons_cell.borrow(Tracked(&mut cons_perm));

        // If the first car is larger than our delete, then we are done - no tokens exist ==> no nodes exist
        if (delete_car < first_cons_view.car) {
            self.release_lock(nil_perm_and_token);
            first_locked_cons.release_lock(Tracked(ConsPermAndToken { cons_perm, map_token }));
            return;
        }

        // // Check if we are deleting the first LockedCons:
        if (delete_car == first_cons_view.car) {
            let mut nil = self.nil_cell.take(Tracked(&mut nil_perm_and_token.nil_perm));
            let mut first_cons = first_locked_cons.cons_cell.take(Tracked(&mut cons_perm));

            proof {
                self.instance.delete_at_head(
                    delete_car, 
                    &mut nil_perm_and_token.list_head,
                    map_token
                );
            }

            nil.cdr = first_cons.cdr;
            self.nil_cell.put(Tracked(&mut nil_perm_and_token.nil_perm), nil);

            self.release_lock(nil_perm_and_token);

            return;
        }
        
        // We can release the dummy node lock.
        self.release_lock(nil_perm_and_token);
        // // and begin our traversal:
        // first_locked_cons.delete(first_cons_perm, delete_car_raw);
    }
}

pub struct Cons {
    pub car: u32,
    pub cdr: Option<Arc<LockedCons>>,
}

pub tracked struct ConsPermAndToken {
    pub cons_perm: PointsTo<Cons>,
    pub map_token: machine::list_representation
}

struct_with_invariants!{
    pub struct LockedCons {
        atomic: AtomicBool<_, Option<ConsPermAndToken>, _>,
        cons_cell: PCell<Cons>,
        instance: Tracked<machine::Instance>,
        view_car: Ghost<u32>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant on atomic with (cons_cell, instance, view_car) is (v: bool, option_cpat: Option<ConsPermAndToken>) {
            match option_cpat {
                None => v == true,
                Some(cpat) => {
                    &&& v == false
                    &&& cpat.cons_perm.is_init()
                    &&& cpat.cons_perm.id() == cons_cell.id()
                    &&& cpat.map_token.instance_id() == instance.id()
                    &&& cpat.map_token.key() == view_car
                    &&& cpat.cons_perm.value().car == view_car
                    &&& (cpat.map_token.value().is_none() <==> cpat.cons_perm.value().cdr.is_none()) 
                    &&& (cpat.map_token.value().is_some() ==> 
                            (
                                cpat.cons_perm.value().cdr.unwrap().wf() &&
                                cpat.cons_perm.value().cdr.unwrap().view_instance() == instance &&
                                cpat.cons_perm.value().cdr.unwrap().view_car() == cpat.map_token.value().unwrap() && 
                                cpat.cons_perm.value().cdr.unwrap().view_car() > cpat.cons_perm.value().car
                            )
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

    pub closed spec fn view_instance(&self) -> (instance: machine::Instance)
    {
        self.instance@
    }

    fn new(car: u32, cdr: Option<Arc<LockedCons>>, instance: Tracked<machine::Instance>, map_token: Tracked<machine::list_representation>) -> (locked_cons: Self)
        requires
            map_token.instance_id() == instance.id(),
            map_token.key() == car,
            (map_token.value().is_none() <==> cdr.is_none()),
            (map_token.value().is_some() ==> 
                (
                    cdr.unwrap().wf() &&
                    cdr.unwrap().view_instance() == instance &&
                    cdr.unwrap().view_car() == map_token.value().unwrap() &&
                    cdr.unwrap().view_car() > car
                )
            ),
        ensures 
            locked_cons.wf(),
            locked_cons.instance == instance,
            locked_cons.view_car == car
    {   
        let view_car = Ghost(car);
        let cons = Cons { car, cdr };
        let (cons_cell, Tracked(cons_perm)) = PCell::new(cons);
        let tracked cpat = ConsPermAndToken { 
            cons_perm, 
            map_token: map_token.get()
        };
        let atomic = AtomicBool::new(Ghost((cons_cell, instance, view_car)), false, Tracked(Some(cpat)));
        Self { atomic, cons_cell, instance, view_car }
    }

    fn acquire_lock(&self) -> (cpat: Tracked<ConsPermAndToken>)
        requires 
            self.wf(),
        ensures 
            cpat.cons_perm.is_init(),
            cpat.cons_perm.id() == self.cons_cell.id(),
            cpat.map_token.instance_id() == self.instance.id(),
            cpat.map_token.key() == self.view_car,
            cpat.cons_perm.value().car == self.view_car,
            (cpat.map_token.value().is_none() <==> cpat.cons_perm.value().cdr.is_none()) ,
            (cpat.map_token.value().is_some() ==> 
                (
                    cpat.cons_perm.value().cdr.unwrap().wf() &&
                    cpat.cons_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    cpat.cons_perm.value().cdr.unwrap().view_car() == cpat.map_token.value().unwrap() &&
                    cpat.cons_perm.value().cdr.unwrap().view_car() > cpat.cons_perm.value().car
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

    fn release_lock(&self, cpat: Tracked<ConsPermAndToken>)
        requires
            self.wf(),
            cpat.cons_perm.is_init(),
            cpat.cons_perm.id() == self.cons_cell.id(),
            cpat.map_token.instance_id() == self.instance.id(),
            cpat.map_token.key() == self.view_car,
            cpat.cons_perm.value().car == self.view_car,
            (cpat.map_token.value().is_none() <==> cpat.cons_perm.value().cdr.is_none()) ,
            (cpat.map_token.value().is_some() ==> 
                (
                    cpat.cons_perm.value().cdr.unwrap().wf() &&
                    cpat.cons_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    cpat.cons_perm.value().cdr.unwrap().view_car() == cpat.map_token.value().unwrap() &&
                    cpat.cons_perm.value().cdr.unwrap().view_car() > cpat.cons_perm.value().car
                )
            ),
        ensures
            self.wf()
    {
        atomic_with_ghost!(
            &self.atomic => store(false);
            ghost points_to_inv => {
                points_to_inv = Some(cpat.get());
            }
        );
    }

    fn insert(self: Arc<Self>, insert_car: u32, mut cpat: Tracked<ConsPermAndToken>)
        requires
            self.wf(),
            cpat.cons_perm.is_init(),
            cpat.cons_perm.id() == self.cons_cell.id(),
            cpat.map_token.instance_id() == self.instance.id(),
            cpat.map_token.key() == self.view_car,
            cpat.cons_perm.value().car == self.view_car,
            (cpat.map_token.value().is_none() <==> cpat.cons_perm.value().cdr.is_none()) ,
            (cpat.map_token.value().is_some() ==> 
                (
                    cpat.cons_perm.value().cdr.unwrap().wf() &&
                    cpat.cons_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    cpat.cons_perm.value().cdr.unwrap().view_car() == cpat.map_token.value().unwrap() &&
                    cpat.cons_perm.value().cdr.unwrap().view_car() > cpat.cons_perm.value().car
                )
            ),
            cpat.cons_perm.value().car < insert_car
        ensures
            self.wf()
    {
        let mut current_locked_cons = self;
        loop 
            invariant
                self.wf(),
                current_locked_cons.wf(),
                current_locked_cons.instance == self.instance,
                cpat.cons_perm.is_init(),
                cpat.cons_perm.id() == current_locked_cons.cons_cell.id(),
                cpat.map_token.instance_id() == current_locked_cons.instance.id(),
                cpat.map_token.key() == current_locked_cons.view_car,
                cpat.cons_perm.value().car == current_locked_cons.view_car,
                (cpat.map_token.value().is_none() <==> cpat.cons_perm.value().cdr.is_none()) ,
                (cpat.map_token.value().is_some() ==> 
                    (
                        cpat.cons_perm.value().cdr.unwrap().wf() &&
                        cpat.cons_perm.value().cdr.unwrap().view_instance() == current_locked_cons.instance &&
                        cpat.cons_perm.value().cdr.unwrap().view_car() == cpat.map_token.value().unwrap() &&
                        cpat.cons_perm.value().cdr.unwrap().view_car() > cpat.cons_perm.value().car
                    )
                ),
                cpat.cons_perm.value().car < insert_car
            // decreases
            //     insert_car - cpat.cons_perm.value().car
        {
            let tracked ConsPermAndToken { cons_perm, map_token } = cpat.get();
            let mut current_cons_view = current_locked_cons.cons_cell.borrow(Tracked(&mut cons_perm));

            // If there is no next LockedCons, then we must insert at the tail after a Cons
            if (current_cons_view.cdr.is_none()) {

                let mut old_tail_cons = current_locked_cons.cons_cell.take(Tracked(&mut cons_perm));

                let tracked token_tuple;
                let tracked updated_old_tail_cons_token;
                let tracked new_tail_cons_token;

                proof {
                    token_tuple = current_locked_cons.instance.insert_at_tail(
                        old_tail_cons.car, 
                        insert_car, 
                        map_token
                    );
                    updated_old_tail_cons_token = token_tuple.0.get();
                    new_tail_cons_token = token_tuple.1.get();
                }

                let locked_cons = LockedCons::new(
                    insert_car, 
                    None::<Arc<LockedCons>>, 
                    current_locked_cons.instance.clone(),
                    Tracked(new_tail_cons_token)
                );

                old_tail_cons.cdr = Some(Arc::new(locked_cons));
                current_locked_cons.cons_cell.put(Tracked(&mut cons_perm), old_tail_cons);
                current_locked_cons.release_lock(Tracked(ConsPermAndToken { cons_perm, map_token: updated_old_tail_cons_token }));
                return;
            } 
            // Otherwise, there is another LockedCons
            else {
                // Acquire the permissions to access the Cons:
                let next_locked_cons = current_cons_view.cdr.as_ref().unwrap().clone();
                let mut next_cpat = next_locked_cons.acquire_lock();
                let tracked ConsPermAndToken { cons_perm: next_cons_perm, map_token: next_map_token } = next_cpat.get();
                let next_cons_view = next_locked_cons.cons_cell.borrow(Tracked(&mut next_cons_perm));

                // If a Cons with this value already exists:
                if (insert_car == next_cons_view.car) {
                    // Return early and do nothing - the Cons exists.
                    current_locked_cons.release_lock(Tracked(ConsPermAndToken { cons_perm, map_token }));
                    next_locked_cons.release_lock(Tracked(ConsPermAndToken { cons_perm: next_cons_perm, map_token: next_map_token }));
                    return;
                }

                // If the next Cons cdr is larger than the insert cdr:
                if (insert_car < next_cons_view.car) {

                    // Then we insert inbetween Cons and Cons
                    let mut current_cons = current_locked_cons.cons_cell.take(Tracked(&mut cons_perm));

                    let tracked token_tuple;
                    let tracked updated_cons_token;
                    let tracked new_cons_token;

                    // insert(lower_elem: u32, insert_elem: u32, upper_elem: u32)

                    proof {
                        token_tuple = current_locked_cons.instance.insert(
                            current_cons.car, 
                            insert_car, 
                            next_cons_view.car, 
                            map_token
                        );
                        updated_cons_token = token_tuple.0.get();
                        new_cons_token = token_tuple.1.get();
                    }

                    let locked_cons = LockedCons::new(
                        insert_car, 
                        Some(next_locked_cons.clone()), 
                        current_locked_cons.instance.clone(),
                        Tracked(new_cons_token),
                    );

                    current_cons.cdr = Some(Arc::new(locked_cons));

                    current_locked_cons.cons_cell.put(Tracked(&mut cons_perm), current_cons);

                    current_locked_cons.release_lock(Tracked(ConsPermAndToken { cons_perm, map_token: updated_cons_token }));
                    return;
                }

                // Otherwise, we give up the previous lock, and loop again
                current_locked_cons.release_lock(Tracked(ConsPermAndToken { cons_perm, map_token }));

                current_locked_cons = next_locked_cons;
                cpat = Tracked(ConsPermAndToken { cons_perm: next_cons_perm, map_token: next_map_token });
            }
        }
    }

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