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

pub struct ListHead {
    pub nil_perm: PointsTo<Nil>,
    pub cons_perm: Option<PointsTo<Cons>>
}

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(variable)]
            pub list_head: ListHead,

            #[sharding(map)]
            pub list_representation: Map<PointsTo<Cons>, Option<PointsTo<Cons>>>,
        }

        #[invariant]
        pub fn empty_list_inv(&self) -> bool {
            self.list_head.cons_perm.is_none() <==> self.list_representation.is_empty()
        }

        #[invariant]
        pub fn non_empty_list_inv(&self) -> bool {
            self.list_head.cons_perm.is_some() <==> self.list_representation.contains_key(self.list_head.cons_perm.unwrap())
        }

        #[invariant]
        pub fn ordered_key_value_pairs_inv(&self) -> bool {
            forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    self.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                points_to_1.value().car < points_to_2.value().car
        }

        #[invariant]
        pub fn list_representation_map_is_complete(&self) -> bool {
            forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    self.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                self.list_representation.contains_key(points_to_2)
        }

        #[invariant]
        pub fn largest_cons_points_to_none_inv(&self) -> bool {
            forall |points_to_1: PointsTo<Cons>| #![auto]
                (
                    self.list_representation.contains_pair(points_to_1, None)
                ) ==> (
                    forall |points_to_2: PointsTo<Cons>| #![auto]
                        (
                            self.list_representation.contains_key(points_to_2) &&
                            points_to_2 != points_to_1
                        ) ==> points_to_1.value().car > points_to_2.value().car
                )
        }

        #[invariant]
        pub fn list_head_has_smallest_cons_inv(&self) -> bool {
            forall |points_to: PointsTo<Cons>| #![auto]
            (
                self.list_head.cons_perm.is_some() &&
                self.list_representation.contains_key(points_to) &&
                points_to != self.list_head.cons_perm.unwrap()
            ) ==>
            self.list_head.cons_perm.unwrap().value().car < points_to.value().car
        }

        #[invariant]
        pub fn unique_values_inv(&self) -> bool {   
            forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>, option_points_to: Option<PointsTo<Cons>>| #![auto]
                (
                    self.list_representation.contains_pair(points_to_1, option_points_to) &&
                    self.list_representation.contains_pair(points_to_2, option_points_to)
                ) ==>
                (
                    points_to_1 == points_to_2
                )      
        }

        #[invariant]
        pub fn key_exclusion_inv(&self) -> bool {   
            forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto] 
                (
                    self.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==> (
                    forall |points_to_3: PointsTo<Cons>| #![auto] 
                        (
                            points_to_1.value().car < points_to_3.value().car &&
                            points_to_3.value().car < points_to_2.value().car
                        ) ==> !self.list_representation.contains_key(points_to_3)
                )      
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
            empty_list_insert(nil_perm: PointsTo<Nil>, insert_perm: PointsTo<Cons>)
            {   
                require(pre.list_head.cons_perm.is_none());
                
                update list_head = ListHead { nil_perm, cons_perm: Some(insert_perm) };
                add list_representation += [insert_perm => None];
            }
        }

        transition!{
            insert_at_head(nil_perm: PointsTo<Nil>, insert_perm: PointsTo<Cons>, upper_perm: PointsTo<Cons>)
            {   
                require(pre.list_head.nil_perm == nil_perm);
                require(pre.list_head.cons_perm == Some(upper_perm));
                require(insert_perm.value().car < upper_perm.value().car);
                
                update list_head = ListHead { nil_perm, cons_perm: Some(insert_perm) };
                add list_representation += [insert_perm => Some(upper_perm)];
            }
        }

        transition!{
            insert(lower_perm: PointsTo<Cons>, insert_perm: PointsTo<Cons>, upper_perm: PointsTo<Cons>)
            {   
                require(lower_perm.value().car < insert_perm.value().car);
                require(insert_perm.value().car < upper_perm.value().car);

                remove list_representation -= [lower_perm => Some(upper_perm)];
                add list_representation += [lower_perm => Some(insert_perm)];
                add list_representation += [insert_perm => Some(upper_perm)];
            }
        }

        transition!{
            insert_at_tail(lower_perm: PointsTo<Cons>, insert_perm: PointsTo<Cons>)
            {   
                require(lower_perm.value().car < insert_perm.value().car);
                
                remove list_representation -= [lower_perm => None];
                add list_representation += [lower_perm => Some(insert_perm)];
                add list_representation += [insert_perm => None];
            }
        }

        // Delete

        transition!{
            empty_delete(list_head: ListHead)
            {   
                require(pre.list_head == list_head);
                require(pre.list_head.cons_perm.is_none());
            }
        }

        transition!{
            delete_at_head(list_head: ListHead, delete_perm: PointsTo<Cons>)
            {   
                require(pre.list_head == list_head);
                require(pre.list_head.cons_perm.is_some());
                require(pre.list_head.cons_perm.unwrap() == delete_perm);

                remove list_representation -= [delete_perm => let option_cons_perm];
                update list_head = ListHead { nil_perm: list_head.nil_perm, cons_perm: option_cons_perm };
            }
        }

        transition!{
            delete(lower_perm: PointsTo<Cons>, delete_perm: PointsTo<Cons>)
            {   
                remove list_representation -= [delete_perm => let option_cons_perm];
                remove list_representation -= [lower_perm => Some(delete_perm)];
                add list_representation += [lower_perm => option_cons_perm];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, nil_perm: PointsTo<Nil>) {
        }

        #[inductive(empty_list_insert)]
        fn empty_list_insert_inductive(pre: Self, post: Self, nil_perm: PointsTo<Nil>, insert_perm: PointsTo<Cons>) { }
       
        #[inductive(insert_at_head)]
        fn insert_at_head_inductive(pre: Self, post: Self, nil_perm: PointsTo<Nil>, insert_perm: PointsTo<Cons>, upper_perm: PointsTo<Cons>) {
            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                points_to_1.value().car < points_to_2.value().car
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                post.list_representation.contains_key(points_to_2)
            );

            assume(
                forall |points_to_1: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, None)
                ) ==> (
                    forall |points_to_2: PointsTo<Cons>| #![auto]
                        (
                            post.list_representation.contains_key(points_to_2) &&
                            points_to_2 != points_to_1
                        ) ==> points_to_1.value().car > points_to_2.value().car
                )
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>, option_points_to: Option<PointsTo<Cons>>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, option_points_to) &&
                    post.list_representation.contains_pair(points_to_2, option_points_to)
                ) ==>
                (
                    points_to_1 == points_to_2
                )    
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto] 
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==> (
                    forall |points_to_3: PointsTo<Cons>| #![auto] 
                        (
                            points_to_1.value().car < points_to_3.value().car &&
                            points_to_3.value().car < points_to_2.value().car
                        ) ==> !post.list_representation.contains_key(points_to_3)
                )      
            );
        }
       
        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, lower_perm: PointsTo<Cons>, insert_perm: PointsTo<Cons>, upper_perm: PointsTo<Cons>) {
            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                points_to_1.value().car < points_to_2.value().car
            );

            assume(
                forall |points_to_1: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, None)
                ) ==> (
                    forall |points_to_2: PointsTo<Cons>| #![auto]
                        (
                            post.list_representation.contains_key(points_to_2) &&
                            points_to_2 != points_to_1
                        ) ==> points_to_1.value().car > points_to_2.value().car
                )
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                post.list_representation.contains_key(points_to_2)
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>, option_points_to: Option<PointsTo<Cons>>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, option_points_to) &&
                    post.list_representation.contains_pair(points_to_2, option_points_to)
                ) ==>
                (
                    points_to_1 == points_to_2
                )    
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto] 
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==> (
                    forall |points_to_3: PointsTo<Cons>| #![auto] 
                        (
                            points_to_1.value().car < points_to_3.value().car &&
                            points_to_3.value().car < points_to_2.value().car
                        ) ==> !post.list_representation.contains_key(points_to_3)
                )      
            );
        }
       
        #[inductive(insert_at_tail)]
        fn insert_at_tail_inductive(pre: Self, post: Self, lower_perm: PointsTo<Cons>, insert_perm: PointsTo<Cons>) {
            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                points_to_1.value().car < points_to_2.value().car
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                post.list_representation.contains_key(points_to_2)
            );

            assume(
                forall |points_to_1: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, None)
                ) ==> (
                    forall |points_to_2: PointsTo<Cons>| #![auto]
                        (
                            post.list_representation.contains_key(points_to_2) &&
                            points_to_2 != points_to_1
                        ) ==> points_to_1.value().car > points_to_2.value().car
                )
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto] 
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==> (
                    forall |points_to_3: PointsTo<Cons>| #![auto] 
                        (
                            points_to_1.value().car < points_to_3.value().car &&
                            points_to_3.value().car < points_to_2.value().car
                        ) ==> !post.list_representation.contains_key(points_to_3)
                )      
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>, option_points_to: Option<PointsTo<Cons>>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, option_points_to) &&
                    post.list_representation.contains_pair(points_to_2, option_points_to)
                ) ==>
                (
                    points_to_1 == points_to_2
                )    
            );
        }
       
        #[inductive(delete_at_head)]
        fn delete_at_head_inductive(pre: Self, post: Self, list_head: ListHead, delete_perm: PointsTo<Cons>) {
            assume(post.list_head.cons_perm.is_none() <==> post.list_representation.is_empty());
            assume(post.list_head.cons_perm.is_some() <==> post.list_representation.contains_key(post.list_head.cons_perm.unwrap()));
            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                points_to_1.value().car < points_to_2.value().car
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                post.list_representation.contains_key(points_to_2)
            );

            assume(
                forall |points_to_1: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, None)
                ) ==> (
                    forall |points_to_2: PointsTo<Cons>| #![auto]
                        (
                            post.list_representation.contains_key(points_to_2) &&
                            points_to_2 != points_to_1
                        ) ==> points_to_1.value().car > points_to_2.value().car
                )
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>, option_points_to: Option<PointsTo<Cons>>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, option_points_to) &&
                    post.list_representation.contains_pair(points_to_2, option_points_to)
                ) ==>
                (
                    points_to_1 == points_to_2
                )    
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto] 
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==> (
                    forall |points_to_3: PointsTo<Cons>| #![auto] 
                        (
                            points_to_1.value().car < points_to_3.value().car &&
                            points_to_3.value().car < points_to_2.value().car
                        ) ==> !post.list_representation.contains_key(points_to_3)
                )      
            );

            assume(
                forall |points_to: PointsTo<Cons>| #![auto]
                (
                    post.list_head.cons_perm.is_some() &&
                    post.list_representation.contains_key(points_to) &&
                    points_to != post.list_head.cons_perm.unwrap()
                ) ==>
                post.list_head.cons_perm.unwrap().value().car < points_to.value().car
            );
        }
       
        #[inductive(delete)]
        fn delete_inductive(pre: Self, post: Self, lower_perm: PointsTo<Cons>, delete_perm: PointsTo<Cons>) {
            assume(post.list_head.cons_perm.is_none() <==> post.list_representation.is_empty());
            assume(post.list_head.cons_perm.is_some() <==> post.list_representation.contains_key(post.list_head.cons_perm.unwrap()));
            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                points_to_1.value().car < points_to_2.value().car
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                post.list_representation.contains_key(points_to_2)
            );

            assume(
                forall |points_to_1: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, None)
                ) ==> (
                    forall |points_to_2: PointsTo<Cons>| #![auto]
                        (
                            post.list_representation.contains_key(points_to_2) &&
                            points_to_2 != points_to_1
                        ) ==> points_to_1.value().car > points_to_2.value().car
                )
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>, option_points_to: Option<PointsTo<Cons>>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, option_points_to) &&
                    post.list_representation.contains_pair(points_to_2, option_points_to)
                ) ==>
                (
                    points_to_1 == points_to_2
                )    
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto] 
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==> (
                    forall |points_to_3: PointsTo<Cons>| #![auto] 
                        (
                            points_to_1.value().car < points_to_3.value().car &&
                            points_to_3.value().car < points_to_2.value().car
                        ) ==> !post.list_representation.contains_key(points_to_3)
                )      
            );

            assume(
                forall |points_to: PointsTo<Cons>| #![auto]
                (
                    post.list_head.cons_perm.is_some() &&
                    post.list_representation.contains_key(points_to) &&
                    points_to != post.list_head.cons_perm.unwrap()
                ) ==>
                post.list_head.cons_perm.unwrap().value().car < points_to.value().car
            );
        }

        #[inductive(empty_delete)]
        fn empty_delete_inductive(pre: Self, post: Self, list_head: ListHead) {
            assume(post.list_head.cons_perm.is_none() <==> post.list_representation.is_empty());
            assume(post.list_head.cons_perm.is_some() <==> post.list_representation.contains_key(post.list_head.cons_perm.unwrap()));
            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                points_to_1.value().car < points_to_2.value().car
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==>
                post.list_representation.contains_key(points_to_2)
            );

            assume(
                forall |points_to_1: PointsTo<Cons>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, None)
                ) ==> (
                    forall |points_to_2: PointsTo<Cons>| #![auto]
                        (
                            post.list_representation.contains_key(points_to_2) &&
                            points_to_2 != points_to_1
                        ) ==> points_to_1.value().car > points_to_2.value().car
                )
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>, option_points_to: Option<PointsTo<Cons>>| #![auto]
                (
                    post.list_representation.contains_pair(points_to_1, option_points_to) &&
                    post.list_representation.contains_pair(points_to_2, option_points_to)
                ) ==>
                (
                    points_to_1 == points_to_2
                )    
            );

            assume(
                forall |points_to_1: PointsTo<Cons>, points_to_2: PointsTo<Cons>| #![auto] 
                (
                    post.list_representation.contains_pair(points_to_1, Some(points_to_2))
                ) ==> (
                    forall |points_to_3: PointsTo<Cons>| #![auto] 
                        (
                            points_to_1.value().car < points_to_3.value().car &&
                            points_to_3.value().car < points_to_2.value().car
                        ) ==> !post.list_representation.contains_key(points_to_3)
                )      
            );

            assume(
                forall |points_to: PointsTo<Cons>| #![auto]
                (
                    post.list_head.cons_perm.is_some() &&
                    post.list_representation.contains_key(points_to) &&
                    points_to != post.list_head.cons_perm.unwrap()
                ) ==>
                post.list_head.cons_perm.unwrap().value().car < points_to.value().car
            );
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
                    &&& npat.list_head.value().nil_perm == npat.nil_perm
                    &&& (npat.list_head.value().cons_perm.is_none() <==> npat.nil_perm.value().cdr.is_none()) 
                    &&& (npat.list_head.value().cons_perm.is_some() ==> 
                            (
                                npat.nil_perm.value().cdr.unwrap().wf() &&
                                 npat.nil_perm.value().cdr.unwrap().view_instance() == instance &&
                                npat.nil_perm.value().cdr.unwrap().view_car() == npat.list_head.value().cons_perm.unwrap().value().car
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
        ) = machine::Instance::initialize(nil_perm);

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
            npat.list_head.value().nil_perm == npat.nil_perm,
            (npat.list_head.value().cons_perm.is_none() <==> npat.nil_perm.value().cdr.is_none()) ,
            (npat.list_head.value().cons_perm.is_some() ==> 
                (
                    npat.nil_perm.value().cdr.unwrap().wf() &&
                    npat.nil_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    npat.nil_perm.value().cdr.unwrap().view_car() == npat.list_head.value().cons_perm.unwrap().value().car
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
            npat.list_head.value().nil_perm == npat.nil_perm,
            (npat.list_head.value().cons_perm.is_none() <==> npat.nil_perm.value().cdr.is_none()) ,
            (npat.list_head.value().cons_perm.is_some() ==> 
                (
                    npat.nil_perm.value().cdr.unwrap().wf() &&
                    npat.nil_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    npat.nil_perm.value().cdr.unwrap().view_car() == npat.list_head.value().cons_perm.unwrap().value().car
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

            let (locked_cons, Tracked(cons_perm)) = LockedCons::new(
                insert_car,  
                None::<Arc<LockedCons>>, 
                self.instance.clone()
            );
            let arc_locked_cons = Arc::new(locked_cons);

            let mut nil = self.nil_cell.take(Tracked(&mut nil_perm_and_token.nil_perm));
            nil.cdr = Some(arc_locked_cons.clone());
            self.nil_cell.put(Tracked(&mut nil_perm_and_token.nil_perm), nil);

            proof {
                map_token = self.instance.empty_list_insert(
                    nil_perm_and_token@.nil_perm,
                    cons_perm,
                    &mut nil_perm_and_token.list_head
                );
            }

            self.release_lock(nil_perm_and_token);
            arc_locked_cons.release_lock(Tracked(ConsPermAndToken { cons_perm, map_token }));
            return;
        } 
        // else {
        //     // We check if we need to insert inbetween Nil and the first Cons
        //     let first_locked_cons = nil_view.cdr.as_ref().unwrap().clone();
        //     let mut first_cons_perm = first_locked_cons.acquire_lock();
        //     let first_cons_view = first_locked_cons.cell.borrow(Tracked(first_cons_perm.borrow_mut()));

        //     // If a Cons with this value already exists:
        //     if (insert_car_raw == first_cons_view.car) {
        //         // Return early and do nothing - the Cons exists.
        //         self.release_lock(nil_perm);
        //         first_locked_cons.release_lock(first_cons_perm);
        //         return;
        //     }

        //     // If the first Cons cdr is larger than the insert cdr:
        //     if (insert_car_raw < first_cons_view.car) {

        //         // Then we insert inbetween Nil and first Cons
        //         let mut nil = self.cell.take(Tracked(nil_perm.borrow_mut()));

        //         let tracked token_tuple;
        //         let tracked updated_nil_token;
        //         let tracked cons_token;

        //         proof {
        //             token_tuple = self.instance.borrow().insert(
        //                 self.view_car(), 
        //                 insert_car, 
        //                 nil.map_token.value(), 
        //                 nil.map_token.get()
        //             );
        //             updated_nil_token = token_tuple.0.get();
        //             cons_token = token_tuple.1.get();
        //         }

        //         let locked_cons = LockedCons::new(
        //             insert_car_raw, 
        //             Tracked(cons_token), 
        //             Some(first_locked_cons.clone()), 
        //             self.instance.clone()
        //         );

        //         nil.cdr = Some(Arc::new(locked_cons));
        //         nil.map_token = Tracked(updated_nil_token);

        //         self.cell.put(Tracked(nil_perm.borrow_mut()), nil);

        //         self.release_lock(nil_perm);
        //         first_locked_cons.release_lock(first_cons_perm);
        //         return;
        //     }

        //     // If we have reached here, we may release the nil lock:
        //     self.release_lock(nil_perm);

        //     // Any insert from here onwards will not involve nil - 
        //     // we may delegate the insert to a chain of LockedCons
        //     first_locked_cons.insert(first_cons_perm, insert_car_raw);
        // }
    }
}

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
                    &&& cpat.map_token.key() == cpat.cons_perm
                    &&& (cpat.map_token.value().is_none() <==> cpat.cons_perm.value().cdr.is_none()) 
                    &&& (cpat.map_token.value().is_some() ==> 
                            (
                                cpat.cons_perm.value().cdr.unwrap().wf() &&
                                cpat.cons_perm.value().cdr.unwrap().view_instance() == instance &&
                                cpat.cons_perm.value().cdr.unwrap().view_car() == cpat.map_token.value().unwrap().value().car
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

    fn new(car: u32, cdr: Option<Arc<LockedCons>>, instance: Tracked<machine::Instance>) -> (cons_and_perm: (Self, Tracked<PointsTo<Cons>>))
        ensures 
            cons_and_perm.0.wf(),
            cons_and_perm.0.instance == instance,
            cons_and_perm.0.view_car == car,
            cons_and_perm.0.cons_cell.id() == cons_and_perm.1.id(),
            cons_and_perm.1.is_init(),
            cons_and_perm.1.value().cdr == cdr,
            cons_and_perm.1.value().car == car
    {   
        let view_car = Ghost(car);
        let cons = Cons { car, cdr };
        let (cons_cell, Tracked(cons_perm)) = PCell::new(cons);
        let atomic = AtomicBool::new(Ghost((cons_cell, instance, view_car)), true, Tracked(None));
        (Self { atomic, cons_cell, instance, view_car }, Tracked(cons_perm))
    }

    fn acquire_lock(&self) -> (cpat: Tracked<ConsPermAndToken>)
        requires 
            self.wf(),
        ensures 
            cpat.cons_perm.is_init(),
            cpat.cons_perm.id() == self.cons_cell.id(),
            cpat.map_token.instance_id() == self.instance.id(),
            cpat.map_token.key() == cpat.cons_perm,
            (cpat.map_token.value().is_none() <==> cpat.cons_perm.value().cdr.is_none()),
            (cpat.map_token.value().is_some() ==> 
                (
                    cpat.cons_perm.value().cdr.unwrap().wf() &&
                    cpat.cons_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    cpat.cons_perm.value().cdr.unwrap().view_car() == cpat.map_token.value().unwrap().value().car
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
            cpat.map_token.key() == cpat.cons_perm,
            (cpat.map_token.value().is_none() <==> cpat.cons_perm.value().cdr.is_none()),
            (cpat.map_token.value().is_some() ==> 
                (
                    cpat.cons_perm.value().cdr.unwrap().wf() &&
                    cpat.cons_perm.value().cdr.unwrap().view_instance() == self.instance &&
                    cpat.cons_perm.value().cdr.unwrap().view_car() == cpat.map_token.value().unwrap().value().car
                )
            )
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