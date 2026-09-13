#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use std::sync::Arc;
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{
    atomic_ghost::*, cell::pcell_maybe_uninit::*, modes::*, pervasive::*, prelude::*, thread::*,
};

verus! {

tokenized_state_machine!{
    machine {
        fields {

            // First element in the list (held by LockedNil)

            #[sharding(variable)]
            pub list_head: Option<u32>,

            // Linked list tokens (held by LockedCell)

            #[sharding(map)]
            pub list_representation: Map<u32, Option<u32>>,
        }

        #[invariant]
        pub fn empty_list_inv(&self) -> bool {
            self.list_head.is_none() <==> self.list_representation.is_empty()
        }

        #[invariant]
        pub fn non_empty_list_inv(&self) -> bool {
            self.list_head.is_some() ==> self.list_representation.contains_key(self.list_head.unwrap())
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
        pub fn largest_cell_points_to_none_inv(&self) -> bool {
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
        pub fn second_largest_cell_points_to_none_inv(&self) -> bool {
            forall |elem_1: u32, elem_2: u32| #![auto]
                (
                    self.list_representation.contains_pair(elem_2, None) &&
                    self.list_representation.contains_pair(elem_1, Some(elem_2))
                ) ==> (
                    forall |elem_3: u32| #![auto]
                        (
                            self.list_representation.contains_key(elem_3) &&
                            elem_3 != elem_1 &&
                            elem_3 != elem_2
                        ) ==> elem_1 > elem_3
                )
        }

        #[invariant]
        pub fn list_head_has_smallest_cell_inv(&self) -> bool {
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
                require(lower_elem < delete_elem);

                remove list_representation -= [lower_elem => Some(delete_elem)];
                remove list_representation -= [delete_elem => let option_elem];
                add list_representation += [lower_elem => option_elem];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(empty_list_insert)]
        fn empty_list_insert_inductive(pre: Self, post: Self, insert_elem: u32) { }

        #[inductive(insert_at_head)]
        fn insert_at_head_inductive(pre: Self, post: Self, insert_elem: u32, upper_elem: u32) {
            assert(
                forall |elem: u32, option_elem: Option<u32>| #![auto]
                (
                    post.list_representation.contains_pair(elem, option_elem)
                ) ==>
                (
                    pre.list_representation.contains_pair(elem, option_elem) || elem == insert_elem
                )
            );
        }

        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, lower_elem: u32, insert_elem: u32, upper_elem: u32) {
            assert(
                forall |elem: u32, option_elem: Option<u32>| #![auto]
                (
                    post.list_representation.contains_pair(elem, option_elem)
                ) ==>
                (
                    pre.list_representation.contains_pair(elem, option_elem) ||
                    (elem == lower_elem && Some(insert_elem) == option_elem) ||
                    (elem == insert_elem && Some(upper_elem) == option_elem)
                )
            );
        }

        #[inductive(insert_at_tail)]
        fn insert_at_tail_inductive(pre: Self, post: Self, lower_elem: u32, insert_elem: u32) {
            assert(
                forall |elem: u32, option_elem: Option<u32>| #![auto]
                (
                    post.list_representation.contains_pair(elem, option_elem)
                ) ==>
                (
                    pre.list_representation.contains_pair(elem, option_elem) ||
                    (elem == lower_elem && Some(insert_elem) == option_elem) ||
                    (elem == insert_elem && None == option_elem)
                )
            );
        }

        #[inductive(delete_at_head)]
        fn delete_at_head_inductive(pre: Self, post: Self, delete_elem: u32) {
            assert(
                forall |elem: u32, option_elem: Option<u32>| #![auto]
                (
                    post.list_representation.contains_pair(elem, option_elem)
                ) ==> pre.list_representation.contains_pair(elem, option_elem)
            );

            assert(
                post.list_head.is_none() <==> pre.list_representation.contains_pair(delete_elem, None)
            );

            assert(
                post.list_head.is_some() ==> (
                    pre.list_representation.contains_pair(delete_elem, pre.list_representation.index(delete_elem)) &&
                    pre.list_representation.contains_key(pre.list_representation.index(delete_elem).unwrap())
                )
            );
        }

        #[inductive(delete)]
        fn delete_inductive(pre: Self, post: Self, lower_elem: u32, delete_elem: u32) {
            assert(
                forall |elem: u32, option_elem: Option<u32>| #![auto]
                (
                    post.list_representation.contains_pair(elem, option_elem)
                ) ==> (
                    pre.list_representation.contains_pair(elem, option_elem) ||
                    (elem == lower_elem && option_elem == pre.list_representation.index(delete_elem))
                )
            );

            if (pre.list_representation.index(delete_elem).is_some()) {
                assert(pre.list_representation.contains_pair(delete_elem, pre.list_representation.index(delete_elem)));
            }
        }
    }
}

pub struct Nil {
    pub next: Option<Arc<LockedCell>>,
}

pub tracked struct NilPermAndToken {
    pub nil_perm: PointsTo<Nil>,
    pub list_head: machine::list_head,
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
                    &&& (npat.list_head.value().is_none() <==> npat.nil_perm.value().next.is_none())
                    &&& (npat.list_head.value().is_some() ==>
                            (
                                npat.nil_perm.value().next.unwrap().wf() &&
                                npat.nil_perm.value().next.unwrap().view_instance() == instance &&
                                npat.nil_perm.value().next.unwrap().view_elem() == npat.list_head.value().unwrap()
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
        let nil = Nil { next: None::<Arc<LockedCell>> };
        let (nil_cell, Tracked(nil_perm)) = PCell::new(nil);

        let tracked (Tracked(instance), Tracked(list_head), Tracked(list_representation)) =
            machine::Instance::initialize();

        let tracked pat = NilPermAndToken { nil_perm, list_head };

        let atomic = AtomicBool::new(
            Ghost((nil_cell, Tracked(instance))),
            false,
            Tracked(Some(pat)),
        );
        Self { atomic, nil_cell, instance: Tracked(instance) }
    }

    fn acquire_lock(&self) -> (npat: Tracked<NilPermAndToken>)
        requires
            self.wf(),
        ensures
            npat.nil_perm.is_init(),
            npat.nil_perm.id() == self.nil_cell.id(),
            npat.list_head.instance_id() == self.instance.id(),
            (npat.list_head.value().is_none() <==> npat.nil_perm.value().next.is_none()),
            (npat.list_head.value().is_some() ==> (npat.nil_perm.value().next.unwrap().wf()
                && npat.nil_perm.value().next.unwrap().view_instance() == self.instance
                && npat.nil_perm.value().next.unwrap().view_elem()
                == npat.list_head.value().unwrap())),
            self.wf(),
    {
        loop
            invariant
                self.wf(),
        {
            let tracked mut points_to_opt = None;
            let res =
                atomic_with_ghost!(
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
            (npat.list_head.value().is_none() <==> npat.nil_perm.value().next.is_none()),
            (npat.list_head.value().is_some() ==> (npat.nil_perm.value().next.unwrap().wf()
                && npat.nil_perm.value().next.unwrap().view_instance() == self.instance
                && npat.nil_perm.value().next.unwrap().view_elem()
                == npat.list_head.value().unwrap())),
            self.wf(),
        ensures
            self.wf(),
    {
        atomic_with_ghost!(
            &self.atomic => store(false);
            ghost points_to_inv => {
                points_to_inv = Some(npat.get());
            }
        );
    }

    fn insert(self: Arc<Self>, insert_elem: u32)
        requires
            self.wf(),
        ensures
            self.wf(),
    {
        // Acquire the lock for the nil node, and view the data inside (without taking)
        let mut nil_perm_and_token = self.acquire_lock();
        let nil_view = self.nil_cell.borrow(Tracked(&mut nil_perm_and_token.nil_perm));

        // If the nil next is none, then we must insert here - at the tail
        if (nil_view.next.is_none()) {
            let tracked map_token;

            proof {
                map_token =
                self.instance.empty_list_insert(insert_elem, &mut nil_perm_and_token.list_head);
            }

            let locked_cell = LockedCell::new(
                insert_elem,
                None::<Arc<LockedCell>>,
                self.instance.clone(),
                Tracked(map_token),
            );

            let arc_locked_cell = Arc::new(locked_cell);

            let mut nil = self.nil_cell.take(Tracked(&mut nil_perm_and_token.nil_perm));
            nil.next = Some(arc_locked_cell.clone());
            self.nil_cell.put(Tracked(&mut nil_perm_and_token.nil_perm), nil);
            self.release_lock(nil_perm_and_token);
            return;
        } else {
            // We check if we need to insert inbetween Nil and the first Cell
            let first_locked_cell = nil_view.next.as_ref().unwrap().clone();
            let mut first_cell_perm_and_token = first_locked_cell.acquire_lock();
            let first_cell_view = first_locked_cell.cell_cell.borrow(
                Tracked(&mut first_cell_perm_and_token.cell_perm),
            );

            // If a Cell with this value already exists:
            if (insert_elem == first_cell_view.elem) {
                // Return early and do nothing - the Cell exists.
                self.release_lock(nil_perm_and_token);
                first_locked_cell.release_lock(first_cell_perm_and_token);
                return;
            }
            // If the first Cell next is larger than the insert next:

            if (insert_elem < first_cell_view.elem) {
                // Then we insert inbetween Nil and first Cell
                let tracked map_token;

                proof {
                    map_token =
                    self.instance.insert_at_head(
                        insert_elem,
                        first_cell_view.elem,
                        &mut nil_perm_and_token.list_head,
                    );
                }

                let locked_cell = LockedCell::new(
                    insert_elem,
                    Some(first_locked_cell.clone()),
                    self.instance.clone(),
                    Tracked(map_token),
                );

                let arc_locked_cell = Arc::new(locked_cell);

                let mut nil = self.nil_cell.take(Tracked(&mut nil_perm_and_token.nil_perm));
                nil.next = Some(arc_locked_cell.clone());
                self.nil_cell.put(Tracked(&mut nil_perm_and_token.nil_perm), nil);

                self.release_lock(nil_perm_and_token);
                first_locked_cell.release_lock(first_cell_perm_and_token);
                return;
            }
            // If we have reached here, we may release the nil lock:

            self.release_lock(nil_perm_and_token);

            // Any insert from here onwards will not involve nil -
            // we may delegate the insert to a chain of LockedCell
            first_locked_cell.insert(insert_elem, first_cell_perm_and_token);
        }
    }

    fn delete(self: Arc<Self>, delete_elem: u32)
        requires
            self.wf(),
        ensures
            self.wf(),
    {
        // Acquire the lock for the nil node, and view the data inside (without taking)
        let mut nil_perm_and_token = self.acquire_lock();
        let nil_view = self.nil_cell.borrow(Tracked(&mut nil_perm_and_token.nil_perm));

        // If the nil next is none, then we are done - no tokens exist ==> no nodes exist
        if (nil_view.next.is_none()) {
            self.release_lock(nil_perm_and_token);
            return;
        }
        // We check if we need to delete the first Cell (hence lower is LockedNil)

        let first_locked_cell = nil_view.next.as_ref().unwrap().clone();
        let mut first_cell_perm_and_token = first_locked_cell.acquire_lock();
        let tracked CellPermAndToken { cell_perm, map_token } = first_cell_perm_and_token.get();

        let first_cell_view = first_locked_cell.cell_cell.borrow(Tracked(&mut cell_perm));

        // If the first elem is larger than our delete, then we are done - no tokens exist ==> no nodes exist
        if (delete_elem < first_cell_view.elem) {
            self.release_lock(nil_perm_and_token);
            first_locked_cell.release_lock(Tracked(CellPermAndToken { cell_perm, map_token }));
            return;
        }//
        // Check if we are deleting the first LockedCell:

        if (delete_elem == first_cell_view.elem) {
            let mut nil = self.nil_cell.take(Tracked(&mut nil_perm_and_token.nil_perm));
            let mut first_cell = first_locked_cell.cell_cell.take(Tracked(&mut cell_perm));

            proof {
                self.instance.delete_at_head(
                    delete_elem,
                    &mut nil_perm_and_token.list_head,
                    map_token,
                );
            }

            nil.next = first_cell.next;
            self.nil_cell.put(Tracked(&mut nil_perm_and_token.nil_perm), nil);

            self.release_lock(nil_perm_and_token);

            return;
        }
        // We can release the dummy node lock.

        self.release_lock(nil_perm_and_token);
        // // and begin our traversal:
        first_locked_cell.delete(delete_elem, Tracked(CellPermAndToken { cell_perm, map_token }));
    }

    #[verifier::external_body]
    pub fn print_list(self: Arc<Self>) {
        let mut nil_perm_and_token = self.acquire_lock();
        let nil_view = self.nil_cell.borrow(Tracked(&mut nil_perm_and_token.nil_perm));

        let first_locked_cell = nil_view.next.as_ref().unwrap().clone();
        let mut first_cell_perm_and_token = first_locked_cell.acquire_lock();

        self.release_lock(nil_perm_and_token);
        first_locked_cell.print_list(first_cell_perm_and_token);
    }
}

pub struct Cell {
    pub elem: u32,
    pub next: Option<Arc<LockedCell>>,
}

pub tracked struct CellPermAndToken {
    pub cell_perm: PointsTo<Cell>,
    pub map_token: machine::list_representation,
}

struct_with_invariants!{
    pub struct LockedCell {
        atomic: AtomicBool<_, Option<CellPermAndToken>, _>,
        cell_cell: PCell<Cell>,
        instance: Tracked<machine::Instance>,
        view_elem: Ghost<u32>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant on atomic with (cell_cell, instance, view_elem) is (v: bool, option_cpat: Option<CellPermAndToken>) {
            match option_cpat {
                None => v == true,
                Some(cpat) => {
                    &&& v == false
                    &&& cpat.cell_perm.is_init()
                    &&& cpat.cell_perm.id() == cell_cell.id()
                    &&& cpat.map_token.instance_id() == instance.id()
                    &&& cpat.map_token.key() == view_elem
                    &&& cpat.cell_perm.value().elem == view_elem
                    &&& (cpat.map_token.value().is_none() <==> cpat.cell_perm.value().next.is_none())
                    &&& (cpat.map_token.value().is_some() ==>
                            (
                                cpat.cell_perm.value().next.unwrap().wf() &&
                                cpat.cell_perm.value().next.unwrap().view_instance() == instance &&
                                cpat.cell_perm.value().next.unwrap().view_elem() == cpat.map_token.value().unwrap() &&
                                cpat.cell_perm.value().next.unwrap().view_elem() > cpat.cell_perm.value().elem
                            )
                        )
                }
            }
        }
    }
}

impl LockedCell {
    pub closed spec fn view_elem(&self) -> (view_elem: u32) {
        self.view_elem@
    }

    pub closed spec fn view_instance(&self) -> (instance: machine::Instance) {
        self.instance@
    }

    fn new(
        elem: u32,
        next: Option<Arc<LockedCell>>,
        instance: Tracked<machine::Instance>,
        map_token: Tracked<machine::list_representation>,
    ) -> (locked_cell: Self)
        requires
            map_token.instance_id() == instance.id(),
            map_token.key() == elem,
            (map_token.value().is_none() <==> next.is_none()),
            (map_token.value().is_some() ==> (next.unwrap().wf() && next.unwrap().view_instance()
                == instance && next.unwrap().view_elem() == map_token.value().unwrap()
                && next.unwrap().view_elem() > elem)),
        ensures
            locked_cell.wf(),
            locked_cell.instance == instance,
            locked_cell.view_elem == elem,
    {
        let view_elem = Ghost(elem);
        let cell = Cell { elem, next };
        let (cell_cell, Tracked(cell_perm)) = PCell::new(cell);
        let tracked cpat = CellPermAndToken { cell_perm, map_token: map_token.get() };
        let atomic = AtomicBool::new(
            Ghost((cell_cell, instance, view_elem)),
            false,
            Tracked(Some(cpat)),
        );
        Self { atomic, cell_cell, instance, view_elem }
    }

    fn acquire_lock(&self) -> (cpat: Tracked<CellPermAndToken>)
        requires
            self.wf(),
        ensures
            cpat.cell_perm.is_init(),
            cpat.cell_perm.id() == self.cell_cell.id(),
            cpat.map_token.instance_id() == self.instance.id(),
            cpat.map_token.key() == self.view_elem,
            cpat.cell_perm.value().elem == self.view_elem,
            (cpat.map_token.value().is_none() <==> cpat.cell_perm.value().next.is_none()),
            (cpat.map_token.value().is_some() ==> (cpat.cell_perm.value().next.unwrap().wf()
                && cpat.cell_perm.value().next.unwrap().view_instance() == self.instance
                && cpat.cell_perm.value().next.unwrap().view_elem()
                == cpat.map_token.value().unwrap()
                && cpat.cell_perm.value().next.unwrap().view_elem() > cpat.cell_perm.value().elem)),
            self.wf(),
    {
        loop
            invariant
                self.wf(),
        {
            let tracked mut points_to_opt = None;
            let res =
                atomic_with_ghost!(
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

    fn release_lock(&self, cpat: Tracked<CellPermAndToken>)
        requires
            self.wf(),
            cpat.cell_perm.is_init(),
            cpat.cell_perm.id() == self.cell_cell.id(),
            cpat.map_token.instance_id() == self.instance.id(),
            cpat.map_token.key() == self.view_elem,
            cpat.cell_perm.value().elem == self.view_elem,
            (cpat.map_token.value().is_none() <==> cpat.cell_perm.value().next.is_none()),
            (cpat.map_token.value().is_some() ==> (cpat.cell_perm.value().next.unwrap().wf()
                && cpat.cell_perm.value().next.unwrap().view_instance() == self.instance
                && cpat.cell_perm.value().next.unwrap().view_elem()
                == cpat.map_token.value().unwrap()
                && cpat.cell_perm.value().next.unwrap().view_elem() > cpat.cell_perm.value().elem)),
        ensures
            self.wf(),
    {
        atomic_with_ghost!(
            &self.atomic => store(false);
            ghost points_to_inv => {
                points_to_inv = Some(cpat.get());
            }
        );
    }

    fn insert(self: Arc<Self>, insert_elem: u32, mut cpat: Tracked<CellPermAndToken>)
        requires
            self.wf(),
            cpat.cell_perm.is_init(),
            cpat.cell_perm.id() == self.cell_cell.id(),
            cpat.map_token.instance_id() == self.instance.id(),
            cpat.map_token.key() == self.view_elem,
            cpat.cell_perm.value().elem == self.view_elem,
            (cpat.map_token.value().is_none() <==> cpat.cell_perm.value().next.is_none()),
            (cpat.map_token.value().is_some() ==> (cpat.cell_perm.value().next.unwrap().wf()
                && cpat.cell_perm.value().next.unwrap().view_instance() == self.instance
                && cpat.cell_perm.value().next.unwrap().view_elem()
                == cpat.map_token.value().unwrap()
                && cpat.cell_perm.value().next.unwrap().view_elem() > cpat.cell_perm.value().elem)),
            cpat.cell_perm.value().elem < insert_elem,
        ensures
            self.wf(),
    {
        let mut current_locked_cell = self;
        loop
            invariant
                self.wf(),
                current_locked_cell.wf(),
                current_locked_cell.instance == self.instance,
                cpat.cell_perm.is_init(),
                cpat.cell_perm.id() == current_locked_cell.cell_cell.id(),
                cpat.map_token.instance_id() == current_locked_cell.instance.id(),
                cpat.map_token.key() == current_locked_cell.view_elem,
                cpat.cell_perm.value().elem == current_locked_cell.view_elem,
                (cpat.map_token.value().is_none() <==> cpat.cell_perm.value().next.is_none()),
                (cpat.map_token.value().is_some() ==> (cpat.cell_perm.value().next.unwrap().wf()
                    && cpat.cell_perm.value().next.unwrap().view_instance()
                    == current_locked_cell.instance
                    && cpat.cell_perm.value().next.unwrap().view_elem()
                    == cpat.map_token.value().unwrap()
                    && cpat.cell_perm.value().next.unwrap().view_elem()
                    > cpat.cell_perm.value().elem)),
                cpat.cell_perm.value().elem < insert_elem,
            decreases insert_elem - cpat.cell_perm.value().elem,
        {
            let tracked CellPermAndToken { cell_perm, map_token } = cpat.get();
            let mut current_cell_view = current_locked_cell.cell_cell.borrow(
                Tracked(&mut cell_perm),
            );

            // If there is no next LockedCell, then we must insert at the tail after a Cell
            if (current_cell_view.next.is_none()) {
                let mut old_tail_cell = current_locked_cell.cell_cell.take(Tracked(&mut cell_perm));

                let tracked token_tuple;
                let tracked updated_old_tail_cell_token;
                let tracked new_tail_cell_token;

                proof {
                    token_tuple =
                    current_locked_cell.instance.insert_at_tail(
                        old_tail_cell.elem,
                        insert_elem,
                        map_token,
                    );
                    updated_old_tail_cell_token = token_tuple.0.get();
                    new_tail_cell_token = token_tuple.1.get();
                }

                let locked_cell = LockedCell::new(
                    insert_elem,
                    None::<Arc<LockedCell>>,
                    current_locked_cell.instance.clone(),
                    Tracked(new_tail_cell_token),
                );

                old_tail_cell.next = Some(Arc::new(locked_cell));
                current_locked_cell.cell_cell.put(Tracked(&mut cell_perm), old_tail_cell);
                current_locked_cell.release_lock(
                    Tracked(CellPermAndToken { cell_perm, map_token: updated_old_tail_cell_token }),
                );
                return;
            }
            // Otherwise, there is another LockedCell
             else {
                // Acquire the permissions to access the Cell:
                let next_locked_cell = current_cell_view.next.as_ref().unwrap().clone();
                let mut next_cpat = next_locked_cell.acquire_lock();
                let tracked CellPermAndToken {
                    cell_perm: next_cell_perm,
                    map_token: next_map_token,
                } = next_cpat.get();
                let next_cell_view = next_locked_cell.cell_cell.borrow(
                    Tracked(&mut next_cell_perm),
                );

                // If a Cell with this value already exists:
                if (insert_elem == next_cell_view.elem) {
                    // Return early and do nothing - the Cell exists.
                    current_locked_cell.release_lock(
                        Tracked(CellPermAndToken { cell_perm, map_token }),
                    );
                    next_locked_cell.release_lock(
                        Tracked(
                            CellPermAndToken {
                                cell_perm: next_cell_perm,
                                map_token: next_map_token,
                            },
                        ),
                    );
                    return;
                }
                // If the next Cell next is larger than the insert next:

                if (insert_elem < next_cell_view.elem) {
                    // Then we insert inbetween Cell and Cell
                    let mut current_cell = current_locked_cell.cell_cell.take(
                        Tracked(&mut cell_perm),
                    );

                    let tracked token_tuple;
                    let tracked updated_cell_token;
                    let tracked new_cell_token;

                    // insert(lower_elem: u32, insert_elem: u32, upper_elem: u32)

                    proof {
                        token_tuple =
                        current_locked_cell.instance.insert(
                            current_cell.elem,
                            insert_elem,
                            next_cell_view.elem,
                            map_token,
                        );
                        updated_cell_token = token_tuple.0.get();
                        new_cell_token = token_tuple.1.get();
                    }

                    let locked_cell = LockedCell::new(
                        insert_elem,
                        Some(next_locked_cell.clone()),
                        current_locked_cell.instance.clone(),
                        Tracked(new_cell_token),
                    );

                    current_cell.next = Some(Arc::new(locked_cell));

                    current_locked_cell.cell_cell.put(Tracked(&mut cell_perm), current_cell);

                    current_locked_cell.release_lock(
                        Tracked(CellPermAndToken { cell_perm, map_token: updated_cell_token }),
                    );
                    next_locked_cell.release_lock(
                        Tracked(
                            CellPermAndToken {
                                cell_perm: next_cell_perm,
                                map_token: next_map_token,
                            },
                        ),
                    );
                    return;
                }
                // Otherwise, we give up the previous lock, and loop again

                current_locked_cell.release_lock(
                    Tracked(CellPermAndToken { cell_perm, map_token }),
                );

                current_locked_cell = next_locked_cell;
                cpat =
                Tracked(CellPermAndToken { cell_perm: next_cell_perm, map_token: next_map_token });
            }
        }
    }

    fn delete(self: Arc<Self>, delete_elem: u32, mut cpat: Tracked<CellPermAndToken>)
        requires
            self.wf(),
            cpat.cell_perm.is_init(),
            cpat.cell_perm.id() == self.cell_cell.id(),
            cpat.map_token.instance_id() == self.instance.id(),
            cpat.map_token.key() == self.view_elem,
            cpat.cell_perm.value().elem == self.view_elem,
            (cpat.map_token.value().is_none() <==> cpat.cell_perm.value().next.is_none()),
            (cpat.map_token.value().is_some() ==> (cpat.cell_perm.value().next.unwrap().wf()
                && cpat.cell_perm.value().next.unwrap().view_instance() == self.instance
                && cpat.cell_perm.value().next.unwrap().view_elem()
                == cpat.map_token.value().unwrap()
                && cpat.cell_perm.value().next.unwrap().view_elem() > cpat.cell_perm.value().elem)),
            cpat.cell_perm.value().elem < delete_elem,
        ensures
            self.wf(),
    {
        let mut current_locked_cell = self;
        loop
            invariant
                self.wf(),
                current_locked_cell.wf(),
                current_locked_cell.instance == self.instance,
                cpat.cell_perm.is_init(),
                cpat.cell_perm.id() == current_locked_cell.cell_cell.id(),
                cpat.map_token.instance_id() == current_locked_cell.instance.id(),
                cpat.map_token.key() == current_locked_cell.view_elem,
                cpat.cell_perm.value().elem == current_locked_cell.view_elem,
                (cpat.map_token.value().is_none() <==> cpat.cell_perm.value().next.is_none()),
                (cpat.map_token.value().is_some() ==> (cpat.cell_perm.value().next.unwrap().wf()
                    && cpat.cell_perm.value().next.unwrap().view_instance()
                    == current_locked_cell.instance
                    && cpat.cell_perm.value().next.unwrap().view_elem()
                    == cpat.map_token.value().unwrap()
                    && cpat.cell_perm.value().next.unwrap().view_elem()
                    > cpat.cell_perm.value().elem)),
                cpat.cell_perm.value().elem < delete_elem
                // decreases
                //     delete_elem_raw - current_cell_perm.value().elem
                ,
        {
            let tracked CellPermAndToken { cell_perm, map_token } = cpat.get();
            let mut current_cell_view = current_locked_cell.cell_cell.borrow(
                Tracked(&mut cell_perm),
            );

            // If there is no next LockedCell, then we have reached the tail.
            // If we have not deleted by now, then we are done - no tokens exist ==> no nodes exist
            if (current_cell_view.next.is_none()) {
                current_locked_cell.release_lock(
                    Tracked(CellPermAndToken { cell_perm, map_token }),
                );
                return;
            }
            // Otherwise, there is another LockedCell
             else {
                // Acquire the permissions to access the Cell:
                let next_locked_cell = current_cell_view.next.as_ref().unwrap().clone();
                let mut next_cpat = next_locked_cell.acquire_lock();
                let tracked CellPermAndToken {
                    cell_perm: next_cell_perm,
                    map_token: next_map_token,
                } = next_cpat.get();
                let next_cell_view = next_locked_cell.cell_cell.borrow(
                    Tracked(&mut next_cell_perm),
                );

                // If the next elem is larger than our delete, then we have:
                // lower_elem < delete_elem < upper_elem
                // Which means that no node exist with value delete_elem.
                // We are done - no tokens exist ==> no nodes exist
                if (delete_elem < next_cell_view.elem) {
                    current_locked_cell.release_lock(
                        Tracked(CellPermAndToken { cell_perm, map_token }),
                    );
                    next_locked_cell.release_lock(
                        Tracked(
                            CellPermAndToken {
                                cell_perm: next_cell_perm,
                                map_token: next_map_token,
                            },
                        ),
                    );
                    return;
                }
                // Check if we are deleting this LockedCell:

                if (delete_elem == next_cell_view.elem) {
                    let mut current_cell = current_locked_cell.cell_cell.take(
                        Tracked(&mut cell_perm),
                    );
                    let mut next_cell = next_locked_cell.cell_cell.take(
                        Tracked(&mut next_cell_perm),
                    );

                    let tracked updated_map_token;

                    proof {
                        updated_map_token =
                        current_locked_cell.instance.delete(
                            current_cell.elem,
                            delete_elem,
                            map_token,
                            next_map_token,
                        );
                    }

                    current_cell.next = next_cell.next;

                    current_locked_cell.cell_cell.put(Tracked(&mut cell_perm), current_cell);
                    current_locked_cell.release_lock(
                        Tracked(CellPermAndToken { cell_perm, map_token: updated_map_token }),
                    );
                    return;
                }
                // Otherwise, we give up the previous lock, and loop again

                current_locked_cell.release_lock(
                    Tracked(CellPermAndToken { cell_perm, map_token }),
                );
                current_locked_cell = next_locked_cell;
                cpat =
                Tracked(CellPermAndToken { cell_perm: next_cell_perm, map_token: next_map_token });
            }
        }
    }

    #[verifier::external_body]
    pub fn print_list(self: Arc<Self>, mut cpat: Tracked<CellPermAndToken>) {
        let mut current_locked_cell = self;
        loop {
            let tracked CellPermAndToken { cell_perm, map_token };
            let mut current_cell_view = current_locked_cell.cell_cell.borrow(
                Tracked(&mut cell_perm),
            );
            println!("{}", current_cell_view.elem);

            if (current_cell_view.next.is_none()) {
                current_locked_cell.release_lock(
                    Tracked(CellPermAndToken { cell_perm, map_token }),
                );
                return;
            }
            let next_locked_cell = current_cell_view.next.as_ref().unwrap().clone();
            let mut next_cpat = next_locked_cell.acquire_lock();

            current_locked_cell.release_lock(Tracked(CellPermAndToken { cell_perm, map_token }));
            current_locked_cell = next_locked_cell;
            cpat = next_cpat;
        }
    }
}

pub struct LinkedList {
    pub locked_nil: Arc<LockedNil>,
}

impl LinkedList {
    pub closed spec fn wf(&self) -> bool {
        self.locked_nil.wf()
    }

    pub fn new() -> (linked_list: Arc<Self>)
        ensures
            linked_list.wf(),
    {
        Arc::new(Self { locked_nil: Arc::new(LockedNil::new()) })
    }

    pub fn insert(&self, elem: u32)
        requires
            self.wf(),
        ensures
            self.wf(),
    {
        self.locked_nil.clone().insert(elem)
    }

    pub fn delete(&self, elem: u32)
        requires
            self.wf(),
        ensures
            self.wf(),
    {
        self.locked_nil.clone().delete(elem)
    }

    #[verifier::external_body]
    pub fn print_list(&self) {
        self.locked_nil.clone().print_list();
    }
}

fn main() {
}

} // verus!
