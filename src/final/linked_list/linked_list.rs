#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use std::sync::Arc;
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{
    atomic_ghost::*, cell::pcell_maybe_uninit::*, modes::*, pervasive::*, prelude::*, thread::*,
};

//
// Verified with Verus version: 0.2026.08.30.b432e82
//

verus! {

tokenized_state_machine!{
    machine {
        fields {

            // First element in the list (held by LockedNil)

            #[sharding(variable)]
            pub list_head: Option<u32>,

            // Linked list tokens (held by LockedNode)

            #[sharding(map)]
            pub list_representation: Map<u32, Option<u32>>,
        }

        // list_head Invariants:

        #[invariant]
        pub fn empty_list_inv(&self) -> bool {
            self.list_head.is_none() <==> self.list_representation.is_empty()
        }

        #[invariant]
        pub fn non_empty_list_inv(&self) -> bool {
            self.list_head.is_some() ==> self.list_representation.contains_key(self.list_head.unwrap())
        }

        // Ordere List Invariants:

        #[invariant]
        pub fn ordered_key_value_pairs_inv(&self) -> bool {
            forall |elem_1: u32, elem_2: u32| #![auto]
                (
                    self.list_representation.contains_pair(elem_1, Some(elem_2))
                ) ==>
                    elem_1 < elem_2
        }

        #[invariant]
        pub fn largest_elem_points_to_none_inv(&self) -> bool {
            forall |elem_1: u32, elem_2: u32| #![auto]
                (
                    self.list_representation.contains_pair(elem_1, None) &&
                    self.list_representation.contains_key(elem_2) &&
                    elem_2 != elem_1
                ) ==>
                    elem_1 > elem_2
        }

        #[invariant]
        pub fn second_largest_elem_points_to_largest_elem_inv(&self) -> bool {
            forall |elem_1: u32, elem_2: u32, elem_3: u32| #![auto]
                (
                    self.list_representation.contains_pair(elem_2, None) &&
                    self.list_representation.contains_pair(elem_1, Some(elem_2)) &&
                    self.list_representation.contains_key(elem_3) &&
                    elem_3 != elem_1 &&
                    elem_3 != elem_2
                ) ==>
                    elem_1 > elem_3
        }

        #[invariant]
        pub fn list_head_has_smallest_elem_inv(&self) -> bool {
            forall |elem: u32| #![auto]
            (
                self.list_head.is_some() &&
                self.list_representation.contains_key(elem) &&
                elem != self.list_head.unwrap()
            ) ==>
            self.list_head.unwrap() < elem
        }

        // List Completeness Invariants:

        #[invariant]
        pub fn list_representation_map_is_complete(&self) -> bool {
            forall |elem_1: u32, elem_2: u32| #![auto]
                (
                    self.list_representation.contains_pair(elem_1, Some(elem_2))
                ) ==>
                self.list_representation.contains_key(elem_2)
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

        // Element Exclusion Invariant:

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

        // Inserts

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

        // Deletes

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
    pub next: Option<Arc<LockedNode>>,
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
        let nil = Nil { next: None::<Arc<LockedNode>> };
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
        // Acquire the lock for the nil node, and view the data inside (without taking):
        let mut nil_perm_and_token = self.acquire_lock();
        let nil_view = self.nil_cell.borrow(Tracked(&mut nil_perm_and_token.nil_perm));

        // If the nil next is none, then we must insert here (the list is empty):
        if (nil_view.next.is_none()) {
            let tracked map_token;

            proof {
                map_token =
                self.instance.empty_list_insert(insert_elem, &mut nil_perm_and_token.list_head);
            }

            let locked_node = LockedNode::new(
                insert_elem,
                None::<Arc<LockedNode>>,
                self.instance.clone(),
                Tracked(map_token),
            );

            let arc_locked_node = Arc::new(locked_node);

            let mut nil = self.nil_cell.take(Tracked(&mut nil_perm_and_token.nil_perm));
            nil.next = Some(arc_locked_node.clone());
            self.nil_cell.put(Tracked(&mut nil_perm_and_token.nil_perm), nil);
            self.release_lock(nil_perm_and_token);
            return;
        }

        // The list is not empty:
         else {
            // Acquire the lock for the nil node, and view the data inside (without taking):
            let first_locked_node = nil_view.next.as_ref().unwrap().clone();
            let mut first_node_perm_and_token = first_locked_node.acquire_lock();
            let first_node_view = first_locked_node.node_cell.borrow(
                Tracked(&mut first_node_perm_and_token.node_perm),
            );

            // If a Node with this value already exists:
            if (insert_elem == first_node_view.elem) {
                // Return early and do nothing - the Node exists.
                self.release_lock(nil_perm_and_token);
                first_locked_node.release_lock(first_node_perm_and_token);
                return;
            }

            // If the first Node's elem is larger than what we are inserting, then we insert here:
            if (insert_elem < first_node_view.elem) {
                let tracked map_token;

                proof {
                    map_token =
                    self.instance.insert_at_head(
                        insert_elem,
                        first_node_view.elem,
                        &mut nil_perm_and_token.list_head,
                    );
                }

                let locked_node = LockedNode::new(
                    insert_elem,
                    Some(first_locked_node.clone()),
                    self.instance.clone(),
                    Tracked(map_token),
                );

                let arc_locked_node = Arc::new(locked_node);

                let mut nil = self.nil_cell.take(Tracked(&mut nil_perm_and_token.nil_perm));
                nil.next = Some(arc_locked_node.clone());
                self.nil_cell.put(Tracked(&mut nil_perm_and_token.nil_perm), nil);

                self.release_lock(nil_perm_and_token);
                first_locked_node.release_lock(first_node_perm_and_token);
                return;
            }

            // We will insert after the first Node, we may release the Nil lock:
            self.release_lock(nil_perm_and_token);

            // Any insert from here onwards will not involve nil -
            // we may delegate the insert to a chain of LockedNode
            first_locked_node.insert(insert_elem, first_node_perm_and_token);
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

        // If the nil_view next is none, then we are done (the list is empty)
        if (nil_view.next.is_none()) {
            self.release_lock(nil_perm_and_token);
            return;
        }

        // Acquire the lock for the first node, and view the data inside (without taking)
        let first_locked_node = nil_view.next.as_ref().unwrap().clone();
        let mut first_node_perm_and_token = first_locked_node.acquire_lock();
        let tracked NodePermAndToken { node_perm, map_token } = first_node_perm_and_token.get();

        let first_node_view = first_locked_node.node_cell.borrow(Tracked(&mut node_perm));

        // If the first elem is larger than our delete, then we are done - no tokens exist ==> no nodes exist
        if (delete_elem < first_node_view.elem) {
            self.release_lock(nil_perm_and_token);
            first_locked_node.release_lock(Tracked(NodePermAndToken { node_perm, map_token }));
            return;
        }

        // Check if we are deleting the first LockedNode:
        if (delete_elem == first_node_view.elem) {
            let mut nil = self.nil_cell.take(Tracked(&mut nil_perm_and_token.nil_perm));
            let mut first_node = first_locked_node.node_cell.take(Tracked(&mut node_perm));

            proof {
                self.instance.delete_at_head(
                    delete_elem,
                    &mut nil_perm_and_token.list_head,
                    map_token,
                );
            }

            nil.next = first_node.next;
            self.nil_cell.put(Tracked(&mut nil_perm_and_token.nil_perm), nil);

            self.release_lock(nil_perm_and_token);

            return;
        }
        // We can release the dummy node lock.

        self.release_lock(nil_perm_and_token);
        // // and begin our traversal:
        first_locked_node.delete(delete_elem, Tracked(NodePermAndToken { node_perm, map_token }));
    }

    #[verifier::external_body]
    pub fn print_list(self: Arc<Self>) {
        let mut nil_perm_and_token = self.acquire_lock();
        let nil_view = self.nil_cell.borrow(Tracked(&mut nil_perm_and_token.nil_perm));

        let first_locked_node = nil_view.next.as_ref().unwrap().clone();
        let mut first_node_perm_and_token = first_locked_node.acquire_lock();

        self.release_lock(nil_perm_and_token);
        first_locked_node.print_list(first_node_perm_and_token);
    }
}

pub struct Node {
    pub elem: u32,
    pub next: Option<Arc<LockedNode>>,
}

pub tracked struct NodePermAndToken {
    pub node_perm: PointsTo<Node>,
    pub map_token: machine::list_representation,
}

struct_with_invariants!{
    pub struct LockedNode {
        atomic: AtomicBool<_, Option<NodePermAndToken>, _>,
        node_cell: PCell<Node>,
        instance: Tracked<machine::Instance>,
        view_elem: Ghost<u32>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant on atomic with (node_cell, instance, view_elem) is (v: bool, option_npat: Option<NodePermAndToken>) {
            match option_npat {
                None => v == true,
                Some(npat) => {
                    &&& v == false
                    &&& npat.node_perm.is_init()
                    &&& npat.node_perm.id() == node_cell.id()
                    &&& npat.map_token.instance_id() == instance.id()
                    &&& npat.map_token.key() == view_elem
                    &&& npat.node_perm.value().elem == view_elem
                    &&& (npat.map_token.value().is_none() <==> npat.node_perm.value().next.is_none())
                    &&& (npat.map_token.value().is_some() ==>
                            (
                                npat.node_perm.value().next.unwrap().wf() &&
                                npat.node_perm.value().next.unwrap().view_instance() == instance &&
                                npat.node_perm.value().next.unwrap().view_elem() == npat.map_token.value().unwrap() &&
                                npat.node_perm.value().next.unwrap().view_elem() > npat.node_perm.value().elem
                            )
                        )
                }
            }
        }
    }
}

impl LockedNode {
    pub closed spec fn view_elem(&self) -> (view_elem: u32) {
        self.view_elem@
    }

    pub closed spec fn view_instance(&self) -> (instance: machine::Instance) {
        self.instance@
    }

    fn new(
        elem: u32,
        next: Option<Arc<LockedNode>>,
        instance: Tracked<machine::Instance>,
        map_token: Tracked<machine::list_representation>,
    ) -> (locked_node: Self)
        requires
            map_token.instance_id() == instance.id(),
            map_token.key() == elem,
            (map_token.value().is_none() <==> next.is_none()),
            (map_token.value().is_some() ==> (next.unwrap().wf() && next.unwrap().view_instance()
                == instance && next.unwrap().view_elem() == map_token.value().unwrap()
                && next.unwrap().view_elem() > elem)),
        ensures
            locked_node.wf(),
            locked_node.instance == instance,
            locked_node.view_elem == elem,
    {
        let view_elem = Ghost(elem);
        let node = Node { elem, next };
        let (node_cell, Tracked(node_perm)) = PCell::new(node);
        let tracked npat = NodePermAndToken { node_perm, map_token: map_token.get() };
        let atomic = AtomicBool::new(
            Ghost((node_cell, instance, view_elem)),
            false,
            Tracked(Some(npat)),
        );
        Self { atomic, node_cell, instance, view_elem }
    }

    fn acquire_lock(&self) -> (npat: Tracked<NodePermAndToken>)
        requires
            self.wf(),
        ensures
            npat.node_perm.is_init(),
            npat.node_perm.id() == self.node_cell.id(),
            npat.map_token.instance_id() == self.instance.id(),
            npat.map_token.key() == self.view_elem,
            npat.node_perm.value().elem == self.view_elem,
            (npat.map_token.value().is_none() <==> npat.node_perm.value().next.is_none()),
            (npat.map_token.value().is_some() ==> (npat.node_perm.value().next.unwrap().wf()
                && npat.node_perm.value().next.unwrap().view_instance() == self.instance
                && npat.node_perm.value().next.unwrap().view_elem()
                == npat.map_token.value().unwrap()
                && npat.node_perm.value().next.unwrap().view_elem() > npat.node_perm.value().elem)),
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

    fn release_lock(&self, npat: Tracked<NodePermAndToken>)
        requires
            self.wf(),
            npat.node_perm.is_init(),
            npat.node_perm.id() == self.node_cell.id(),
            npat.map_token.instance_id() == self.instance.id(),
            npat.map_token.key() == self.view_elem,
            npat.node_perm.value().elem == self.view_elem,
            (npat.map_token.value().is_none() <==> npat.node_perm.value().next.is_none()),
            (npat.map_token.value().is_some() ==> (npat.node_perm.value().next.unwrap().wf()
                && npat.node_perm.value().next.unwrap().view_instance() == self.instance
                && npat.node_perm.value().next.unwrap().view_elem()
                == npat.map_token.value().unwrap()
                && npat.node_perm.value().next.unwrap().view_elem() > npat.node_perm.value().elem)),
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

    fn insert(self: Arc<Self>, insert_elem: u32, mut npat: Tracked<NodePermAndToken>)
        requires
            self.wf(),
            npat.node_perm.is_init(),
            npat.node_perm.id() == self.node_cell.id(),
            npat.map_token.instance_id() == self.instance.id(),
            npat.map_token.key() == self.view_elem,
            npat.node_perm.value().elem == self.view_elem,
            (npat.map_token.value().is_none() <==> npat.node_perm.value().next.is_none()),
            (npat.map_token.value().is_some() ==> (npat.node_perm.value().next.unwrap().wf()
                && npat.node_perm.value().next.unwrap().view_instance() == self.instance
                && npat.node_perm.value().next.unwrap().view_elem()
                == npat.map_token.value().unwrap()
                && npat.node_perm.value().next.unwrap().view_elem() > npat.node_perm.value().elem)),
            npat.node_perm.value().elem < insert_elem,
        ensures
            self.wf(),
    {
        let mut current_locked_node = self;
        loop
            invariant
                self.wf(),
                current_locked_node.wf(),
                current_locked_node.instance == self.instance,
                npat.node_perm.is_init(),
                npat.node_perm.id() == current_locked_node.node_cell.id(),
                npat.map_token.instance_id() == current_locked_node.instance.id(),
                npat.map_token.key() == current_locked_node.view_elem,
                npat.node_perm.value().elem == current_locked_node.view_elem,
                (npat.map_token.value().is_none() <==> npat.node_perm.value().next.is_none()),
                (npat.map_token.value().is_some() ==> (npat.node_perm.value().next.unwrap().wf()
                    && npat.node_perm.value().next.unwrap().view_instance()
                    == current_locked_node.instance
                    && npat.node_perm.value().next.unwrap().view_elem()
                    == npat.map_token.value().unwrap()
                    && npat.node_perm.value().next.unwrap().view_elem()
                    > npat.node_perm.value().elem)),
                npat.node_perm.value().elem < insert_elem,
            decreases insert_elem - npat.node_perm.value().elem,
        {
            let tracked NodePermAndToken { node_perm, map_token } = npat.get();
            let mut current_node_view = current_locked_node.node_cell.borrow(
                Tracked(&mut node_perm),
            );

            // If there is no next LockedNode, then we must insert at the tail
            if (current_node_view.next.is_none()) {
                let mut old_tail_node = current_locked_node.node_cell.take(Tracked(&mut node_perm));

                let tracked token_tuple;
                let tracked updated_old_tail_node_token;
                let tracked new_tail_node_token;

                proof {
                    token_tuple =
                    current_locked_node.instance.insert_at_tail(
                        old_tail_node.elem,
                        insert_elem,
                        map_token,
                    );
                    updated_old_tail_node_token = token_tuple.0.get();
                    new_tail_node_token = token_tuple.1.get();
                }

                let locked_node = LockedNode::new(
                    insert_elem,
                    None::<Arc<LockedNode>>,
                    current_locked_node.instance.clone(),
                    Tracked(new_tail_node_token),
                );

                old_tail_node.next = Some(Arc::new(locked_node));
                current_locked_node.node_cell.put(Tracked(&mut node_perm), old_tail_node);
                current_locked_node.release_lock(
                    Tracked(NodePermAndToken { node_perm, map_token: updated_old_tail_node_token }),
                );
                return;
            }

            // Otherwise, there is another LockedNode
             else {
                // Acquire the permissions to access the Node:
                let next_locked_node = current_node_view.next.as_ref().unwrap().clone();
                let mut next_npat = next_locked_node.acquire_lock();
                let tracked NodePermAndToken {
                    node_perm: next_node_perm,
                    map_token: next_map_token,
                } = next_npat.get();
                let next_node_view = next_locked_node.node_cell.borrow(
                    Tracked(&mut next_node_perm),
                );

                // If a Node with this value already exists:
                if (insert_elem == next_node_view.elem) {

                    // Return early without inserting
                    current_locked_node.release_lock(
                        Tracked(NodePermAndToken { node_perm, map_token }),
                    );
                    next_locked_node.release_lock(
                        Tracked(
                            NodePermAndToken {
                                node_perm: next_node_perm,
                                map_token: next_map_token,
                            },
                        ),
                    );
                    return;
                }

                // If the next Node's elem larger than what we are inserting:
                if (insert_elem < next_node_view.elem) {

                    // Then we insert inbetween Node and Node
                    let mut current_node = current_locked_node.node_cell.take(
                        Tracked(&mut node_perm),
                    );

                    let tracked token_tuple;
                    let tracked updated_node_token;
                    let tracked new_node_token;

                    proof {
                        token_tuple =
                        current_locked_node.instance.insert(
                            current_node.elem,
                            insert_elem,
                            next_node_view.elem,
                            map_token,
                        );
                        updated_node_token = token_tuple.0.get();
                        new_node_token = token_tuple.1.get();
                    }

                    let locked_node = LockedNode::new(
                        insert_elem,
                        Some(next_locked_node.clone()),
                        current_locked_node.instance.clone(),
                        Tracked(new_node_token),
                    );

                    current_node.next = Some(Arc::new(locked_node));

                    current_locked_node.node_cell.put(Tracked(&mut node_perm), current_node);

                    current_locked_node.release_lock(
                        Tracked(NodePermAndToken { node_perm, map_token: updated_node_token }),
                    );
                    next_locked_node.release_lock(
                        Tracked(
                            NodePermAndToken {
                                node_perm: next_node_perm,
                                map_token: next_map_token,
                            },
                        ),
                    );
                    return;
                }

                // Otherwise, we give up the previous lock, and loop again
                current_locked_node.release_lock(
                    Tracked(NodePermAndToken { node_perm, map_token }),
                );
                current_locked_node = next_locked_node;
                npat =
                Tracked(NodePermAndToken { node_perm: next_node_perm, map_token: next_map_token });
            }
        }
    }

    fn delete(self: Arc<Self>, delete_elem: u32, mut npat: Tracked<NodePermAndToken>)
        requires
            self.wf(),
            npat.node_perm.is_init(),
            npat.node_perm.id() == self.node_cell.id(),
            npat.map_token.instance_id() == self.instance.id(),
            npat.map_token.key() == self.view_elem,
            npat.node_perm.value().elem == self.view_elem,
            (npat.map_token.value().is_none() <==> npat.node_perm.value().next.is_none()),
            (npat.map_token.value().is_some() ==> (npat.node_perm.value().next.unwrap().wf()
                && npat.node_perm.value().next.unwrap().view_instance() == self.instance
                && npat.node_perm.value().next.unwrap().view_elem()
                == npat.map_token.value().unwrap()
                && npat.node_perm.value().next.unwrap().view_elem() > npat.node_perm.value().elem)),
            npat.node_perm.value().elem < delete_elem,
        ensures
            self.wf(),
    {
        let mut current_locked_node = self;
        loop
            invariant
                self.wf(),
                current_locked_node.wf(),
                current_locked_node.instance == self.instance,
                npat.node_perm.is_init(),
                npat.node_perm.id() == current_locked_node.node_cell.id(),
                npat.map_token.instance_id() == current_locked_node.instance.id(),
                npat.map_token.key() == current_locked_node.view_elem,
                npat.node_perm.value().elem == current_locked_node.view_elem,
                (npat.map_token.value().is_none() <==> npat.node_perm.value().next.is_none()),
                (npat.map_token.value().is_some() ==> (npat.node_perm.value().next.unwrap().wf()
                    && npat.node_perm.value().next.unwrap().view_instance()
                    == current_locked_node.instance
                    && npat.node_perm.value().next.unwrap().view_elem()
                    == npat.map_token.value().unwrap()
                    && npat.node_perm.value().next.unwrap().view_elem()
                    > npat.node_perm.value().elem)),
                npat.node_perm.value().elem < delete_elem,
            decreases delete_elem - npat.node_perm.value().elem,
        {
            let tracked NodePermAndToken { node_perm, map_token } = npat.get();
            let mut current_node_view = current_locked_node.node_cell.borrow(
                Tracked(&mut node_perm),
            );

            // If there is no next LockedNode, then we have reached the tail
            // The delete terminates as no node has the value
            if (current_node_view.next.is_none()) {
                current_locked_node.release_lock(
                    Tracked(NodePermAndToken { node_perm, map_token }),
                );
                return;
            }

            // Otherwise, there is another LockedNode
             else {
                // Acquire the permissions to access the Node:
                let next_locked_node = current_node_view.next.as_ref().unwrap().clone();
                let mut next_npat = next_locked_node.acquire_lock();
                let tracked NodePermAndToken {
                    node_perm: next_node_perm,
                    map_token: next_map_token,
                } = next_npat.get();
                let next_node_view = next_locked_node.node_cell.borrow(
                    Tracked(&mut next_node_perm),
                );

                // If the next elem is larger than our delete, then we have:
                // lower_elem < delete_elem < upper_elem
                // Which means that no node exist with value delete_elem.
                if (delete_elem < next_node_view.elem) {
                    current_locked_node.release_lock(
                        Tracked(NodePermAndToken { node_perm, map_token }),
                    );
                    next_locked_node.release_lock(
                        Tracked(
                            NodePermAndToken {
                                node_perm: next_node_perm,
                                map_token: next_map_token,
                            },
                        ),
                    );
                    return;
                }

                // If we are deleting the node we are on:
                if (delete_elem == next_node_view.elem) {
                    let mut current_node = current_locked_node.node_cell.take(
                        Tracked(&mut node_perm),
                    );
                    let mut next_node = next_locked_node.node_cell.take(
                        Tracked(&mut next_node_perm),
                    );

                    let tracked updated_map_token;

                    proof {
                        updated_map_token =
                        current_locked_node.instance.delete(
                            current_node.elem,
                            delete_elem,
                            map_token,
                            next_map_token,
                        );
                    }

                    current_node.next = next_node.next;

                    current_locked_node.node_cell.put(Tracked(&mut node_perm), current_node);
                    current_locked_node.release_lock(
                        Tracked(NodePermAndToken { node_perm, map_token: updated_map_token }),
                    );
                    return;
                }

                // Otherwise, we give up the previous lock, and loop again
                current_locked_node.release_lock(
                    Tracked(NodePermAndToken { node_perm, map_token }),
                );
                current_locked_node = next_locked_node;
                npat =
                Tracked(NodePermAndToken { node_perm: next_node_perm, map_token: next_map_token });
            }
        }
    }

    #[verifier::external_body]
    pub fn print_list(self: Arc<Self>, mut npat: Tracked<NodePermAndToken>) {
        let mut current_locked_node = self;
        loop {
            let tracked NodePermAndToken { node_perm, map_token };
            let mut current_node_view = current_locked_node.node_cell.borrow(
                Tracked(&mut node_perm),
            );
            println!("{}", current_node_view.elem);

            if (current_node_view.next.is_none()) {
                current_locked_node.release_lock(
                    Tracked(NodePermAndToken { node_perm, map_token }),
                );
                return;
            }
            let next_locked_node = current_node_view.next.as_ref().unwrap().clone();
            let mut next_npat = next_locked_node.acquire_lock();

            current_locked_node.release_lock(Tracked(NodePermAndToken { node_perm, map_token }));
            current_locked_node = next_locked_node;
            npat = next_npat;
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
