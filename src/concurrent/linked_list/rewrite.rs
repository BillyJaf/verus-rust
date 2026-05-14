#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use verus_state_machines_macros::tokenized_state_machine;
use verus_builtin::*;
use verus_builtin_macros::*;
use std::sync::Arc;
use std::cmp::Ordering;
use vstd::{
    atomic_ghost::*,
    modes::*,
    prelude::*,
    thread::*,
    pervasive::*, 
    prelude::*, 
    cell::pcell,
    set::*
};

verus! {

pub enum NodeData {
    Nil,
    Data(u32)
}

impl NodeData {
    pub fn clone(&self) -> (cloned: Self) 
        ensures
            *self == cloned
    {
        match self {
            NodeData::Nil => NodeData::Nil,
            NodeData::Data(i) => NodeData::Data(*i),
        }
    }

    pub fn get(&self) -> (value: u32) 
        requires
            *self != NodeData::Nil
        ensures
            *self == NodeData::Data(value)
    {
        match self {
            NodeData::Data(i) => *i,
            _ => 0
        }
    }

    pub open spec fn spec_lt(self, other: Self) -> bool {
        match (self, other) {
            (NodeData::Nil, NodeData::Nil) => false,
            (NodeData::Nil, _) => true,
            (_, NodeData::Nil) => false,
            (NodeData::Data(a), NodeData::Data(b)) => a < b,
        }
    }
}

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(map)]
            pub nodes: Map<NodeData, Option<NodeData>>,
            
            #[sharding(variable)]
            pub initialized: bool,
        }

        #[invariant]
        pub fn sorted_inv(&self) -> bool {
            (
                // If the map is initialised with real data
                (self.initialized && self.nodes[NodeData::Nil] != None::<NodeData>) ==> 
                    (
                        // The nil node points to the smallest element in the list:
                        (
                            forall |i: u32| #![auto] 
                                self.nodes[NodeData::Nil] == Some(NodeData::Data(i)) ==>
                                forall |j: u32| #![auto] j < i ==> !self.nodes.dom().contains(NodeData::Data(j))
                        
                        ) &&

                        // The tail node points to the largest element in the list:
                        (
                            forall |i: u32| #![auto]
                                (
                                    self.nodes.dom().contains(NodeData::Data(i)) && 
                                    self.nodes[NodeData::Data(i)] == None::<NodeData>
                                ) ==>
                                (
                                    (forall |j: u32| #![auto] i < j ==> !self.nodes.dom().contains(NodeData::Data(j)))
                                )
                        ) &&

                        // Everything in the list is sorted (smallest to largest).
                        // Nodes either point to something strictly larger, or to None
                        (
                            forall |i: u32| #![auto] 
                                (
                                    self.nodes.dom().contains(NodeData::Data(i)) && 
                                    self.nodes[NodeData::Data(i)] != None::<NodeData>
                                ) ==> (
                                    (exists |j: u32| #![auto] self.nodes[NodeData::Data(i)] == Some(NodeData::Data(j)) && i < j)
                                )
                        ) &&

                        // No two nodes point to the same data:
                        (
                            forall |i: u32, j: u32| #![auto] 
                                (
                                    self.nodes.dom().contains(NodeData::Data(i)) &&
                                    self.nodes.dom().contains(NodeData::Data(j)) &&
                                    self.nodes[NodeData::Data(i)] == self.nodes[NodeData::Data(j)]
                                ) ==>
                                (
                                    i == j
                                )
                        ) &&

                        // // We must assert that for any mapping [a => c], there are no entries in the map
                        // // with key b such that a < b < c. 
                        (
                            forall |i: u32| #![auto] 
                                (
                                    self.nodes.dom().contains(NodeData::Data(i)) && 
                                    self.nodes[NodeData::Data(i)] != None::<NodeData>
                                ) ==> (
                                    exists |j: u32| #![auto] self.nodes[NodeData::Data(i)] == Some(NodeData::Data(j)) && 
                                    forall |k: u32| #![auto] i < k < j ==> !self.nodes.dom().contains(NodeData::Data(k))
                                )
                        )
                    )
            )
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            // If the map is uninitialised, then it doesn't contain anything, not even the nil node (and vice versa)
            (!self.initialized <==> self.nodes.is_empty()) &&

            // If the map is initialised, then it must at least have the nil node:
            // This case looks redundant, but I believe it will help the SMT solver.
            (self.initialized <==> self.nodes.dom().contains(NodeData::Nil)) &&

            // If the map contains [NodeData::Nil => None], then it can't contain anything else
            (
                (self.initialized && self.nodes[NodeData::Nil] == None::<NodeData>) <==> 
                (self.nodes =~= Map::empty().insert(NodeData::Nil, None::<NodeData>))
            )
        }

        init!{
            initialize()
            {
                init nodes = Map::empty();
                init initialized = false;
            }
        }

        transition!{
            add_nil_node()
            {   
                require(!pre.initialized);
                update initialized = true;
                add nodes += [NodeData::Nil => None];
            }
        }

        transition!{
            add_to_nil_tail(new_tail: u32)
            {   
                remove nodes -= [NodeData::Nil => None];
                add nodes += [NodeData::Nil => Some(NodeData::Data(new_tail))];
                add nodes += [NodeData::Data(new_tail) => None];
            }
        }

        transition!{
            add_to_node_tail(current_tail: u32, new_tail: u32)
            {   
                require(new_tail > current_tail);
                remove nodes -= [NodeData::Data(current_tail) => None];
                add nodes += [NodeData::Data(current_tail) => Some(NodeData::Data(new_tail))];
                add nodes += [NodeData::Data(new_tail) => None];
            }
        }

        transition!{
            insert_node_inbetween_normal_and_normal(lower_node: u32, upper_node: u32, new_node: u32)
            {   
                require(lower_node < new_node);
                require(new_node < upper_node);
                remove nodes -= [NodeData::Data(lower_node) => Some(NodeData::Data(upper_node))];
                add nodes += [NodeData::Data(lower_node) => Some(NodeData::Data(new_node))];
                add nodes += [NodeData::Data(new_node) => Some(NodeData::Data(upper_node))];
            }
        }

        transition!{
            insert_node_inbetween_nil_and_normal(upper_node: u32, new_node: u32)
            {   
                require(new_node < upper_node);
                remove nodes -= [NodeData::Nil => Some(NodeData::Data(upper_node))];
                add nodes += [NodeData::Nil => Some(NodeData::Data(new_node))];
                add nodes += [NodeData::Data(new_node) => Some(NodeData::Data(upper_node))];
            }
        }

        transition!{
            delete_tail_after_nil_node(delete_node: u32)
            {   
                remove nodes -= [NodeData::Nil => Some(NodeData::Data(delete_node))];
                remove nodes -= [NodeData::Data(delete_node) => None];
                add nodes += [NodeData::Nil => None];
            }
        }

        transition!{
            delete_tail_node_after_normal_node(delete_node: u32, lower_node: u32)
            {   
                remove nodes -= [NodeData::Data(lower_node) => Some(NodeData::Data(delete_node))];
                remove nodes -= [NodeData::Data(delete_node) => None];
                add nodes += [NodeData::Data(lower_node) => None];
            }
        }

        transition!{
            delete_inbetween_nil_and_normal(delete_node: u32, upper_node: u32)
            {   
                remove nodes -= [NodeData::Nil => Some(NodeData::Data(delete_node))];
                remove nodes -= [NodeData::Data(delete_node) => Some(NodeData::Data(upper_node))];
                add nodes += [NodeData::Nil => Some(NodeData::Data(upper_node))];
            }
        }

        transition!{
            delete_inbetween_normal_and_normal(delete_node: u32, lower_node: u32, upper_node: u32)
            {   
                remove nodes -= [NodeData::Data(lower_node) => Some(NodeData::Data(delete_node))];
                remove nodes -= [NodeData::Data(delete_node) => Some(NodeData::Data(upper_node))];
                add nodes += [NodeData::Data(lower_node) => Some(NodeData::Data(upper_node))];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { 
        }

        #[inductive(add_nil_node)]
        fn add_nil_node_inductive(pre: Self, post: Self) { 
        }

        #[inductive(add_to_nil_tail)]
        fn add_to_nil_tail_inductive(pre: Self, post: Self, new_tail: u32) { 
        }

        #[inductive(add_to_node_tail)]
        fn add_to_node_tail_inductive(pre: Self, post: Self, current_tail: u32, new_tail: u32) { 
        }

        #[inductive(insert_node_inbetween_normal_and_normal)]
        fn insert_node_inbetween_normal_and_normal_inductive(pre: Self, post: Self, lower_node: u32, upper_node: u32, new_node: u32) { 
        }

        #[inductive(insert_node_inbetween_nil_and_normal)]
        fn insert_node_inbetween_nil_and_normal_inductive(pre: Self, post: Self, upper_node: u32, new_node: u32) { 
        }

        #[inductive(delete_tail_after_nil_node)]
        fn delete_tail_after_nil_node_inductive(pre: Self, post: Self, delete_node: u32) {                     
            assert(post.nodes =~= Map::empty().insert(NodeData::Nil, None::<NodeData>)) by {
                
                assert(forall |i: u32| #![auto] 
                    !post.nodes.dom().contains(NodeData::Data(i)));

                assert forall |node_data: NodeData| post.nodes.dom().contains(node_data) 
                    implies node_data == NodeData::Nil by {
                        match node_data {
                            NodeData::Nil => {}
                            NodeData::Data(i) => {
                                assert(!post.nodes.dom().contains(NodeData::Data(i)))
                            }
                        }
                    }
            
                assert(post.nodes[NodeData::Nil] == None::<NodeData>);
            };
        }

        #[inductive(delete_tail_node_after_normal_node)]
        fn delete_tail_node_after_normal_node_inductive(pre: Self, post: Self, delete_node: u32, lower_node: u32) { 
        }

        #[inductive(delete_inbetween_nil_and_normal)]
        fn delete_inbetween_nil_and_normal_inductive(pre: Self, post: Self, delete_node: u32, upper_node: u32) {
            assert(post.initialized <==> post.nodes.dom().contains(NodeData::Nil));
        }

        #[inductive(delete_inbetween_normal_and_normal)]
        fn delete_inbetween_normal_and_normal_inductive(pre: Self, post: Self, delete_node: u32, lower_node: u32, upper_node: u32) {
        }

        property!{
            no_smaller_token_exists(first_node_data: u32) {
                have nodes >= [NodeData::Nil => Some(NodeData::Data(first_node_data))];
                birds_eye let n = pre.nodes;

                assert(
                    forall |data: u32| #![auto]
                        data < first_node_data ==>
                            !n.dom().contains(NodeData::Data(data))
                );
            }
        }

        property!{
            no_larger_token_exists(last_node_data: u32) {
                have nodes >= [NodeData::Data(last_node_data) => None];
                birds_eye let n = pre.nodes;

                assert(
                    forall |data: u32| #![auto]
                        data > last_node_data ==>
                            !n.dom().contains(NodeData::Data(data))
                );
            }
        }

        property!{
            no_inbetween_token_exists(lower_node_data: u32, upper_node_data: u32) {
                have nodes >= [NodeData::Data(lower_node_data) => Some(NodeData::Data(upper_node_data))];
                birds_eye let n = pre.nodes;

                assert(
                    forall |data: u32| #![auto]
                        (lower_node_data < data && data < upper_node_data) ==>
                            !n.dom().contains(NodeData::Data(data))
                );
            }
        }
    }
}

pub struct Nil {
    pub cdr: Option<Arc<LockedCons>>,
    pub map_token: Tracked<machine::nodes>
}

struct_with_invariants!{
    pub struct LockedNil {
        atomic: AtomicBool<_, Option<pcell::PointsTo<Nil>>, _>,
        cell: pcell::PCell<Nil>,
        instance: Tracked<machine::Instance>,
    }

    spec fn wf(&self) -> bool 
    {
        invariant on atomic with (cell, instance) is (v: bool, g: Option<pcell::PointsTo<Nil>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    points_to.value().map_token@.instance_id() == instance@.id() && 
                    points_to.value().map_token@.key() == NodeData::Nil &&
                    (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()) && 
                    (points_to.value().map_token@.value().is_some() ==> 
                        (
                            points_to.value().cdr.unwrap().wf() &&
                            points_to.value().cdr.unwrap().view_instance() == instance &&
                            points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
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
            locked_nil.wf()
    {
        let tracked (
            Tracked(instance),
            Tracked(nodes),
            Tracked(initialized),
        ) = machine::Instance::initialize();

        let tracked map_token;
        proof {
            map_token = instance.add_nil_node(&mut initialized)
        };

        let node = Nil { cdr: None::<Arc<LockedCons>>, map_token: Tracked(map_token) };
        let (cell, Tracked(perm)) = pcell::PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, Tracked(instance))), false, Tracked(Some(perm)));

        Self { 
            atomic, 
            cell, 
            instance: Tracked(instance)
        }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<pcell::PointsTo<Nil>>)
        requires 
            self.wf(),
        ensures 
            points_to.id() == self.cell.id(),
            points_to.value().map_token@.instance_id() == self.instance@.id(), 
            points_to.value().map_token@.key() == NodeData::Nil,
            (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()), 
            (points_to.value().map_token@.value().is_some() ==> 
                (
                    points_to.value().cdr.unwrap().wf() &&
                    points_to.value().cdr.unwrap().view_instance() == self.instance &&
                    points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
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

    fn release_lock(&self, points_to: Tracked<pcell::PointsTo<Nil>>)
        requires
            self.wf(),
            points_to.id() == self.cell.id(),
            points_to.value().map_token@.instance_id() == self.instance@.id(), 
            points_to.value().map_token@.key() == NodeData::Nil,
            (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()), 
            (points_to.value().map_token@.value().is_some() ==> 
                (
                    points_to.value().cdr.unwrap().wf() &&
                    points_to.value().cdr.unwrap().view_instance() == self.instance &&
                    points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
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
}

pub struct Cons {
    pub car: u32,
    pub cdr: Option<Arc<LockedCons>>,
    pub map_token: Tracked<machine::nodes>
}

struct_with_invariants!{
    pub struct LockedCons {
        atomic: AtomicBool<_, Option<pcell::PointsTo<Cons>>, _>,
        cell: pcell::PCell<Cons>,
        instance: Tracked<machine::Instance>,
        view_car: NodeData,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant on atomic with (cell, instance, view_car) is (v: bool, g: Option<pcell::PointsTo<Cons>>) {
            match g {
                None => v == true,
                Some(points_to) => {
                    v == false &&
                    points_to.id() == cell.id() &&
                    NodeData::Data(points_to.value().car) == view_car &&
                    points_to.value().map_token@.instance_id() == instance@.id() &&
                    points_to.value().map_token@.key() == NodeData::Data(points_to.value().car) &&
                    (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()) && 
                    (points_to.value().map_token@.value().is_some() ==> 
                        (
                            points_to.value().cdr.unwrap().wf() &&
                            points_to.value().cdr.unwrap().view_instance() == instance &&
                            NodeData::Data(points_to.value().car) < points_to.value().cdr.unwrap().view_car() &&
                            points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
                        )
                    )
                }
            }
        }
    }
}

impl LockedCons {
    fn new(car: u32, map_token: Tracked<machine::nodes>, cdr: Option<Arc<LockedCons>>, instance: Tracked<machine::Instance>) -> (new_node: Self)
        requires
            map_token@.instance_id() == instance@.id(),
            map_token@.key() == NodeData::Data(car),
            map_token@.value().is_none() <==> cdr.is_none(),
            map_token@.value().is_some() ==> (
                cdr.is_some() &&
                cdr.unwrap().wf() &&
                cdr.unwrap().view_instance() == instance &&
                NodeData::Data(car) < cdr.unwrap().view_car() &&
                cdr.unwrap().view_car() == map_token@.value().unwrap()
            ),
        ensures 
            new_node.wf(),
            new_node.instance == instance,
            new_node.view_car == NodeData::Data(car),
    {   
        let view_car = NodeData::Data(car);
        let node = Cons { car, cdr, map_token: map_token };
        let (cell, Tracked(perm)) = pcell::PCell::new(node);
        let atomic = AtomicBool::new(Ghost((cell, instance, view_car)), false, Tracked(Some(perm)));
        Self { atomic, cell, instance, view_car }
    }

    fn acquire_lock(&self) -> (points_to: Tracked<pcell::PointsTo<Cons>>)
        requires 
            self.wf(),
        ensures 
            points_to.id() == self.cell.id(),
            NodeData::Data(points_to.value().car) == self.view_car,
            points_to.value().map_token@.instance_id() == self.instance@.id(),
            points_to.value().map_token@.key() == NodeData::Data(points_to.value().car),
            (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()), 
            (points_to.value().map_token@.value().is_some() ==> 
                (
                    points_to.value().cdr.unwrap().wf() &&
                    points_to.value().cdr.unwrap().view_instance() == self.instance &&
                    NodeData::Data(points_to.value().car) < points_to.value().cdr.unwrap().view_car() &&
                    points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
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

    fn release_lock(&self, points_to: Tracked<pcell::PointsTo<Cons>>)
        requires
            self.wf(),
            points_to.id() == self.cell.id(),
            NodeData::Data(points_to.value().car) == self.view_car,
            points_to.value().map_token@.instance_id() == self.instance@.id(),
            points_to.value().map_token@.key() == NodeData::Data(points_to.value().car),
            (points_to.value().map_token@.value().is_none() <==> points_to.value().cdr.is_none()), 
            (points_to.value().map_token@.value().is_some() ==> 
                (
                    points_to.value().cdr.unwrap().wf() &&
                    points_to.value().cdr.unwrap().view_instance() == self.instance &&
                    NodeData::Data(points_to.value().car) < points_to.value().cdr.unwrap().view_car() &&
                    points_to.value().cdr.unwrap().view_car() == points_to.value().map_token@.value().unwrap()
                )
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

    pub closed spec fn view_car(&self) -> (view_car: NodeData)
    {
        self.view_car
    }

    pub closed spec fn view_instance(&self) -> (instance: machine::Instance)
    {
        self.instance@
    }
}

pub struct LinkedList {
    pub locked_nil: LockedNil,
}

impl LinkedList {
    pub fn new() -> Self {
        Self { locked_nil: LockedNil::new() }
    }
}

fn main() {
    let linked_list = Arc::new(LinkedList::new());
}
}