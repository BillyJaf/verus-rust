#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use std::sync::Arc;
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{atomic_ghost::*, pervasive::*, prelude::*, simple_pptr::*};

mod linked_list_no_tsm;
use linked_list_no_tsm::{LinkedList};

verus! {

// #[verifier::external_body]
// fn print_header(header: &str) {
//     println!("\n======= {} =======\n", header);
// }

// #[verifier::external_body]
// fn print_description(description: &str) {
//     println!("{}\n", description);
// }

fn simple_insert_test(linked_list: Arc<LinkedList>)
    requires
        linked_list.wf(),
    ensures
        linked_list.wf(),
{
    linked_list.insert(1);
    linked_list.insert(2);
    linked_list.insert(3);
    linked_list.insert(4);
    linked_list.insert(5);
    linked_list.print_list()
}

fn simple_insert_test_duplicate_inserts(linked_list: Arc<LinkedList>)
    requires
        linked_list.wf(),
    ensures
        linked_list.wf(),
{
    linked_list.insert(1);
    linked_list.insert(2);
    linked_list.insert(3);
    linked_list.insert(4);
    linked_list.insert(5);
    linked_list.insert(1);
    linked_list.insert(2);
    linked_list.insert(3);
    linked_list.insert(4);
    linked_list.insert(5);
    linked_list.print_list()
}

fn simple_delete_test(linked_list: Arc<LinkedList>)
    requires
        linked_list.wf(),
    ensures
        linked_list.wf(),
{
    linked_list.insert(1);
    linked_list.insert(2);
    linked_list.insert(3);
    linked_list.insert(4);
    linked_list.insert(5);
    linked_list.delete(2);
    linked_list.delete(4);
    linked_list.print_list()
}

fn simple_delete_test_duplicate_deletes(linked_list: Arc<LinkedList>)
    requires
        linked_list.wf(),
    ensures
        linked_list.wf(),
{
    linked_list.insert(1);
    linked_list.insert(2);
    linked_list.insert(3);
    linked_list.insert(4);
    linked_list.insert(5);
    linked_list.delete(2);
    linked_list.delete(4);
    linked_list.delete(2);
    linked_list.delete(4);
    linked_list.print_list()
}

fn multithreaded_double_inserts(linked_list: Arc<LinkedList>)
    requires
        linked_list.wf(),
    ensures
        linked_list.wf(),
{
    let mut join_handles = Vec::new();
    let num_interations = 10;
    let mut i = 0;
    while i < num_interations
        invariant
            linked_list.wf(),
    {
        let thread_linked_list = linked_list.clone();
        join_handles.push(
            vstd::thread::spawn(
                move ||
                    {
                        thread_linked_list.insert(i);
                    },
            ),
        );
        i = i + 1;
    }

    for handle in join_handles.into_iter() {
        let _ = handle.join();
    }

    let mut join_handles = Vec::new();
    let mut i = 0;
    while i < num_interations
        invariant
            linked_list.wf(),
    {
        let thread_linked_list = linked_list.clone();
        join_handles.push(
            vstd::thread::spawn(
                move ||
                    {
                        thread_linked_list.insert(i);
                    },
            ),
        );
        i = i + 1;
    }

    for handle in join_handles.into_iter() {
        let _ = handle.join();
    }

    linked_list.print_list();
}

fn multithreaded_insert_delete(linked_list: Arc<LinkedList>)
    requires
        linked_list.wf(),
    ensures
        linked_list.wf(),
{
    let mut join_handles = Vec::new();
    let num_interations = 10;
    let mut i = 0;
    while i < num_interations
        invariant
            linked_list.wf(),
    {
        let thread_linked_list = linked_list.clone();
        join_handles.push(
            vstd::thread::spawn(
                move ||
                    {
                        thread_linked_list.insert(i);
                    },
            ),
        );
        i = i + 1;
    }

    for handle in join_handles.into_iter() {
        let _ = handle.join();
    }

    let mut join_handles = Vec::new();
    let mut i = 0;
    while i < num_interations
        invariant
            linked_list.wf(),
            i <= num_interations <= u32::MAX - 100
    {
        let thread_linked_list = linked_list.clone();
        join_handles.push(
            vstd::thread::spawn(
                move ||
                    {
                        thread_linked_list.delete(i);
                        thread_linked_list.insert(i + 100);
                    },
            ),
        );
        i = i + 1;
    }

    for handle in join_handles.into_iter() {
        let _ = handle.join();
    }

    linked_list.print_list();
}

pub fn main() {
    let linked_list = LinkedList::new();
    multithreaded_insert_delete(linked_list.clone());

    // simple_test(treiber_stack.clone());
    // multithreaded_no_empty_stack_test(treiber_stack.clone());
    // multithreaded_with_possible_empty_stack_test(treiber_stack.clone());
}

} // verus!
