use std::sync::Arc;
use verus_builtin::*;
use verus_builtin_macros::*;

mod linked_list;
use linked_list::{LinkedList};

verus! {

#[verifier::external_body]
fn print_header(header: &str) {
    println!("\n======= {} =======\n", header);
}

#[verifier::external_body]
fn print_description(description: &str) {
    println!("{}\n", description);
}

fn simple_insert_test(linked_list: Arc<LinkedList>)
    requires
        linked_list.wf(),
    ensures
        linked_list.wf(),
{
    print_header("SINGLE THREADED INSERT TEST");
    print_description("Expect 1, 2, 3, 4, 5 - in that order.");
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
    print_header("SINGLE THREADED DUPLICATE-INSERT TEST");
    print_description("Expect 1, 2, 3, 4, 5 - in that order.");
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
    print_header("SINGLE THREADED DELETE TEST");
    print_description("Expect 1, 3, 5 - in that order.");
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
    print_header("SINGLE THREADED DUPLICATE-DELETE TEST");
    print_description("Expect 1, 3, 5 - in that order.");
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
    print_header("MULTI THREADED DUPLICATE-INSERT TEST");
    print_description("Expect 0, 1, ..., 9 - in that order.");

    let mut join_handles = Vec::new();
    let num_interations = 10;
    let mut i = 0;
    while i < num_interations
        invariant
            linked_list.wf()
        decreases
            num_interations - i
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
            linked_list.wf()
        decreases
            num_interations - i
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
        linked_list.wf()
    ensures
        linked_list.wf()
{
    print_header("MULTI THREADED INSERT-DELETE TEST");
    print_description("Expect 100, 101, ..., 109 - in that order.");
    let mut join_handles = Vec::new();
    let num_interations = 10;
    let mut i = 0;
    while i < num_interations
        invariant
            linked_list.wf()
        decreases
            num_interations - i
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
        decreases
            num_interations - i
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
    
    simple_insert_test(linked_list.clone());
    simple_insert_test_duplicate_inserts(linked_list.clone());
    simple_delete_test(linked_list.clone());
    simple_delete_test_duplicate_deletes(linked_list.clone());
    multithreaded_double_inserts(linked_list.clone());
    multithreaded_insert_delete(linked_list.clone());
}

} // verus!
