#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use std::sync::Arc;
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{
    atomic_ghost::*, 
    prelude::*, 
    pervasive::*,
    simple_pptr::*,
};

mod stack;
use stack::{PoppedElemAndWitness, TreiberStack};


verus!{

#[verifier::external_body]
fn print_pop(peaw: PoppedElemAndWitness) {
    match peaw.elem {
        Some(elem) => println!("{}", elem),
        None => println!("None"),

    }
}

#[verifier::external_body]
fn print_header(header: &str) {
    println!("\n======= {} =======\n", header);
}

#[verifier::external_body]
fn print_description(description: &str) {
    println!("{}\n", description);
}

fn simple_test(treiber_stack: Arc<TreiberStack>)
    requires
        treiber_stack.wf()
    ensures
        treiber_stack.wf()
{
    print_header("SINGLE THREADED TEST");
    print_description("Expect 1, 2, 3 - in that order.");
    treiber_stack.push(3);
    treiber_stack.push(2);
    treiber_stack.push(1);

    let x = treiber_stack.pop();
    print_pop(x);

    let x = treiber_stack.pop();
    print_pop(x);

    let x = treiber_stack.pop();
    print_pop(x);
}

fn multithreaded_no_empty_stack_test(treiber_stack: Arc<TreiberStack>)
    requires
        treiber_stack.wf()
    ensures
        treiber_stack.wf()
{
    print_header("MULTI THREADED TEST 1");
    print_description("Expect 0, 1, ..., 9 - in any order.");

    let mut join_handles = Vec::new();
    let num_interations = 10;
    let mut i = 0;
    while i < num_interations 
        invariant
            treiber_stack.wf()
    {
        let thread_treiber_stack = treiber_stack.clone();
        join_handles.push(
            vstd::thread::spawn(move || {
                thread_treiber_stack.push(i);
            })
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
            treiber_stack.wf()
    {
        let thread_treiber_stack = treiber_stack.clone();
        join_handles.push(
            vstd::thread::spawn(move || {
                let x = thread_treiber_stack.pop();
                print_pop(x);
            })
        );
        i = i + 1;
    }

    for handle in join_handles.into_iter() {
        let _ = handle.join();
    }
}

fn multithreaded_with_possible_empty_stack_test(treiber_stack: Arc<TreiberStack>)
    requires
        treiber_stack.wf()
    ensures
        treiber_stack.wf()
{
    print_header("MULTI THREADED TEST 2");
    print_description("Expect a subset of 0, 1, ..., 9 - in any order, some None.\nThen expect the rest of the elements that weren't printed already.");

    let mut join_handles = Vec::new();
    let num_interations = 10;
    let mut i = 0;
    while i < num_interations 
        invariant
            treiber_stack.wf()
    {
        let thread_treiber_stack = treiber_stack.clone();
        join_handles.push(
            vstd::thread::spawn(move || {
                thread_treiber_stack.push(i);
            })
        );

        let thread_treiber_stack = treiber_stack.clone();
        join_handles.push(
            vstd::thread::spawn(move || {
                let x = thread_treiber_stack.pop();
                print_pop(x);
            })
        );
        i = i + 1;
    }

    for handle in join_handles.into_iter() {
        let _ = handle.join();
    }

    print_description("\nThese are the elements left in the stack, they should not have already been printed:");

    loop 
        invariant
            treiber_stack.wf()
    {
        let x = treiber_stack.pop();
        match x.elem {
            None => break,
            Some(_) => print_pop(x)
        }
    }
}

pub fn main() {
    let treiber_stack = Arc::new(TreiberStack::new());

    simple_test(treiber_stack.clone());
    multithreaded_no_empty_stack_test(treiber_stack.clone());
    multithreaded_with_possible_empty_stack_test(treiber_stack.clone());
}
} // verus!
