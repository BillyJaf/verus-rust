use vstd::prelude::*;

include!("../swap_elements/swap_elements_once.rs");

verus!{
    // fn sort(input_array: &mut Vec<i32>)
    //     requires
    //         1 < old(input_array).len() <= (i32::MAX)
    //     ensures
    //         is_permutation(input_array@, old(input_array)@),
    // {
    //     let mut i = 1;

    //     while i < input_array.len() 
    //     {
    //         let current_element = input_array[i];
    //         let mut j = i as i32 - 1;
    //         while j >= 0  && input_array[j as usize] > current_element {
    //             input_array[j as usize + 1] = input_array[j as usize];
    //             input_array[j as usize] = current_element;
    //             j -= 1;
    //         }
    //         i += 1;
    //     }
    // }   

    fn inner_loop(mut input_array: Vec<i32>, current_element: i32, current_element_index: usize) -> (swapped_array: Vec<i32>)
        requires
            1 < input_array.len() <= (i32::MAX),
            0 <= current_element_index < input_array.len(),
            input_array@.contains(current_element),
            is_sorted(input_array@.subrange(0,current_element_index as int))
        ensures
            is_permutation(input_array@, swapped_array@),
            is_sorted(swapped_array@.subrange(0,current_element_index as int + 1))
    {
        if current_element_index == 0 {
            return input_array;
        }

        let mut swapped_array = input_array.clone();

        let mut i = current_element_index - 1;

        assert(is_sorted(swapped_array@.subrange(0,current_element_index as int)));
        assert(is_sorted(swapped_array@.subrange(current_element_index as int,current_element_index as int + 1)));

        // assert(is_sorted(swapped_array@.subrange(0,i as int))) by {
        //     is_sorted_recursive(swapped_array@, 0, current_element_index as int)
        // };

        while i > 0 && input_array[i as usize] > current_element 
            invariant
                is_permutation(input_array@, swapped_array@),
                0 <= i < current_element_index < swapped_array.len(),
                swapped_array.len() == input_array.len(),
                is_sorted(swapped_array@.subrange(0,i as int + 1)),
                is_sorted(swapped_array@.subrange(i as int + 1, current_element_index as int + 1))
            decreases
                i
        {
            swapped_array = swap_two_elements(swapped_array, i, i+1);
            assert(forall |j: int| 0 <= j < i ==> swapped_array@.index(j) == input_array@.index(j));
            // assume(is_sorted(swapped_array@.subrange(0 as int,i as int)));
            // assume(is_sorted(swapped_array@.subrange(i as int,current_element_index as int + 1)));
            i -= 1;
        }

        if i == 0 && swapped_array[i as usize] > current_element {
            swapped_array = swap_two_elements(swapped_array, 0, 1);
            assume(is_sorted(swapped_array@.subrange(0 as int,current_element_index as int + 1)));
        }

        assert(is_sorted(swapped_array@.subrange(0,current_element_index as int + 1)));

        swapped_array

    }   
}