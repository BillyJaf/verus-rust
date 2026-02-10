use vstd::prelude::*;

include!("../swap_elements/swap_elements_once.rs");

verus!{
    pub open spec fn is_sorted(array: Seq<i32>) -> bool
    {   
        forall |i: int| 0 <= i <= (array.len() - 1) ==> #[trigger] array.index(i) <= array.index(i + 1)
    }

    pub open spec fn is_permutation(array1: Seq<i32>, array2: Seq<i32>) -> bool
    {
        array1.to_multiset() == array2.to_multiset()
    }

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
        ensures
            is_permutation(input_array@, swapped_array@),
    {
        if current_element_index == 0 {
            return input_array;
        }

        let mut swapped_array = input_array.clone();

        let mut i = current_element_index - 1;

        while i > 0 && input_array[i as usize] > current_element 
            invariant
                is_permutation(input_array@, swapped_array@),
                0 <= i < current_element_index < swapped_array.len(),
                swapped_array.len() == input_array.len(),
                is_permutation(input_array@, swapped_array@),
            decreases
                i + 1
        {
            swapped_array = swap_two_elements(swapped_array, i, i+1);
            i -= 1;
        }

        if i == 0 && swapped_array[i as usize] > current_element {
            swapped_array = swap_two_elements(swapped_array, 0, 1);
        }

        swapped_array

    }   
}