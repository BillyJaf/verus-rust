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

    fn inner_loop(mut input_array: Vec<i32>, starting_element_index: usize) -> (swapped_array: Vec<i32>)
        requires
            1 < input_array.len() <= (i32::MAX),
            0 <= starting_element_index < input_array.len(),
            is_sorted(input_array@.subrange(0,starting_element_index as int))
        ensures
            is_permutation(input_array@, swapped_array@),
            is_sorted(swapped_array@.subrange(0,starting_element_index as int + 1))
    {
        if starting_element_index == 0 {
            return input_array;
        }

        let mut swapped_array = input_array.clone();

        assert(is_sorted(swapped_array@.subrange(0,starting_element_index as int)));
        assert(is_sorted(swapped_array@.subrange(starting_element_index as int,starting_element_index as int + 1)));

        // assert(is_sorted(swapped_array@.subrange(0,i as int))) by {
        //     is_sorted_recursive(swapped_array@, 0, current_element_index as int)
        // };

        let mut i = starting_element_index;

        while i > 0 && swapped_array[i as usize] < swapped_array[i as usize - 1] 
            invariant
                is_permutation(input_array@, swapped_array@),
                0 <= i <= starting_element_index < swapped_array.len(),
                swapped_array.len() == input_array.len(),
                is_sorted(swapped_array@.subrange(0,i as int)),
                is_sorted(swapped_array@.subrange(i as int, starting_element_index as int + 1))
            decreases
                i
        {
            let ghost before_swapping = swapped_array@;
            swapped_array = swap_two_consecutive_elements_sorted(swapped_array, i);
            assert(swapped_array[(i as usize) as int] > swapped_array[(i as usize - 1) as int]);
            
            // assert(is_sorted(swapped_array@.subrange(i as int, starting_element_index as int + 1))) by {
            //     assert(forall |j: int| i < j < starting_element_index + 1 ==> #[trigger] before_swapping.index(j) == swapped_array@.index(j));
            //     assert(before_swapping.subrange(i as int + 1, starting_element_index as int + 1) == swapped_array@.subrange(i as int + 1, starting_element_index as int + 1));
            //     assert(is_sorted(before_swapping.subrange(i as int, starting_element_index as int + 1)));
            //     assert(swapped_array@.index((i as usize - 1) as int) < swapped_array@.index((i as usize) as int));
            // };

            assert(forall |j: int| i < j < starting_element_index + 1 ==> #[trigger] before_swapping.index(j) == swapped_array@.index(j));
            assert(before_swapping.subrange(i as int + 1, starting_element_index as int + 1) == swapped_array@.subrange(i as int + 1, starting_element_index as int + 1));

            proof {
                let ghost sub_array = before_swapping.subrange(i as int, starting_element_index as int + 1);
                assert(sub_array.subrange(1, sub_array.len() as int) == before_swapping.subrange(i as int + 1, starting_element_index as int + 1));
                assert(is_sorted(sub_array));
                is_sorted_subarray(sub_array, 1, sub_array.len() as int);
                assert(is_sorted(sub_array.subrange(1, sub_array.len() as int)));
                assert(is_sorted(before_swapping.subrange(i as int + 1, starting_element_index as int + 1)));
            }

            // assert(is_sorted(before_swapping.subrange(i as int, starting_element_index as int + 1)));
            // assert(is_sorted(before_swapping.subrange(i as int + 1, starting_element_index as int + 1)));

            assert(is_sorted(swapped_array@.subrange(i as int + 1, starting_element_index as int + 1)));
            assert(swapped_array@.index(i as int) <= swapped_array@.index(i as int + 1));

            // assert(is_sorted(before_swapping.subrange(i as int, starting_element_index as int + 1)));
            // assert(is_sorted(before_swapping.subrange(i as int + 1, starting_element_index as int + 1))) by {
            //     assert(is_sorted(before_swapping.subrange(i as int, starting_element_index as int + 1)));
            //     assert(forall |j: int| i <= j < starting_element_index as int ==> #[trigger] before_swapping.index(j) <= before_swapping.index(j + 1));
            // };

            // assert(forall |j: int| i <= j < starting_element_index as int ==> #[trigger] before_swapping.index(j) <= before_swapping.index(j + 1)) by {
            //     assert(is_sorted(before_swapping.subrange(i as int, starting_element_index as int + 1)));
            // };

            assert(swapped_array@.index((i as usize - 1) as int) < swapped_array@.index((i as usize) as int));

            i -= 1;
        }

        // if i == 0 && swapped_array[i as usize] > current_element {
        //     swapped_array = swap_two_elements(swapped_array, 0, 1);
        //     assume(is_sorted(swapped_array@.subrange(0 as int,current_element_index as int + 1)));
        // }

        assert(is_sorted(swapped_array@.subrange(0,starting_element_index as int + 1)));

        swapped_array

    }   
}