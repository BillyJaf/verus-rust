use vstd::prelude::*;

include!("../swap_elements/swap_elements_once.rs");

verus!{
    pub fn insertion_sort(arr: &mut Vec<i32>)
        requires
            old(arr).len() <= i32::MAX,
        ensures
            is_sorted(arr@),
            is_permutation(arr@, old(arr)@),
            arr.len() == old(arr).len()
    {
        let mut i = 1;

        // Nothing to sort here
        if arr.len() <= 1 {
            return
        }

        while i < arr.len() 
            invariant
                1 <= i <= arr.len(),
                // is_sorted(arr@.subrange(0,i as int)),
                is_sorted_indexed(arr@, 0, i as int),
                is_permutation(arr@, old(arr)@),
                arr.len() == old(arr).len()
            decreases
                arr.len() - i
        {
            let mut j = i;
            while j > 0 && arr[j - 1] > arr[j]
                invariant
                    0 <= j <= i < arr.len(),
                    is_permutation(arr@, old(arr)@),
                    //is_sorted(arr@.subrange(0,j as int)),
                    // is_sorted(arr@.subrange(j as int, i as int + 1)),
                    is_sorted_indexed(arr@, 0, j as int),
                    is_sorted_indexed(arr@, j as int, i as int + 1),
                    forall |x: int, y: int|
                        0 <= x < j && j < y <= i ==> arr@[x] <= arr@[y],
                    arr.len() == old(arr).len(),
                decreases
                    j
            {   
                // let k = j - 1;
                // (*arr).swap(j, k);
                swap_two_elements_ref(arr, j, j-1);
                // let temp = arr[j];
                // arr[j] = arr[j - 1];
                // arr[j - 1] = temp;
                j -= 1;
            }
            i += 1;
        }
    }



    // fn inner_loop(mut input_array: Vec<i32>, starting_element_index: usize) -> (swapped_array: Vec<i32>)
    //     requires
    //         1 < input_array.len() <= (i32::MAX),
    //         0 <= starting_element_index < input_array.len(),
    //         is_sorted(input_array@.subrange(0,starting_element_index as int))
    //     ensures
    //         is_permutation(input_array@, swapped_array@),
    //         is_sorted(swapped_array@.subrange(0,starting_element_index as int + 1))
    // {
    //     if starting_element_index == 0 {
    //         return input_array;
    //     }

    //     let mut swapped_array = input_array.clone();

    //     assert(is_sorted(swapped_array@.subrange(0,starting_element_index as int)));
    //     assert(is_sorted(swapped_array@.subrange(starting_element_index as int,starting_element_index as int + 1)));

    //     // assert(is_sorted(swapped_array@.subrange(0,i as int))) by {
    //     //     is_sorted_recursive(swapped_array@, 0, current_element_index as int)
    //     // };

    //     let mut i = starting_element_index;

    //     while i > 0 && swapped_array[i as usize] < swapped_array[i as usize - 1] 
    //         invariant
    //             is_permutation(input_array@, swapped_array@),
    //             0 <= i <= starting_element_index < swapped_array.len(),
    //             swapped_array.len() == input_array.len(),
    //             is_sorted(swapped_array@.subrange(0,i as int)),
    //             is_sorted(swapped_array@.subrange(i as int, starting_element_index as int + 1))
    //         decreases
    //             i
    //     {
    //         let ghost before_swapping = swapped_array@;
    //         assert(is_sorted(swapped_array@.subrange(0,i as int)));
    //         assert(is_sorted(swapped_array@.subrange(i as int, starting_element_index as int + 1)));

    //         swapped_array = swap_two_consecutive_elements_sorted(swapped_array, i);

    //         assert(is_sorted(swapped_array@.subrange(0,i as int))) by {
    //             assert(is_sorted(swapped_array@.subrange(0,i as int - 1)));
    //             assert(swapped_array@.subrange(0,i as int - 1).len() == 0 || swapped_array@.subrange(0,i as int - 1).last() <= swapped_array@.index(i as usize - 1));
    //         };

            
    //         // assert(is_sorted(swapped_array@.subrange(i as int, starting_element_index as int + 1))) by {
    //         //     assert(forall |j: int| i < j < starting_element_index + 1 ==> #[trigger] before_swapping.index(j) == swapped_array@.index(j));
    //         //     assert(before_swapping.subrange(i as int + 1, starting_element_index as int + 1) == swapped_array@.subrange(i as int + 1, starting_element_index as int + 1));
    //         //     assert(is_sorted(before_swapping.subrange(i as int, starting_element_index as int + 1)));
    //         //     assert(swapped_array@.index((i as usize - 1) as int) < swapped_array@.index((i as usize) as int));
    //         // };

    //         assert(forall |j: int| i < j < starting_element_index + 1 ==> #[trigger] before_swapping.index(j) == swapped_array@.index(j));
    //         assert(before_swapping.subrange(i as int + 1, starting_element_index as int + 1) == swapped_array@.subrange(i as int + 1, starting_element_index as int + 1));

    //         proof {
    //             let ghost sub_array = before_swapping.subrange(i as int, starting_element_index as int + 1);
    //             assert(sub_array.subrange(1, sub_array.len() as int) == before_swapping.subrange(i as int + 1, starting_element_index as int + 1));
    //             assert(is_sorted(sub_array));
    //             is_sorted_subarray(sub_array, 1, sub_array.len() as int);
    //             assert(is_sorted(sub_array.subrange(1, sub_array.len() as int)));
    //             assert(is_sorted(before_swapping.subrange(i as int + 1, starting_element_index as int + 1)));
    //         }

    //         // assert(is_sorted(before_swapping.subrange(i as int, starting_element_index as int + 1)));
    //         // assert(is_sorted(before_swapping.subrange(i as int + 1, starting_element_index as int + 1)));

    //         assert(is_sorted(swapped_array@.subrange(i as int + 1, starting_element_index as int + 1)));
    //         assert(swapped_array@.index(i as int) <= swapped_array@.index(i as int + 1));

    //         // assert(is_sorted(before_swapping.subrange(i as int, starting_element_index as int + 1)));
    //         // assert(is_sorted(before_swapping.subrange(i as int + 1, starting_element_index as int + 1))) by {
    //         //     assert(is_sorted(before_swapping.subrange(i as int, starting_element_index as int + 1)));
    //         //     assert(forall |j: int| i <= j < starting_element_index as int ==> #[trigger] before_swapping.index(j) <= before_swapping.index(j + 1));
    //         // };

    //         // assert(forall |j: int| i <= j < starting_element_index as int ==> #[trigger] before_swapping.index(j) <= before_swapping.index(j + 1)) by {
    //         //     assert(is_sorted(before_swapping.subrange(i as int, starting_element_index as int + 1)));
    //         // };

    //         assert(swapped_array@.index((i as usize - 1) as int) < swapped_array@.index((i as usize) as int));

    //         i -= 1;
    //     }

    //     // if i == 0 && swapped_array[i as usize] > current_element {
    //     //     swapped_array = swap_two_elements(swapped_array, 0, 1);
    //     //     assume(is_sorted(swapped_array@.subrange(0 as int,current_element_index as int + 1)));
    //     // }

    //     assert(is_sorted(swapped_array@.subrange(0,starting_element_index as int + 1)));

    //     swapped_array

    // }   
}