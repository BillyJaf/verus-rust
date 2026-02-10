use vstd::prelude::*;

verus!{
    // pub open spec fn is_sorted(array: Seq<int>) -> bool
    // {   
    //     forall |i: int| 0 <= i <= (array.len() - 1) ==> #[trigger] array.index(i) <= array.index(i + 1)
    // }

    // pub open spec fn has_same_elements(array1: Seq<int>, array2: Seq<int>) -> bool
    // {
    //     array1.len() == array2.len() && array1.to_multiset() =~= array2.to_multiset()
    // }

    // fn sort(mut input_array: Vec<i32>) -> (sorted_array: Vec<i32>)
    //     requires
    //         1 < input_array.len() <= (i32::MAX)
    //     ensures
    //         // is_sorted(sorted_array@.map_values(|elem| elem as int)), 
    //         has_same_elements(input_array@.map_values(|elem| elem as int), sorted_array@.map_values(|elem| elem as int)),
    // {
    //     let mut i = 1;
    //     let ghost original_seq = input_array@.map_values(|elem| elem as int);

    //     while i < input_array.len() 
    //         invariant
    //             1 <= i <= input_array.len(),
    //             input_array.len() <= (i32::MAX),
    //             has_same_elements(input_array@.map_values(|elem| elem as int), original_seq),
    //             // is_sorted(input_array@.subrange(0,i as int).map_values(|elem| elem as int)),
    //         decreases 
    //             input_array.len() - i
    //     {
    //         let mut j = i as i32 - 1;

    //         while 0 <= j && (j as usize + 1) < input_array.len() && input_array[j as usize] > input_array[j as usize + 1]
    //             invariant
    //                 -1 <= j,
    //                 j < i,
    //                 has_same_elements(input_array@.map_values(|elem| elem as int), original_seq),
    //             decreases 
    //                 j + 1
    //         {   
    //             let ghost before_swap = input_array@.map_values(|elem| elem as int);
    //             let current_element = input_array[j as usize + 1];
    //             input_array[j as usize + 1] = input_array[j as usize];
    //             input_array[j as usize] = current_element;

    //             j -= 1;
    //         }

    //         i += 1;
    //     }
    //     return input_array;
    // }   

    pub open spec fn is_sorted(array: Seq<i32>) -> bool
    {   
        forall |i: int| 0 <= i <= (array.len() - 1) ==> #[trigger] array.index(i) <= array.index(i + 1)
    }

    // pub 
}