use vstd::prelude::*;

use crate::permutation::permutation::is_permutation;
use crate::sorted::sorted::{is_sorted, is_sorted_range};
use crate::swap_elements::swap_elements_once::swap_two_elements;

verus!{
    pub fn merge_sort(arr: &mut [i32])
        // ensures
        //     is_sorted(arr@),
        //     is_permutation(arr@, old(arr)@),
        //     arr.len() == old(arr).len()
    {

    }

    fn merge(left: &[i32], right: &[i32]) -> (merged_array: Vec<i32>)
        requires
            left.len() + right.len() <= usize::MAX,
        ensures
            is_sorted(merged_array@),
            is_permutation(left@ + right@, merged_array@),
            left.len() + right.len() == merged_array.len()
    {   
        let mut merged_array = Vec::with_capacity(left.len() + right.len());

        let mut left_pointer = 0;
        let mut right_pointer = 0;

        while left_pointer < left.len() && right_pointer < right.len() 
            invariant
                0 <= left_pointer <= left.len(),
                0 <= right_pointer <= right.len(),
                is_sorted_range(merged_array@, 0, left_pointer + right_pointer)
            decreases
                right.len() - right_pointer + left.len() - left_pointer
        {   

            if left[left_pointer] <= right[right_pointer] {
                merged_array.push(left[left_pointer]);
                left_pointer += 1;
            } else {
                merged_array.push(right[right_pointer]);
                right_pointer += 1;
            }
        }

        while left_pointer < left.len() 
            ensures
                0 <= left_pointer <= left.len(),
                is_sorted(merged_array@)
            decreases
                left.len() - left_pointer
        {
            merged_array.push(left[left_pointer]);
            left_pointer += 1;
        }

        while right_pointer < right.len() 
            ensures
                0 <= right_pointer <= right.len(),
                is_sorted(merged_array@)
            decreases
                right.len() - right_pointer
        {
            merged_array.push(right[right_pointer]);
            right_pointer += 1;
        }

        merged_array
    }
}