use vstd::prelude::*;

use crate::permutation::permutation::is_permutation;
use crate::sorted::sorted::{is_sorted, is_sorted_range};
use crate::swap_elements::swap_elements_once::swap_two_elements;

verus!{
    pub fn insertion_sort(arr: &mut [i32])
        ensures
            is_sorted(arr@),
            is_permutation(arr@, old(arr)@),
            arr.len() == old(arr).len()
    {
        if arr.len() <= 1 {
            return
        }

        let mut i = 1;
        while i < arr.len() 
            invariant
                1 <= i <= arr.len(),
                is_sorted_range(arr@, 0, i as int),
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
                    is_sorted_range(arr@, 0, j as int),
                    is_sorted_range(arr@, j as int, i as int + 1),
                    forall |x: int, y: int|
                        0 <= x < j && j < y <= i ==> arr@[x] <= arr@[y],
                    arr.len() == old(arr).len(),
                decreases
                    j
            {   
                swap_two_elements(arr, j, j-1);
                j -= 1;
            }
            i += 1;
        }
    }
}