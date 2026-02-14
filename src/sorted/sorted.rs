use vstd::prelude::*;

verus!{
    // Find out about why triggers get upset when I do this:
    // pub open spec fn is_sorted(array: Seq<i32>) -> bool
    // {   
    //     forall |i: int| 0 <= i < array.len() - 1 ==> array[i] <= array[i + 1]
    // }

    pub open spec fn is_sorted(array: Seq<i32>) -> bool
    {   
        forall |i: int, j: int| 0 <= i < j < array.len() ==> array[i] <= array[j]
    }

    pub open spec fn is_sorted_range(array: Seq<i32>, low: int, high: int) -> bool
    {   
        forall |i: int, j: int| 0 <= low <= i <= j < high <= array.len() ==> array[i] <= array[j]
    }
}