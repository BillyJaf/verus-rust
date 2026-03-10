use vstd::prelude::*;

verus!{
    pub open spec fn is_sorted(array: Seq<i32>) -> bool
    {   
        forall |i: int, j: int| 0 <= i < j < array.len() ==> array[i] <= array[j]
    }

    pub open spec fn is_sorted_range(array: Seq<i32>, low: int, high: int) -> bool
    {   
        forall |i: int, j: int| 0 <= low <= i <= j < high <= array.len() ==> array[i] <= array[j]
    }
}