use vstd::prelude::*;

verus!{
    proof fn is_sorted_recursive(array: Seq<i32>, i: int, j: int) 
        requires
            0 <= i < j <= array.len()
        ensures
            is_sorted(array.subrange(i,j)) ==> is_sorted(array.subrange(i,j - 1))
        decreases
            j
    {
        if i + 1 == j {}
        else { is_sorted_recursive(array, i, j - 1) }
    }

    proof fn is_sorted_subarray(array: Seq<i32>, i: int, j: int)
        requires
            is_sorted(array),
            0 <= i <= j <= array.len(),
        ensures
            is_sorted(array.subrange(i,j))
    {}

    // Find out about why triggers get upset when I do this:
    // pub open spec fn is_sorted(array: Seq<i32>) -> bool
    // {   
    //     forall |i: int| 0 <= i < array.len() - 1 ==> array[i] <= array[i + 1]
    // }

    pub open spec fn is_sorted(array: Seq<i32>) -> bool
    {   
        forall |i: int, j: int| 0 <= i < j < array.len() ==> array[i] <= array[j]
    }

    pub open spec fn is_sorted_indexed(array: Seq<i32>, low: int, high: int) -> bool
    {   
        forall |i: int, j: int| 0 <= low <= i <= j < high <= array.len() ==> array[i] <= array[j]
    }
}