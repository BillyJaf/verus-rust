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

    pub open spec fn is_sorted(array: Seq<i32>) -> bool
    {   
        if array.len() <= 1 {
            true
        } else {
            forall |i: int| 0 <= i < array.len() - 1 ==> #[trigger] array.index(i) <= array.index(i + 1)
        }
    }
}