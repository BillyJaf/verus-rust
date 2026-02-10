use vstd::prelude::*;

verus!{
    pub open spec fn is_permutation(array1: Seq<i32>, array2: Seq<i32>) -> bool
    {
        array1.to_multiset() == array2.to_multiset()
    }
}