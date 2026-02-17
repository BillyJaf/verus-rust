use vstd::prelude::*;

use super::clone_vec_range::clone_vec_range;

verus!{
    pub fn split_vec(vec: &Vec<i32>, midpoint: usize) -> (vecs: (Vec<i32>, Vec<i32>))
        requires
            0 <= midpoint < vec.len()
        ensures
            vecs.0.len() == midpoint,
            vecs.1.len() == vec.len() - midpoint,
            forall |i: int| 0 <= i < midpoint ==> #[trigger] vec[i] == vecs.0[i],
            forall |i: int| midpoint <= i < vec.len() ==> vec[i] == vecs.1[i - midpoint],
            vec@ == vecs.0@.add(vecs.1@)
    {   
        let mut left = clone_vec_range(vec, 0, midpoint);
        let mut right = clone_vec_range(vec, midpoint, vec.len());
        (left, right)
    }
}