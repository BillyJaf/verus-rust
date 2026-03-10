use vstd::prelude::*;

verus!{
    pub fn clone_vec_range(vec: &Vec<i32>, start: usize, end: usize) -> (new_vec: Vec<i32>)
        requires
            0 <= start < vec.len(),
            0 <= end <= vec.len(),
            start <= end,
        ensures
            end - start == new_vec.len(),
            forall |i: int| 0 <= i < new_vec.len() ==> vec[i + start] == new_vec[i],
            new_vec@ == vec@.subrange(start as int, end as int)
    {   
        let mut new_vec = Vec::with_capacity(end - start);
        let mut i = start;

        while i < end 
            invariant
                0 <= start <= i <= end <= vec.len(),
                new_vec@ == vec@.subrange(start as int, i as int),
                new_vec.len() == i - start,
            decreases
                end - i
        {
            new_vec.push(vec[i]);
            i += 1;
        }
        new_vec
    }
}