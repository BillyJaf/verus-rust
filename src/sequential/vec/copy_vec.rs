use vstd::prelude::*;

verus!{
    pub fn copy_vec(vec1: &Vec<i32>, vec2: &mut Vec<i32>)
        requires
            vec1.len() == old(vec2).len()
        ensures
            vec2.len() == old(vec2).len(),
            forall |i: int| 0 <= i < vec1.len() ==> vec1[i] == vec2[i],
            vec1@ == vec2@
    {       
        let mut i = 0;
        while i < vec1.len() 
            invariant
                vec1.len() == vec2.len(),
                0 <= i <= vec1.len(),
                forall |j: int| 0 <= j < i ==> vec1[j] == vec2[j],
            decreases
                vec1.len() - i
        {
            vec2[i] = vec1[i];
            i += 1;
        }
    }
}