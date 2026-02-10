use vstd::prelude::*;

include!("../swap_elements/swap_elements_once.rs");

verus!{
    pub open spec fn is_sorted(array: Seq<i32>) -> bool
    {   
        forall |i: int| 0 <= i <= (array.len() - 1) ==> #[trigger] array.index(i) <= array.index(i + 1)
    }

    pub open spec fn has_same_elements(array1: Seq<i32>, array2: Seq<i32>) -> bool
    {
        array1.to_multiset() == array2.to_multiset()
    }

    fn sort(input_array: &mut Vec<i32>)
        requires
            1 < old(input_array).len() <= (i32::MAX)
        ensures
            has_same_elements(input_array@, old(input_array)@),
    {
        let mut i = 1;

        while i < input_array.len() 
        {
            let current_element = input_array[i];
            let mut j = i as i32 - 1;
            while j >= 0  && input_array[j as usize] > current_element {
                input_array[j as usize + 1] = input_array[j as usize];
                input_array[j as usize] = current_element;
                j -= 1;
            }
            i += 1;
        }
    }   
}