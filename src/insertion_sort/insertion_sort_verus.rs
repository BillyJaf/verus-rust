use vstd::prelude::*;

verus!{
    pub open spec fn is_sorted(array: Seq<int>) -> bool
    {   
        forall |i: int| 0 <= i <= (array.len() - 1) ==> #[trigger] array.index(i) <= array.index(i + 1)
    }

    // proof fn test_is_sorted(array: Seq<int>)
    //     ensures
    //         is_sorted(array)
    // {}

    pub open spec fn count_instances_of_element(array: Seq<int>, element: int) -> nat
        decreases array.len()
    {
        if array.len() == 0 {
            0
        } else {
            (if array.index(array.len() - 1) == element { 1nat } else { 0nat }) + count_instances_of_element(array.subrange(0, array.len() - 1), element)
        }
    }

    pub open spec fn has_same_elements(array1: Seq<int>, array2: Seq<int>) -> bool
    {
        (array1.len() == array2.len()) && (forall |i: int| 0 <= i < array1.len() ==> count_instances_of_element(array1, array1.index(i)) == count_instances_of_element(array2, array1.index(i)))

    }

    // proof fn test_has_same_elements(array1: Seq<int>, array2: Seq<int>)
    //     ensures
    //         has_same_elements(array1, array2)
    // {}

    pub fn sort(mut input_array: Vec<i32>) -> (sorted_array: Vec<i32>)
        requires
            input_array.len() <= (u32::MAX >> 1) as usize
        ensures
            is_sorted(sorted_array@.map_values(|elem| elem as int)) && has_same_elements(input_array@.map_values(|elem| elem as int), sorted_array@.map_values(|elem| elem as int)),
    {
        let mut i = 0;
        let original_array = input_array.clone();

        while i < input_array.len() 
            invariant
                0 <= i,
                i <= input_array.len(),
                has_same_elements(input_array@.map_values(|elem| elem as int), original_array@.map_values(|elem| elem as int)),
            ensures
                is_sorted(input_array@.map_values(|elem| elem as int))
            decreases 
                input_array.len() - i
        {
            let current_element = input_array[i];
            let mut j = (i - 1) as i32;

            while j >= 0 
                invariant
                    -1 <= j,
                    j <= (i - 1) as i32
                ensures
                    is_sorted(input_array@.map_values(|elem| elem as int).subrange(0,j+1))
                decreases
                    j
            {
                if input_array[j as usize] >= current_element {
                    input_array[(j + 1) as usize] = input_array[j as usize];
                    j -= 1;
                } else {
                    break
                }
            }

            input_array[(j + 1) as usize] = current_element;
        }
        return input_array;
    }   
}