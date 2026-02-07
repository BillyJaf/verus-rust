use vstd::prelude::*;

include!("insertion_sort/insertion_sort_verus.rs");

verus!{
    fn main() {
        let array_to_sort = vec![5,4,3,2,1];
        let sorted_array = sort(array_to_sort);
        let correct_sorted_array = vec![1,2,3,4,5];
        assert(sorted_array == correct_sorted_array)
    }
}