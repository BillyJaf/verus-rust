use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::multiset::*;

verus!{
    pub open spec fn only_swapped_elements(old_array: Seq<i32>, new_array: Seq<i32>, index_1: int, index_2: int) -> bool
    {
        new_array.len() == old_array.len() && 
        new_array[index_1 as int] == old_array[index_2 as int] &&
        new_array[index_2 as int] == old_array[index_1 as int] &&
        (forall |k: int|
            0 <= k && k < new_array.len() && k != index_1 && k != index_2 ==> new_array[k] == old_array[k]) &&
        old_array.to_multiset() == new_array.to_multiset()
    }

    pub fn swap_two_elements(array: &mut Vec<i32>, index_1: usize, index_2: usize)
        requires
            index_1 < old(array).len(),
            index_2 < old(array).len(),
        ensures
            only_swapped_elements(old(array)@, array@, index_1 as int, index_2 as int)
    {   
        let temp_1 = array[index_1];
        let temp_2 = array[index_2];
        array[index_1] = temp_2;

        assert(array@ == old(array)@.update(index_1 as int, temp_2));
        assert(array@.to_multiset() == old(array)@.update(index_1 as int, temp_2).to_multiset());

        assert(old(array)@.to_multiset().insert(temp_2).remove(old(array)[index_1 as int]) == old(array)@.update(index_1 as int, temp_2).to_multiset()) by {
            to_multiset_update(old(array)@, index_1 as int, temp_2)
        };

        array[index_2] = temp_1;

        assert(array@ == old(array)@.update(index_1 as int, temp_2).update(index_2 as int, temp_1));

        assert(old(array)@.update(index_1 as int, temp_2).update(index_2 as int, temp_1).to_multiset() == old(array)@.to_multiset().insert(temp_2).remove(temp_1).insert(temp_1).remove(temp_2)) by { 
            to_multiset_update(old(array)@.update(index_1 as int, temp_2), index_2 as int, temp_1);
            to_multiset_update(old(array)@, index_1 as int, temp_2)
        };

        assert(old(array)@.to_multiset() == old(array)@.to_multiset().insert(temp_2).remove(temp_1).insert(temp_1).remove(temp_2)) by {
            old(array)@.to_multiset_ensures();
        };

        assert(old(array)@.to_multiset() == array@.to_multiset());
    }
}