use vstd::prelude::*;
use vstd::multiset::*;

use crate::permutation::permutation::is_permutation;
use crate::sorted::sorted::{is_sorted, is_sorted_range};
use crate::swap_elements::swap_elements_once::swap_two_elements;

verus!{
    pub fn merge_sort(arr: &mut Vec<i32>)
        requires
            old(arr).len() <= usize::MAX,
        ensures
            is_sorted(arr@),
            is_permutation(arr@, old(arr)@),
            arr.len() == old(arr).len()
        decreases
            old(arr).len()
    {
        let mid_point = arr.len() / 2;
        if mid_point == 0 {
            return;
        }

        let mut left = Vec::with_capacity(mid_point);
        let mut right = Vec::with_capacity(arr.len() - mid_point);

        let mut i = 0;
        while i < mid_point 
            invariant
                0 <= i <= mid_point <= arr.len(),
                left@ == arr@.subrange(0,i as int),
            decreases
                mid_point - i
        {
            left.push(arr[i]);
            i += 1;
        }

        while i < arr.len() 
            invariant
                mid_point <= i <= arr.len(),
                right@ == arr@.subrange(mid_point as int,i as int),
            decreases
                arr.len() - i
        {
            right.push(arr[i]);
            i += 1;
        }

        merge_sort(&mut left);
        merge_sort(&mut right);

        let sorted = merge(&left, &right);

        assert(sorted@.to_multiset() =~= left@.add(right@).to_multiset());
        assert(arr@.subrange(0,mid_point as int).to_multiset() =~= left@.to_multiset());
        assert(arr@.subrange(mid_point as int, arr.len() as int).to_multiset() =~= right@.to_multiset());
        assert(arr@.subrange(0,mid_point as int).to_multiset().add(arr@.subrange(mid_point as int, arr.len() as int).to_multiset()) =~= left@.to_multiset().add(right@.to_multiset()));
        assert(arr@.subrange(0,mid_point as int).add(arr@.subrange(mid_point as int, arr.len() as int)).to_multiset() =~= left@.add(right@).to_multiset()) by {
            concat_to_multiset(arr@.subrange(0,mid_point as int), arr@.subrange(mid_point as int, arr.len() as int));
            concat_to_multiset(left@, right@);
        };

        assert(arr@ =~= arr@.subrange(0,mid_point as int).add(arr@.subrange(mid_point as int, arr.len() as int)));
        assert(arr@.to_multiset() =~= arr@.subrange(0,mid_point as int).add(arr@.subrange(mid_point as int, arr.len() as int)).to_multiset());
        assert(arr@.to_multiset() =~= left@.add(right@).to_multiset());

        
        let mut i = 0;
        while i < sorted.len() 
            invariant
                sorted.len() == arr.len(),
                0 <= i <= sorted.len(),
                forall |j: int| 0 <= j < i ==> sorted[j] == arr[j],
            decreases
                sorted.len() - i
        {
            arr[i] = sorted[i];
            i += 1;
        }

        assert(arr@ == sorted@);
        assert(arr@.to_multiset() == sorted@.to_multiset());
    }

    pub fn merge(left: &[i32], right: &[i32]) -> (merged_array: Vec<i32>) 
        requires
            left.len() + right.len() <= usize::MAX,
            is_sorted(left@),
            is_sorted(right@)
        ensures
            is_sorted(merged_array@),
            is_permutation(merged_array@, left@.add(right@)),
            left.len() + right.len() == merged_array.len()
    {
        let mut merged_array = Vec::with_capacity(left.len() + right.len());
        let mut left_pointer = 0;
        let mut right_pointer = 0;

        assert(merged_array@.to_multiset() =~= Multiset::<i32>::empty()) by {
            merged_array@.to_multiset_ensures();
        };

        assert(left@.subrange(0,left_pointer as int).to_multiset() =~= Multiset::<i32>::empty()) by {
            left@.subrange(0,left_pointer as int).to_multiset_ensures();
        };

        assert(right@.subrange(0,right_pointer as int).to_multiset() =~= Multiset::<i32>::empty()) by {
            right@.subrange(0,right_pointer as int).to_multiset_ensures();
        };

        while left_pointer < left.len() && right_pointer < right.len()
            invariant
                0 <= left_pointer <= left.len(),
                0 <= right_pointer <= right.len(),
                merged_array.len() == left_pointer + right_pointer,
                merged_array@.to_multiset() =~= left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)).to_multiset(),
                is_sorted(left@),
                is_sorted(right@),
                is_sorted(merged_array@),
                added_element_is_largest_seen_so_far(merged_array@, left@, left_pointer as int, right@, right_pointer as int),
            decreases
                left.len() - left_pointer + right.len() - right_pointer
        {   
            let ghost old_merged_array = merged_array@;

            if left[left_pointer] <= right[right_pointer] {
                merged_array.push(left[left_pointer]);
                left_pointer += 1;

                let ghost added_element = merged_array@.last();

                assert(merged_array@.drop_last() == old_merged_array);
                assert(merged_array@ == old_merged_array.push(added_element));
                assert(merged_array@.to_multiset() == old_merged_array.push(added_element).to_multiset());
                assert(old_merged_array.push(added_element).to_multiset() == old_merged_array.to_multiset().insert(added_element)) by {
                    old_merged_array.to_multiset_ensures()
                };
                assert(merged_array@.to_multiset() == old_merged_array.to_multiset().insert(added_element));

                assert(old_merged_array.to_multiset() =~= left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset());
                assert(merged_array@.to_multiset() == left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset().insert(added_element));

                assert(added_element == left[left_pointer as int - 1]);
                assert(merged_array@.to_multiset() == left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset().insert(added_element));

                assert(left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset().insert(added_element) == left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).push(added_element).to_multiset()) by {
                    left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset_ensures();
                };

                assert(left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset().insert(added_element) =~= left@.subrange(0,left_pointer as int - 1).to_multiset().insert(added_element).add(right@.subrange(0,right_pointer as int).to_multiset())) by {
                    concat_to_multiset(left@.subrange(0,left_pointer as int - 1), right@.subrange(0,right_pointer as int));
                };

                assert(left@.subrange(0,left_pointer as int - 1).to_multiset().insert(added_element).add(right@.subrange(0,right_pointer as int).to_multiset()) =~= left@.subrange(0,left_pointer as int - 1).push(added_element).to_multiset().add(right@.subrange(0,right_pointer as int).to_multiset())) by {
                    left@.subrange(0,left_pointer as int - 1).to_multiset_ensures();
                };

                assert(left@.subrange(0,left_pointer as int) =~= left@.subrange(0,left_pointer as int - 1).push(added_element));
                assert(left@.subrange(0,left_pointer as int - 1).push(added_element).to_multiset().add(right@.subrange(0,right_pointer as int).to_multiset()) =~= left@.subrange(0,left_pointer as int).to_multiset().add(right@.subrange(0,right_pointer as int).to_multiset()));

                assert(left@.subrange(0,left_pointer as int).to_multiset().add(right@.subrange(0,right_pointer as int).to_multiset()) =~= left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)).to_multiset()) by {
                    concat_to_multiset(left@.subrange(0,left_pointer as int), right@.subrange(0,right_pointer as int));
                };

            } else {
                merged_array.push(right[right_pointer]);
                right_pointer += 1;

                let ghost added_element = merged_array@.last();

                assert(merged_array@.drop_last() == old_merged_array);
                assert(merged_array@ == old_merged_array.push(added_element));
                assert(merged_array@.to_multiset() == old_merged_array.push(added_element).to_multiset());
                assert(old_merged_array.push(added_element).to_multiset() == old_merged_array.to_multiset().insert(added_element)) by {
                    old_merged_array.to_multiset_ensures()
                };
                assert(merged_array@.to_multiset() == old_merged_array.to_multiset().insert(added_element));

                assert(old_merged_array.to_multiset() =~= left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).to_multiset());
                assert(merged_array@.to_multiset() == left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).to_multiset().insert(added_element));

                assert(added_element == right[right_pointer as int - 1]);
                assert(merged_array@.to_multiset() == left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).to_multiset().insert(added_element));

                assert(left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).to_multiset().insert(added_element) == left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).push(added_element).to_multiset()) by {
                    left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).to_multiset_ensures();
                };

                assert(left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).push(added_element) == left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)));
                assert(left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).push(added_element).to_multiset() == left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)).to_multiset());

                assert(merged_array@.to_multiset() =~= left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)).to_multiset());
            }
        }

        if right_pointer == right.len() {
            while left_pointer < left.len() 
                invariant
                    0 <= left_pointer <= left.len(),
                    0 <= right_pointer <= right.len(),
                    merged_array.len() == left_pointer + right_pointer,
                    merged_array@.to_multiset() =~= left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)).to_multiset(),
                    is_sorted(left@),
                    is_sorted(right@),
                    is_sorted(merged_array@),
                    added_element_is_largest_seen_so_far_left(merged_array@, left@, left_pointer as int),
                decreases
                    left.len() - left_pointer
            {
                let ghost old_merged_array = merged_array@;

                merged_array.push(left[left_pointer]);
                left_pointer += 1;

                let ghost added_element = merged_array@.last();

                assert(merged_array@.drop_last() == old_merged_array);
                assert(merged_array@ == old_merged_array.push(added_element));
                assert(merged_array@.to_multiset() == old_merged_array.push(added_element).to_multiset());
                assert(old_merged_array.push(added_element).to_multiset() == old_merged_array.to_multiset().insert(added_element)) by {
                    old_merged_array.to_multiset_ensures()
                };
                assert(merged_array@.to_multiset() == old_merged_array.to_multiset().insert(added_element));

                assert(old_merged_array.to_multiset() =~= left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset());
                assert(merged_array@.to_multiset() == left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset().insert(added_element));

                assert(added_element == left[left_pointer as int - 1]);
                assert(merged_array@.to_multiset() == left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset().insert(added_element));

                assert(left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset().insert(added_element) == left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).push(added_element).to_multiset()) by {
                    left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset_ensures();
                };

                assert(left@.subrange(0,left_pointer as int - 1).add(right@.subrange(0,right_pointer as int)).to_multiset().insert(added_element) =~= left@.subrange(0,left_pointer as int - 1).to_multiset().insert(added_element).add(right@.subrange(0,right_pointer as int).to_multiset())) by {
                    concat_to_multiset(left@.subrange(0,left_pointer as int - 1), right@.subrange(0,right_pointer as int));
                };

                assert(left@.subrange(0,left_pointer as int - 1).to_multiset().insert(added_element).add(right@.subrange(0,right_pointer as int).to_multiset()) =~= left@.subrange(0,left_pointer as int - 1).push(added_element).to_multiset().add(right@.subrange(0,right_pointer as int).to_multiset())) by {
                    left@.subrange(0,left_pointer as int - 1).to_multiset_ensures();
                };

                assert(left@.subrange(0,left_pointer as int) =~= left@.subrange(0,left_pointer as int - 1).push(added_element));
                assert(left@.subrange(0,left_pointer as int - 1).push(added_element).to_multiset().add(right@.subrange(0,right_pointer as int).to_multiset()) =~= left@.subrange(0,left_pointer as int).to_multiset().add(right@.subrange(0,right_pointer as int).to_multiset()));

                assert(left@.subrange(0,left_pointer as int).to_multiset().add(right@.subrange(0,right_pointer as int).to_multiset()) =~= left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)).to_multiset()) by {
                    concat_to_multiset(left@.subrange(0,left_pointer as int), right@.subrange(0,right_pointer as int));
                };
            }
        } else {

            while right_pointer < right.len() 
                invariant
                    0 <= left_pointer <= left.len(),
                    0 <= right_pointer <= right.len(),
                    merged_array.len() == left_pointer + right_pointer,
                    merged_array@.to_multiset() =~= left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)).to_multiset(),
                    is_sorted(left@),
                    is_sorted(right@),
                    is_sorted(merged_array@),
                    added_element_is_largest_seen_so_far_right(merged_array@, right@, right_pointer as int),
                decreases
                    right.len() - right_pointer
            {
                let ghost old_merged_array = merged_array@;

                merged_array.push(right[right_pointer]);
                right_pointer += 1;

                let ghost added_element = merged_array@.last();

                assert(merged_array@.drop_last() == old_merged_array);
                assert(merged_array@ == old_merged_array.push(added_element));
                assert(merged_array@.to_multiset() == old_merged_array.push(added_element).to_multiset());
                assert(old_merged_array.push(added_element).to_multiset() == old_merged_array.to_multiset().insert(added_element)) by {
                    old_merged_array.to_multiset_ensures()
                };
                assert(merged_array@.to_multiset() == old_merged_array.to_multiset().insert(added_element));

                assert(old_merged_array.to_multiset() =~= left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).to_multiset());
                assert(merged_array@.to_multiset() == left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).to_multiset().insert(added_element));

                assert(added_element == right[right_pointer as int - 1]);
                assert(merged_array@.to_multiset() == left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).to_multiset().insert(added_element));

                assert(left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).to_multiset().insert(added_element) == left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).push(added_element).to_multiset()) by {
                    left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).to_multiset_ensures();
                };

                assert(left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).push(added_element) == left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)));
                assert(left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int - 1)).push(added_element).to_multiset() == left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)).to_multiset());

                assert(merged_array@.to_multiset() =~= left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)).to_multiset());
            }
        }

        assert(merged_array@.to_multiset() =~= left@.subrange(0,left_pointer as int).add(right@.subrange(0,right_pointer as int)).to_multiset());
        assert(left@ =~= left@.subrange(0,left_pointer as int));
        assert(right@ =~= right@.subrange(0,right_pointer as int));
        assert(merged_array@.to_multiset() =~= left@.add(right@).to_multiset());

        merged_array
    }


    proof fn concat_to_multiset(seq1: Seq<i32>, seq2: Seq<i32>)
        ensures
            seq1.add(seq2).to_multiset() =~= seq1.to_multiset().add(seq2.to_multiset())
    {
        assert forall |x: i32| #[trigger] seq1.add(seq2).to_multiset().count(x) =~= seq1.to_multiset().add(seq2.to_multiset()).count(x) by {

            assert(seq1.add(seq2).to_multiset().count(x) == seq1.to_multiset().count(x) + seq2.to_multiset().count(x)) by {
                add_multisets_count(seq1, seq2, x);
            };

            assert(seq1.to_multiset().add(seq2.to_multiset()).count(x) == seq1.to_multiset().count(x) + seq2.to_multiset().count(x));
        };
    }

    proof fn add_multisets_count(seq1: Seq<i32>, seq2: Seq<i32>, element: i32)
        ensures
            seq1.add(seq2).to_multiset().count(element) == seq1.to_multiset().count(element) + seq2.to_multiset().count(element)
        decreases
            seq2.len()
    {
        if seq2.len() == 0 {
            assert(seq2.to_multiset() =~= Multiset::<i32>::empty()) by {
                seq2.to_multiset_ensures();
            };
        } else {
            let prefix = seq2.drop_last();
            let last = seq2.last();

            add_multisets_count(seq1, prefix, element);

            assert(seq2 == prefix.push(last));
            assert(seq1.add(seq2) == seq1.add(prefix).push(last));

            assert(seq1.add(prefix).push(last).to_multiset() == seq1.add(prefix).to_multiset().insert(last)) by {
                seq1.add(prefix).to_multiset_ensures();
            };

            assert(seq2.to_multiset() == prefix.to_multiset().insert(last)) by {
                prefix.to_multiset_ensures();
            };
        }
    }

    pub open spec fn added_element_is_largest_seen_so_far(merged_array: Seq<i32>, left: Seq<i32>, left_pointer: int, right: Seq<i32>, right_pointer: int) -> bool
    {
        merged_array.len() > 0 ==> ((left_pointer < left.len() ==> merged_array.last() <= left[left_pointer]) && (right_pointer < right.len() ==> merged_array.last() <= right[right_pointer]))
    }

    pub open spec fn added_element_is_largest_seen_so_far_left(merged_array: Seq<i32>, left: Seq<i32>, left_pointer: int) -> bool
    {
        merged_array.len() > 0 ==> (left_pointer < left.len() ==> merged_array.last() <= left[left_pointer])
    }

    pub open spec fn added_element_is_largest_seen_so_far_right(merged_array: Seq<i32>, right: Seq<i32>, right_pointer: int) -> bool
    {
        merged_array.len() > 0 ==> (right_pointer < right.len() ==> merged_array.last() <= right[right_pointer])
    }

}