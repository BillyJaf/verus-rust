use vstd::prelude::*;
use vstd::multiset::*;
use vstd::seq_lib::*;
use crate::sequential::utils::sorted::sorted::{is_sorted, is_sorted_range};

verus! {

    pub struct SortedList {
        list: Vec<i32>
    }

    impl SortedList {
        pub closed spec fn view(&self) -> Seq<i32> {
            self.list@
        }

        pub fn new() -> (sorted_list: Self) 
            ensures
                sorted_list.view().len() == 0
        {
            SortedList { list: Vec::new() }
        }

        pub fn insert(&mut self, elem: i32) 
            requires
                old(self).view().len() <= usize::MAX / 2,
                is_sorted(old(self).view())
            ensures
                is_sorted(self.view()),
                old(self).view().to_multiset().insert(elem) =~= self.view().to_multiset()
        {   
            broadcast use group_seq_properties;

            let mut lp = 0;
            let mut rp = self.list.len();

            while lp < rp 
                invariant
                    0 <= lp <= rp <= self.view().len() <= usize::MAX / 2,
                    is_sorted(self.view()),
                    forall |i: int| 0 <= i < lp ==> elem >= self.view()[i],
                    forall |i: int| rp <= i < self.view().len() ==> elem <= self.view()[i]
                ensures
                    lp == rp,
                    is_sorted(self.view()),
                    forall |i: int| 0 <= i < lp ==> elem >= self.view()[i],
                    forall |i: int| rp <= i < self.view().len() ==> elem <= self.view()[i]
                decreases
                    rp - lp
            {
                let mid = (lp + rp) / 2;
                if elem > self.list[mid] {
                    lp = mid + 1;
                } else if elem < self.list[mid] {
                    rp = mid;
                } else {
                    lp = mid;
                    rp = mid;
                    break;
                }
            }
            self.list.insert(lp, elem);
        }

        pub fn index_of(&self, elem: i32) -> (elem_index: Option<usize>) 
            requires
                self.view().len() <= usize::MAX / 2,
                is_sorted(self.view())
            ensures
                elem_index.is_none() <==> !self.view().contains(elem),
                elem_index.is_some() ==> (
                    0 <= elem_index.unwrap() < self.view().len() &&
                    self.view()[elem_index.unwrap() as int] == elem
                ),
                is_sorted(self.view())
        {
            let mut lp = 0;
            let mut rp = self.list.len();

            while lp < rp 
                invariant
                    0 <= lp <= rp <= self.view().len() <= usize::MAX / 2,
                    is_sorted(self.view()),
                    forall |i: int| 0 <= i < lp ==> elem > self.view()[i],
                    forall |i: int| rp <= i < self.view().len() ==> elem < self.view()[i]
                decreases
                    rp - lp
            {
                let mid = (lp + rp) / 2;
                if elem > self.list[mid] {
                    lp = mid + 1;
                } else if elem < self.list[mid] {
                    rp = mid;
                } else {
                    return Some(mid);
                }
            }
            return None;
        }

        pub fn remove(&mut self, elem: i32) -> (removed_element: bool)
            requires
                old(self).view().len() <= usize::MAX / 2,
                is_sorted(old(self).view())
            ensures
                is_sorted(self.view()),
                removed_element ==> (
                    old(self).view().contains(elem) && 
                    self.view().to_multiset() =~= old(self).view().to_multiset().remove(elem)
                ),
                !removed_element ==> (
                    !old(self).view().contains(elem) && 
                    old(self).view() == self.view()
                )
        {
            broadcast use group_seq_properties; 
            if let Some(index) = self.index_of(elem) {
                Vec::remove(&mut self.list, index);
                return true;
            }
            return false;
        }

        pub fn view_list(&self) -> (list_ref: &[i32]) 
            ensures
                self.view().len() == list_ref.len(),
                forall |i: int| 0 <= i < self.view().len() ==> self.view()[i] == list_ref[i]
        {
            &self.list
        }
    }
}