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
            
            if self.list.len() == 0 {
                self.list.push(elem);
                return;
            }

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

        // pub fn contains(&self, elem: &T) -> bool {
        //     let mut lp = 0;
        //     let mut rp = self.list.len() - 1;

        //     while lp != rp {
        //         let mid = (lp + rp) / 2;
        //         if *elem > self.list[mid] {
        //             lp = mid;
        //         } else if *elem < self.list[mid] {
        //             rp = mid;
        //         } else {
        //             return true;
        //         }
        //     }

        //     return false;
        // }

        // pub fn remove(&mut self, elem: &T) {
        //     let mut lp = 0;
        //     let mut rp = self.list.len() - 1;

        //     while lp != rp {
        //         let mid = (lp + rp) / 2;
        //         if *elem > self.list[mid] {
        //             lp = mid;
        //         } else if *elem < self.list[mid] {
        //             rp = mid;
        //         } else {
        //             self.list.remove(mid);
        //         }
        //     }
        // }

        // pub fn remove_all_instances_of(&mut self, elem: &T) {
        //     while self.contains(elem) {
        //         self.remove(elem);
        //     }
        // }

        pub fn view_list(&self) -> (list_ref: &[i32]) 
            ensures
                self.view().len() == list_ref.len(),
                forall |i: int| 0 <= i < self.view().len() ==> self.view()[i] == list_ref[i]
        {
            &self.list
        }
    }
}