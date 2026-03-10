pub struct SortedList<T: Eq + PartialEq + Ord + PartialOrd> {
    list: Vec<T>
}

impl<T: Eq + PartialEq + Ord + PartialOrd> SortedList<T> {
    pub fn new() -> Self {
        SortedList { list: Vec::<T>::new() }
    }

    pub fn insert(&mut self, elem: T) {
        let mut lp = 0;
        let mut rp = self.list.len();

        while lp != rp {
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

        self.list.insert(lp, elem)
    }

    pub fn contains(&self, elem: &T) -> bool {
        let mut lp = 0;
        let mut rp = self.list.len();

        while lp != rp {
            let mid = (lp + rp) / 2;
            if *elem > self.list[mid] {
                lp = mid + 1;
            } else if *elem < self.list[mid] {
                rp = mid;
            } else {
                return true;
            }
        }

        return false;
    }

    pub fn remove(&mut self, elem: &T) {
        let mut lp = 0;
        let mut rp = self.list.len();

        while lp != rp {
            let mid = (lp + rp) / 2;
            if *elem > self.list[mid] {
                lp = mid + 1;
            } else if *elem < self.list[mid] {
                rp = mid;
            } else {
                self.list.remove(mid);
            }
        }
    }

    pub fn remove_all_instances_of(&mut self, elem: &T) {
        while self.contains(elem) {
            self.remove(elem);
        }
    }

    pub fn view_list(&self) -> &[T] {
        &self.list
    }
}