use vstd::prelude::*;

verus!{
    pub struct Stack<T> {
        stack: Vec<T>
    }

    impl<T> Stack<T> {
        pub closed spec fn view(&self) -> Seq<T> {
            self.stack@
        }

        pub fn new() -> (new: Self) 
            ensures
                new.view().len() == 0
        {
            Stack { stack: Vec::<T>::new() }
        }

        pub fn push(&mut self, elem: T) 
            ensures
                old(self).view().len() + 1 == self.view().len(),
                forall |i: int| 0 <= i < old(self).view().len() ==> old(self).view()[i] == self.view()[i],
                self.view()[self.view().len() - 1] == elem
        {
            self.stack.push(elem);
        }

        pub fn pop(&mut self) -> (elem: Option<T>) 
            ensures
                old(self).view().len() == 0 ==> (old(self).view() == self.view() && elem == None::<T>),
                old(self).view().len() > 0 ==> (
                    old(self).view().len() - 1 == self.view().len() && 
                    forall |i: int| 0 <= i < self.view().len() ==> old(self).view()[i] == self.view()[i] &&
                    elem == Some(old(self).view()[old(self).view().len() - 1])
                )
        {
            self.stack.pop()
        }
        
        pub fn peek(&self) -> (elem: Option<&T>) 
            ensures
                self.view().len() == 0 ==> elem == None::<&T>,
                self.view().len() > 0 ==> elem == Some(&self.view()[self.view().len() - 1])
        {
            match self.stack.len() {
                0 => None,
                _ => Some(&self.stack[self.stack.len() - 1])
            }
        }

        pub fn len(&self) -> (len: usize) 
            ensures
                self.view().len() == len
        {
            self.stack.len()
        }
    }
}