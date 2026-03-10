pub struct Stack<T> {
    stack: Vec<T>
}

impl<T> Stack<T> {
    pub fn new() -> Self {
        Stack { stack: Vec::<T>::new() }
    }

    pub fn push(&mut self, elem: T) {
        self.stack.push(elem);
    }

    pub fn pop(&mut self) -> Option<T> {
        self.stack.pop()
    }

    pub fn len(&self) -> usize {
        self.stack.len()
    }
    
    pub fn peek(&self) -> Option<&T> {
        match self.stack.len() {
            0 => None,
            _ => Some(&self.stack[self.stack.len() - 1])
        }
    }
}