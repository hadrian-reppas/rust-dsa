use std::any::{Any, TypeId};

/// A [stack](https://en.wikipedia.org/wiki/Stack_(abstract_data_type))
/// that can hold arbitrary types.
///
/// # Example
/// ```
/// use rust_dsa::AnyStack;
///
/// // First, we create a new deque
/// let mut stack = AnyStack::new();
///
/// // We can push elements of different types.
/// stack.push(4);
/// stack.push(true);
/// stack.push('a');
/// stack.push("str");
///
/// // We can check the top type.
/// assert!(stack.top_is::<&str>());
/// assert!(!stack.top_is::<char>());
///
/// // We can peek the top value.
/// assert_eq!(stack.peek::<&str>(), Some(&"str"));
///
/// // If we try to peek the wrong type, we get None
/// assert_eq!(stack.peek::<bool>(), None);
///
/// // We can also pop values.
/// assert_eq!(stack.pop::<&str>(), Some("str"));
/// assert_eq!(stack.pop::<char>(), Some('a'));
///
/// // We can check the stack's length.
/// assert_eq!(stack.len(), 2);
///
/// // And clear the stack.
/// stack.clear();
/// assert!(stack.is_empty());
/// ```
pub struct AnyStack(Vec<MyAny>);

impl AnyStack {
    /// Creates a new stack.
    pub fn new() -> AnyStack {
        AnyStack(Vec::new())
    }

    /// Pushes a value onto the stack.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::AnyStack;
    ///
    /// let mut stack = AnyStack::new();
    /// stack.push(5);
    ///
    /// assert_eq!(stack.pop::<i32>(), Some(5));
    /// assert_eq!(stack.pop::<i32>(), None);
    /// ```
    pub fn push<T: Any>(&mut self, value: T) {
        self.0.push(MyAny::new(value));
    }

    /// Tries to pop a value of type `T` from the stack.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::AnyStack;
    ///
    /// let mut stack = AnyStack::new();
    /// stack.push('a');
    ///
    /// assert_eq!(stack.pop::<i32>(), None);
    /// assert_eq!(stack.pop::<char>(), Some('a'));
    /// assert_eq!(stack.pop::<char>(), None);
    /// ```
    pub fn pop<T: Any>(&mut self) -> Option<T> {
        if self.top_is::<T>() {
            self.0.pop().map(MyAny::into)
        } else {
            None
        }
    }

    /// Tries to peek a value of type `T` from the top of the stack.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::AnyStack;
    ///
    /// let mut stack = AnyStack::new();
    /// stack.push(4);
    ///
    /// assert_eq!(stack.peek::<i32>(), Some(&4));
    /// assert_eq!(stack.peek::<char>(), None);
    /// ```
    pub fn peek<T: Any>(&self) -> Option<&T> {
        if self.top_is::<T>() {
            self.0.last().map(MyAny::borrow)
        } else {
            None
        }
    }

    /// Returns `true` if the top of the stack has type `T`.
    ///
    /// This function returns `false` if the stack is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::AnyStack;
    ///
    /// let mut stack = AnyStack::new();
    /// stack.push('z');
    ///
    /// assert!(stack.top_is::<char>());
    /// assert!(!stack.top_is::<i32>());
    /// ```
    pub fn top_is<T: Any>(&self) -> bool {
        self.0.last().map_or(false, MyAny::is::<T>)
    }

    /// Returns the length of the stack.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::AnyStack;
    ///
    /// let mut stack = AnyStack::new();
    /// stack.push(1);
    /// stack.push(2.0);
    /// stack.push("three");
    ///
    /// assert_eq!(stack.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the stack is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Removes all values from the stack.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::AnyStack;
    ///
    /// let mut stack = AnyStack::new();
    /// stack.push(1);
    /// stack.push(false);
    /// assert_eq!(stack.len(), 2);
    ///
    /// stack.clear();
    ///
    /// assert!(stack.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.0.clear()
    }
}

impl Default for AnyStack {
    fn default() -> AnyStack {
        AnyStack::new()
    }
}

struct MyAny(Box<dyn Any>);

impl MyAny {
    fn new<T: Any>(value: T) -> MyAny {
        MyAny(Box::new(value))
    }

    fn is<T: Any>(&self) -> bool {
        let r: &dyn Any = &*self.0;
        r.type_id() == TypeId::of::<T>()
    }

    fn into<T: Any>(self) -> T {
        fn downcast<T: Any>(value: Box<dyn Any>) -> Box<T> {
            value.downcast::<T>().unwrap()
        }

        *downcast::<T>(self.0)
    }

    fn borrow<T: Any>(&self) -> &T {
        fn downcast<T: Any>(value: &dyn Any) -> &T {
            value.downcast_ref::<T>().unwrap()
        }

        downcast::<T>(&*self.0)
    }
}
