use std::{fmt::Debug, iter};

/// An implementation of a [LIFO stack](https://en.wikipedia.org/wiki/Stack_(abstract_data_type))
/// that supports *O*(1) push, pop and find-minimum.
///
/// Internally, each element on the stack contains a value and the index of the minimum value below it
/// (or itself if it is smaller than everything below it). Each time we push, we compare the new value
/// to the smallest value already on the stack. If it is smaller, we push the new value with its *own*
/// index. Otherwise, we push the new value with the index of the smaller value that was already on
/// the stack.
///
/// To find the minimum value, we just use the index of the last element on the stack.
///
/// # Example
/// ```
/// use rust_dsa::MinStack;
///
/// // First, we create a new stack.
/// let mut stack = MinStack::new();
///
/// // We can push elements.
/// stack.push(2);
/// stack.push(3);
/// stack.push(6);
/// stack.push(1);
///
/// // We can get the minimum element.
/// assert_eq!(stack.get_min(), Some(&1));
///
/// // We can peek and pop as usual.
/// assert_eq!(stack.peek(), Some(&1));
/// assert_eq!(stack.pop(), Some(1));
///
/// // The min element reflects the stack's new state.
/// assert_eq!(stack.get_min(), Some(&2));
///
/// // We can iterate over the stack.
/// for x in stack {
///     // Prints 6, 3 and 2.
///     println!("{x}");
/// }
///
/// // We can also create stacks from arrays.
/// let a = MinStack::from(['s', 't', 'a', 'c', 'k']);
///
/// // And iterators.
/// let b: MinStack<char> = "stack".chars().collect();
///
/// assert!(a == b);
/// ```
#[derive(Clone)]
pub struct MinStack<T> {
    stack: Vec<(T, usize)>,
}

// [5, 3, 4, 8, 2, 6, 1] -> [(5, 0), (3, 1), (4, 1), (8, 1), (2, 4), (6, 4), (1, 6)]

impl<T> MinStack<T> {
    /// Creates an empty stack.
    pub fn new() -> Self {
        MinStack { stack: Vec::new() }
    }

    /// Creates an empty stack with the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        MinStack {
            stack: Vec::with_capacity(capacity),
        }
    }

    /// Pushes an element onto the top of the stack.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinStack;
    ///
    /// let mut stack = MinStack::new();
    /// stack.push(5);
    ///
    /// assert_eq!(stack.pop(), Some(5));
    /// assert_eq!(stack.pop(), None);
    /// ```
    pub fn push(&mut self, value: T)
    where
        T: Ord,
    {
        if let Some((_, index)) = self.stack.last() {
            if value < self.stack[*index].0 {
                self.stack.push((value, self.len()));
            } else {
                self.stack.push((value, *index));
            }
        } else {
            self.stack.push((value, 0));
        }
    }

    /// Removes the last element on the stack and returns it or `None` if the stack is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinStack;
    ///
    /// let mut stack = MinStack::from([5]);
    ///
    /// assert_eq!(stack.pop(), Some(5));
    /// assert_eq!(stack.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.stack.pop().map(|(value, _)| value)
    }

    /// Returns a reference the last element on the stack or `None` if the stack is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinStack;
    ///
    /// let mut stack = MinStack::from(vec!['a']);
    ///
    /// assert_eq!(stack.peek(), Some(&'a'));
    ///
    /// stack.pop();
    ///
    /// assert_eq!(stack.peek(), None);
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.stack.last().map(|(value, _)| value)
    }

    /// Returns the smallest element on the stack or `None` if the stack is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinStack;
    ///
    /// let mut stack = MinStack::from([5, 3, 4, 8, 2, 6, 1]);
    ///
    /// assert_eq!(stack.get_min(), Some(&1));
    ///
    /// stack.pop();
    ///
    /// assert_eq!(stack.get_min(), Some(&2));
    ///
    /// stack.clear();
    ///
    /// assert_eq!(stack.get_min(), None);
    /// ```
    pub fn get_min(&mut self) -> Option<&T> {
        if let Some((_, index)) = self.stack.last() {
            self.stack.get(*index).map(|(value, _)| value)
        } else {
            None
        }
    }

    /// Returns the number of elements on the stack.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinStack;
    ///
    /// let mut stack = MinStack::from([5, 3, 4, 8, 2, 6, 1]);
    ///
    /// assert_eq!(stack.len(), 7);
    ///
    /// stack.clear();
    ///
    /// assert_eq!(stack.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        self.stack.len()
    }

    /// Returns `true` if the stack is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinStack;
    ///
    /// let mut stack = MinStack::from([5, 3, 4, 8, 2, 6, 1]);
    ///
    /// assert!(!stack.is_empty());
    ///
    /// stack.clear();
    ///
    /// assert!(stack.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the stack.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinStack;
    ///
    /// let mut stack = MinStack::from([5, 3, 4, 8, 2, 6, 1]);
    ///
    /// assert!(!stack.is_empty());
    ///
    /// stack.clear();
    ///
    /// assert!(stack.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.stack.clear();
    }

    // for MinQueue
    pub(crate) fn bottom(&self) -> Option<&T> {
        self.stack.get(0).map(|(value, _)| value)
    }

    // for MinQueue
    pub(crate) fn borrow_stack(&self) -> &Vec<(T, usize)> {
        &self.stack
    }

    // for MinQueue
    pub(crate) fn get_stack(self) -> Vec<(T, usize)> {
        self.stack
    }
}

impl<T> Default for MinStack<T> {
    fn default() -> Self {
        MinStack::new()
    }
}

impl<T, const N: usize> From<[T; N]> for MinStack<T>
where
    T: Ord,
{
    fn from(arr: [T; N]) -> Self {
        arr.into_iter().collect()
    }
}

impl<T> From<Vec<T>> for MinStack<T>
where
    T: Ord,
{
    fn from(vec: Vec<T>) -> Self {
        vec.into_iter().collect()
    }
}

impl<T> FromIterator<T> for MinStack<T>
where
    T: Ord,
{
    fn from_iter<A: IntoIterator<Item = T>>(iter: A) -> Self {
        let iter = iter.into_iter();
        let mut stack = MinStack::with_capacity(iter.size_hint().0);
        for value in iter {
            stack.push(value);
        }
        stack
    }
}

impl<T> IntoIterator for MinStack<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;
    fn into_iter(self) -> Self::IntoIter {
        let mut vec: Vec<_> = self.stack.into_iter().map(|(value, _)| value).collect();
        vec.reverse();
        IntoIter {
            iter: vec.into_iter(),
        }
    }
}

pub struct IntoIter<T> {
    iter: std::vec::IntoIter<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, T> IntoIterator for &'a MinStack<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            stack: self.stack.iter().map(|(value, _)| value).collect(),
        }
    }
}

pub struct Iter<'a, T: 'a> {
    stack: Vec<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.stack.pop()
    }
}

impl<T> Debug for MinStack<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (i, value) in self.into_iter().enumerate() {
            if i == 0 {
                write!(f, "{:?}", value)?;
            } else {
                write!(f, ", {:?}", value)?;
            }
        }
        write!(f, "]")
    }
}

impl<T> PartialEq for MinStack<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() == other.len() {
            for (s, o) in iter::zip(self, other) {
                if s != o {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
}

impl<T: Eq> Eq for MinStack<T> {}
