use crate::MinStack;
use std::{fmt::Debug, iter};

/// An implementation of a [FIFO queue](http://en.wikipedia.org/wiki/Queue_(data_structure))
/// that supports O(1) push, pop and find-minimum.
///
/// Keith Schwarz explains how this works [here](https://keithschwarz.com/interesting/code/?dir=min-queue).
///
/// # Example
/// ```
/// use rust_dsa::MinQueue;
///
/// // First, we create a new queue.
/// let mut queue = MinQueue::new();
///
/// // We can push elements.
/// queue.push(1);
/// queue.push(6);
/// queue.push(2);
/// queue.push(3);
///
/// // We can get the minimum element.
/// assert_eq!(queue.get_min(), Some(&1));
///
/// // We can peek and poll as usual.
/// assert_eq!(queue.peek(), Some(&1));
/// assert_eq!(queue.poll(), Some(1));
///
/// // The min element reflects the queue's new state.
/// assert_eq!(queue.get_min(), Some(&2));
///
/// // We can iterate over the queue.
/// for x in queue {
///     // Prints 6, 2 and 3.
///     println!("{x}");
/// }
///
/// // We can also create queues from arrays.
/// let a = MinQueue::from(['q', 'u', 'e', 'u', 'e']);
///
/// // And iterators.
/// let b: MinQueue<char> = "queue".chars().collect();
///
/// assert!(a == b);
/// ```
#[derive(Clone)]
pub struct MinQueue<T> {
    old: MinStack<T>,
    new: MinStack<T>,
}

impl<T> MinQueue<T> {
    /// Creates an empty queue.
    pub fn new() -> Self {
        MinQueue {
            old: MinStack::new(),
            new: MinStack::new(),
        }
    }

    /// Creates an empty queue with the specified capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        MinQueue {
            old: MinStack::new(),
            new: MinStack::with_capacity(capacity),
        }
    }

    /// Pushes an element into the queue.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinQueue;
    ///
    /// let mut queue = MinQueue::new();
    /// queue.push(5);
    ///
    /// assert_eq!(queue.poll(), Some(5));
    /// assert_eq!(queue.poll(), None);
    /// ```
    pub fn push(&mut self, value: T)
    where
        T: Ord,
    {
        self.new.push(value);
    }

    /// Removes the next element in the queue and returns it or `None` if the queue is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinQueue;
    ///
    /// let mut queue = MinQueue::from([5]);
    ///
    /// assert_eq!(queue.poll(), Some(5));
    /// assert_eq!(queue.poll(), None);
    /// ```
    pub fn poll(&mut self) -> Option<T>
    where
        T: Ord,
    {
        if self.old.is_empty() {
            while let Some(value) = self.new.pop() {
                self.old.push(value);
            }
        }
        self.old.pop()
    }

    /// Returns a reference the next element in the queue or `None` if the queue is queue.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinQueue;
    ///
    /// let mut queue = MinQueue::from(['a']);
    ///
    /// assert_eq!(queue.peek(), Some(&'a'));
    ///
    /// queue.poll();
    ///
    /// assert_eq!(queue.peek(), None);
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.old.peek().or_else(|| self.new.bottom())
    }

    /// Returns the smallest element in the queue or `None` if the queue is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinQueue;
    ///
    /// let mut queue = MinQueue::from([1, 5, 3, 4, 8, 2, 6]);
    ///
    /// assert_eq!(queue.get_min(), Some(&1));
    ///
    /// queue.poll();
    ///
    /// assert_eq!(queue.get_min(), Some(&2));
    ///
    /// queue.clear();
    ///
    /// assert_eq!(queue.get_min(), None);
    /// ```
    pub fn get_min(&mut self) -> Option<&T>
    where
        T: Ord,
    {
        match (self.new.get_min(), self.old.get_min()) {
            (None, None) => None,
            (new_min, None) => new_min,
            (None, old_min) => old_min,
            (Some(new_min), Some(old_min)) => {
                if new_min < old_min {
                    Some(new_min)
                } else {
                    Some(old_min)
                }
            }
        }
    }

    /// Returns the number of elements in the queue.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinQueue;
    ///
    /// let mut queue = MinQueue::from([1, 5, 3, 4, 8, 2, 6]);
    ///
    /// assert_eq!(queue.len(), 7);
    ///
    /// queue.clear();
    ///
    /// assert_eq!(queue.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        self.old.len() + self.new.len()
    }

    /// Returns `true` if the queue is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinQueue;
    ///
    /// let mut queue = MinQueue::from([1, 5, 3, 4, 8, 2, 6]);
    ///
    /// assert!(!queue.is_empty());
    ///
    /// queue.clear();
    ///
    /// assert!(queue.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the queue.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MinQueue;
    ///
    /// let mut queue = MinQueue::from([5, 3, 4, 8, 2, 6, 1]);
    ///
    /// assert!(!queue.is_empty());
    ///
    /// queue.clear();
    ///
    /// assert!(queue.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.old.clear();
        self.new.clear();
    }
}

impl<T> Default for MinQueue<T> {
    fn default() -> Self {
        MinQueue::new()
    }
}

impl<T, const N: usize> From<[T; N]> for MinQueue<T>
where
    T: Ord,
{
    fn from(arr: [T; N]) -> Self {
        arr.into_iter().collect()
    }
}

impl<T> FromIterator<T> for MinQueue<T>
where
    T: Ord,
{
    fn from_iter<A: IntoIterator<Item = T>>(iter: A) -> Self {
        let iter = iter.into_iter();
        let mut stack = MinQueue::with_capacity(iter.size_hint().0);
        for value in iter {
            stack.push(value);
        }
        stack
    }
}

impl<T> IntoIterator for MinQueue<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;
    fn into_iter(self) -> Self::IntoIter {
        let mut vec = Vec::with_capacity(self.len());
        vec.extend(
            self.old
                .get_stack()
                .into_iter()
                .map(|(value, _)| value)
                .rev(),
        );
        vec.extend(self.new.get_stack().into_iter().map(|(value, _)| value));
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

impl<'a, T> IntoIterator for &'a MinQueue<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;
    fn into_iter(self) -> Self::IntoIter {
        let mut queue = Vec::with_capacity(self.len());
        queue.extend(self.old.borrow_stack().iter().map(|(value, _)| value).rev());
        queue.extend(self.new.borrow_stack().iter().map(|(value, _)| value));
        Iter { queue }
    }
}

pub struct Iter<'a, T: 'a> {
    queue: Vec<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.queue.pop()
    }
}

impl<T> Debug for MinQueue<T>
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

impl<T> PartialEq for MinQueue<T>
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

impl<T: Eq> Eq for MinQueue<T> {}
