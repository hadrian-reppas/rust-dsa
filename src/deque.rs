#![allow(dead_code)]

use std::{mem::MaybeUninit, ops::RangeBounds};

const MIN_CAPACITY: usize = 10;

/// A deque implementation backed by a ring buffer.
///
/// # Example
/// ```
/// use rust_dsa::Deque;
///
/// // First, we create a new deque.
/// let mut deque = Deque::new();
///
/// // Then we can push values onto the front or back.
/// deque.push_back(4);
/// deque.push_back(1);
/// deque.push_front(3);
///
/// // And pop from the front or back
/// assert_eq!(deque.pop_back(), Some(1));
/// assert_eq!(deque.pop_front(), Some(3));
/// assert_eq!(deque.pop_front(), Some(4));
///
/// // We can also crate deques from arrays.
/// let deque_a = Deque::from(['d', 'e', 'q', 'u', 'e']);
///
/// // And iterators.
/// let deque_b: Deque<_> = "deque".chars().collect();
///
/// // We can also iterate over a deque.
/// for (a, b) in deque_a.into_iter().zip(deque_b) {
///     assert_eq!(a, b);
/// }
/// ```
///
/// # Runtime complexity
///
/// | Operation           | Runtime Complexity |
/// | ------------------- | ------------------ |
/// | [Deque::push_back]  | *O*(1)             |
/// | [Deque::push_front] | *O*(1)             |
/// | [Deque::pop_back]   | *O*(1)             |
/// | [Deque::pop_front]  | *O*(1)             |
pub struct Deque<T> {
    buffer: Vec<MaybeUninit<T>>,
    front: usize,
    back: usize,
    len: usize,
}

impl<T> Deque<T> {
    /// Creates an empty deque.
    pub fn new() -> Self {
        Deque {
            buffer: Vec::new(),
            front: 0,
            back: 0,
            len: 0,
        }
    }

    /// Creates an empty deque with the given capacity.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let deque: Deque<i32> = Deque::with_capacity(10);
    ///
    /// assert_eq!(deque.capacity(), 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Deque {
            buffer: (0..capacity).map(|_| MaybeUninit::uninit()).collect(),
            front: 0,
            back: 0,
            len: 0,
        }
    }

    /// Pushes a value onto the back of the deque.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let mut deque = Deque::new();
    ///
    /// deque.push_back(5);
    ///
    /// assert_eq!(deque.peek_back(), Some(&5));
    /// ```
    pub fn push_back(&mut self, value: T) {
        if self.len() == self.capacity() {
            self.grow();
        }

        self.len += 1;
        self.buffer[self.back] = MaybeUninit::new(value);
        self.back = self.increment(self.back);
    }

    /// Pushes a value onto the front of the deque.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let mut deque = Deque::new();
    ///
    /// deque.push_front(5);
    ///
    /// assert_eq!(deque.peek_front(), Some(&5));
    /// ```
    pub fn push_front(&mut self, value: T) {
        if self.len() == self.capacity() {
            self.grow();
        }

        self.len += 1;
        self.front = self.decrement(self.front);
        self.buffer[self.front] = MaybeUninit::new(value);
    }

    /// Pops a value from the back of the deque.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let mut deque = Deque::from([1, 2, 3]);
    ///
    /// assert_eq!(deque.pop_back(), Some(3));
    /// assert_eq!(deque.pop_back(), Some(2));
    /// assert_eq!(deque.pop_back(), Some(1));
    /// assert_eq!(deque.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            self.len -= 1;
            self.back = self.decrement(self.back);
            Some(unsafe { self.buffer[self.back].assume_init_read() })
        }
    }

    /// Pops a value from the front of the deque.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let mut deque = Deque::from([1, 2, 3]);
    ///
    /// assert_eq!(deque.pop_front(), Some(1));
    /// assert_eq!(deque.pop_front(), Some(2));
    /// assert_eq!(deque.pop_front(), Some(3));
    /// assert_eq!(deque.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            self.len -= 1;
            let value = unsafe { self.buffer[self.front].assume_init_read() };
            self.front = self.increment(self.front);
            Some(value)
        }
    }

    /// Peeks the value at the back of the deque.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let deque = Deque::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(deque.peek_back(), Some(&'c'));
    ///
    /// let empty: Deque<u8> = Deque::new();
    /// assert_eq!(empty.peek_back(), None);
    /// ```
    pub fn peek_back(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { self.buffer[self.decrement(self.back)].assume_init_ref() })
        }
    }

    /// Peeks the value at the front of the deque.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let deque = Deque::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(deque.peek_front(), Some(&'a'));
    ///
    /// let empty: Deque<u8> = Deque::new();
    /// assert_eq!(empty.peek_front(), None);
    /// ```
    pub fn peek_front(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { self.buffer[self.front].assume_init_ref() })
        }
    }

    /// Returns a reference to the element in position `index` if `index` is in bounds.
    ///
    /// `.get(0)` is equivalent to `.peek_front()`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let mut deque = Deque::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(deque.get(1), Some(&'b'));
    ///
    /// deque.pop_front();
    /// assert_eq!(deque.get(1), Some(&'c'));
    ///
    /// deque.pop_front();
    /// assert_eq!(deque.get(1), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len() {
            let i = self.add(self.front, index);
            self.buffer
                .get(i)
                .map(|value| unsafe { value.assume_init_ref() })
        } else {
            None
        }
    }

    /// Removes the specified range from the deque, returning all removed elements as an iterator.
    ///
    /// To simplify the implementation, this always reallocates the deque.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let mut deque: Deque<_> = ('a'..='z').collect();
    ///
    /// let mut drain = deque.drain(1..25);
    /// assert_eq!(drain.next(), Some('b'));
    /// assert_eq!(drain.next(), Some('c'));
    /// // etc...
    ///
    /// // Now, deque is just ['a', 'z']
    /// assert_eq!(deque.pop_front(), Some('a'));
    /// assert_eq!(deque.pop_front(), Some('z'));
    /// assert_eq!(deque.pop_front(), None);
    /// ```
    ///
    /// # Panics
    /// Panics if the starting point is greater than the end point or if the
    /// end point is greater than the length of the deque.
    pub fn drain<R>(&mut self, range: R) -> Drain<T>
    where
        R: RangeBounds<usize>,
    {
        let mut elements = Vec::with_capacity(self.len());
        let mut i = self.front;
        for _ in 0..self.len() {
            elements.push(unsafe { self.buffer[i].assume_init_read() });
            i = self.increment(i);
        }

        let mut drained_elements: Vec<_> = elements.drain(range).collect();
        drained_elements.reverse();

        *self = elements.into_iter().collect();

        Drain {
            elements: drained_elements,
        }
    }

    /// Returns the length of the deque.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let full: Deque<_> = (0..10).collect();
    /// assert_eq!(full.len(), 10);
    ///
    /// let empty: Deque<bool> = Deque::new();
    /// assert_eq!(empty.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the deque is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let empty: Deque<bool> = Deque::new();
    /// assert!(empty.is_empty());
    ///
    /// let full: Deque<_> = (0..10).collect();
    /// assert!(!full.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the deque.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let mut deque = Deque::from([1, 2, 3]);
    ///
    /// assert!(!deque.is_empty());
    ///
    /// deque.clear();
    ///
    /// assert!(deque.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.drain(..);
    }

    /// Shrinks the capacity of the buffer if possible.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let mut deque = Deque::with_capacity(10);
    /// deque.push_back("foo");
    /// deque.push_back("bar");
    ///
    /// assert_eq!(deque.capacity(), 10);
    /// assert_eq!(deque.len(), 2);
    ///
    /// deque.shrink_to_fit();
    ///
    /// assert_eq!(deque.capacity(), 2);
    /// assert_eq!(deque.len(), 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.buffer = self.drain(..).map(MaybeUninit::new).collect();
        self.len = self.buffer.len();
    }

    /// Returns the number of elements the deque can hold without reallocating.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Deque;
    ///
    /// let mut deque = Deque::with_capacity(10);
    ///
    /// assert_eq!(deque.capacity(), 10);
    ///
    /// for i in 0..20 {
    ///     deque.push_back(i);
    /// }
    ///
    /// assert!(deque.capacity() > 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.buffer.len()
    }

    fn grow(&mut self) {
        let old_capacity = self.capacity();
        let new_capacity = std::cmp::max(MIN_CAPACITY, 2 * old_capacity);
        let delta = new_capacity - old_capacity;
        let new_buffer: Vec<_> = self
            .drain(..)
            .map(MaybeUninit::new)
            .chain((0..delta).map(|_| MaybeUninit::uninit()))
            .collect();

        *self = Deque {
            buffer: new_buffer,
            front: 0,
            back: old_capacity,
            len: old_capacity,
        }
    }

    fn increment(&self, index: usize) -> usize {
        self.add(index, 1)
    }

    fn add(&self, mut index: usize, delta: usize) -> usize {
        index += delta;
        index % self.capacity()
    }

    fn decrement(&self, index: usize) -> usize {
        if index == 0 {
            self.capacity() - 1
        } else {
            index - 1
        }
    }
}

impl<T> IntoIterator for Deque<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter { deque: self }
    }
}

pub struct IntoIter<T> {
    deque: Deque<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.deque.pop_front()
    }
}

pub struct Drain<T> {
    elements: Vec<T>,
}

impl<T> Iterator for Drain<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.elements.pop()
    }
}

impl<T> FromIterator<T> for Deque<T> {
    fn from_iter<A: IntoIterator<Item = T>>(iter: A) -> Self {
        let buffer: Vec<_> = iter.into_iter().map(MaybeUninit::new).collect();
        Deque {
            len: buffer.len(),
            buffer,
            front: 0,
            back: 0,
        }
    }
}

impl<T, const N: usize> From<[T; N]> for Deque<T> {
    fn from(array: [T; N]) -> Self {
        array.into_iter().collect()
    }
}

impl<T> From<Vec<T>> for Deque<T> {
    fn from(vec: Vec<T>) -> Self {
        vec.into_iter().collect()
    }
}

impl<T> Default for Deque<T> {
    fn default() -> Self {
        Deque::new()
    }
}
