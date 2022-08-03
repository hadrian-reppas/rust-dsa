use std::collections::LinkedList;
use std::fmt::Debug;
use std::iter;

/// A dynamic array implementation backed by a [VList](https://rosettacode.org/wiki/VList).
///
/// # Example
/// ```
/// use rust_dsa::VList;
///
/// // First, we create a new list.
/// let mut list = VList::new();
///
/// // Then we can push values.
/// list.push(4);
/// list.push(1);
/// list.push(3);
///
/// // We can get values.
/// assert_eq!(list.get(0), Some(&4));
/// assert_eq!(list.get(1), Some(&1));
/// assert_eq!(list.last(), Some(&3));
///
/// // And pop from them off.
/// assert_eq!(list.pop(), Some(3));
/// assert_eq!(list.pop(), Some(1));
/// assert_eq!(list.pop(), Some(4));
///
/// assert!(list.is_empty());
///
/// // We can also crate lists from arrays.
/// let list_a = VList::from(['v', 'l', 'i', 's', 't']);
///
/// // And iterators.
/// let list_b: VList<_> = "vlist".chars().collect();
///
/// // We can iterate over a list.
/// for (a, b) in std::iter::zip(list_a, list_b) {
///     assert_eq!(a, b);
/// }
/// ```
#[derive(Clone)]
pub struct VList<T> {
    nodes: LinkedList<Vec<T>>,
    len: usize,
}

impl<T> VList<T> {
    /// Creates an empty list.
    pub fn new() -> Self {
        VList {
            nodes: LinkedList::new(),
            len: 0,
        }
    }

    /// Pushes a value onto the end of the list.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::VList;
    ///
    /// let mut list = VList::new();
    ///
    /// list.push(5);
    ///
    /// assert_eq!(list.last(), Some(&5));
    /// ```
    pub fn push(&mut self, value: T) {
        if let Some(back) = self.nodes.back_mut() {
            if back.len() == back.capacity() {
                let mut new_back = Vec::with_capacity(2 * back.capacity());
                new_back.push(value);
                self.nodes.push_back(new_back);
            } else {
                back.push(value);
            }
        } else {
            self.nodes.push_back(vec![value]);
        }
        self.len += 1;
    }

    /// Removes and returns the value at the end of the list, or `None` if the list is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::VList;
    ///
    /// let mut list = VList::new();
    ///
    /// list.push(5);
    ///
    /// assert_eq!(list.pop(), Some(5));
    /// assert_eq!(list.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if let Some(back) = self.nodes.back_mut() {
            self.len -= 1;
            if back.len() == 1 {
                let value = back.pop();
                self.nodes.pop_back();
                value
            } else {
                back.pop()
            }
        } else {
            None
        }
    }

    /// Returns a reference to value at the end of the list, or `None` if the list is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::VList;
    ///
    /// let mut list = VList::from([5]);
    ///
    /// assert_eq!(list.last(), Some(&5));
    ///
    /// list.pop();
    ///
    /// assert_eq!(list.last(), None);
    /// ```
    pub fn last(&mut self) -> Option<&T> {
        if let Some(back) = self.nodes.back_mut() {
            back.last()
        } else {
            None
        }
    }

    /// Returns a reference to the value at position `index` if one exists.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::VList;
    ///
    /// let list = VList::from(['a', 'b', 'c', 'd']);
    ///
    /// assert_eq!(list.get(0), Some(&'a'));
    /// assert_eq!(list.get(1), Some(&'b'));
    /// assert_eq!(list.get(2), Some(&'c'));
    /// assert_eq!(list.get(3), Some(&'d'));
    /// assert_eq!(list.get(4), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        let node_index = (usize::BITS - (index + 1).leading_zeros() - 1) as usize;
        if let Some(node) = self.nodes.iter().nth(node_index) {
            node.get((index + 1) ^ (1 << node_index))
        } else {
            None
        }
    }

    /// Returns the length of the list.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::VList;
    ///
    /// let full: VList<_> = (0..10).collect();
    /// assert_eq!(full.len(), 10);
    ///
    /// let empty: VList<i32> = VList::new();
    /// assert_eq!(empty.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the list is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::VList;
    ///
    /// let mut list = VList::from([5, 6, 4, 2, 8]);
    ///
    /// assert!(!list.is_empty());
    ///
    /// list.clear();
    ///
    /// assert!(list.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the list.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::VList;
    ///
    /// let mut list = VList::from([5, 6, 4, 2, 8]);
    ///
    /// assert!(!list.is_empty());
    ///
    /// list.clear();
    ///
    /// assert!(list.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.len = 0;
    }
}

impl<T> Default for VList<T> {
    fn default() -> Self {
        VList::new()
    }
}

impl<T, const N: usize> From<[T; N]> for VList<T> {
    fn from(arr: [T; N]) -> Self {
        arr.into_iter().collect()
    }
}

impl<T> FromIterator<T> for VList<T> {
    /// # Example
    /// ```
    /// use rust_dsa::VList;
    ///
    /// let mut ints: VList<_> = (0..100_000).collect();
    ///
    /// for i in (0..100_000).rev() {
    ///     assert_eq!(ints.get(i), Some(&i));
    ///     assert_eq!(ints.pop(), Some(i));
    /// }
    /// ```
    fn from_iter<A: IntoIterator<Item = T>>(iter: A) -> Self {
        let iter = iter.into_iter();
        let mut list = VList::new();
        for value in iter {
            list.push(value);
        }
        list
    }
}

use std::{collections::linked_list, iter::Flatten};

impl<T> IntoIterator for VList<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            iter: self.nodes.into_iter().flatten(),
        }
    }
}

pub struct IntoIter<T> {
    iter: Flatten<linked_list::IntoIter<Vec<T>>>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<'a, T> IntoIterator for &'a VList<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            iter: self.nodes.iter().flatten(),
        }
    }
}

pub struct Iter<'a, T: 'a> {
    iter: Flatten<linked_list::Iter<'a, Vec<T>>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

impl<T> Debug for VList<T>
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

impl<T> PartialEq for VList<T>
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

impl<T: Eq> Eq for VList<T> {}
