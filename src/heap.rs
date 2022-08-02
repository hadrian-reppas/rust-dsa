#![allow(dead_code)]

use std::cmp::Ord;
use std::convert::From;

/// A [priority queue](http://en.wikipedia.org/wiki/Priority_queue) implementation
/// backed by a [binary heap](https://en.wikipedia.org/wiki/Binary_heap).
///
/// [BinaryHeap::pop] removes the *smallest* item.
///
/// # Example
///
/// ```
/// use rust_dsa::BinaryHeap;
///
/// // First, we create a new heap.
/// let mut heap = BinaryHeap::new();
///
/// // Then we can add items in any order.
/// heap.insert(4);
/// heap.insert(1);
/// heap.insert(3);
///
/// // And pop them off in ascending order.
/// assert_eq!(heap.pop(), Some(1));
/// assert_eq!(heap.pop(), Some(3));
/// assert_eq!(heap.pop(), Some(4));
/// assert_eq!(heap.pop(), None);
///
/// // We can also create heaps from arrays.
/// let mut heap = BinaryHeap::from([2, 6, 2]);
///
/// // And heaps can contain duplicate items.
/// assert_eq!(heap.pop(), Some(2));
/// assert_eq!(heap.pop(), Some(2));
///
/// assert_eq!(heap.len(), 1);
/// ```
///
/// # Runtime complexity
///
/// | Operation              | Runtime Complexity |
/// | ---------------------- | ------------------ |
/// | [`BinaryHeap::insert`] | *O*(log *n*)       |
/// | [`BinaryHeap::peek`]   | *O*(1)             |
/// | [`BinaryHeap::pop`]    | *O*(log *n*)       |
/// | [`BinaryHeap::from`]   | *O*(*n*)           |
pub struct BinaryHeap<T> {
    items: Vec<T>,
}

impl<T> BinaryHeap<T> {
    /// Creates an empty heap.
    pub fn new() -> Self {
        BinaryHeap { items: Vec::new() }
    }

    /// Inserts an item into the binary heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::new();
    /// heap.insert(4);
    /// heap.insert(1);
    /// heap.insert(3);
    ///
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    pub fn insert(&mut self, item: T)
    where
        T: Ord,
    {
        self.items.push(item);
        self.bubble_up(self.len() - 1);
    }

    /// Returns the smallest item in the binary heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([2, 1]);
    /// assert_eq!(heap.peek(), Some(&1));
    ///
    /// heap.clear();
    /// assert_eq!(heap.peek(), None);
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.items.get(0)
    }

    /// Removes and returns the smallest item in the binary heap, or returns `None`
    /// if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([4, 1, 3]);
    ///
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(4));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T>
    where
        T: Ord,
    {
        if self.is_empty() {
            None
        } else {
            let min = self.items.swap_remove(0);
            self.bubble_down(0);
            Some(min)
        }
    }

    /// Returns the length of the binary heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([1, 2, 3]);
    /// assert_eq!(heap.len(), 3);
    ///
    /// heap.clear();
    /// assert_eq!(heap.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Returns `true` if the binary heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([1, 2]);
    /// assert!(!heap.is_empty());
    ///
    /// heap.clear();
    /// assert!(heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the binary heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([1, 2]);
    ///
    /// heap.clear();
    /// assert!(heap.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.items.clear()
    }

    /// Repeatedly swaps the node at `index` with its parent until the heap
    /// invariant is restored.
    fn bubble_up(&mut self, mut index: usize)
    where
        T: Ord,
    {
        while index > 0 {
            let parent = (index - 1) / 2;
            if self.items[parent] > self.items[index] {
                self.items.swap(parent, index);
                index = parent;
            } else {
                break;
            }
        }
    }

    /// Repeatedly swaps the node at `index` with one of its children until the heap
    /// invariant is restored.
    fn bubble_down(&mut self, mut index: usize)
    where
        T: Ord,
    {
        loop {
            // find the index of the smallest child
            let child1 = 2 * index + 1;
            let child2 = child1 + 1;
            let mindex = if child2 >= self.len() || self.items[child1] < self.items[child2] {
                child1
            } else {
                child2
            };

            // if the item at `index` is greater than its smallest child, swap the two
            if mindex < self.len() && self.items[index] > self.items[mindex] {
                self.items.swap(index, mindex);
                index = mindex;
            } else {
                break;
            }
        }
    }
}

impl<T> IntoIterator for BinaryHeap<T>
where
    T: Ord,
{
    type IntoIter = IntoIter<T>;
    type Item = T;
    /// Creates an iterator that iterates over the heap's items in ascending order.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinaryHeap;
    ///
    /// let heap = BinaryHeap::from([4, 2, 3, 1]);
    ///
    /// for x in heap {
    ///     // prints 1, 2, 3, 4
    ///     println!("{x}");
    /// }
    /// ```
    fn into_iter(self) -> IntoIter<T> {
        IntoIter { heap: self }
    }
}

pub struct IntoIter<T> {
    heap: BinaryHeap<T>,
}

impl<T> Iterator for IntoIter<T>
where
    T: Ord,
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.heap.pop()
    }
}

impl<T, const N: usize> From<[T; N]> for BinaryHeap<T>
where
    T: Ord,
{
    /// Uses the [heapify algorithm](https://johnderinger.wordpress.com/2012/12/28/heapify/)
    /// to create a [BinaryHeap] in *O*(*n*) time.
    fn from(array: [T; N]) -> BinaryHeap<T>
    where
        T: Ord,
    {
        let mut heap = BinaryHeap {
            items: array.into(),
        };
        for i in (0..heap.len()).rev() {
            heap.bubble_down(i);
        }
        heap
    }
}

impl<T> Default for BinaryHeap<T> {
    fn default() -> Self {
        BinaryHeap::new()
    }
}
