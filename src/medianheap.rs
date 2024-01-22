use std::cmp::{Ordering, Reverse};
use std::collections::BinaryHeap;
use std::mem;

/// A data structure for efficiently calculating a running median.
///
/// # Example
/// ```
/// use rust_dsa::{MedianHeap, Median};
///
/// // First, we create a new heap.
/// let mut heap = MedianHeap::new();
///
/// // Then we can add values in any order.
/// heap.insert(4);
/// heap.insert(1);
/// heap.insert(3);
/// heap.insert(6);
/// heap.insert(2);
///
/// // We can get the median value.
/// assert_eq!(heap.median(), Some(Median::One(&3)));
///
/// heap.insert(9);
///
/// // If the heap size is even, there are two medians.
/// assert_eq!(heap.median(), Some(Median::Two(&3, &4)));
///
/// // We can pop the median value.
/// assert_eq!(heap.pop(), Some(3));
/// assert_eq!(heap.pop(), Some(4));
///
/// // And we can add values from an iterator.
/// heap.extend(3..8);
///
/// assert_eq!(heap.median(), Some(Median::One(&5)));
/// assert_eq!(heap.len(), 9);
/// ```
///
/// # Runtime complexity
///
/// | Operation              | Runtime Complexity |
/// | ---------------------- | ------------------ |
/// | [`MedianHeap::insert`] | *O*(log *n*)       |
/// | [`MedianHeap::median`] | *O*(1)             |
/// | [`MedianHeap::pop`]    | *O*(log *n*)       |
#[derive(Clone)]
pub struct MedianHeap<T> {
    low_median: Option<T>,
    high_median: Option<T>,
    low: BinaryHeap<T>,
    high: BinaryHeap<Reverse<T>>,
}

impl<T> MedianHeap<T> {
    // Creates a new heap.
    pub fn new() -> Self
    where
        T: Ord,
    {
        MedianHeap {
            low_median: None,
            high_median: None,
            low: BinaryHeap::new(),
            high: BinaryHeap::new(),
        }
    }

    /// Inserts a new value into the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::{Median, MedianHeap};
    ///
    /// let mut heap = MedianHeap::new();
    ///
    /// heap.insert(5);
    /// heap.insert(2);
    ///
    /// assert_eq!(heap.median(), Some(Median::Two(&2, &5)));
    ///
    /// heap.insert(3);
    ///
    /// assert_eq!(heap.median(), Some(Median::One(&3)));
    /// ```
    pub fn insert(&mut self, value: T)
    where
        T: Ord,
    {
        match (&self.low_median, &self.high_median) {
            (None, None) => self.low_median = Some(value),
            (Some(median), None) => match value.cmp(median) {
                Ordering::Less => {
                    if self.low.peek().map_or(false, |peek| &value < peek) {
                        mem::swap(&mut self.low_median, &mut self.high_median);
                        self.low_median = self.low.pop();
                        self.low.push(value);
                    } else {
                        let old_median = mem::replace(&mut self.low_median, Some(value));
                        self.high_median = old_median;
                    }
                }
                Ordering::Equal => self.high_median = Some(value),
                Ordering::Greater => {
                    if self.high.peek().map_or(false, |peek| value > peek.0) {
                        self.high_median = self.high.pop().map(|v| v.0);
                        self.high.push(Reverse(value));
                    } else {
                        self.high_median = Some(value);
                    }
                }
            },
            (Some(low), Some(high)) => {
                if &value < low {
                    self.low.push(value);
                    self.high.push(Reverse(self.high_median.take().unwrap()));
                } else if &value > high {
                    let old_low = mem::replace(&mut self.low_median, self.high_median.take());
                    self.low.push(old_low.unwrap());
                    self.high.push(Reverse(value));
                } else {
                    let old_low = mem::replace(&mut self.low_median, Some(value));
                    let old_high = self.high_median.take();
                    self.low.push(old_low.unwrap());
                    self.high.push(Reverse(old_high.unwrap()));
                }
            }
            (None, Some(_)) => unreachable!(),
        }
    }

    /// Pops the median element from the heap.
    ///
    /// If there are two median values (i.e., [`MedianHeap::median`] would
    /// return [`Median::Two`]), then this function returns the *smaller* of
    /// the two values.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MedianHeap;
    ///
    /// let mut heap: MedianHeap<_> = "acb".chars().collect();
    ///
    /// assert_eq!(heap.pop(), Some('b'));
    /// assert_eq!(heap.pop(), Some('a'));
    /// assert_eq!(heap.pop(), Some('c'));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T>
    where
        T: Ord,
    {
        match (self.low_median.is_some(), self.high_median.is_some()) {
            (false, false) => None,
            (true, false) => {
                let result = self.low_median.take();
                self.low_median = self.low.pop();
                self.high_median = self.high.pop().map(|v| v.0);
                result
            }
            (true, true) => mem::replace(&mut self.low_median, self.high_median.take()),
            (false, true) => unreachable!(),
        }
    }

    /// Returns one or two median values in the heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::{Median, MedianHeap};
    ///
    /// let mut heap = MedianHeap::from([13, 8, 5, 3, 2, 1, 1]);
    /// assert_eq!(heap.median(), Some(Median::One(&3)));
    ///
    /// heap.pop();
    /// assert_eq!(heap.median(), Some(Median::Two(&2, &5)));
    ///
    /// heap.clear();
    /// assert_eq!(heap.median(), None);
    /// ```
    pub fn median(&self) -> Option<Median<'_, T>> {
        match (&self.low_median, &self.high_median) {
            (None, None) => None,
            (Some(median), None) => Some(Median::One(median)),
            (Some(low), Some(high)) => Some(Median::Two(low, high)),
            (None, Some(_)) => unreachable!(),
        }
    }

    /// Returns the number of elements in the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MedianHeap;
    ///
    /// let mut heap: MedianHeap<_> = "abcdefgh".chars().collect();
    /// assert_eq!(heap.len(), 8);
    ///
    /// heap.extend("xyz".chars());
    /// assert_eq!(heap.len(), 11);
    /// ```
    pub fn len(&self) -> usize {
        usize::from(self.low_median.is_some())
            + usize::from(self.high_median.is_some())
            + self.low.len()
            + self.high.len()
    }

    /// Returns `true` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MedianHeap;
    ///
    /// let mut heap = MedianHeap::from([1, 2, 3]);
    /// assert!(!heap.is_empty());
    ///
    /// heap.clear();
    /// assert!(heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::MedianHeap;
    ///
    /// let mut heap = MedianHeap::from(["foo", "bar", "baz"]);
    /// assert!(!heap.is_empty());
    ///
    /// heap.clear();
    /// assert!(heap.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.low_median = None;
        self.high_median = None;
        self.low.clear();
        self.high.clear();
    }
}

/// An enum representing the median in a [`MedianHeap`].
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum Median<'a, T> {
    One(&'a T),
    Two(&'a T, &'a T),
}

impl<T> FromIterator<T> for MedianHeap<T>
where
    T: Ord,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut heap = MedianHeap::new();
        for value in iter {
            heap.insert(value);
        }
        heap
    }
}

impl<T, const N: usize> From<[T; N]> for MedianHeap<T>
where
    T: Ord,
{
    fn from(array: [T; N]) -> Self {
        array.into_iter().collect()
    }
}

impl<T> Extend<T> for MedianHeap<T>
where
    T: Ord,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for value in iter {
            self.insert(value);
        }
    }
}

impl<T> Default for MedianHeap<T>
where
    T: Ord,
{
    fn default() -> Self {
        MedianHeap::new()
    }
}
