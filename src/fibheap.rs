use std::collections::HashMap;

/// A [priority queue](http://en.wikipedia.org/wiki/Priority_queue) implementation
/// backed by a [Fibonacci heap](https://en.wikipedia.org/wiki/Fibonacci_heap).
///
/// [`FibonacciHeap::pop`] removes the *smallest* item.
///
/// **TODO: implement** `change_value`**.**
///
/// # Example
///
/// ```
/// use rust_dsa::FibonacciHeap;
///
/// // First, we create a new heap.
/// let mut heap = FibonacciHeap::new();
///
/// // Then we can add items in any order.
/// heap.insert(4);
/// heap.insert(1);
/// heap.insert(3);
///
/// // We can peek at the minimum item.
/// assert_eq!(heap.peek(), Some(&1));
///
/// // And pop them off in ascending order.
/// assert_eq!(heap.pop(), Some(1));
/// assert_eq!(heap.pop(), Some(3));
/// assert_eq!(heap.pop(), Some(4));
/// assert_eq!(heap.pop(), None);
///
/// // We can also create heaps from arrays.
/// let mut heap = FibonacciHeap::from([2, 6, 2]);
///
/// // And heaps can contain duplicate items.
/// assert_eq!(heap.pop(), Some(2));
/// assert_eq!(heap.pop(), Some(2));
///
/// assert_eq!(heap.len(), 1);
///
/// // We can also join two heaps together.
/// let mut heap: FibonacciHeap<_> = "xbz".chars().collect();
/// let other: FibonacciHeap<_> = "ayc".chars().collect();
/// heap.extend(other);
///
/// assert_eq!(heap.len(), 6);
/// assert_eq!(heap.pop(), Some('a'));
/// assert_eq!(heap.pop(), Some('b'));
/// assert_eq!(heap.pop(), Some('c'));
/// assert_eq!(heap.pop(), Some('x'));
/// assert_eq!(heap.pop(), Some('y'));
/// assert_eq!(heap.pop(), Some('z'));
/// assert_eq!(heap.pop(), None);
/// ```
///
/// # Runtime complexity
///
/// | Operation                 | Runtime Complexity |
/// | ------------------------- | ------------------ |
/// | [`FibonacciHeap::insert`] | *O*(1)             |
/// | [`FibonacciHeap::peek`]   | *O*(1)             |
/// | [`FibonacciHeap::pop`]    | *O*(log *n*)       |
/// | [`FibonacciHeap::extend`] | *O*(1)             |
/// | [`FibonacciHeap::from`]   | *unclear...*       |
pub struct FibonacciHeap<T> {
    nodes: Vec<Node<T>>,
    mindex: usize,
    len: usize,
}

impl<T> FibonacciHeap<T> {
    /// Creates a new heap.
    pub fn new() -> FibonacciHeap<T> {
        FibonacciHeap {
            nodes: Vec::new(),
            mindex: 0,
            len: 0,
        }
    }

    /// Inserts a value into the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FibonacciHeap;
    ///
    /// let mut heap = FibonacciHeap::new();
    /// heap.insert(4);
    /// heap.insert(1);
    /// heap.insert(3);
    ///
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek(), Some(&1));
    /// ```
    pub fn insert(&mut self, value: T)
    where
        T: Ord,
    {
        if let Some(min) = self.peek() {
            if &value < min {
                self.mindex = self.nodes.len();
            }
        }
        self.nodes.push(Node::new(value));
        self.len += 1;
    }

    /// Returns the smallest item in the heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FibonacciHeap;
    ///
    /// let mut heap = FibonacciHeap::from([2, 1]);
    /// assert_eq!(heap.peek(), Some(&1));
    ///
    /// heap.clear();
    /// assert_eq!(heap.peek(), None);
    /// ```
    pub fn peek(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            Some(&self.nodes[self.mindex].value)
        }
    }

    /// Removes and returns the smallest item in the heap, or returns `None`
    /// if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FibonacciHeap;
    ///
    /// let mut heap = FibonacciHeap::from([4, 1, 3]);
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
            let Node {
                value,
                mut children,
            } = self.nodes.swap_remove(self.mindex);
            self.nodes.append(&mut children);
            self.consolidate();
            self.len -= 1;
            Some(value)
        }
    }

    /// Inserts the elements from annother heap into this one.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FibonacciHeap;
    ///
    /// let mut heap = FibonacciHeap::from([3, 4, 5]);
    /// let other = FibonacciHeap::from([1, 2]);
    ///
    /// heap.extend(other);
    ///
    /// assert_eq!(heap.len(), 5);
    ///
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), Some(2));
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(4));
    /// assert_eq!(heap.pop(), Some(5));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn extend(&mut self, other: FibonacciHeap<T>)
    where
        T: Ord,
    {
        let FibonacciHeap {
            mut nodes,
            mindex,
            len,
        } = other;

        if len > 0 {
            if self.is_empty() {
                *self = FibonacciHeap { nodes, mindex, len };
            } else {
                if nodes[mindex].value < self.nodes[self.mindex].value {
                    self.mindex = self.nodes.len() + mindex;
                }
                self.nodes.append(&mut nodes);
                self.len += len;
            }
        }
    }

    /*
        /// Changes the element with the given id.
        pub fn change_key(&mut self, id: HeapId, new_value: T) -> T
        where
            T: Ord,
        {
            todo!()
        }
    */

    /// Returns the number of elements in the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FibonacciHeap;
    ///
    /// let mut heap = FibonacciHeap::from([1, 2, 3]);
    /// assert_eq!(heap.len(), 3);
    ///
    /// heap.clear();
    /// assert_eq!(heap.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FibonacciHeap;
    ///
    /// let mut heap = FibonacciHeap::from([1, 2]);
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
    /// use rust_dsa::FibonacciHeap;
    ///
    /// let mut heap = FibonacciHeap::from([1, 2]);
    ///
    /// heap.clear();
    /// assert!(heap.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.len = 0;
    }

    /// Consolidates the heap so no two nodes have the same rank.
    pub fn consolidate(&mut self)
    where
        T: Ord,
    {
        if self.is_empty() {
            return;
        }

        let mut map = HashMap::new();

        for mut node in self.nodes.drain(..) {
            while let Some(other) = map.remove(&node.rank()) {
                node = node.combine_with(other);
            }
            map.insert(node.rank(), node);
        }

        self.nodes.extend(map.into_values());

        self.mindex = 0;
        for i in 1..self.nodes.len() {
            if self.nodes[i].value < self.nodes[self.mindex].value {
                self.mindex = i;
            }
        }
    }
}

struct Node<T> {
    value: T,
    children: Vec<Node<T>>,
}

impl<T> Node<T> {
    fn new(value: T) -> Node<T> {
        Node {
            value,
            children: Vec::new(),
        }
    }

    fn combine_with(mut self, mut other: Node<T>) -> Node<T>
    where
        T: Ord,
    {
        if other.value < self.value {
            other.children.push(self);
            other
        } else {
            self.children.push(other);
            self
        }
    }

    fn rank(&self) -> usize {
        self.children.len()
    }
}

impl<T> IntoIterator for FibonacciHeap<T>
where
    T: Ord,
{
    type IntoIter = IntoIter<T>;
    type Item = T;
    /// Creates an iterator that iterates over the heap's items in ascending order.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FibonacciHeap;
    ///
    /// let heap = FibonacciHeap::from([4, 2, 3, 1]);
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
    heap: FibonacciHeap<T>,
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

impl<T> FromIterator<T> for FibonacciHeap<T>
where
    T: Ord,
{
    /// Creates a heap from an iterator.
    ///
    /// ```
    /// use rust_dsa::FibonacciHeap;
    ///
    /// let mut heap: FibonacciHeap<i64> = (0..10_001).map(|_| rand::random()).collect();
    ///
    /// let mut prev = heap.pop().unwrap();
    ///
    /// for _ in 0..10_000 {
    ///     assert!(&prev <= heap.peek().unwrap());
    ///     prev = heap.pop().unwrap();
    /// }
    ///
    /// assert_eq!(heap.pop(), None);
    /// ```
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> FibonacciHeap<T> {
        let mut heap = FibonacciHeap::new();
        for value in iter {
            heap.insert(value);
        }
        heap.consolidate();
        heap
    }
}

impl<T, const N: usize> From<[T; N]> for FibonacciHeap<T>
where
    T: Ord,
{
    fn from(arr: [T; N]) -> FibonacciHeap<T>
    where
        T: Ord,
    {
        arr.into_iter().collect()
    }
}

impl<T> Default for FibonacciHeap<T> {
    fn default() -> FibonacciHeap<T> {
        FibonacciHeap::new()
    }
}
