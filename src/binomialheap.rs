/// A [priority queue](http://en.wikipedia.org/wiki/Priority_queue) implementation
/// backed by a [binomial heap](https://en.wikipedia.org/wiki/Binomial_heap).
///
/// [`BinomialHeap::pop`] removes the *smallest* item.
///
/// **TODO: implement** `change_value`**.**
///
/// # Example
///
/// ```
/// use rust_dsa::BinomialHeap;
///
/// // First, we create a new heap.
/// let mut heap = BinomialHeap::new();
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
/// let mut heap = BinomialHeap::from([2, 6, 2]);
///
/// // And heaps can contain duplicate items.
/// assert_eq!(heap.pop(), Some(2));
/// assert_eq!(heap.pop(), Some(2));
///
/// assert_eq!(heap.len(), 1);
///
/// // We can also join two heaps together.
/// let mut heap: BinomialHeap<_> = "xbz".chars().collect();
/// let other: BinomialHeap<_> = "ayc".chars().collect();
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
/// | Operation                | Runtime Complexity |
/// | ------------------------ | ------------------ |
/// | [`BinomialHeap::insert`] | *O*(log *n*)       |
/// | [`BinomialHeap::peek`]   | *O*(log *n*)       |
/// | [`BinomialHeap::pop`]    | *O*(log *n*)       |
/// | [`BinomialHeap::extend`] | *O*(log *n*)       |
/// | [`BinomialHeap::from`]   | *unclear...*       |
pub struct BinomialHeap<T> {
    nodes: Vec<Node<T>>,
}

impl<T> BinomialHeap<T> {
    /// Creates a new heap.
    pub fn new() -> BinomialHeap<T> {
        BinomialHeap { nodes: Vec::new() }
    }

    /// Creates a heap with a single element.
    pub fn singleton(value: T) -> BinomialHeap<T> {
        BinomialHeap {
            nodes: vec![Node::new(value)],
        }
    }

    /// Inserts a value into the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinomialHeap;
    ///
    /// let mut heap = BinomialHeap::new();
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
        let other = BinomialHeap::singleton(value);
        self.extend(other);
    }

    /// Returns the smallest item in the heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinomialHeap;
    ///
    /// let mut heap = BinomialHeap::from([2, 1]);
    /// assert_eq!(heap.peek(), Some(&1));
    ///
    /// heap.clear();
    /// assert_eq!(heap.peek(), None);
    /// ```
    pub fn peek(&self) -> Option<&T>
    where
        T: Ord,
    {
        if self.is_empty() {
            None
        } else {
            let mindex = self.get_mindex();
            Some(&self.nodes[mindex].value)
        }
    }

    /// Removes and returns the smallest item in the heap, or returns `None`
    /// if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinomialHeap;
    ///
    /// let mut heap = BinomialHeap::from([4, 1, 3]);
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
            let mindex = self.get_mindex();
            let Node { value, children } = self.nodes.remove(mindex);
            let other = BinomialHeap { nodes: children };
            self.extend(other);
            Some(value)
        }
    }

    /// Inserts the elements from annother heap into this one.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinomialHeap;
    ///
    /// let mut heap = BinomialHeap::from([3, 4, 5]);
    /// let other = BinomialHeap::from([1, 2]);
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
    pub fn extend(&mut self, mut other: BinomialHeap<T>)
    where
        T: Ord,
    {
        let mut self_nodes: Vec<_> = (0..usize::BITS).map(|_| None).collect();
        let mut other_nodes: Vec<_> = (0..usize::BITS).map(|_| None).collect();

        for node in self.nodes.drain(..) {
            let degree = node.degree();
            self_nodes[degree] = Some(node);
        }

        for node in other.nodes.drain(..) {
            let degree = node.degree();
            other_nodes[degree] = Some(node);
        }

        let mut nodes = Vec::new();
        let mut carry = None;

        for i in 0..(usize::BITS as usize) {
            match (self_nodes[i].take(), other_nodes[i].take(), carry.take()) {
                (None, None, None) => {}
                (None, None, Some(c)) => nodes.push(c),
                (None, Some(o), None) => nodes.push(o),
                (None, Some(o), Some(c)) => carry = Some(o.join_with(c)),
                (Some(s), None, None) => nodes.push(s),
                (Some(s), None, Some(c)) => carry = Some(s.join_with(c)),
                (Some(s), Some(o), None) => carry = Some(s.join_with(o)),
                (Some(s), Some(o), Some(c)) => {
                    carry = Some(s.join_with(o));
                    nodes.push(c);
                }
            }
        }

        nodes.reverse();
        self.nodes = nodes;
    }

    /// Returns the number of elements in the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinomialHeap;
    ///
    /// let mut heap = BinomialHeap::from([1, 2, 3, 4, 5, 6, 7, 8, 9]);
    /// assert_eq!(heap.len(), 9);
    ///
    /// heap.pop();
    /// assert_eq!(heap.len(), 8);
    ///
    /// heap.clear();
    /// assert_eq!(heap.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        let mut len = 0;
        for child in &self.nodes {
            len += 1 << child.degree();
        }
        len
    }

    /// Returns `true` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinomialHeap;
    ///
    /// let mut heap = BinomialHeap::from([1, 2]);
    /// assert!(!heap.is_empty());
    ///
    /// heap.clear();
    /// assert!(heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Clears the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinomialHeap;
    ///
    /// let mut heap = BinomialHeap::from([1, 2]);
    ///
    /// heap.clear();
    /// assert!(heap.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.nodes.clear()
    }

    fn get_mindex(&self) -> usize
    where
        T: Ord,
    {
        let mut mindex = 0;
        for i in 1..self.nodes.len() {
            if self.nodes[i].value < self.nodes[mindex].value {
                mindex = i;
            }
        }
        mindex
    }

    #[allow(dead_code)]
    fn meets_invariant(&self) -> bool
    where
        T: Ord,
    {
        if let Some(false) = self.nodes.get(0).map(Node::meets_invariant) {
            return false;
        }
        for i in 1..self.nodes.len() {
            if self.nodes[i - 1].degree() <= self.nodes[i].degree() {
                return false;
            }
            if !self.nodes[i].meets_invariant() {
                return false;
            }
        }
        true
    }
}

impl<T> IntoIterator for BinomialHeap<T>
where
    T: Ord,
{
    type IntoIter = IntoIter<T>;
    type Item = T;
    /// Creates an iterator that iterates over the heap's items in ascending order.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinomialHeap;
    ///
    /// let heap = BinomialHeap::from([4, 2, 3, 1]);
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
    heap: BinomialHeap<T>,
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

impl<T> FromIterator<T> for BinomialHeap<T>
where
    T: Ord,
{
    /// Creates a heap from an iterator.
    ///
    /// ```
    /// use rust_dsa::BinomialHeap;
    ///
    /// let mut heap: BinomialHeap<i64> = (0..10_001).map(|_| rand::random()).collect();
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
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> BinomialHeap<T> {
        let mut heap = BinomialHeap::new();
        for value in iter {
            heap.insert(value);
        }
        heap
    }
}

impl<T, const N: usize> From<[T; N]> for BinomialHeap<T>
where
    T: Ord,
{
    fn from(arr: [T; N]) -> BinomialHeap<T>
    where
        T: Ord,
    {
        arr.into_iter().collect()
    }
}

impl<T> Default for BinomialHeap<T> {
    fn default() -> BinomialHeap<T> {
        BinomialHeap::new()
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

    fn degree(&self) -> usize {
        self.children.len()
    }

    fn join_with(mut self, mut other: Node<T>) -> Node<T>
    where
        T: Ord,
    {
        debug_assert!(self.degree() == other.degree());
        if other.value < self.value {
            other.children.insert(0, self);
            other
        } else {
            self.children.insert(0, other);
            self
        }
    }

    #[allow(dead_code)]
    fn meets_invariant(&self) -> bool
    where
        T: Ord,
    {
        for (i, child) in self.children.iter().rev().enumerate() {
            if child.degree() != i {
                return false;
            }
            if child.value < self.value {
                return false;
            }
            if !child.meets_invariant() {
                return false;
            }
        }
        true
    }
}
