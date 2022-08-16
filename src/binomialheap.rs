pub struct BinomialHeap<T> {
    _data: std::marker::PhantomData<T>,
}

impl<T> BinomialHeap<T> {
    /// Creates a new heap.
    pub fn new() -> BinomialHeap<T> {
        todo!()
    }

    /// Inserts an item into the heap.
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
    pub fn insert(&mut self, item: T)
    where
        T: Ord,
    {
        todo!()
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
    pub fn peek(&self) -> Option<&T> {
        todo!()
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
        todo!()
    }

    /// Returns the number of elements in the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BinomialHeap;
    ///
    /// let mut heap = BinomialHeap::from([1, 2, 3]);
    /// assert_eq!(heap.len(), 3);
    ///
    /// heap.clear();
    /// assert_eq!(heap.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        todo!()
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
        self.len() == 0
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
        todo!()
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
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> BinomialHeap<T> {
        todo!()
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
        todo!()
    }
}

impl<T> Default for BinomialHeap<T> {
    fn default() -> BinomialHeap<T> {
        BinomialHeap::new()
    }
}
