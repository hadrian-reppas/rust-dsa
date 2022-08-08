use std::mem;

/// An [interval heap](https://en.wikipedia.org/wiki/Double-ended_priority_queue#Interval_heaps)
/// implementation for use as a [double-ended priority queue](http://en.wikipedia.org/wiki/Double-ended_priority_queue).
///
/// # Example
/// ```
/// use rust_dsa::IntervalHeap;
///
/// // First, we create a new heap.
/// let mut heap = IntervalHeap::new();
///
/// // Then we can add values in any order.
/// heap.insert(4);
/// heap.insert(1);
/// heap.insert(3);
/// heap.insert(6);
///
/// // We can peek at the min and max values.
/// assert_eq!(heap.peek_min(), Some(&1));
/// assert_eq!(heap.peek_max(), Some(&6));
///
/// // And pop them off from both ends.
/// assert_eq!(heap.pop_min(), Some(1));
/// assert_eq!(heap.pop_min(), Some(3));
/// assert_eq!(heap.pop_max(), Some(6));
/// assert_eq!(heap.pop_min(), Some(4));
/// assert_eq!(heap.pop_min(), None);
///
/// // We can also create heaps from arrays.
/// let mut heap = IntervalHeap::from([2, 6, 2]);
///
/// // And heaps can contain duplicate items.
/// assert_eq!(heap.pop_min(), Some(2));
/// assert_eq!(heap.pop_min(), Some(2));
///
/// assert_eq!(heap.len(), 1);
/// ```
///
/// # Runtime complexity
///
/// | Operation                  | Runtime Complexity |
/// | ---------------------------| ------------------ |
/// | [`IntervalHeap::insert`]   | *O*(log *n*)       |
/// | [`IntervalHeap::pop_min`]  | *O*(log *n*)       |
/// | [`IntervalHeap::pop_max`]  | *O*(log *n*)       |
/// | [`IntervalHeap::peek_min`] | *O*(1)             |
/// | [`IntervalHeap::peek_max`] | *O*(1)             |
/// | [`IntervalHeap::from`]     | *O*(*n* log *n*)   |
#[derive(Clone)]
pub struct IntervalHeap<T> {
    nodes: Vec<Node<T>>,
}

impl<T> IntervalHeap<T> {
    /// Creates an empty heap.
    pub fn new() -> IntervalHeap<T> {
        IntervalHeap { nodes: Vec::new() }
    }

    /// Inserts a value into the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::IntervalHeap;
    ///
    /// let mut heap = IntervalHeap::new();
    ///
    /// heap.insert('h');
    /// heap.insert('n');
    ///
    /// assert_eq!(heap.peek_min(), Some(&'h'));
    /// assert_eq!(heap.peek_max(), Some(&'n'));
    /// ```
    pub fn insert(&mut self, value: T)
    where
        T: Ord,
    {
        match self.nodes.last() {
            None => self.nodes.push(Node::new_odd(value)),
            Some(Node::Normal { .. }) => {
                self.nodes.push(Node::Odd { value });
                self.bubble_up_odd();
            }
            Some(Node::Odd { .. }) => {
                if let Some(Node::Odd { value: old_value }) = self.nodes.pop() {
                    if old_value < value {
                        self.nodes.push(Node::new_normal(old_value, value));
                        self.bubble_up_high(self.nodes.len() - 1);
                    } else {
                        self.nodes.push(Node::new_normal(value, old_value));
                        self.bubble_up_low(self.nodes.len() - 1);
                    }
                } else {
                    unreachable!();
                }
            }
        }
    }

    /// Removes and returns the smallest value in the heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::IntervalHeap;
    ///
    /// let mut heap = IntervalHeap::from([4, 3, 6]);
    ///
    /// assert_eq!(heap.pop_min(), Some(3));
    /// assert_eq!(heap.pop_min(), Some(4));
    /// assert_eq!(heap.pop_min(), Some(6));
    /// assert_eq!(heap.pop_min(), None);
    /// ```
    pub fn pop_min(&mut self) -> Option<T>
    where
        T: Ord,
    {
        match self.nodes.pop() {
            None => None,
            Some(Node::Normal { low, high }) => {
                if let Some(root) = self.nodes.get_mut(0) {
                    let min = root.replace_low(low);
                    self.nodes.push(Node::new_odd(high));
                    self.bubble_down_low();
                    Some(min)
                } else {
                    self.nodes.push(Node::new_odd(high));
                    Some(low)
                }
            }
            Some(Node::Odd { value }) => {
                if let Some(root) = self.nodes.get_mut(0) {
                    let min = root.replace_low(value);
                    self.bubble_down_low();
                    Some(min)
                } else {
                    Some(value)
                }
            }
        }
    }

    /// Removes and returns the largest value in the heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::IntervalHeap;
    ///
    /// let mut heap = IntervalHeap::from([4, 3, 6]);
    ///
    /// assert_eq!(heap.pop_max(), Some(6));
    /// assert_eq!(heap.pop_max(), Some(4));
    /// assert_eq!(heap.pop_max(), Some(3));
    /// assert_eq!(heap.pop_max(), None);
    /// ```
    pub fn pop_max(&mut self) -> Option<T>
    where
        T: Ord,
    {
        match self.nodes.pop() {
            None => None,
            Some(Node::Normal { low, high }) => {
                if let Some(root) = self.nodes.get_mut(0) {
                    let max = root.replace_high(high);
                    self.nodes.push(Node::new_odd(low));
                    self.bubble_down_high();
                    Some(max)
                } else {
                    self.nodes.push(Node::new_odd(low));
                    Some(high)
                }
            }
            Some(Node::Odd { value }) => {
                if let Some(root) = self.nodes.get_mut(0) {
                    let max = root.replace_high(value);
                    self.bubble_down_high();
                    Some(max)
                } else {
                    Some(value)
                }
            }
        }
    }

    /// Returns a reference to the smallest value in the heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::IntervalHeap;
    ///
    /// let mut heap = IntervalHeap::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(heap.peek_min(), Some(&'a'));
    ///
    /// heap.clear();
    ///
    /// assert_eq!(heap.peek_min(), None);
    /// ```
    pub fn peek_min(&self) -> Option<&T> {
        match self.nodes.get(0) {
            None => None,
            Some(Node::Normal { low, .. }) => Some(low),
            Some(Node::Odd { value }) => Some(value),
        }
    }

    /// Returns a reference to the largest value in the heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::IntervalHeap;
    ///
    /// let mut heap = IntervalHeap::from(['a', 'b', 'c']);
    ///
    /// assert_eq!(heap.peek_max(), Some(&'c'));
    ///
    /// heap.clear();
    ///
    /// assert_eq!(heap.peek_min(), None);
    /// ```
    pub fn peek_max(&self) -> Option<&T> {
        match self.nodes.get(0) {
            None => None,
            Some(Node::Normal { high, .. }) => Some(high),
            Some(Node::Odd { value }) => Some(value),
        }
    }

    /// Returns the number of elements in the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::IntervalHeap;
    ///
    /// let mut heap: IntervalHeap<_> = (0..42).collect();
    ///
    /// assert_eq!(heap.len(), 42);
    ///
    /// heap.pop_max();
    ///
    /// assert_eq!(heap.len(), 41);
    ///
    /// heap.clear();
    ///
    /// assert_eq!(heap.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        match self.nodes.last() {
            None => 0,
            Some(Node::Normal { .. }) => 2 * self.nodes.len(),
            Some(Node::Odd { .. }) => 2 * self.nodes.len() - 1,
        }
    }

    /// Returns `true` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::IntervalHeap;
    ///
    /// let mut heap: IntervalHeap<_> = ('a'..='z').collect();
    ///
    /// assert!(!heap.is_empty());
    ///
    /// heap.clear();
    ///
    /// assert!(heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the heap.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::IntervalHeap;
    ///
    /// let mut heap: IntervalHeap<_> = ('a'..='z').collect();
    ///
    /// assert!(!heap.is_empty());
    ///
    /// heap.clear();
    ///
    /// assert!(heap.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.nodes.clear();
    }

    fn bubble_up_high(&mut self, mut index: usize)
    where
        T: Ord,
    {
        debug_assert!(matches!(self.nodes.get(index), Some(Node::Normal { .. })));

        while index > 0 {
            let parent_index = (index - 1) / 2;
            let (parent, cur) = self.nodes.get_both_mut(parent_index, index);
            if cur.high() > parent.high() {
                mem::swap(cur.high_mut(), parent.high_mut());
                index = parent_index;
            } else {
                break;
            }
        }
    }

    fn bubble_up_low(&mut self, mut index: usize)
    where
        T: Ord,
    {
        debug_assert!(matches!(self.nodes.get(index), Some(Node::Normal { .. })));

        while index > 0 {
            let parent_index = (index - 1) / 2;
            let (parent, cur) = self.nodes.get_both_mut(parent_index, index);
            if cur.low() < parent.low() {
                mem::swap(cur.low_mut(), parent.low_mut());
                index = parent_index;
            } else {
                break;
            }
        }
    }

    fn bubble_up_odd(&mut self)
    where
        T: Ord,
    {
        debug_assert!(self.nodes.len() > 1);
        debug_assert!(matches!(self.nodes.last(), Some(Node::Odd { .. })));

        let parent_index = (self.nodes.len() - 2) / 2;
        let (parent, cur) = self.nodes.get_both_mut(parent_index, self.nodes.len() - 1);
        if cur.value() > parent.high() {
            mem::swap(cur.value_mut(), parent.high_mut());
            self.bubble_up_high(parent_index);
        } else if cur.value() < parent.low() {
            mem::swap(cur.value_mut(), parent.low_mut());
            self.bubble_up_low(parent_index);
        }
    }

    fn bubble_down_high(&mut self)
    where
        T: Ord,
    {
        debug_assert!(matches!(self.nodes.get(0), Some(Node::Normal { .. })));

        let mut index = 0;
        loop {
            let child1 = 2 * index + 1;
            let child2 = child1 + 1;
            let max_child = if child2 >= self.nodes.len()
                || self.nodes[child1].high() > self.nodes[child2].high_or_value()
            {
                child1
            } else {
                child2
            };

            if max_child < self.nodes.len()
                && self.nodes[index].high() < self.nodes[max_child].high_or_value()
            {
                let (parent, child) = self.nodes.get_both_mut(index, max_child);
                mem::swap(parent.high_mut(), child.high_or_value_mut());
                child.order_bounds();
                index = max_child;
            } else {
                break;
            }
        }
    }

    fn bubble_down_low(&mut self)
    where
        T: Ord,
    {
        debug_assert!(matches!(self.nodes.get(0), Some(Node::Normal { .. })));

        let mut index = 0;
        loop {
            let child1 = 2 * index + 1;
            let child2 = child1 + 1;
            let min_child = if child2 >= self.nodes.len()
                || self.nodes[child1].low() < self.nodes[child2].low_or_value()
            {
                child1
            } else {
                child2
            };

            if min_child < self.nodes.len()
                && self.nodes[index].low() > self.nodes[min_child].low_or_value()
            {
                let (parent, child) = self.nodes.get_both_mut(index, min_child);
                mem::swap(parent.low_mut(), child.low_or_value_mut());
                child.order_bounds();
                index = min_child;
            } else {
                break;
            }
        }
    }
}

impl<T> Default for IntervalHeap<T> {
    fn default() -> IntervalHeap<T> {
        IntervalHeap::new()
    }
}

impl<T, const N: usize> From<[T; N]> for IntervalHeap<T>
where
    T: Ord,
{
    /// ```
    /// use rust_dsa::IntervalHeap;
    ///
    /// let random: Vec<i32> = (0..10_000).map(|_| rand::random()).collect();
    ///
    /// let mut sorted = random.clone();
    /// sorted.sort();
    /// let mut iter = sorted.into_iter();
    ///
    /// let mut heap: IntervalHeap<_> = random.into_iter().collect();
    ///
    /// for _ in 0..10_001 {
    ///     if rand::random() {
    ///         assert_eq!(heap.pop_min(), iter.next());
    ///     } else {
    ///         assert_eq!(heap.pop_max(), iter.next_back());
    ///     }
    /// }
    /// ```
    fn from(array: [T; N]) -> IntervalHeap<T> {
        array.into_iter().collect()
    }
}

impl<T> FromIterator<T> for IntervalHeap<T>
where
    T: Ord,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> IntervalHeap<T> {
        let mut heap = IntervalHeap::new();
        for value in iter {
            heap.insert(value);
        }
        heap
    }
}

#[derive(Clone)]
enum Node<T> {
    Normal { low: T, high: T },
    Odd { value: T },
}

impl<T> Node<T> {
    fn new_normal(low: T, high: T) -> Node<T> {
        Node::Normal { low, high }
    }

    fn new_odd(value: T) -> Node<T> {
        Node::Odd { value }
    }

    fn order_bounds(&mut self)
    where
        T: Ord,
    {
        if let Node::Normal { low, high } = self {
            if high < low {
                mem::swap(high, low);
            }
        }
    }

    fn replace_high(&mut self, new_high: T) -> T {
        match self {
            Node::Normal { high, .. } => mem::replace(high, new_high),
            _ => panic!(),
        }
    }

    fn replace_low(&mut self, new_low: T) -> T {
        match self {
            Node::Normal { low, .. } => mem::replace(low, new_low),
            _ => panic!(),
        }
    }

    fn high(&self) -> &T {
        match self {
            Node::Normal { high, .. } => high,
            _ => panic!(),
        }
    }

    fn low(&self) -> &T {
        match self {
            Node::Normal { low, .. } => low,
            _ => panic!(),
        }
    }

    fn value(&self) -> &T {
        match self {
            Node::Odd { value } => value,
            _ => panic!(),
        }
    }

    fn high_mut(&mut self) -> &mut T {
        match self {
            Node::Normal { high, .. } => high,
            _ => panic!(),
        }
    }

    fn low_mut(&mut self) -> &mut T {
        match self {
            Node::Normal { low, .. } => low,
            _ => panic!(),
        }
    }

    fn value_mut(&mut self) -> &mut T {
        match self {
            Node::Odd { value } => value,
            _ => panic!(),
        }
    }

    fn high_or_value(&self) -> &T {
        match self {
            Node::Normal { high, .. } => high,
            Node::Odd { value } => value,
        }
    }

    fn low_or_value(&self) -> &T {
        match self {
            Node::Normal { low, .. } => low,
            Node::Odd { value } => value,
        }
    }

    fn high_or_value_mut(&mut self) -> &mut T {
        match self {
            Node::Normal { high, .. } => high,
            Node::Odd { value } => value,
        }
    }

    fn low_or_value_mut(&mut self) -> &mut T {
        match self {
            Node::Normal { low, .. } => low,
            Node::Odd { value } => value,
        }
    }
}

trait GetBothMut {
    type Item;
    fn get_both_mut(
        &mut self,
        parent_index: usize,
        child_index: usize,
    ) -> (&mut Self::Item, &mut Self::Item);
}

impl<T> GetBothMut for Vec<T> {
    type Item = T;
    fn get_both_mut(&mut self, parent_index: usize, child_index: usize) -> (&mut T, &mut T) {
        assert!(parent_index < child_index);
        let (first_slice, second_slice) = self.split_at_mut(child_index);
        (&mut first_slice[parent_index], &mut second_slice[0])
    }
}
