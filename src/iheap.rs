/// An [interval heap](https://en.wikipedia.org/wiki/Double-ended_priority_queue#Interval_heaps)
/// implementation for use as a double-ended priority queue.
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
#[derive(Clone)]
pub struct IntervalHeap<T> {
    nodes: Vec<Node<T>>,
}

impl<T> IntervalHeap<T> {
    /// Creates an empty heap.
    pub fn new() -> Self {
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
    pub fn peek_min(&mut self) -> Option<&T> {
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
    pub fn peek_max(&mut self) -> Option<&T> {
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
                std::mem::swap(cur.high_mut(), parent.high_mut());
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
                std::mem::swap(cur.low_mut(), parent.low_mut());
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
            std::mem::swap(cur.value_mut(), parent.high_mut());
            self.bubble_up_high(parent_index);
        } else if cur.value() < parent.low() {
            std::mem::swap(cur.value_mut(), parent.low_mut());
            self.bubble_up_low(parent_index);
        }
    }

    fn bubble_down_high(&mut self)
    where
        T: Ord,
    {
        // TODO: Clean up
        let mut index = 0;
        loop {
            // find the index of the biggest child
            let child1 = 2 * index + 1;
            let child2 = child1 + 1;
            let max_child = if child2 >= self.nodes.len()
                || self.nodes[child1].high() > self.nodes[child2].high_or_value()
            {
                child1
            } else {
                child2
            };

            // if the `high` value at `index` is smaller than its biggest child, swap the two
            if max_child < self.nodes.len()
                && self.nodes[index].high() < self.nodes[max_child].high_or_value()
            {
                let (parent, child) = self.nodes.get_both_mut(index, max_child);
                std::mem::swap(parent.high_mut(), child.high_or_value_mut());
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
        // TODO: Clean up
        let mut index = 0;
        loop {
            // find the index of the smallest child
            let child1 = 2 * index + 1;
            let child2 = child1 + 1;
            let min_child = if child2 >= self.nodes.len()
                || self.nodes[child1].low() < self.nodes[child2].low_or_value()
            {
                child1
            } else {
                child2
            };

            // if the `low` value at `index` is bigger than its smallest child, swap the two
            if min_child < self.nodes.len()
                && self.nodes[index].low() > self.nodes[min_child].low_or_value()
            {
                let (parent, child) = self.nodes.get_both_mut(index, min_child);
                std::mem::swap(parent.low_mut(), child.low_or_value_mut());
                child.order_bounds();
                index = min_child;
            } else {
                break;
            }
        }
    }
}

impl<T> Default for IntervalHeap<T> {
    fn default() -> Self {
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
    /// let random = [
    ///     49, 166, 19, 170, 83, 176, 51, 192, 81, 73, 147, 121, 232, 178, 202, 122, 202, 237, 158,
    ///     243, 170, 129, 8, 204, 217, 105, 132, 35, 246, 160, 250, 41, 149, 110, 76, 46, 183, 8, 13,
    ///     4, 226, 173, 81, 101, 227, 132, 6, 5, 209, 131, 191, 137, 234, 126, 119, 24, 37, 156, 32,
    ///     177, 46, 180, 144, 58, 80, 82, 103, 5, 71, 55, 90, 102, 127, 80, 87, 172, 28, 59, 161, 201,
    ///     103, 241, 148, 163, 3, 119, 112, 15, 36, 209, 45, 124, 6, 110, 185, 148, 51, 236, 43, 157,
    /// ];
    ///
    /// let bools: Vec<_> = random.iter().map(|i| i % 2 == 0).collect();
    ///
    /// let mut sorted = random.clone();
    /// sorted.sort();
    /// let mut iter = sorted.into_iter();
    ///
    /// let mut heap = IntervalHeap::from(random);
    ///
    /// for take_from_front in bools {
    ///     if take_from_front {
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
    fn from_iter<A: IntoIterator<Item = T>>(iter: A) -> Self {
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
    fn new_normal(low: T, high: T) -> Self {
        Node::Normal { low, high }
    }

    fn new_odd(value: T) -> Self {
        Node::Odd { value }
    }

    fn order_bounds(&mut self)
    where
        T: Ord,
    {
        if let Node::Normal { low, high } = self {
            if high < low {
                std::mem::swap(high, low);
            }
        }
    }

    fn replace_high(&mut self, new_high: T) -> T {
        match self {
            Node::Normal { high, .. } => std::mem::replace(high, new_high),
            _ => panic!(),
        }
    }

    fn replace_low(&mut self, new_low: T) -> T {
        match self {
            Node::Normal { low, .. } => std::mem::replace(low, new_low),
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
