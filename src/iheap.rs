/// An [interval heap](https://en.wikipedia.org/wiki/Double-ended_priority_queue#Interval_heaps)
/// implementation for use as a double-ended priority queue.
///
/// # Example
/// ```
/// todo!()
/// ```
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
    /// todo!()
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
    /// todo!()
    /// ```
    pub fn pop_min(&mut self) -> Option<T>
    where
        T: Ord,
    {
        // TODO: combine this into one match
        if self.nodes.len() <= 1 {
            match self.nodes.pop() {
                None => None,
                Some(Node::Normal { low, high }) => {
                    self.nodes.push(Node::new_odd(high));
                    Some(low)
                }
                Some(Node::Odd { value }) => Some(value),
            }
        } else {
            let value = match self.nodes.pop().unwrap() {
                Node::Normal { low, high } => {
                    let value = self.nodes[0].replace_low(low);
                    self.nodes.push(Node::new_odd(high));
                    value
                }
                Node::Odd { value } => self.nodes[0].replace_low(value),
            };
            self.bubble_down_low();
            Some(value)
        }
    }

    /// Removes and returns the largest value in the heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// todo!()
    /// ```
    pub fn pop_max(&mut self) -> Option<T>
    where
        T: Ord,
    {
        // TODO: combine this into one match
        if self.nodes.len() <= 1 {
            match self.nodes.pop() {
                None => None,
                Some(Node::Normal { low, high }) => {
                    self.nodes.push(Node::new_odd(low));
                    Some(high)
                }
                Some(Node::Odd { value }) => Some(value),
            }
        } else {
            let value = match self.nodes.pop().unwrap() {
                Node::Normal { low, high } => {
                    let value = self.nodes[0].replace_high(high);
                    self.nodes.push(Node::new_odd(low));
                    value
                }
                Node::Odd { value } => self.nodes[0].replace_high(value),
            };
            self.bubble_down_high();
            Some(value)
        }
    }

    /// Returns a reference to the smallest value in the heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// todo!()
    /// ```
    pub fn peek_min(&mut self) -> Option<&T> {
        match self.nodes.get(0) {
            Some(Node::Normal { low, .. }) => Some(low),
            Some(Node::Odd { value }) => Some(value),
            None => None,
        }
    }

    /// Returns a reference to the largest value in the heap, or `None` if the heap is empty.
    ///
    /// # Example
    /// ```
    /// todo!()
    /// ```
    pub fn peek_max(&mut self) -> Option<&T> {
        match self.nodes.get(0) {
            Some(Node::Normal { high, .. }) => Some(high),
            Some(Node::Odd { value }) => Some(value),
            None => None,
        }
    }

    /// Returns the number of elements in the heap.
    ///
    /// # Example
    /// ```
    /// todo!()
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
    /// todo!()
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the heap.
    ///
    /// # Example
    /// ```
    /// todo!()
    /// ```
    pub fn clear(&mut self) {
        self.nodes.clear();
    }

    fn bubble_up_high(&mut self, mut index: usize)
    where
        T: Ord,
    {
        while index > 0 {
            let parent_index = (index - 1) / 2;
            let (parent, cur) = mut_refs(parent_index, index, &mut self.nodes);
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
        while index > 0 {
            let parent_index = (index - 1) / 2;
            let (parent, cur) = mut_refs(parent_index, index, &mut self.nodes);
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
        if self.nodes.len() <= 1 {
            return;
        }
        let parent_index = (self.nodes.len() - 2) / 2;
        let (parent, odd) = mut_refs(parent_index, self.nodes.len() - 1, &mut self.nodes);
        if odd.value() > parent.high() {
            std::mem::swap(odd.value_mut(), parent.high_mut());
            self.bubble_up_high(parent_index);
        } else if odd.value() < parent.low() {
            std::mem::swap(odd.value_mut(), parent.low_mut());
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
                let (parent, child) = mut_refs(index, max_child, &mut self.nodes);
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
                let (parent, child) = mut_refs(index, min_child, &mut self.nodes);
                std::mem::swap(parent.low_mut(), child.low_or_value_mut());
                child.order_bounds();
                index = min_child;
            } else {
                break;
            }
        }
    }
}

fn mut_refs<T>(parent_index: usize, child_index: usize, slice: &mut [T]) -> (&mut T, &mut T) {
    assert!(parent_index < child_index);
    let (first_slice, second_slice) = slice.split_at_mut(child_index);
    (&mut first_slice[parent_index], &mut second_slice[0])
}

#[derive(Debug, Clone)]
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

impl<T> Default for IntervalHeap<T> {
    fn default() -> Self {
        IntervalHeap::new()
    }
}

impl<T, const N: usize> From<[T; N]> for IntervalHeap<T>
where
    T: Ord,
{
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

fn is_heap<T: Ord>(heap: &[Node<T>]) -> bool {
    is_heap_rec(heap, 0)
}

fn is_heap_rec<T: Ord>(heap: &[Node<T>], index: usize) -> bool {
    let (plow, phigh) = match heap.get(index) {
        Some(Node::Normal { low, high }) => (low, high),
        _ => return true,
    };

    let child1 = 2 * index + 1;
    let child2 = child1 + 1;
    (match heap.get(child1) {
        Some(Node::Normal { low, high }) => {
            plow <= low && low <= high && high <= phigh && is_heap_rec(heap, child1)
        }
        Some(Node::Odd { value }) => plow <= value && value <= phigh,
        None => true,
    }) && (match heap.get(child2) {
        Some(Node::Normal { low, high }) => {
            plow <= low && low <= high && high <= phigh && is_heap_rec(heap, child1)
        }
        Some(Node::Odd { value }) => plow <= value && value <= phigh,
        None => true,
    })
}

#[cfg(test)]
mod tests {
    use super::IntervalHeap;
    use rand::Rng;
    #[test]
    fn test() {
        /*
        let mut heap = IntervalHeap::new();
        heap.insert(1);
        heap.insert(2);
        heap.insert(5);
        heap.insert(3);
        heap.insert(8);
        heap.insert(-3);
        heap.insert(2);
        heap.insert(4);
        heap.insert(14);

        println!("{:?}", heap.nodes);

        println!("POP MIN: {:?}", heap.pop_min());

        println!("{:?}", heap.nodes);

        assert!(false);
        */

        let n = 10_000_000;

        let mut rng = rand::thread_rng();
        let vec: Vec<_> = (0..n).map(|_| rng.gen::<u64>()).collect();
        let mut sorted = vec.clone();
        sorted.sort();
        //let blow = sorted.clone();
        //let mut i = 0;
        //let mut j = blow.len();
        let mut heap: IntervalHeap<_> = vec.into_iter().collect();

        // println!("sorted: {:?}", sorted);

        let mut iter = sorted.into_iter();

        for _ in 0..n {
            //mlet last = heap.nodes.clone();
            //if !super::is_heap(&heap.nodes) {
            //    println!("\x1b[31mNOT A HEAP!!\x1b[0m");
            //}
            //println!("heap.nodes: {:?}", heap.nodes);
            //println!("blow: {:?}", &blow[i..j]);

            if rng.gen::<bool>() {
                let a = heap.pop_min();
                let b = iter.next();
                //i += 1;
                //println!("{:?} {:?}", a, b);
                if a != b {
                    // println!("heap.nodes: {:?}", last);
                }
                assert_eq!(a, b);
            } else {
                let a = heap.pop_max();
                let b = iter.next_back();
                //j -= 1;
                //println!("{:?} {:?}", a, b);
                if a != b {
                    // println!("heap.nodes: {:?}", last);
                }
                assert_eq!(a, b);
            }
        }
    }
}
