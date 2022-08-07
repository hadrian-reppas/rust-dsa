use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;

/// A [disjoint-set data structure](https://en.wikipedia.org/wiki/Disjoint-set_data_structure)
/// backed by a disjoint set forest.
///
/// # Example
/// ```
/// use rust_dsa::UnionFind;
///
/// // First, we create a new structure.
/// let mut uf = UnionFind::new();
///
/// // Then we can insert values.
/// uf.insert(1);
/// uf.insert(2);
/// uf.insert(3);
/// uf.insert(4);
/// uf.insert(5);
///
/// // And union some of the elements.
/// uf.union(&1, &2);
/// uf.union(&2, &4);
/// uf.union(&3, &5);
///
/// // Now, we can query to see if elements are in the same set.
/// assert_eq!(uf.find(&1), uf.find(&2));
/// assert_eq!(uf.find(&2), uf.find(&4));
/// assert_eq!(uf.find(&4), uf.find(&1));
/// assert_eq!(uf.find(&3), uf.find(&5));
/// assert_eq!(uf.find(&5), uf.find(&3));
///
/// assert_ne!(uf.find(&1), uf.find(&3));
/// assert_ne!(uf.find(&5), uf.find(&4));
///
/// // We can also create `UnionFind`s from arrays.
/// let uf = UnionFind::from(["foo", "bar"]);
///
/// // And iterators.
/// let uf: UnionFind<_> = "string".chars().collect();
/// ```
pub struct UnionFind<T> {
    map: HashMap<T, usize>,
    nodes: Vec<Node>,
}

impl<T> UnionFind<T> {
    /// Creates a new [`UnionFind`] structure.
    pub fn new() -> UnionFind<T> {
        UnionFind {
            map: HashMap::new(),
            nodes: Vec::new(),
        }
    }

    /// Creates a new [`UnionFind`] structure with the specified capacity.
    pub fn with_capacity(capacity: usize) -> UnionFind<T> {
        UnionFind {
            map: HashMap::with_capacity(capacity),
            nodes: Vec::with_capacity(capacity),
        }
    }

    /// Inserts a value into the [`UnionFind`] structure.
    ///
    /// Returns `true` if the [`UnionFind`] structure did not contain `value`
    /// and `false` if it did.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::UnionFind;
    ///
    /// let mut uf = UnionFind::new();
    ///
    /// uf.insert('a');
    /// uf.insert('b');
    ///
    /// assert!(uf.contains(&'a'));
    /// assert!(uf.contains(&'b'));
    /// ```
    pub fn insert(&mut self, value: T) -> bool
    where
        T: Hash + Eq,
    {
        let old_len = self.len();
        match self.map.entry(value) {
            Entry::Occupied(_) => false,
            Entry::Vacant(entry) => {
                entry.insert(old_len);
                self.nodes.push(Node::new(old_len, 0));
                true
            }
        }
    }

    /// Returns a [`usize`] representing the set that contains `value` or `None` if the
    /// [`UnionFind`] structure does not contain `value`.
    ///
    /// This method applies path compression as it searches.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::UnionFind;
    ///
    /// let mut uf = UnionFind::from([1, 2, 3]);
    /// uf.union(&1, &2);
    ///
    /// assert_eq!(uf.find(&1), uf.find(&2));
    /// assert_ne!(uf.find(&1), uf.find(&3));
    /// ```
    pub fn find(&mut self, value: &T) -> Option<usize>
    where
        T: Hash + Eq,
    {
        let start = *self.map.get(value)?;

        let mut index = start;
        while self.nodes[index].parent != index {
            index = self.nodes[index].parent;
        }

        let mut trace = start;
        while trace != index {
            let last = trace;
            trace = self.nodes[trace].parent;
            self.nodes[last].parent = index;
        }

        Some(index)
    }

    /// Returns a [`usize`] representing the set that contains `value` or `None` if the
    /// [`UnionFind`] structure does not contain `value`.
    ///
    /// This method does not apply path compression as it searches.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::UnionFind;
    ///
    /// let mut uf = UnionFind::from([1, 2, 3]);
    /// uf.union(&1, &2);
    ///
    /// assert_eq!(uf.static_find(&1), uf.static_find(&2));
    /// assert_ne!(uf.static_find(&1), uf.static_find(&3));
    /// ```
    pub fn static_find(&self, value: &T) -> Option<usize>
    where
        T: Hash + Eq,
    {
        let mut index = *self.map.get(value)?;

        while self.nodes[index].parent != index {
            index = self.nodes[index].parent;
        }

        Some(index)
    }

    /// Joins the two sets containing `a` and `b`. Returns `None` if `a` or `b`
    /// is not in the [`UnionFind`] structure. Returns `Some(true)` if `a` and `b` were
    /// in different sets before the union operation was preformed and `Some(false)` if
    /// they were already in the same set.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::UnionFind;
    ///
    /// let mut uf = UnionFind::from(['x', 'y', 'z']);
    ///
    /// assert_eq!(uf.union(&'x', &'y'), Some(true));
    ///
    /// // Returns `Some(false)` if we try again.
    /// assert_eq!(uf.union(&'x', &'y'), Some(false));
    ///
    /// assert!(uf.friends(&'x', &'y').unwrap());
    /// assert!(!uf.friends(&'y', &'z').unwrap());
    /// ```
    pub fn union(&mut self, a: &T, b: &T) -> Option<bool>
    where
        T: Hash + Eq,
    {
        let a_id = self.find(a)?;
        let b_id = self.find(b)?;

        if a_id != b_id {
            // we hash `a` and `b` twice which is kinda dumb...
            let a_index = self.map[a];
            let b_index = self.map[b];

            let a_rank = self.nodes[a_index].rank;
            let b_rank = self.nodes[b_index].rank;

            match a_rank.cmp(&b_rank) {
                Ordering::Less => self.nodes[a_index].parent = b_index,
                Ordering::Greater => self.nodes[b_index].parent = a_index,
                Ordering::Equal => {
                    self.nodes[a_index].parent = b_index;
                    self.nodes[b_index].rank += 1;
                }
            }

            Some(true)
        } else {
            Some(false)
        }
    }

    /// Returns `Some(true)` if `a` and `b` are members of the same set and `Some(false)`
    /// if they are not. If `a` or `b` is not in the [`UnionFind`] structure, `None`
    /// is returned.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::UnionFind;
    ///
    /// let mut uf = UnionFind::from([1, 2, 3]);
    ///
    /// uf.union(&1, &2);
    ///
    /// assert_eq!(uf.friends(&1, &2), Some(true));
    /// assert_eq!(uf.friends(&1, &3), Some(false));
    /// assert_eq!(uf.friends(&1, &999), None);
    /// ```
    pub fn friends(&self, a: &T, b: &T) -> Option<bool>
    where
        T: Hash + Eq,
    {
        Some(self.static_find(a)? == self.static_find(b)?)
    }

    /// Returns `true` if the value is in the [`UnionFind`] structure.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::UnionFind;
    ///
    /// let mut uf = UnionFind::new();
    ///
    /// uf.insert('a');
    /// uf.insert('b');
    ///
    /// assert!(uf.contains(&'a'));
    /// assert!(uf.contains(&'b'));
    /// ```
    pub fn contains(&self, value: &T) -> bool
    where
        T: Hash + Eq,
    {
        self.map.contains_key(value)
    }

    /// Returns the number of elements in the [`UnionFind`] structure.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::UnionFind;
    ///
    /// let mut uf: UnionFind<_> = (0..42).collect();
    ///
    /// assert_eq!(uf.len(), 42);
    ///
    /// uf.clear();
    ///
    /// assert_eq!(uf.len(), 0);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the [`UnionFind`] structure is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::UnionFind;
    ///
    /// let mut uf: UnionFind<_> = "chars".chars().collect();
    ///
    /// assert!(!uf.is_empty());
    ///
    /// uf.clear();
    ///
    /// assert!(uf.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the [`UnionFind`] structure.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::UnionFind;
    ///
    /// let mut uf: UnionFind<_> = "chars".chars().collect();
    ///
    /// assert!(!uf.is_empty());
    ///
    /// uf.clear();
    ///
    /// assert!(uf.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.map.clear();
        self.nodes.clear();
    }
}

impl<T> Default for UnionFind<T> {
    fn default() -> UnionFind<T> {
        UnionFind::new()
    }
}

impl<T> FromIterator<T> for UnionFind<T>
where
    T: Hash + Eq,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> UnionFind<T> {
        let iter = iter.into_iter();
        let mut uf = UnionFind::with_capacity(iter.size_hint().0);
        for value in iter {
            uf.insert(value);
        }
        uf
    }
}

impl<T, const N: usize> From<[T; N]> for UnionFind<T>
where
    T: Hash + Eq,
{
    fn from(arr: [T; N]) -> UnionFind<T> {
        arr.into_iter().collect()
    }
}

struct Node {
    parent: usize,
    rank: usize,
}

impl Node {
    fn new(parent: usize, rank: usize) -> Node {
        Node { parent, rank }
    }
}
