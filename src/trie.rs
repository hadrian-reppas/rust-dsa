use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// A [trie](https://en.wikipedia.org/wiki/Trie) for mapping sequences of keys to values.
///
/// # Example
/// ```
/// use rust_dsa::GenericTrie;
///
/// // First, we create a new trie.
/// let mut trie = GenericTrie::new();
///
/// // Then we can insert keys and items.
/// trie.insert([1, 2, 3], "foo");
/// trie.insert([1, 2, 4], "bar");
/// trie.insert([1, 2, 4, 0], "baz");
///
/// assert!(trie.contains_key(&[1, 2, 3]));
/// assert!(trie.contains_key(&[1, 2, 4]));
/// assert!(trie.contains_key(&[1, 2, 4, 0]));
///
/// // We can get the values.
/// assert_eq!(trie.get(&[1, 2, 3]), Some(&"foo"));
/// assert_eq!(trie.get(&[1, 2, 4]), Some(&"bar"));
/// assert_eq!(trie.get(&[1, 2]), None);
///
/// // We can iterate over the values with a given prefix.
/// use std::collections::HashSet;
/// let get_prefix: HashSet<_> = trie.get_prefix(&[1, 2, 4]).collect();
/// assert_eq!(get_prefix, HashSet::from([&"bar", &"baz"]));
///
/// // We can remove values.
/// let removed = trie.remove(&[1, 2, 3]);
///
/// assert_eq!(removed, Some("foo"));
/// assert!(!trie.contains_key(&[1, 2, 3]));
///
/// assert_eq!(trie.len(), 2);
/// ```
pub struct GenericTrie<K, V> {
    children: HashMap<K, GenericTrie<K, V>>,
    value: Option<V>,
}

impl<K, V> GenericTrie<K, V> {
    /// Creates a new trie.
    pub fn new() -> GenericTrie<K, V> {
        GenericTrie {
            children: HashMap::new(),
            value: None,
        }
    }

    /// Inserts the key value pair into the trie, cloning each element in the key.
    ///
    /// Returns the previous value, if it exists.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut trie = GenericTrie::new();
    ///
    /// trie.insert(['c', 'a', 'b'], 0);
    /// trie.insert(['c', 'a', 'r'], 0);
    /// trie.insert(['c'], 0);
    ///
    /// assert!(trie.contains_key(&['c', 'a', 'b']));
    /// assert!(trie.contains_key(&['c', 'a', 'r']));
    /// assert!(trie.contains_key(&['c']));
    /// ```
    pub fn insert<I>(&mut self, key: I, value: V) -> Option<V>
    where
        I: IntoIterator<Item = K>,
        K: Hash + Eq,
    {
        self.insert_iterator(&mut key.into_iter(), value)
    }

    pub fn insert_iterator(&mut self, key: &mut dyn Iterator<Item = K>, value: V) -> Option<V>
    where
        K: Hash + Eq,
    {
        match key.next() {
            Some(item) => self
                .children
                .entry(item)
                .or_default()
                .insert_iterator(key, value),
            None => self.value.replace(value),
        }
    }

    /// Returns a reference to the value associated with the key, if one exists.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut trie = GenericTrie::new();
    ///
    /// trie.insert(['c', 'a', 'b'], 1);
    /// trie.insert(['c', 'a', 'r'], 2);
    ///
    /// assert_eq!(trie.get(&['c', 'a', 'b']), Some(&1));
    /// assert_eq!(trie.get(&['c', 'a', 'r']), Some(&2));
    /// assert_eq!(trie.get(&['c', 'a', 't']), None);
    /// ```
    pub fn get(&self, key: &[K]) -> Option<&V>
    where
        K: Hash + Eq,
    {
        match key.split_first() {
            Some((first, rest)) => self.children.get(first).and_then(|trie| trie.get(rest)),
            None => self.value.as_ref(),
        }
    }

    /// Removes and returns the value associated with the key, if it exists.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut trie = GenericTrie::new();
    ///
    /// trie.insert([1, 2, 3], 'a');
    /// trie.insert([1, 2, 4], 'b');
    ///
    /// assert_eq!(trie.get(&[1, 2, 3]), Some(&'a'));
    /// assert_eq!(trie.get(&[1, 2, 4]), Some(&'b'));
    ///
    /// let removed = trie.remove(&[1, 2, 3]);
    ///
    /// assert_eq!(removed, Some('a'));
    /// assert!(!trie.contains_key(&[1, 2, 3]));
    /// ```
    pub fn remove(&mut self, key: &[K]) -> Option<V>
    where
        K: Hash + Eq,
    {
        match key.split_first() {
            Some((first, rest)) => self
                .children
                .get_mut(first)
                .and_then(|trie| trie.remove(rest)),
            None => self.value.take(),
        }
    }

    /// Returns an iterator over the values whose associated keys begin with `prefix`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut trie = GenericTrie::new();
    ///
    /// trie.insert([1, 2, 3], 'a');
    /// trie.insert([1, 2, 3, 4], 'b');
    /// trie.insert([1, 2], 'c');
    /// trie.insert([1], 'd');
    ///
    /// use std::collections::HashSet;
    /// assert_eq!(
    ///     trie.get_prefix(&[1, 2]).collect::<HashSet<_>>(),
    ///     HashSet::from([&'a', &'b', &'c'])
    /// );
    /// ```
    pub fn get_prefix(&self, prefix: &[K]) -> Values<'_, V>
    where
        K: Hash + Eq,
    {
        match prefix.split_first() {
            Some((first, rest)) => self
                .children
                .get(first)
                .map(|trie| trie.get_prefix(rest))
                .unwrap_or_default(),
            None => self.values(),
        }
    }

    /// Returns `true` if the trie contains `key`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut trie = GenericTrie::new();
    /// trie.insert([true, true, false], 0);
    ///
    /// assert!(trie.contains_key(&[true, true, false]));
    /// assert!(!trie.contains_key(&[true, false]));
    /// ```
    pub fn contains_key(&self, key: &[K]) -> bool
    where
        K: Hash + Eq,
    {
        match key.split_first() {
            Some((first, rest)) => self
                .children
                .get(first)
                .map(|trie| trie.contains_key(rest))
                .unwrap_or(false),
            None => self.value.is_some(),
        }
    }

    /// Returns `true` if the trie contains a key with the given prefix.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut trie = GenericTrie::new();
    /// trie.insert([true, true, false], 0);
    ///
    /// assert!(trie.contains_prefix(&[true, true, false]));
    /// assert!(trie.contains_prefix(&[true, true]));
    /// assert!(trie.contains_prefix(&[true]));
    /// assert!(!trie.contains_prefix(&[false]));
    /// assert!(!trie.contains_prefix(&[true, false]));
    /// ```
    pub fn contains_prefix(&self, prefix: &[K]) -> bool
    where
        K: Hash + Eq,
    {
        {
            match prefix.split_first() {
                Some((first, rest)) => self
                    .children
                    .get(first)
                    .map(|trie| trie.contains_prefix(rest))
                    .unwrap_or(false),
                None => !self.is_empty(),
            }
        }
    }

    /// Returns the number of elements in the trie.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut trie = GenericTrie::new();
    /// trie.insert([1, 2, 3], 'a');
    /// trie.insert([1, 2], 'b');
    /// trie.insert([1, 2, 3], 'c');
    ///
    /// assert_eq!(trie.len(), 2);
    ///
    /// trie.remove(&[1, 2]);
    ///
    /// assert_eq!(trie.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        let mut len = self.value.is_some() as usize;
        for child in self.children.values() {
            len += child.len();
        }
        len
    }

    /// Returns `true` if the trie is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut trie = GenericTrie::new();
    /// trie.insert([1, 2, 3], 'a');
    /// trie.insert([1, 2], 'b');
    ///
    /// assert!(!trie.is_empty());
    ///
    /// trie.clear();
    ///
    /// assert!(trie.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the trie.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut trie = GenericTrie::new();
    /// trie.insert([1, 2, 3], 'a');
    /// trie.insert([1, 2], 'b');
    ///
    /// assert!(!trie.is_empty());
    ///
    /// trie.clear();
    ///
    /// assert!(trie.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.children.clear();
        self.value = None;
    }

    /// Returns an iterator over the trie's values.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut trie = GenericTrie::new();
    ///
    /// trie.insert([1, 2, 3], 'a');
    /// trie.insert([1, 2, 3, 4], 'b');
    /// trie.insert([1, 2], 'c');
    /// trie.insert([1], 'd');
    ///
    /// use std::collections::HashSet;
    /// assert_eq!(
    ///     trie.values().collect::<HashSet<_>>(),
    ///     HashSet::from([&'a', &'b', &'c', &'d'])
    /// );
    /// ```
    pub fn values(&self) -> Values<'_, V> {
        let mut values = Vec::new();
        self.values_rec(&mut values);
        Values { values }
    }

    fn values_rec<'a>(&'a self, values: &mut Vec<&'a V>) {
        if let Some(ref value) = self.value {
            values.push(value);
        }
        for child in self.children.values() {
            child.values_rec(values);
        }
    }
}

impl<K, V> Default for GenericTrie<K, V> {
    fn default() -> GenericTrie<K, V> {
        GenericTrie::new()
    }
}

impl<K, V> PartialEq for GenericTrie<K, V>
where
    K: Hash + Eq,
    V: PartialEq,
{
    /// Returns `true` if the tries are equal.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericTrie;
    ///
    /// let mut a = GenericTrie::new();
    /// a.insert(['a', 'b', 'c'], 1);
    /// a.insert(['a', 'x'], 2);
    ///
    /// let mut b = GenericTrie::new();
    /// b.insert(['a', 'b', 'c'], 1);
    /// b.insert(['a', 'x'], 2);
    /// b.insert(['z'], 3);
    ///
    /// assert!(a != b);
    ///
    /// b.remove(&['z']);
    ///
    /// assert!(a == b);
    /// ```
    fn eq(&self, other: &GenericTrie<K, V>) -> bool {
        if self.value != other.value {
            return false;
        }

        let mut keys = HashSet::new();
        keys.extend(self.children.keys());
        keys.extend(other.children.keys());

        for key in keys {
            if let (Some(self_child), Some(other_child)) =
                (self.children.get(key), other.children.get(key))
            {
                if self_child != other_child {
                    return false;
                }
            } else if self
                .children
                .get(key)
                .map(|child| !child.is_empty())
                .unwrap_or(false)
                || other
                    .children
                    .get(key)
                    .map(|child| !child.is_empty())
                    .unwrap_or(false)
            {
                return false;
            }
        }

        true
    }
}

impl<K, V> Eq for GenericTrie<K, V>
where
    K: Hash + Eq,
    V: Eq,
{
}

pub struct Values<'a, V: 'a> {
    values: Vec<&'a V>,
}

impl<'a, V> Iterator for Values<'a, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        self.values.pop()
    }
}

impl<'a, V> Default for Values<'a, V> {
    fn default() -> Values<'a, V> {
        Values { values: Vec::new() }
    }
}

/// A [trie](https://en.wikipedia.org/wiki/Trie) for mapping [`str`]s to values.
///
/// # Example
/// ```
/// use rust_dsa::Trie;
///
/// // First, we create a new trie.
/// let mut trie = Trie::new();
///
/// // Then we can insert keys and items.
/// trie.insert("foo", 1);
/// trie.insert("bar", 2);
/// trie.insert("ba", 3);
///
/// assert!(trie.contains_key("foo"));
/// assert!(trie.contains_key("bar"));
/// assert!(trie.contains_key("ba"));
///
/// // We can get the values.
/// assert_eq!(trie.get("foo"), Some(&1));
/// assert_eq!(trie.get("bar"), Some(&2));
/// assert_eq!(trie.get("ba"), Some(&3));
/// assert_eq!(trie.get("baz"), None);
///
/// // We can iterate over the values with a given prefix.
/// use std::collections::HashSet;
/// let get_prefix: HashSet<_> = trie.get_prefix("ba").collect();
/// assert_eq!(get_prefix, HashSet::from([&2, &3]));
///
/// // We can remove values.
/// let removed = trie.remove("ba");
///
/// assert_eq!(removed, Some(3));
/// assert!(!trie.contains_key("ba"));
///
/// assert_eq!(trie.len(), 2);
/// ```
pub struct Trie<V> {
    inner: GenericTrie<char, V>,
}

impl<V> Trie<V> {
    /// Creates a new trie.
    pub fn new() -> Trie<V> {
        Trie {
            inner: GenericTrie::new(),
        }
    }

    /// Inserts the key value pair into the trie.
    ///
    /// Returns the previous value, if it exists.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let mut trie = Trie::new();
    ///
    /// trie.insert("cab", 0);
    /// trie.insert("car", 0);
    /// trie.insert("c", 0);
    ///
    /// assert!(trie.contains_key("cab"));
    /// assert!(trie.contains_key("car"));
    /// assert!(trie.contains_key("c"));
    /// ```
    pub fn insert(&mut self, key: &str, value: V) -> Option<V> {
        self.inner.insert(key.chars(), value)
    }

    /// Returns a reference to the value associated with the key, if one exists.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let mut trie = Trie::new();
    ///
    /// trie.insert("cab", 1);
    /// trie.insert("car", 2);
    ///
    /// assert_eq!(trie.get("cab"), Some(&1));
    /// assert_eq!(trie.get("car"), Some(&2));
    /// assert_eq!(trie.get("cat"), None);
    /// ```
    pub fn get(&self, key: &str) -> Option<&V> {
        let chars: Vec<_> = key.chars().collect();
        self.inner.get(&chars)
    }

    /// Removes and returns the value associated with the key, if it exists.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let mut trie = Trie::new();
    ///
    /// trie.insert("foo", 1);
    /// trie.insert("bar", 2);
    ///
    /// assert_eq!(trie.get("foo"), Some(&1));
    /// assert_eq!(trie.get("bar"), Some(&2));
    ///
    /// let removed = trie.remove("foo");
    ///
    /// assert_eq!(removed, Some(1));
    /// assert!(!trie.contains_key("foo"));
    /// ```
    pub fn remove(&mut self, key: &str) -> Option<V> {
        let chars: Vec<_> = key.chars().collect();
        self.inner.remove(&chars)
    }

    /// Returns an iterator over the values whose associated keys begin with `prefix`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let mut trie = Trie::new();
    ///
    /// trie.insert("abc", 1);
    /// trie.insert("abcd", 2);
    /// trie.insert("ab", 3);
    /// trie.insert("a", 4);
    ///
    /// use std::collections::HashSet;
    /// assert_eq!(
    ///     trie.get_prefix("ab").collect::<HashSet<_>>(),
    ///     HashSet::from([&1, &2, &3])
    /// );
    /// ```
    pub fn get_prefix(&self, prefix: &str) -> Values<'_, V> {
        let chars: Vec<_> = prefix.chars().collect();
        self.inner.get_prefix(&chars)
    }

    /// Returns `true` if the trie contains `key`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let mut trie = Trie::new();
    /// trie.insert("cat", 0);
    ///
    /// assert!(trie.contains_key("cat"));
    /// assert!(!trie.contains_key("ca"));
    /// ```
    pub fn contains_key(&self, key: &str) -> bool {
        let chars: Vec<_> = key.chars().collect();
        self.inner.contains_key(&chars)
    }

    /// Returns `true` if the trie contains a key with the given prefix.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let mut trie = Trie::new();
    /// trie.insert("xyz", 0);
    ///
    /// assert!(trie.contains_prefix("xyz"));
    /// assert!(trie.contains_prefix("xy"));
    /// assert!(trie.contains_prefix("x"));
    /// assert!(!trie.contains_prefix("y"));
    /// assert!(!trie.contains_prefix("xz"));
    /// ```
    pub fn contains_prefix(&self, prefix: &str) -> bool {
        let chars: Vec<_> = prefix.chars().collect();
        self.inner.contains_prefix(&chars)
    }

    /// Returns the number of elements in the trie.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let mut trie = Trie::new();
    /// trie.insert("abc", 1);
    /// trie.insert("ab", 2);
    /// trie.insert("abc", 3);
    ///
    /// assert_eq!(trie.len(), 2);
    ///
    /// trie.remove("ab");
    ///
    /// assert_eq!(trie.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns `true` if the trie is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let mut trie = Trie::new();
    /// trie.insert("abc", 1);
    /// trie.insert("ab", 2);
    ///
    /// assert!(!trie.is_empty());
    ///
    /// trie.clear();
    ///
    /// assert!(trie.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the trie.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let mut trie = Trie::new();
    /// trie.insert("abc", 1);
    /// trie.insert("ab", 2);
    ///
    /// assert!(!trie.is_empty());
    ///
    /// trie.clear();
    ///
    /// assert!(trie.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Returns an iterator over the trie's values.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let mut trie = Trie::new();
    ///
    /// trie.insert("abc", 1);
    /// trie.insert("abcd", 2);
    /// trie.insert("ab", 3);
    /// trie.insert("a", 4);
    ///
    /// use std::collections::HashSet;
    /// assert_eq!(
    ///     trie.values().collect::<HashSet<_>>(),
    ///     HashSet::from([&1, &2, &3, &4])
    /// );
    /// ```
    pub fn values(&self) -> Values<'_, V> {
        self.inner.values()
    }
}

impl<V> Default for Trie<V> {
    fn default() -> Trie<V> {
        Trie::new()
    }
}

impl<V> FromIterator<(&'static str, V)> for Trie<V> {
    fn from_iter<T: IntoIterator<Item = (&'static str, V)>>(iter: T) -> Trie<V> {
        let mut trie = Trie::new();
        for (key, value) in iter {
            trie.insert(key, value);
        }
        trie
    }
}

impl<V, const N: usize> From<[(&'static str, V); N]> for Trie<V> {
    /// Creates a trie from an array of key value pairs.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::Trie;
    ///
    /// let trie = Trie::from([("foo", 1), ("bar", 2), ("baz", 3)]);
    /// assert_eq!(trie.get("foo"), Some(&1));
    /// assert_eq!(trie.get("bar"), Some(&2));
    /// assert_eq!(trie.get("baz"), Some(&3));
    /// assert_eq!(trie.get("boo"), None);
    /// ```
    fn from(array: [(&'static str, V); N]) -> Trie<V> {
        array.into_iter().collect()
    }
}

impl<V> PartialEq for Trie<V>
where
    V: PartialEq,
{
    fn eq(&self, other: &Trie<V>) -> bool {
        self.inner == other.inner
    }
}

impl<V> Eq for Trie<V> where V: Eq {}
