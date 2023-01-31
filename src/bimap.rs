use std::borrow::Borrow;
use std::collections::{hash_map::Entry, HashMap};
use std::fmt;
use std::hash::Hash;
use std::rc::Rc;

/// A [bidirectional map](https://en.wikipedia.org/wiki/Bidirectional_map).
///
/// # Example
/// ```
/// use rust_dsa::BiMap;
///
/// // First, we create a new map.
/// let mut map = BiMap::new();
///
/// // Then we insert values.
/// map.insert(1, 'a');
/// map.insert(2, 'b');
/// map.insert(3, 'c');
///
/// assert_eq!(map.len(), 3);
/// assert!(map.contains_left(&1));
/// assert!(map.contains_right(&'c'));
///
/// // We can get values.
/// assert_eq!(map.get_by_left(&1), Some(&'a'));
/// assert_eq!(map.get_by_left(&2), Some(&'b'));
/// assert_eq!(map.get_by_right(&'c'), Some(&3));
/// assert_eq!(map.get_by_left(&99), None);
/// assert_eq!(map.get_by_right(&'z'), None);
///
/// use rust_dsa::Removed;
///
/// // Inserting returns the old elements.
/// let removed = map.insert(3, 'z');
/// assert_eq!(removed, Removed::Single((3, 'c')));
///
/// // (1, 'z') touches two pairs ((1, 'a') and (3, 'z'))
/// let removed = map.insert(1, 'z');
/// assert_eq!(removed, Removed::Double((1, 'a'), (3, 'z')));
///
/// // (5, 'm') touches nothing
/// let removed = map.insert(5, 'm');
/// assert_eq!(removed, Removed::Nothing);
///
/// assert_eq!(map.len(), 3);
///
/// // We can also remove items.
/// assert_eq!(map.remove_by_left(&1), Some((1, 'z')));
/// assert_eq!(map.remove_by_right(&'b'), Some((2, 'b')));
/// assert_eq!(map.remove_by_right(&'m'), Some((5, 'm')));
/// assert_eq!(map.remove_by_left(&99), None);
///
/// assert!(map.is_empty());
/// ```
pub struct BiMap<L, R> {
    left_to_right: HashMap<MyRc<L>, MyRc<R>>,
    right_to_left: HashMap<MyRc<R>, MyRc<L>>,
}

impl<L, R> BiMap<L, R> {
    /// Creates a new map.
    pub fn new() -> BiMap<L, R> {
        BiMap {
            left_to_right: HashMap::new(),
            right_to_left: HashMap::new(),
        }
    }

    /// Creates a new map with the given capacity.
    pub fn with_capacity(capacity: usize) -> BiMap<L, R> {
        BiMap {
            left_to_right: HashMap::with_capacity(capacity),
            right_to_left: HashMap::with_capacity(capacity),
        }
    }

    /// Inserts a pair into the map. Returns the removed items.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::{BiMap, Removed};
    ///
    /// let mut map = BiMap::new();
    ///
    /// let removed = map.insert(1, 2);
    /// assert_eq!(removed, Removed::Nothing);
    /// let removed = map.insert(3, 4);
    /// assert_eq!(removed, Removed::Nothing);
    ///
    /// let removed = map.insert(1, 3);
    /// assert_eq!(removed, Removed::Single((1, 2)));
    ///
    /// let removed = map.insert(1, 4);
    /// assert_eq!(removed, Removed::Double((1, 3), (3, 4)));
    ///
    /// let removed = map.insert(1, 4);
    /// assert_eq!(removed, Removed::Single((1, 4)));
    /// ```
    pub fn insert(&mut self, left: L, right: R) -> Removed<L, R>
    where
        L: Hash + Eq,
        R: Hash + Eq,
    {
        let removed_by_left = self.remove_by_left(&left);
        let removed_by_right = self.remove_by_right(&right);
        let rc_left = MyRc::new(left);
        let rc_right = MyRc::new(right);
        self.left_to_right.insert(rc_left.clone(), rc_right.clone());
        self.right_to_left.insert(rc_right, rc_left);

        Removed::new(removed_by_left, removed_by_right)
    }

    /// Returns a reference to the right value based on the left value.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BiMap;
    ///
    /// let map = BiMap::from([(1, 'a'), (2, 'b')]);
    ///
    /// assert_eq!(map.get_by_left(&1), Some(&'a'));
    /// assert_eq!(map.get_by_left(&2), Some(&'b'));
    /// assert_eq!(map.get_by_left(&3), None);
    /// ```
    pub fn get_by_left(&self, left: &L) -> Option<&R>
    where
        L: Hash + Eq,
    {
        let wrapped = Wrapper::wrap(left);
        self.left_to_right.get(wrapped).map(MyRc::as_ref)
    }

    /// Returns a reference to the left value based on the right value.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BiMap;
    ///
    /// let map = BiMap::from([(1, 'a'), (2, 'b')]);
    ///
    /// assert_eq!(map.get_by_right(&'a'), Some(&1));
    /// assert_eq!(map.get_by_right(&'b'), Some(&2));
    /// assert_eq!(map.get_by_right(&'c'), None);
    /// ```
    pub fn get_by_right(&self, right: &R) -> Option<&L>
    where
        R: Hash + Eq,
    {
        let wrapped = Wrapper::wrap(right);
        self.right_to_left.get(wrapped).map(MyRc::as_ref)
    }

    /// Removes a pair from the map based on the left value.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BiMap;
    ///
    /// let mut map = BiMap::from([(1, 'a'), (2, 'b')]);
    ///
    /// assert_eq!(map.remove_by_left(&1), Some((1, 'a')));
    /// assert_eq!(map.remove_by_left(&2), Some((2, 'b')));
    /// assert_eq!(map.remove_by_left(&1), None);
    ///
    /// assert!(map.is_empty());
    /// ```
    pub fn remove_by_left(&mut self, left: &L) -> Option<Item<L, R>>
    where
        L: Hash + Eq,
        R: Hash + Eq,
    {
        let wrapped = Wrapper::wrap(left);
        let (_, rc_right) = self.left_to_right.remove_entry(wrapped)?;
        let (rc_right, rc_left) = match self.right_to_left.entry(rc_right) {
            Entry::Occupied(entry) => entry.remove_entry(),
            Entry::Vacant(_) => unreachable!(),
        };

        Some((rc_left.value(), rc_right.value()))
    }

    /// Removes a pair from the map based on the right value.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BiMap;
    ///
    /// let mut map = BiMap::from([(1, 'a'), (2, 'b')]);
    ///
    /// assert_eq!(map.remove_by_right(&'a'), Some((1, 'a')));
    /// assert_eq!(map.remove_by_right(&'b'), Some((2, 'b')));
    /// assert_eq!(map.remove_by_right(&'a'), None);
    ///
    /// assert!(map.is_empty());
    /// ```
    pub fn remove_by_right(&mut self, right: &R) -> Option<Item<L, R>>
    where
        L: Hash + Eq,
        R: Hash + Eq,
    {
        let wrapped = Wrapper::wrap(right);
        let (_, rc_left) = self.right_to_left.remove_entry(wrapped)?;
        let (rc_left, rc_right) = match self.left_to_right.entry(rc_left) {
            Entry::Occupied(entry) => entry.remove_entry(),
            Entry::Vacant(_) => unreachable!(),
        };

        Some((rc_left.value(), rc_right.value()))
    }

    /// Returns `true` if the map contains the left value.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BiMap;
    ///
    /// let map = BiMap::from([(1, 'a'), (2, 'b')]);
    ///
    /// assert!(map.contains_left(&1));
    /// assert!(map.contains_left(&2));
    /// assert!(!map.contains_left(&3));
    /// ```
    pub fn contains_left(&self, left: &L) -> bool
    where
        L: Hash + Eq,
    {
        let wrapped = Wrapper::wrap(left);
        self.left_to_right.contains_key(wrapped)
    }

    /// Returns `true` if the map contains the right value.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BiMap;
    ///
    /// let map = BiMap::from([(1, 'a'), (2, 'b')]);
    ///
    /// assert!(map.contains_right(&'a'));
    /// assert!(map.contains_right(&'b'));
    /// assert!(!map.contains_right(&'c'));
    /// ```
    pub fn contains_right(&self, right: &R) -> bool
    where
        R: Hash + Eq,
    {
        let wrapped = Wrapper::wrap(right);
        self.right_to_left.contains_key(wrapped)
    }

    /// Returns the number of pairs in the map.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BiMap;
    ///
    /// let mut map = BiMap::from([(1, 'a'), (2, 'b'), (3, 'c')]);
    ///
    /// assert_eq!(map.len(), 3);
    ///
    /// map.remove_by_left(&1);
    ///
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.left_to_right.len()
    }

    /// Returns `true` if the map is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BiMap;
    ///
    /// let mut map = BiMap::from([(1, 'a'), (2, 'b'), (3, 'c')]);
    ///
    /// assert!(!map.is_empty());
    ///
    /// map.clear();
    ///
    /// assert!(map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the map.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BiMap;
    ///
    /// let mut map = BiMap::from([(1, 'a'), (2, 'b'), (3, 'c')]);
    ///
    /// assert!(!map.is_empty());
    ///
    /// map.clear();
    ///
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.left_to_right.clear();
        self.right_to_left.clear();
    }

    /// Returns an iterator over the items in the map.
    pub fn iter(&self) -> Iter<'_, L, R> {
        self.into_iter()
    }

    /// Returns the left values in the map.
    pub fn lefts(&self) -> Vec<&L> {
        self.iter().map(|(left, _)| left).collect()
    }

    /// Returns the left values in the map.
    pub fn into_lefts(self) -> Vec<L> {
        self.into_iter().map(|(left, _)| left).collect()
    }

    /// Returns right values in the map.
    pub fn rights(&self) -> Vec<&R> {
        self.iter().map(|(_, right)| right).collect()
    }

    /// Returns right values in the map.
    pub fn into_rights(self) -> Vec<R> {
        self.into_iter().map(|(_, right)| right).collect()
    }
}

impl<L, R> FromIterator<Item<L, R>> for BiMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn from_iter<I: IntoIterator<Item = Item<L, R>>>(iter: I) -> BiMap<L, R> {
        let iter = iter.into_iter();
        let mut map = BiMap::with_capacity(iter.size_hint().0);
        for (left, right) in iter {
            map.insert(left, right);
        }
        map
    }
}

impl<L, R, const N: usize> From<[Item<L, R>; N]> for BiMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn from(array: [(L, R); N]) -> BiMap<L, R> {
        array.into_iter().collect()
    }
}

impl<L, R> Default for BiMap<L, R> {
    fn default() -> BiMap<L, R> {
        BiMap::new()
    }
}

impl<L, R> fmt::Debug for BiMap<L, R>
where
    L: fmt::Debug,
    R: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, (l, r)) in self.iter().enumerate() {
            if i == 0 {
                write!(f, "{:?}: {:?}", l, r)?;
            } else {
                write!(f, ", {:?}: {:?}", l, r)?;
            }
        }
        Ok(())
    }
}

impl<L, R> PartialEq for BiMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn eq(&self, other: &BiMap<L, R>) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for (left, right) in self {
            if self.get_by_left(left).map(|r| r != right).unwrap_or(true) {
                return false;
            }
        }
        true
    }
}

impl<L, R> Eq for BiMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
}

impl<L, R> Clone for BiMap<L, R>
where
    L: Clone + Hash + Eq,
    R: Clone + Hash + Eq,
{
    fn clone(&self) -> BiMap<L, R> {
        let mut map = BiMap::with_capacity(self.len());
        for (left, right) in self {
            map.insert(left.clone(), right.clone());
        }
        map
    }
}

impl<L, R> IntoIterator for BiMap<L, R> {
    type IntoIter = IntoIter<L, R>;
    type Item = Item<L, R>;
    fn into_iter(mut self) -> Self::IntoIter {
        self.right_to_left.clear();
        IntoIter {
            items: self
                .left_to_right
                .into_iter()
                .map(|(l, r)| (l.value(), r.value()))
                .collect(),
        }
    }
}

pub struct IntoIter<L, R> {
    items: Vec<Item<L, R>>,
}

impl<L, R> Iterator for IntoIter<L, R> {
    type Item = Item<L, R>;
    fn next(&mut self) -> Option<Self::Item> {
        self.items.pop()
    }
}

impl<'a, L, R> IntoIterator for &'a BiMap<L, R> {
    type IntoIter = Iter<'a, L, R>;
    type Item = (&'a L, &'a R);
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            items: self
                .left_to_right
                .iter()
                .map(|(l, r)| (MyRc::as_ref(l), MyRc::as_ref(r)))
                .collect(),
        }
    }
}

pub struct Iter<'a, L: 'a, R: 'a> {
    items: Vec<(&'a L, &'a R)>,
}

impl<'a, L, R> Iterator for Iter<'a, L, R> {
    type Item = (&'a L, &'a R);
    fn next(&mut self) -> Option<Self::Item> {
        self.items.pop()
    }
}

pub type Item<L, R> = (L, R);

/// An enum representing the items remove from a [`BiMap`].
#[derive(PartialEq, Eq, Debug)]
pub enum Removed<L, R> {
    Nothing,
    Single(Item<L, R>),
    Double(Item<L, R>, Item<L, R>),
}

impl<L, R> Removed<L, R> {
    fn new(
        removed_by_left: Option<Item<L, R>>,
        removed_by_right: Option<Item<L, R>>,
    ) -> Removed<L, R> {
        match (removed_by_left, removed_by_right) {
            (Some(left), Some(right)) => Removed::Double(left, right),
            (Some(left), None) => Removed::Single(left),
            (None, Some(right)) => Removed::Single(right),
            (None, None) => Removed::Nothing,
        }
    }
}

// from https://crates.io/crates/bimap
#[derive(PartialEq, Eq, Hash)]
pub struct MyRc<T> {
    inner: Rc<T>,
}

impl<T> MyRc<T> {
    fn new(value: T) -> MyRc<T> {
        MyRc {
            inner: Rc::new(value),
        }
    }

    fn value(self) -> T {
        match Rc::try_unwrap(self.inner) {
            Ok(value) => value,
            Err(_) => unreachable!(),
        }
    }
}

impl<T> Clone for MyRc<T> {
    fn clone(&self) -> MyRc<T> {
        MyRc {
            inner: self.inner.clone(),
        }
    }
}

impl<T> AsRef<T> for MyRc<T> {
    fn as_ref(&self) -> &T {
        Rc::as_ref(&self.inner)
    }
}

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
struct Wrapper<T>(T);

impl<T> Wrapper<T> {
    fn wrap(value: &T) -> &Wrapper<T> {
        unsafe { std::mem::transmute(value) }
    }
}

impl<K, Q> Borrow<Wrapper<Q>> for MyRc<K>
where
    K: Borrow<Q>,
{
    fn borrow(&self) -> &Wrapper<Q> {
        let k: &K = self.inner.borrow();
        let q: &Q = k.borrow();

        Wrapper::wrap(q)
    }
}
