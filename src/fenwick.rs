use std::ops::{Bound, Index, RangeBounds};

use num_traits::{PrimInt, WrappingAdd, WrappingSub};

/// A [Fenwick tree](https://en.wikipedia.org/wiki/Fenwick_tree) that is generic
/// over any type `T` and associative function `F`.
///
/// A Fenwick tree behaves more or less like a `Vec<T>`. Values can be pushed,
/// popped and indexed as usual. But Fenwick trees are equipped with an addition
/// operation that calculates prefix sums in *O*(log *n*) time. Note that "sum"
/// is used in the documentation because addition is the most common operation,
/// but any associative operation with an identity (any
/// [monoid](https://en.wikipedia.org/wiki/Monoid)) works.
///
/// For all values `a`, `b` and `c`, `f` and `id` should obey the following
/// properties:
/// ```text
/// f(f(a, b), c) == f(a, f(b, c))
/// f(id, a) == a == f(a, id)
/// ```
///
/// See also: [`FenwickTree`].
///
/// # Example
/// ```
/// use rust_dsa::GenericFenwickTree;
///
/// // First, we create a new tree.
/// let mut tree = GenericFenwickTree::new(0, |&a, &b| a + b);
///
/// // Then we push some values.
/// tree.push(1);
/// tree.push(4);
/// tree.push(3);
/// tree.push(-2);
///
/// // We can index into the tree.
/// assert_eq!(tree[1], 4);
/// assert_eq!(tree.get(2), Some(&3));
/// assert_eq!(tree.get(4), None);
///
/// // And we can calculate prefix sums.
/// assert_eq!(tree.sum_to(2), 5);
/// assert_eq!(tree.sum_to(3), 8);
/// assert_eq!(tree.total(), 6);
///
/// // We can also pop values.
/// assert_eq!(tree.pop(), Some(-2));
/// assert_eq!(tree.pop(), Some(3));
///
/// // Fenwick trees work with any associative function.
/// let mut strings = GenericFenwickTree::new(
///     String::new(),
///     |a, b| format!("{a}{b}"),
/// );
/// strings.push("foo".into());
/// strings.push("bar".into());
/// strings.push("baz".into());
///
/// assert_eq!(strings.sum_to(2), "foobar");
///
/// // We can also create them direcly from arrays.
/// let prod = GenericFenwickTree::from_array(
///     1,
///     |&a, &b| a * b,
///     [1, 2, 3, 4, 5, 6],
/// );
///
/// assert_eq!(prod.sum_to(4), 24);
/// assert_eq!(prod.total(), 720);
/// ```
///
/// # Runtime complexity
///
/// | Operation                          | Runtime Complexity       |
/// | ---------------------------------- | ------------------------ |
/// | [`GenericFenwickTree::from_array`] | *O*(*n*)                 |
/// | [`GenericFenwickTree::push`]       | *O*(log *n*)             |
/// | [`GenericFenwickTree::sum_to`]     | *O*(log *n*)             |
/// | [`GenericFenwickTree::update`]     | *O*(log<sup>2</sup> *n*) |
/// | [`GenericFenwickTree::get`]        | *O*(1)                   |
/// | [`GenericFenwickTree::pop`]        | *O*(1)                   |
#[derive(Clone)]
pub struct GenericFenwickTree<T, F> {
    id: T,
    pairs: Vec<Pair<T>>,
    f: F,
}

impl<T, F> GenericFenwickTree<T, F>
where
    F: Fn(&T, &T) -> T,
{
    /// Creates a Fenwick tree.
    pub fn new(id: T, f: F) -> Self {
        GenericFenwickTree {
            id,
            pairs: Vec::new(),
            f,
        }
    }

    /// Creates a Fenwick tree from an array in linear time.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let tree = GenericFenwickTree::from_array(
    ///     String::new(),
    ///     |a, b| format!("{a}{b}"),
    ///     [
    ///         "foo".into(),
    ///         "bar".into(),
    ///         "b".into(),
    ///         "az".into(),
    ///         "!".into(),
    ///     ],
    /// );
    ///
    /// assert_eq!(tree.total(), "foobarbaz!");
    /// assert_eq!(tree.sum_to(2), "foobar");
    /// ```
    pub fn from_array<const N: usize>(id: T, f: F, array: [T; N]) -> Self {
        let mut pairs: Vec<_> = array
            .into_iter()
            .map(|value| Pair {
                value,
                sum: f(&id, &id),
            })
            .collect();
        for i in 0..pairs.len() {
            pairs[i].sum = f(&pairs[i].sum, &pairs[i].value);
            let j = i + lsb(i + 1);
            if j < pairs.len() {
                pairs[j].sum = f(&pairs[j].sum, &pairs[i].sum);
            }
        }
        GenericFenwickTree { id, pairs, f }
    }

    /// Pushes a value onto the end of the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let mut tree = GenericFenwickTree::new(0, |&a, &b| a + b);
    /// tree.push(1);
    /// tree.push(4);
    /// tree.push(3);
    /// tree.push(-1);
    ///
    /// assert_eq!(tree.len(), 4);
    /// assert_eq!(tree.get(1), Some(&4));
    /// assert_eq!(tree.total(), 7);
    /// ```
    pub fn push(&mut self, value: T) {
        let mut sum = (self.f)(&value, &self.id);
        if self.len() % 2 == 0 {
            self.pairs.push(Pair { value, sum });
        } else {
            let stop = parent(self.len() + 1);
            let mut i = self.len();
            while i > stop {
                sum = (self.f)(&self.pairs[i - 1].sum, &sum);
                i = parent(i);
            }
            self.pairs.push(Pair { value, sum });
        }
    }

    /// Returns a reference to the value at position `index` if one exists.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let tree = GenericFenwickTree::from_array(
    ///     0,
    ///     |&a, &b| a + b,
    ///     [8, 4, 2],
    /// );
    ///
    /// assert_eq!(tree.get(1), Some(&4));
    /// assert_eq!(tree.get(6), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        self.pairs.get(index).map(|pair| &pair.value)
    }

    /// Removes and returns the last value in the tree, or `None` if the
    /// tree is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let mut tree = GenericFenwickTree::from_array(
    ///     0,
    ///     |&a, &b| a + b,
    ///     [8, 4, 2],
    /// );
    ///
    /// assert_eq!(tree.pop(), Some(2));
    /// assert_eq!(tree.pop(), Some(4));
    /// assert_eq!(tree.pop(), Some(8));
    /// assert_eq!(tree.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.pairs.pop().map(|pair| pair.value)
    }

    /// Returns a reference to the last value in the tree, or `None` if the
    /// tree is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let tree = GenericFenwickTree::from_array(
    ///     0,
    ///     |&a, &b| a + b,
    ///     [8, 4, 2],
    /// );
    ///
    /// assert_eq!(tree.last(), Some(&2));
    /// ```
    pub fn last(&self) -> Option<&T> {
        self.pairs.last().map(|pair| &pair.value)
    }

    /// Returns the associative operation `f` applied to the values with indices
    /// in the range `[0, end)`.
    ///
    /// # Panics
    /// Panics if `end` is larger than the number of values in the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let tree = GenericFenwickTree::from_array(
    ///     1,
    ///     |&a, &b| a * b,
    ///     [1, 2, 3, 4, 5],
    /// );
    ///
    /// assert_eq!(tree.sum_to(0), 1);
    /// assert_eq!(tree.sum_to(3), 6);
    /// assert_eq!(tree.sum_to(5), 120);
    /// ```
    #[track_caller]
    pub fn sum_to(&self, end: usize) -> T {
        if end == 0 {
            (self.f)(&self.id, &self.id)
        } else if end > self.len() {
            panic!(
                "index out of bounds: len is {}, but end is {}",
                self.len(),
                end
            );
        } else {
            let mut sum = (self.f)(&self.pairs[end - 1].sum, &self.id);
            let mut i = parent(end);
            while i > 0 {
                sum = (self.f)(&self.pairs[i - 1].sum, &sum);
                i = parent(i);
            }
            sum
        }
    }

    /// Returns the associative operation `f` applied to all values in the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let tree = GenericFenwickTree::from_array(
    ///     Vec::new(),
    ///     |a, b| [a.clone(), b.clone()].concat(),
    ///     [
    ///         vec![1, 2, 3],
    ///         vec![-2, -1],
    ///         vec![8],
    ///     ],
    /// );
    ///
    /// assert_eq!(tree.total(), vec![1, 2, 3, -2, -1, 8]);
    /// ```
    pub fn total(&self) -> T {
        self.sum_to(self.len())
    }

    /// Updates the value at `index`.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let mut tree = GenericFenwickTree::new(
    ///     0,
    ///     |&a, &b| a + b
    /// );
    /// tree.push(1);
    /// tree.push(4);
    /// tree.push(2);
    ///
    /// assert_eq!(tree.total(), 7);
    ///
    /// tree.update(0, &2);
    /// tree.update(1, &-1);
    ///
    /// assert_eq!(tree[0], 3);
    /// assert_eq!(tree[1], 3);
    /// assert_eq!(tree.total(), 8);
    /// ```
    #[track_caller]
    pub fn update(&mut self, index: usize, delta: &T) {
        self.pairs[index].value = (self.f)(&self.pairs[index].value, delta);
        self.pairs[index].sum = (self.f)(&self.pairs[index].sum, delta);
        let mut i = index + lsb(index + 1);
        while i < self.len() {
            let mut new_sum = (self.f)(&self.pairs[i].value, &self.id);
            let stop = parent(i + 1);
            let mut j = i;
            while j > stop {
                new_sum = (self.f)(&self.pairs[j - 1].sum, &new_sum);
                j = parent(j);
            }
            self.pairs[i].sum = new_sum;
            i = i + lsb(i + 1);
        }
    }

    /// Returns the number of values in the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let mut tree = GenericFenwickTree::new(0.0, |&a, &b| a + b);
    ///
    /// assert_eq!(tree.len(), 0);
    ///
    /// tree.push(1.5);
    ///
    /// assert_eq!(tree.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.pairs.len()
    }

    /// Returns `true` if the tree is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let mut tree = GenericFenwickTree::new(0.0, |&a, &b| a + b);
    ///
    /// assert!(tree.is_empty());
    ///
    /// tree.push(4.2);
    ///
    /// assert!(!tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Empties the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::GenericFenwickTree;
    ///
    /// let mut tree = GenericFenwickTree::from_array(
    ///     1,
    ///     |&a, &b| a * b,
    ///     [1, 2, 3, 4, 5],
    /// );
    ///
    /// assert!(!tree.is_empty());
    ///
    /// tree.clear();
    ///
    /// assert!(tree.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.pairs.clear();
    }
}

fn lsb(i: usize) -> usize {
    let i = i as isize;
    (i & -i) as usize
}

fn parent(i: usize) -> usize {
    i - lsb(i)
}

#[derive(Clone)]
struct Pair<T> {
    value: T,
    sum: T,
}

impl<T, F> Index<usize> for GenericFenwickTree<T, F> {
    type Output = T;
    #[track_caller]
    fn index(&self, index: usize) -> &Self::Output {
        &self.pairs[index].value
    }
}

pub struct IntoIter<T>(Vec<Pair<T>>);

impl<T, F> IntoIterator for GenericFenwickTree<T, F> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(mut self) -> Self::IntoIter {
        self.pairs.reverse();
        IntoIter(self.pairs)
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop().map(|pair| pair.value)
    }
}

pub struct Iter<'a, T>(std::slice::Iter<'a, Pair<T>>);

impl<'a, T, F> IntoIterator for &'a GenericFenwickTree<T, F> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        Iter(self.pairs.iter())
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|pair| &pair.value)
    }
}

/// A [Fenwick tree](https://en.wikipedia.org/wiki/Fenwick_tree) specialized for
/// primitive integers and addition.
///
/// Allowing only primitive integers enables the [`sum`](`FenwickTree::sum`) and
/// [`set`](`FenwickTree::set`) operations along with a *O*(log *n*)
/// [`update`](`FenwickTree::update`) implementation.
///
/// See also: [`GenericFenwickTree`].
///
/// # Example
/// ```
/// use rust_dsa::FenwickTree;
///
/// // First, we create an empty tree.
/// let mut tree = FenwickTree::new();
///
/// // Then we push some values.
/// tree.push(1);
/// tree.push(4);
/// tree.push(3);
/// tree.push(-2);
///
/// // We can index into the tree.
/// assert_eq!(tree[1], 4);
/// assert_eq!(tree.get(2), Some(3));
/// assert_eq!(tree.get(4), None);
///
/// // And we can calculate sums.
/// assert_eq!(tree.sum_to(2), 5);
/// assert_eq!(tree.sum(1..3), 7);
/// assert_eq!(tree.total(), 6);
///
/// // We can also pop values.
/// assert_eq!(tree.pop(), Some(-2));
/// assert_eq!(tree.pop(), Some(3));
///
/// // We can create trees from iterators.
/// let mut digits: FenwickTree<u64> = (0..=9).collect();
///
/// // And update/set values.
/// digits.update(2, 4);
/// digits.set(6, 0);
///
/// assert_eq!(digits[2], 6);
/// assert_eq!(digits[6], 0);
///
/// // We can also create trees from arrays.
/// let more_digits = FenwickTree::from([0, 1, 6, 3, 4, 5, 0, 7, 8, 9]);
///
/// assert!(digits == more_digits);
/// ```
///
/// # Runtime complexity
///
/// | Operation                   | Runtime Complexity |
/// | --------------------------- | ------------------ |
/// | [`FenwickTree::from_iter`]  | *O*(*n*)           |
/// | [`FenwickTree::push`]       | *O*(log *n*)       |
/// | [`FenwickTree::sum_to`]     | *O*(log *n*)       |
/// | [`FenwickTree::sum`]        | *O*(log *n*)       |
/// | [`FenwickTree::update`]     | *O*(log *n*)       |
/// | [`FenwickTree::set`]        | *O*(log *n*)       |
/// | [`FenwickTree::get`]        | *O*(1)             |
/// | [`FenwickTree::pop`]        | *O*(1)             |
#[derive(Clone)]
pub struct FenwickTree<I>(GenericFenwickTree<I, fn(&I, &I) -> I>);

impl<I: PrimInt> FenwickTree<I> {
    /// Creates a Fenwick tree.
    pub fn new() -> Self
    where
        I: WrappingAdd,
    {
        FenwickTree(GenericFenwickTree::new(
            I::zero(),
            WrappingAdd::wrapping_add,
        ))
    }

    /// Pushes a value onto the end of the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let mut tree = FenwickTree::new();
    /// tree.push(1);
    /// tree.push(4);
    /// tree.push(3);
    /// tree.push(-1);
    ///
    /// assert_eq!(tree.len(), 4);
    /// assert_eq!(tree.get(1), Some(4));
    /// assert_eq!(tree.total(), 7);
    /// ```
    pub fn push(&mut self, value: I) {
        self.0.push(value);
    }

    /// Returns the value at position `index` if one exists.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let tree = FenwickTree::from([8, 4, 2]);
    ///
    /// assert_eq!(tree.get(1), Some(4));
    /// assert_eq!(tree.get(3), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<I> {
        self.0.get(index).copied()
    }

    /// Removes and returns the last value in the tree, or returns `None` if the
    /// tree is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let mut tree = FenwickTree::from([8, 4, 2]);
    ///
    /// assert_eq!(tree.pop(), Some(2));
    /// assert_eq!(tree.pop(), Some(4));
    /// assert_eq!(tree.pop(), Some(8));
    /// assert_eq!(tree.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<I> {
        self.0.pop()
    }

    /// Returns the last value in the tree, or `None` if the tree is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let tree = FenwickTree::from([8, 4, 2]);
    ///
    /// assert_eq!(tree.last(), Some(2));
    ///
    /// let empty: FenwickTree<u8> = FenwickTree::new();
    ///
    /// assert_eq!(empty.last(), None);
    /// ```
    pub fn last(&self) -> Option<I> {
        self.0.last().copied()
    }

    /// Returns the sum of the values with indices in the range `[0, end)`.
    ///
    /// # Panics
    /// Panics if `end` is larger than the number of values in the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let tree = FenwickTree::from([1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(tree.sum_to(0), 0);
    /// assert_eq!(tree.sum_to(3), 6);
    /// assert_eq!(tree.sum_to(5), 15);
    /// ```
    #[track_caller]
    pub fn sum_to(&self, end: usize) -> I {
        self.0.sum_to(end)
    }

    /// Returns the sum of the values with indices in `range`.
    ///
    /// # Panics
    /// Panics if the starting point is greater than the end point or if the end
    /// point is greater than the number of values in the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let tree: FenwickTree<_> = (2..12).collect();
    ///
    /// assert_eq!(tree.sum(4..8), 30);
    /// assert_eq!(tree.sum(..=3), 14);
    /// assert_eq!(tree.sum(5..), 45);
    /// assert_eq!(tree.sum(..), 65);
    /// ```
    #[track_caller]
    pub fn sum<R: RangeBounds<usize>>(&self, range: R) -> I
    where
        I: WrappingSub,
    {
        let low = match range.start_bound() {
            Bound::Unbounded => 0,
            Bound::Included(low) => *low,
            Bound::Excluded(low) => 1 + *low,
        };
        let high = match range.end_bound() {
            Bound::Unbounded => self.len(),
            Bound::Included(high) => 1 + *high,
            Bound::Excluded(high) => *high,
        };

        if low > high {
            panic!("end of range ({high}) is smaller than start of range ({low})");
        }
        if high > self.len() {
            panic!(
                "index out of bounds: len is {}, but range ends at {}",
                self.len(),
                high
            );
        }

        self.sum_to(high).wrapping_sub(&self.sum_to(low))
    }

    /// Returns sum of all values in the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let tree = FenwickTree::from([1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(tree.total(), 15);
    /// ```
    pub fn total(&self) -> I {
        self.0.total()
    }

    /// Updates the value at `index`.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let mut tree = FenwickTree::from([1, 2, 3, 4, 5]);
    ///
    /// tree.update(1, 4);
    /// tree.update(2, -1);
    ///
    /// assert_eq!(tree[1], 6);
    /// assert_eq!(tree[2], 2);
    /// assert_eq!(tree.total(), 18);
    /// ```
    #[track_caller]
    pub fn update(&mut self, index: usize, delta: I) {
        self.0.pairs[index].value = (self.0.f)(&self.0.pairs[index].value, &delta);
        self.0.pairs[index].sum = (self.0.f)(&self.0.pairs[index].sum, &delta);
        let mut i = index + lsb(index + 1);
        while i < self.len() {
            self.0.pairs[i].sum = (self.0.f)(&self.0.pairs[i].sum, &delta);
            i = i + lsb(i + 1);
        }
    }

    /// Sets the value at `index`.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let mut tree = FenwickTree::from([1_usize, 4, 8, 16]);
    ///
    /// tree.set(1, 6);
    /// tree.set(2, 2);
    ///
    /// assert_eq!(tree[1], 6);
    /// assert_eq!(tree[2], 2);
    /// assert_eq!(tree.total(), 25);
    /// ```
    #[track_caller]
    pub fn set(&mut self, index: usize, new_value: I)
    where
        I: WrappingSub,
    {
        let old_value = self[index];
        let delta = new_value.wrapping_sub(&old_value);
        self.update(index, delta);
    }

    /// Returns the number of values in the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let mut tree = FenwickTree::from([1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(tree.len(), 5);
    ///
    /// tree.pop();
    ///
    /// assert_eq!(tree.len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the tree is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let mut tree = FenwickTree::from([1, 2, 3, 4, 5]);
    ///
    /// assert!(!tree.is_empty());
    ///
    /// tree.clear();
    ///
    /// assert!(tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Empties the tree.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::FenwickTree;
    ///
    /// let mut tree = FenwickTree::from([1, 2, 3, 4, 5]);
    ///
    /// assert!(!tree.is_empty());
    ///
    /// tree.clear();
    ///
    /// assert!(tree.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.0.clear();
    }
}

impl<I> Index<usize> for FenwickTree<I> {
    type Output = I;
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<I> IntoIterator for FenwickTree<I> {
    type Item = I;
    type IntoIter = IntoIter<I>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

pub struct IntIter<'a, I>(std::slice::Iter<'a, Pair<I>>);

impl<'a, I: Copy> IntoIterator for &'a FenwickTree<I> {
    type Item = I;
    type IntoIter = IntIter<'a, I>;
    fn into_iter(self) -> Self::IntoIter {
        IntIter(self.0.pairs.iter())
    }
}

impl<'a, I: Copy> Iterator for IntIter<'a, I> {
    type Item = I;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|pair| pair.value)
    }
}

impl<I: PrimInt + WrappingAdd> FromIterator<I> for FenwickTree<I> {
    fn from_iter<T: IntoIterator<Item = I>>(iter: T) -> Self {
        let mut pairs: Vec<_> = iter
            .into_iter()
            .map(|value| Pair {
                value,
                sum: I::zero(),
            })
            .collect();
        for i in 0..pairs.len() {
            pairs[i].sum = pairs[i].sum.wrapping_add(&pairs[i].value);
            let j = i + lsb(i + 1);
            if j < pairs.len() {
                pairs[j].sum = pairs[j].sum.wrapping_add(&pairs[i].sum);
            }
        }
        FenwickTree(GenericFenwickTree {
            id: I::zero(),
            pairs,
            f: WrappingAdd::wrapping_add,
        })
    }
}

impl<I: PrimInt + WrappingAdd, const N: usize> From<[I; N]> for FenwickTree<I> {
    fn from(array: [I; N]) -> Self {
        FenwickTree(GenericFenwickTree::from_array(
            I::zero(),
            WrappingAdd::wrapping_add,
            array,
        ))
    }
}

impl<I: PrimInt + WrappingAdd> Default for FenwickTree<I> {
    fn default() -> Self {
        FenwickTree::new()
    }
}

impl<I: PrimInt> PartialEq for FenwickTree<I> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        for (i, j) in self.into_iter().zip(other.into_iter()) {
            if i != j {
                return false;
            }
        }
        true
    }
}

impl<I: PrimInt> Eq for FenwickTree<I> {}
