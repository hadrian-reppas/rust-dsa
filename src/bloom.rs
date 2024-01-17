use std::collections::hash_map::RandomState;
use std::hash::Hash;
use std::hash::{BuildHasher, Hasher};
use std::iter;
use std::marker::PhantomData;

/// A Bloom filter.
///
/// Note that the number of bits in the Bloom filter is 64 times `M` because
/// bits are stored in an array of [`u64`]'s.
///
/// # Example
/// ```
/// use rust_dsa::BloomFilter;
///
/// // First, we create a new Bloom filter.
/// let mut filter: BloomFilter<_, 32, 2> = BloomFilter::new();
///
/// // We can insert some values.
/// filter.insert('a');
/// filter.insert('b');
/// filter.insert('c');
///
/// // We can check if the set probably contains values.
/// assert!(filter.maybe_contains(&'a'));
/// assert!(filter.maybe_contains(&'b'));
/// assert!(filter.maybe_contains(&'c'));
///
/// // For values not in the set, we may get false positives
/// // assert!(!filter.maybe_contains(&'z'));
///
/// // We can estimate the false positive rate
/// assert!(filter.false_positive_rate() < 1e-5);
/// ```
#[derive(Clone)]
pub struct BloomFilter<T, const M: usize, const K: usize, S = RandomState> {
    bits: [u64; M],
    hash_builders: [S; K],
    _data: PhantomData<T>,
}

impl<T, const M: usize, const K: usize, S> BloomFilter<T, M, K, S> {
    /// Creates an empty Bloom filter.
    ///
    /// # Panics
    /// Panics if `M` or `K` is zero.
    pub fn new() -> Self
    where
        S: Default,
    {
        assert_ne!(M, 0);
        assert_ne!(K, 0);

        let hash_builders: Vec<_> = iter::repeat_with(S::default).take(K).collect();
        BloomFilter {
            bits: [0; M],
            hash_builders: hash_builders.try_into().ok().unwrap(),
            _data: PhantomData,
        }
    }

    /// Creates an empty Bloom filter which will use the given hash builders.
    ///
    /// # Panics
    /// Panics if `M` or `K` is zero.
    pub fn with_hashers(hash_builders: [S; K]) -> Self {
        assert_ne!(M, 0);
        assert_ne!(K, 0);

        BloomFilter {
            bits: [0; M],
            hash_builders,
            _data: PhantomData,
        }
    }

    /// Checks if a Bloom filter is empty (i.e., if all the bits are zero).
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BloomFilter;
    ///
    /// let mut filter: BloomFilter::<_, 4, 2> = BloomFilter::new();
    /// assert!(filter.is_empty());
    ///
    /// filter.insert(1);
    /// assert!(!filter.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.bits.iter().all(|b| *b == 0)
    }

    /// Sets all the bits to zero.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BloomFilter;
    ///
    /// let mut filter: BloomFilter::<_, 8, 4> = "hello".chars().collect();
    /// assert!(!filter.is_empty());
    ///
    /// filter.clear();
    /// assert!(filter.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.bits = [0; M];
    }

    /// Counts the number of set bits in the Bloom filter.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BloomFilter;
    ///
    /// let mut filter: BloomFilter::<_, 8, 4> = BloomFilter::from([1, 2, 3]);
    /// assert!(filter.count_ones() > 0);
    ///
    /// filter.clear();
    /// assert_eq!(filter.count_ones(), 0);
    /// ```
    pub fn count_ones(&self) -> usize {
        self.bits.iter().map(|b| b.count_ones() as usize).sum()
    }

    /// Estimates the [false positive rate](https://en.wikipedia.org/wiki/Bloom_filter#Probability_of_false_positives)
    /// of this Bloom filter if it had `n` elements in it.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BloomFilter;
    ///
    /// let filter: BloomFilter<char, 8, 4> = BloomFilter::new();
    ///
    /// let expected = 0.15966130015118526;
    /// assert!((filter.epsilon(128) - expected).abs() < 1e-10);
    /// ```
    pub fn epsilon(&self, n: usize) -> f64 {
        let k = K as f64;
        let m = M as f64 * 64.0;
        let n = n as f64;
        (1.0 - (-k * n / m).exp()).powf(k)
    }

    /// Estimates the [false positive rate](https://en.wikipedia.org/wiki/Bloom_filter#Probability_of_false_positives)
    /// of this Bloom filter based on how many bits are set.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BloomFilter;
    ///
    /// let filter: BloomFilter<_, 8, 2> = "abcdefgh".chars().collect();
    ///
    /// let expected = 0.0009765625;
    /// assert!((filter.false_positive_rate() - expected) < 1e-10);
    /// ```
    pub fn false_positive_rate(&self) -> f64 {
        let k = K as f64;
        let m = M as f64 * 64.0;
        let x = self.count_ones() as f64;
        (x / m).powf(k)
    }

    /// Estimates the [number of items](https://en.wikipedia.org/wiki/Bloom_filter#Approximating_the_number_of_items_in_a_Bloom_filter)
    /// in this Bloom filter based on how many bits are set.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BloomFilter;
    ///
    /// let filter: BloomFilter<_, 16, 4> = BloomFilter::from(["foo", "bar", "baz"]);
    ///
    /// assert_eq!(filter.approx_len().round(), 3.0);
    /// ```
    pub fn approx_len(&self) -> f64 {
        let k = K as f64;
        let m = M as f64 * 64.0;
        let x = self.count_ones() as f64;
        -m * (1.0 - x / m).ln() / k
    }
}

impl<T, const M: usize, const K: usize, S> BloomFilter<T, M, K, S>
where
    T: Hash,
    S: BuildHasher,
{
    /// Inserts a value into the Bloom filter.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BloomFilter;
    ///
    /// let mut filter: BloomFilter<_, 10, 4> = BloomFilter::new();
    ///
    /// assert!(!filter.maybe_contains(&1)); // guaranteed to return false
    ///
    /// filter.insert(1);
    /// filter.insert(2);
    /// filter.insert(3);
    ///
    /// // guaranteed to return true
    /// assert!(filter.maybe_contains(&1));
    /// assert!(filter.maybe_contains(&2));
    /// assert!(filter.maybe_contains(&3));
    ///
    /// // filter.maybe_contains(4); // may return true or false
    /// ```
    pub fn insert(&mut self, value: T) {
        for hash_builder in &self.hash_builders {
            let mut hasher = hash_builder.build_hasher();
            value.hash(&mut hasher);
            let hash = hasher.finish() % (64 * M as u64);
            let (index, bit) = (hash / 64, hash % 64);
            self.bits[index as usize] |= 1 << bit;
        }
    }

    /// Queries the Bloom filter for a given value.
    ///
    /// If the Bloom filter contains the value, this function is guaranteed to
    /// return `true`, but it may return false positives.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BloomFilter;
    ///
    /// let mut filter: BloomFilter<_, 8, 2> = BloomFilter::new();
    /// assert!(!filter.maybe_contains(&1));
    ///
    /// filter.insert(1);
    /// assert!(filter.maybe_contains(&1));
    /// ```
    pub fn maybe_contains(&mut self, value: &T) -> bool {
        for hash_builder in &self.hash_builders {
            let mut hasher = hash_builder.build_hasher();
            value.hash(&mut hasher);
            let hash = hasher.finish() % (64 * M as u64);
            let (index, bit) = (hash / 64, hash % 64);
            if self.bits[index as usize] & 1 << bit == 0 {
                return false;
            }
        }
        true
    }
}

impl<T, const M: usize, const K: usize, S> Extend<T> for BloomFilter<T, M, K, S>
where
    T: Hash,
    S: BuildHasher + Default,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for value in iter {
            self.insert(value);
        }
    }
}

impl<T, const M: usize, const K: usize, S> FromIterator<T> for BloomFilter<T, M, K, S>
where
    T: Hash,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut filter = BloomFilter::new();
        for value in iter {
            filter.insert(value);
        }
        filter
    }
}

impl<T, const M: usize, const K: usize, S, const N: usize> From<[T; N]> for BloomFilter<T, M, K, S>
where
    T: Hash,
    S: BuildHasher + Default,
{
    fn from(array: [T; N]) -> Self {
        array.into_iter().collect()
    }
}

impl<T, const M: usize, const K: usize, S> Default for BloomFilter<T, M, K, S>
where
    S: Default,
{
    fn default() -> Self {
        BloomFilter::new()
    }
}
