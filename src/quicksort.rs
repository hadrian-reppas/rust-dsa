use crate::partition;
use std::cmp::Ord;

/// An implementation of the [quicksort](https://en.wikipedia.org/wiki/Quicksort)
/// algorithm.
///
/// # Example
/// ```
/// use rust_dsa::quicksort;
///
/// let mut ints = [42, 14, 2, 18, 33, 19, 21, 38];
/// quicksort(&mut ints);
/// assert_eq!(&ints, &[2, 14, 18, 19, 21, 33, 38, 42]);
///
/// let mut food = ["banana", "eggplant", "dragonfruit", "apple", "carrot"];
/// quicksort(&mut food);
/// assert_eq!(&food, &["apple", "banana", "carrot", "dragonfruit", "eggplant"]);
///
/// let mut random: Vec<i64> = (0..100_000).map(|_| rand::random()).collect();
/// quicksort(&mut random);
/// for i in 1..random.len() {
///     assert!(random[i - 1] <= random[i]);
/// }
/// ```
pub fn quicksort<T>(slice: &mut [T])
where
    T: Ord,
{
    if slice.len() > 1 {
        let pivot_index = partition(slice, 0);
        quicksort(&mut slice[..pivot_index]);
        quicksort(&mut slice[(pivot_index + 1)..]);
    }
}
