#![allow(dead_code)]

use std::cmp::Ord;

/// An implementation of the [insertion sort](https://en.wikipedia.org/wiki/Insertion_sort)
/// algorithm.
///
/// # Example
/// ```
/// use rust_dsa::insertion_sort;
///
/// let mut ints = vec![42, 14, 2, 18, 33, 19, 21, 38];
/// insertion_sort(ints.as_mut_slice());
/// assert_eq!(ints, vec![2, 14, 18, 19, 21, 33, 38, 42]);
///
/// let mut food = vec!["banana", "eggplant", "dragonfruit", "apple", "carrot"];
/// insertion_sort(food.as_mut_slice());
/// assert_eq!(food, vec!["apple", "banana", "carrot", "dragonfruit", "eggplant"]);
///
/// let mut range: Vec<_> = (0..1000).rev().collect();
/// insertion_sort(range.as_mut_slice());
/// assert_eq!(
///     range,
///     (0..1000).collect::<Vec<_>>()
/// );
/// ```
pub fn insertion_sort<T>(arr: &mut [T])
where
    T: Ord,
{
    for i in 1..arr.len() {
        let mut j = i;
        while j > 0 && arr[j - 1] > arr[j] {
            arr.swap(j - 1, j);
            j -= 1;
        }
    }
}
