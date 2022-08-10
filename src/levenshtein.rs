use std::{cmp, iter, mem};

/// Returns the [Levenshtein distance](https://en.wikipedia.org/wiki/Levenshtein_distance)
/// between two slices.
///
/// # Example
/// ```
/// use rust_dsa::edit_distance;
///
/// let a = [9, 4, 8, 5, 9, 3, 8, 5];
/// let b = [1, 9, 4, 8, 3, 5];
/// assert_eq!(edit_distance(&a, &b), 4);
///
/// let kitten = ['k', 'i', 't', 't', 'e', 'n'];
/// let sitting = ['s', 'i', 't', 't', 'i', 'n', 'g'];
/// assert_eq!(edit_distance(&kitten, &sitting), 3);
///
/// let x = ["foo", "bar", "baz", "baz"];
/// let y = ["baz", "foo", "bar", "baz"];
/// assert_eq!(edit_distance(&x, &y), 2);
/// ```
pub fn edit_distance<T>(a: &[T], b: &[T]) -> usize
where
    T: PartialEq,
{
    if a.is_empty() {
        return b.len();
    } else if b.is_empty() {
        return a.len();
    }

    let mut old_row: Vec<_> = (0..(b.len() + 1)).collect();
    let mut new_row: Vec<_> = iter::repeat(0).take(b.len() + 1).collect();

    #[allow(clippy::needless_range_loop)]
    for i in 0..a.len() {
        new_row[0] = i + 1;
        for j in 0..b.len() {
            let ne = a[i] != b[j];
            new_row[j + 1] = min(new_row[j] + 1, old_row[j + 1] + 1, old_row[j] + ne as usize);
        }
        mem::swap(&mut new_row, &mut old_row);
    }

    old_row[b.len()]
}

/// Returns the [Levenshtein distance](https://en.wikipedia.org/wiki/Levenshtein_distance)
/// between two [`str`]s.
///
/// # Example
/// ```
/// use rust_dsa::str_distance;
///
/// assert_eq!(str_distance("kitten", "sitting"), 3);
///
/// assert_eq!(str_distance("intention", "execution"), 5);
///
/// assert_eq!(str_distance("sail", "wail"), 1);
///
/// assert_eq!(str_distance("Levenshtein", "Levenshtein"), 0);
///
/// assert_eq!(str_distance("", "foo"), 3);
/// ```
pub fn str_distance(a: &str, b: &str) -> usize {
    let a: Vec<_> = a.chars().collect();
    let b: Vec<_> = b.chars().collect();

    edit_distance(&a, &b)
}

fn min<T>(a: T, b: T, c: T) -> T
where
    T: Ord,
{
    cmp::min(cmp::min(a, b), c)
}
