use std::cmp::Ordering;

/// Returns a reference to the `k`<sup>th</sup> smallest element in the slice.
///
/// This uses the [quickselect](https://en.wikipedia.org/wiki/Quickselect)
/// algorithm.
///
/// # Panics
/// Panics if `k` is out of bounds.
///
/// # Example
/// ```
/// use rust_dsa::select;
///
/// let nums = [80, 61, 36, 70, 53, 54, 59, 17, 76, 49];
///
/// assert_eq!(select(&nums, 4), &54);
/// assert_eq!(select(&nums, 6), &61);
/// assert_eq!(select(&nums, 0), &17);
/// assert_eq!(select(&nums, 9), &80);
///
/// let strs = ["foo", "bar", "baz"];
///
/// assert_eq!(select(&strs, 0), &"bar");
/// assert_eq!(select(&strs, 1), &"baz");
/// assert_eq!(select(&strs, 2), &"foo");
/// ```
pub fn select<T>(slice: &[T], k: usize) -> &T
where
    T: Ord,
{
    let mut refs: Vec<_> = slice.iter().collect();
    select_in_place(&mut refs, k)
}

/// Returns a reference to the `k`<sup>th</sup> smallest element in the slice.
///
/// The elements in the slice may get rearanged according to the
/// [quickselect](https://en.wikipedia.org/wiki/Quickselect) algorithm.
///
/// # Panics
/// Panics if `k` is out of bounds.
///
/// # Example
/// ```
/// use rust_dsa::select;
///
/// let mut nums = [80, 61, 36, 70, 53, 54, 59, 17, 76, 49];
///
/// assert_eq!(select(&mut nums, 4), &54);
/// assert_eq!(select(&mut nums, 6), &61);
/// assert_eq!(select(&mut nums, 0), &17);
/// assert_eq!(select(&mut nums, 9), &80);
///
/// let mut strs = ["foo", "bar", "baz"];
///
/// assert_eq!(select(&mut strs, 0), &"bar");
/// assert_eq!(select(&mut strs, 1), &"baz");
/// assert_eq!(select(&mut strs, 2), &"foo");
/// ```
pub fn select_in_place<T>(slice: &mut [T], k: usize) -> &mut T
where
    T: Ord,
{
    if k >= slice.len() {
        panic!(
            "index {k} is out of bounds for slice of length {}",
            slice.len()
        );
    } else {
        select_rec(slice, k)
    }
}

fn select_rec<T>(slice: &mut [T], k: usize) -> &mut T
where
    T: Ord,
{
    // we could choose something other than 0 for the pivot index...
    let pivot_index = partition(slice, 0);

    match k.cmp(&pivot_index) {
        Ordering::Equal => &mut slice[k],
        Ordering::Less => select_rec(&mut slice[..pivot_index], k),
        Ordering::Greater => select_rec(&mut slice[(pivot_index + 1)..], k - pivot_index - 1),
    }
}

/// Partitions the slice around the element at `pivot_index`.
///
/// Returns the pivot's new index.
///
/// # Panics
/// Panics if `pivot_index` is out of bounds.
///
/// # Example
/// ```
/// use rust_dsa::partition;
///
/// let mut nums = [4, 10, 3, 0, 2, 6, 7, 1, 5, 8, 9];
///
/// let pivot_index = partition(&mut nums, 0);
///
/// assert_eq!(pivot_index, 4);
///
/// for &num in &nums[..pivot_index] {
///     assert!(num < nums[pivot_index]);
/// }
///
/// for &num in &nums[(pivot_index + 1)..] {
///     assert!(nums[pivot_index] <= num);
/// }
///
///
/// let mut nums: Vec<i32> = (0..10_000).map(|_| rand::random()).collect();
///
/// assert!(nums.len() > 0);
///
/// let pivot_index = partition(&mut nums, 0);
/// let pivot = nums[pivot_index];
///
/// for &num in &nums[0..pivot_index] {
///     assert!(num < pivot);
/// }
///
/// for &num in &nums[(pivot_index + 1)..] {
///     assert!(num >= pivot);
/// }
///
/// let mut single = [1];
/// assert_eq!(partition(&mut single, 0), 0);
/// ```
pub fn partition<T>(slice: &mut [T], pivot_index: usize) -> usize
where
    T: Ord,
{
    if pivot_index >= slice.len() {
        panic!(
            "pivot index {pivot_index} is out of bounds for slice of length {}",
            slice.len()
        );
    } else if slice.len() == 1 {
        return 0;
    }

    let mut start = usize::MAX;
    let mut end = slice.len() - 1;

    slice.swap(pivot_index, end);

    loop {
        let pivot = slice.last().unwrap();

        start = start.wrapping_add(1);
        while start < end && &slice[start] < pivot {
            start += 1;
        }

        assert!(end > 0);
        end -= 1;
        while start < end && &slice[end] >= pivot {
            assert!(end > 0);
            end -= 1;
        }

        if start < end {
            slice.swap(start, end);
        } else {
            slice.swap(start, slice.len() - 1);
            return start;
        }
    }
}
