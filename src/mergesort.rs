use std::cmp::Ordering;
use std::mem::ManuallyDrop;

/// An implementation of the [mergesort](https://en.wikipedia.org/wiki/Merge_sort)
/// algorithm.
///
/// # Example
/// ```
/// use rust_dsa::mergesort;
///
/// let mut ints = [42, 14, 2, 18, 33, 19, 21, 38];
/// mergesort(&mut ints);
/// assert_eq!(&ints, &[2, 14, 18, 19, 21, 33, 38, 42]);
///
/// let mut food = ["banana", "eggplant", "dragonfruit", "apple", "carrot"];
/// mergesort(&mut food);
/// assert_eq!(&food, &["apple", "banana", "carrot", "dragonfruit", "eggplant"]);
///
/// let mut random: Vec<i64> = (0..100_000).map(|_| rand::random()).collect();
/// mergesort(&mut random);
/// for i in 1..random.len() {
///     assert!(random[i - 1] <= random[i]);
/// }
/// ```
pub fn mergesort<T>(slice: &mut [T])
where
    T: Ord,
{
    let indices: Vec<_> = (0..slice.len()).collect();
    let indices = mergesort_impl(&indices, &|a, b| slice[a].cmp(&slice[b]));

    let mut copies = Vec::with_capacity(slice.len());
    unsafe {
        for ptr in slice.iter().map(|r| r as *const T) {
            copies.push(ManuallyDrop::new(ptr.read()));
        }
        for (i, index) in indices.into_iter().enumerate() {
            let ptr = &mut slice[i] as *mut T;
            ptr.write(ManuallyDrop::take(&mut copies[index]));
        }
    }
}

fn mergesort_impl(indices: &[usize], cmp: &impl Fn(usize, usize) -> Ordering) -> Vec<usize> {
    if indices.len() < 2 {
        return indices.to_vec();
    }

    let (left, right) = indices.split_at(indices.len() / 2);
    let left = mergesort_impl(left, cmp);
    let right = mergesort_impl(right, cmp);

    let mut out = Vec::with_capacity(indices.len());
    let (mut l, mut r) = (0, 0);

    while l < left.len() && r < right.len() {
        if cmp(left[l], right[r]) == Ordering::Greater {
            out.push(right[r]);
            r += 1;
        } else {
            out.push(left[l]);
            l += 1;
        }
    }

    while l < left.len() {
        out.push(left[l]);
        l += 1;
    }

    while r < right.len() {
        out.push(right[r]);
        r += 1;
    }

    out
}
