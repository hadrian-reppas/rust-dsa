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
    let copies: Vec<_> = slice.iter().map(CursedCell::new).collect();
    let sorted = mergesort_impl(&copies);
    unsafe { std::ptr::copy(sorted.as_ptr() as *const T, slice.as_mut_ptr(), slice.len()) }
}

fn mergesort_impl<T>(slice: &[CursedCell<T>]) -> Vec<CursedCell<T>>
where
    T: Ord,
{
    if slice.len() < 2 {
        return slice.to_vec();
    }

    let (left, right) = slice.split_at(slice.len() / 2);
    let left = mergesort_impl(left);
    let right = mergesort_impl(right);

    let mut out = Vec::with_capacity(slice.len());
    let (mut l, mut r) = (0, 0);

    while l < left.len() && r < right.len() {
        if left[l] > right[r] {
            out.push(right[r].clone());
            r += 1;
        } else {
            out.push(left[l].clone());
            l += 1;
        }
    }

    while l < left.len() {
        out.push(left[l].clone());
        l += 1;
    }

    while r < right.len() {
        out.push(right[r].clone());
        r += 1;
    }

    out
}

#[repr(transparent)]
#[derive(PartialEq, Eq, PartialOrd, Ord)]
struct CursedCell<T>(ManuallyDrop<T>);

impl<T> CursedCell<T> {
    fn new(val: &T) -> Self {
        CursedCell(ManuallyDrop::new(unsafe {
            std::ptr::read(val as *const T)
        }))
    }
}

impl<T> Clone for CursedCell<T> {
    fn clone(&self) -> Self {
        let val: &T = &self.0;
        let inner = unsafe { std::ptr::read(val as *const T) };
        CursedCell(ManuallyDrop::new(inner))
    }
}
