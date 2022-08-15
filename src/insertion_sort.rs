/// An implementation of the [insertion sort](https://en.wikipedia.org/wiki/Insertion_sort)
/// algorithm.
///
/// # Example
/// ```
/// use rust_dsa::insertion_sort;
///
/// let mut ints = [42, 14, 2, 18, 33, 19, 21, 38];
/// insertion_sort(&mut ints);
/// assert_eq!(&ints, &[2, 14, 18, 19, 21, 33, 38, 42]);
///
/// let mut food = ["banana", "eggplant", "dragonfruit", "apple", "carrot"];
/// insertion_sort(&mut food);
/// assert_eq!(&food, &["apple", "banana", "carrot", "dragonfruit", "eggplant"]);
///
/// let mut random: Vec<i64> = (0..1_000).map(|_| rand::random()).collect();
/// insertion_sort(&mut random);
/// for i in 1..random.len() {
///     assert!(random[i - 1] <= random[i]);
/// }
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
