/// An implementation of the [heapsort](https://en.wikipedia.org/wiki/Heapsort)
/// algorithm.
///
/// # Example
/// ```
/// use rust_dsa::heapsort;
///
/// let mut ints = [42, 14, 2, 18, 33, 19, 21, 38];
/// heapsort(&mut ints);
/// assert_eq!(&ints, &[2, 14, 18, 19, 21, 33, 38, 42]);
///
/// let mut food = ["banana", "eggplant", "dragonfruit", "apple", "carrot"];
/// heapsort(&mut food);
/// assert_eq!(&food, &["apple", "banana", "carrot", "dragonfruit", "eggplant"]);
///
/// let mut random: Vec<i64> = (0..100_000).map(|_| rand::random()).collect();
/// heapsort(&mut random);
/// for i in 1..random.len() {
///     assert!(random[i - 1] <= random[i]);
/// }
/// ```
pub fn heapsort<T>(slice: &mut [T])
where
    T: Ord,
{
    for i in (0..slice.len()).rev() {
        bubble_down(slice, i);
    }

    for i in 0..slice.len() {
        let to_process = slice.len() - i - 1;
        slice.swap(0, to_process);
        bubble_down(&mut slice[0..to_process], 0);
    }
}

fn bubble_down<T>(slice: &mut [T], mut index: usize)
where
    T: Ord,
{
    loop {
        // find the index of the biggest child
        let child1 = 2 * index + 1;
        let child2 = child1 + 1;
        let max_index = if child2 >= slice.len() || slice[child1] > slice[child2] {
            child1
        } else {
            child2
        };

        // if the item at `index` is smaller than its biggest child, swap the two
        if max_index < slice.len() && slice[index] < slice[max_index] {
            slice.swap(index, max_index);
            index = max_index;
        } else {
            break;
        }
    }
}
