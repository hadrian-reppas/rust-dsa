/// An implementation of the [radix sort](https://en.wikipedia.org/wiki/Radix_sort)
/// algorithm.
///
/// # Example
/// ```
/// use rust_dsa::radix_sort;
///
/// let mut ints = [42, 14, 2, 18, 33, 19, 21, 38];
/// radix_sort(&mut ints);
/// assert_eq!(&ints, &[2, 14, 18, 19, 21, 33, 38, 42]);
///
/// let mut random: Vec<_> = (0..100_000).map(|_| rand::random()).collect();
/// radix_sort(&mut random);
/// for i in 1..random.len() {
///     assert!(random[i - 1] <= random[i]);
/// }
/// ```
pub fn radix_sort(slice: &mut [usize]) {
    let mut scratch = slice.to_vec();
    for i in 0..(usize::BITS as usize / 16) {
        radix_pass(slice, &mut scratch, 16 * i);
        radix_pass(&mut scratch, slice, 16 * i + 8);
    }
}

fn radix_pass(input: &mut [usize], output: &mut [usize], offset: usize) {
    let mut counts = [0usize; 256];
    for num in input.iter() {
        let i = (*num >> offset) & 0xff;
        counts[i] += 1;
    }
    for i in 1..256 {
        counts[i] += counts[i - 1];
    }

    for i in (0..input.len()).rev() {
        let j = (input[i] >> offset) & 0xff;
        counts[j] -= 1;
        output[counts[j]] = input[i];
    }
}
