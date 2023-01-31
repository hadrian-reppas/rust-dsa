use std::cmp::Ordering;

use num_traits::int::PrimInt;

type Point<T> = (T, T);

/// Returns a subset of the input points representing their convex hull.
///
/// Points are returned in counterclockwise order, starting with the point
/// that has the smallest y value (and smallest x value if there is a tie).
///
/// This function uses [Graham's scan](https://en.wikipedia.org/wiki/Graham_scan)
/// to find the convex hull. To keep things generic and simple, this function
/// takes 2-tulples of integers.
///
/// # Panics
/// Panics if any of the calculations overflow and debug assertions are on.
///
/// # Example
/// ```
/// use rust_dsa::graham_scan;
///
/// let points = [
///     (6, 0), (-4, 10), (-9, -6), (-15, -6), (15, 14), (1, -16), (3, -19), (17, 11),
///     (5, -7), (2, 3), (10, 3), (20, 3), (-8, 1), (20, -13), (-10, 1), (8, 16),
/// ];
/// let expected_hull = [(3, -19), (20, -13), (20, 3), (17, 11), (15, 14), (8, 16), (-4, 10), (-15, -6)];
///
/// assert_eq!(graham_scan(&points), expected_hull.to_vec());
///
///
/// let points = [(0, 0), (1, 2), (4, 0), (2, 4), (0, 8)];
/// let expected_hull = [(0, 0), (4, 0), (0, 8)];
///
/// assert_eq!(graham_scan(&points), expected_hull.to_vec());
/// ```
pub fn graham_scan<I>(points: &[Point<I>]) -> Vec<Point<I>>
where
    I: PrimInt,
{
    let (start_index, start) = match points
        .iter()
        .enumerate()
        .min_by(|(_, a), (_, b)| a.flip().cmp(&b.flip()))
    {
        Some((index, start)) => (index, *start),
        None => return Vec::new(),
    };

    let mut points: Vec<_> = points.to_vec();

    points.swap_remove(start_index);

    points.sort_by(|&a, &b| match get_orientation(start, a, b) {
        Orientation::Counterclockwise => Ordering::Less,
        Orientation::Clockwise => Ordering::Greater,
        Orientation::Collinear => square_dist(start, a).cmp(&square_dist(start, b)),
    });

    points.dedup_by(|a, b| get_orientation(start, *a, *b) == Orientation::Collinear);

    let mut stack = vec![start];

    for point in points {
        while !counterclockwise(&stack, point) {
            stack.pop();
        }
        stack.push(point);
    }

    stack
}

fn counterclockwise<I>(points: &Vec<Point<I>>, point: Point<I>) -> bool
where
    I: PrimInt,
{
    if points.len() > 1 {
        let a = points[points.len() - 2];
        let b = points[points.len() - 1];
        get_orientation(a, b, point) == Orientation::Counterclockwise
    } else {
        true
    }
}

#[derive(PartialEq)]
enum Orientation {
    Counterclockwise,
    Clockwise,
    Collinear,
}

fn get_orientation<I>(a: Point<I>, b: Point<I>, c: Point<I>) -> Orientation
where
    I: PrimInt,
{
    let p = (b.0 - a.0) * (c.1 - a.1);
    let q = (c.0 - a.0) * (b.1 - a.1);

    match p.cmp(&q) {
        Ordering::Equal => Orientation::Collinear,
        Ordering::Greater => Orientation::Counterclockwise,
        Ordering::Less => Orientation::Clockwise,
    }
}

fn square_dist<I>(a: Point<I>, b: Point<I>) -> I
where
    I: PrimInt,
{
    let dx = a.0 - b.0;
    let dy = a.1 - b.1;

    dx * dx + dy * dy
}

trait Flip {
    fn flip(&self) -> Self;
}

impl<I> Flip for Point<I>
where
    I: Copy,
{
    fn flip(&self) -> Point<I> {
        let &(x, y) = self;
        (y, x)
    }
}
