use std::{fmt::Debug, ops::RangeBounds, rc::Rc};

const ARITY: usize = 4;

/// An immutable vector implementation with efficient edits/clones.
///
/// Internally, the vector is represented like a [finger tree](https://en.wikipedia.org/wiki/Finger_tree).
/// Each interal node holds up to 32 children, and each leaf node holds up to 32 values.
/// Most operations take *O*(log<sub>32</sub> *n*) time, but log<sub>32</sub> grows
/// *really* slowly (log<sub>32</sub>(`usize::MAX`) < 13), so in pracice they are
/// basically *O*(1).
///
/// # Example
/// ```
/// use rust_dsa::ImmutableVector;
///
/// let vector = ImmutableVector::new();
///
/// // Each time we push a value, the original vector doesn't change.
/// let vector1 = vector.push(1);
/// let vector2 = vector1.push(2);
/// let vector3 = vector2.push(3);
///
/// assert_eq!(vector, ImmutableVector::from([]));
/// assert_eq!(vector1, ImmutableVector::from([1]));
/// assert_eq!(vector2, ImmutableVector::from([1, 2]));
/// assert_eq!(vector3, ImmutableVector::from([1, 2, 3]));
///
/// // We can also remove elements.
/// let vector4 = vector3.remove(1);
/// assert_eq!(vector4, ImmutableVector::from([1, 3]));
///
/// // And join two vectors.
/// let vector5 = vector4.join(&vector2);
/// assert_eq!(vector5, ImmutableVector::from([1, 3, 1, 2]));
///
/// // We can iterate over vectors.
/// for x in vector5 {
///     // x has type Rc<i32>
///     println!("{x}");
/// }
///
/// for x in &vector4 {
///     // x has type &i32
///     println!("{x}");
/// }
///
/// // And create vectors from iterators.
/// let vector6: ImmutableVector<_> = ('a'..='z').collect();
/// assert_eq!(vector6.len(), 26);
/// ```
///
/// # Runtime complexity
///
/// | Operation                  | Runtime Complexity        |
/// | -------------------------- | ------------------------- |
/// | [ImmutableVector::push]    | *O*(log<sub>32</sub> *n*) |
/// | [ImmutableVector::remove]  | *O*(log<sub>32</sub> *n*) |
/// | [ImmutableVector::replace] | *O*(log<sub>32</sub> *n*) |
/// | [ImmutableVector::join]    | *O*(1)                    |
/// | [ImmutableVector::clone]   | *O*(1)                    |
#[derive(Clone)]
pub struct ImmutableVector<T> {
    item: Rc<Item<T>>,
}

impl<T> ImmutableVector<T> {
    /// Creates an empty vector.
    pub fn new() -> Self {
        ImmutableVector {
            item: Rc::new(Item::new()),
        }
    }

    /// Returns a reference to the element at `index` or None if out of bounds.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::ImmutableVector;
    ///
    /// let vector = ImmutableVector::from([1, 2, 3, 4, 5, 6, 7]);
    ///
    /// assert_eq!(vector.get(3), Some(&4));
    /// assert_eq!(vector.get(10), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        self.item.get(index)
    }

    /// Returns a new vector that contains the elements in the specified range.
    ///
    /// # Panics
    /// Panics if the starting point is greater than the end point or if the end
    /// point is greater than the length of the vector.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::ImmutableVector;
    ///
    /// let racecar: ImmutableVector<char> = "racecar".chars().collect();
    /// let car: ImmutableVector<char> = "car".chars().collect();
    ///
    /// assert_eq!(racecar.range(4..), car);
    /// ```
    pub fn range<R>(&self, range: R) -> ImmutableVector<T>
    where
        R: RangeBounds<usize>,
    {
        self.get_range(range)
            .map(|i| self.get_rc(i))
            .map(Option::unwrap)
            .collect()
    }

    /// Returns an [Rc] that contains to the element at `index` or None if out of bounds.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::ImmutableVector;
    /// use std::rc::Rc;
    ///
    /// let vector = ImmutableVector::from([1, 2, 3, 4, 5, 6, 7]);
    ///
    /// assert_eq!(vector.get_rc(3), Some(Rc::new(4)));
    /// assert_eq!(vector.get_rc(10), None);
    /// ```
    pub fn get_rc(&self, index: usize) -> Option<Rc<T>> {
        self.item.get_rc(index)
    }

    /// Returns a *new* vector with the value appended.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::ImmutableVector;
    ///
    /// let vector = ImmutableVector::new();
    /// let vector = vector.push(1);
    /// let vector = vector.push(2);
    /// let vector = vector.push(3);
    ///
    /// assert_eq!(vector, ImmutableVector::from([1, 2, 3]));
    /// ```
    pub fn push(&self, value: T) -> ImmutableVector<T> {
        ImmutableVector {
            item: Rc::new(self.item.push(value)),
        }
    }

    /// Returns a *new* vector without the value at `index`.
    ///
    /// # Panics
    /// Panics if `index >= len`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::ImmutableVector;
    ///
    /// let feast: ImmutableVector<char> = "feast".chars().collect();
    ///
    /// let east = feast.remove(0);
    ///
    /// assert_eq!(
    ///     east,
    ///     ImmutableVector::from(['e', 'a', 's', 't'])
    /// );
    /// ```
    pub fn remove(&self, index: usize) -> ImmutableVector<T> {
        ImmutableVector {
            item: Rc::new(self.item.remove(index)),
        }
    }

    /// Returns a *new* vector with `value` at position `index`.
    ///
    /// # Panics
    /// Panics if `index >= len`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::ImmutableVector;
    ///
    /// let unseasonably: ImmutableVector<char> = "unseasonably".chars().collect();
    /// let unreasonably: ImmutableVector<char> = "unreasonably".chars().collect();
    ///
    /// assert_eq!(
    ///     unseasonably.replace(2, 'r'),
    ///     unreasonably
    /// );
    /// ```
    pub fn replace(&self, index: usize, value: T) -> ImmutableVector<T> {
        ImmutableVector {
            item: Rc::new(self.item.replace(index, value)),
        }
    }

    /// Returns a *new* vector that contains the elements in `self`
    /// followed by the elements in `other`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::ImmutableVector;
    ///
    /// let fruits = ImmutableVector::from(["apple", "banana"]);
    /// let veggies = ImmutableVector::from(["asparagus", "broccoli"]);
    ///
    /// let both = fruits.join(&veggies);
    ///
    /// assert_eq!(
    ///     both,
    ///     ImmutableVector::from(["apple", "banana", "asparagus", "broccoli"])
    /// );
    /// ```
    pub fn join(&self, other: &ImmutableVector<T>) -> ImmutableVector<T> {
        ImmutableVector {
            item: Rc::new(Item::new_internal(
                vec![self.item.clone(), other.item.clone()],
                self.len() + other.len(),
            )),
        }
    }

    /// Returns the length of the vector.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::ImmutableVector;
    ///
    /// let empty: ImmutableVector<i32> = ImmutableVector::new();
    /// let forty: ImmutableVector<i32> = (0..40).collect();
    ///
    /// assert_eq!(empty.len(), 0);
    /// assert_eq!(forty.len(), 40);
    /// ```
    pub fn len(&self) -> usize {
        self.item.len()
    }

    /// Returns `true` if the vector is empty.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::ImmutableVector;
    ///
    /// let empty: ImmutableVector<i32> = ImmutableVector::new();
    /// let forty: ImmutableVector<i32> = (0..40).collect();
    ///
    /// assert!(empty.is_empty());
    /// assert!(!forty.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.item.is_empty()
    }

    fn get_range<R>(&self, range: R) -> std::ops::Range<usize>
    where
        R: RangeBounds<usize>,
    {
        let end = match range.end_bound() {
            std::ops::Bound::Included(end) => end + 1,
            std::ops::Bound::Excluded(end) => *end,
            std::ops::Bound::Unbounded => self.len(),
        };
        if end > self.len() {
            panic!(
                "range's end point is {end} but the vector has len {}",
                self.len()
            );
        }
        let start = match range.start_bound() {
            std::ops::Bound::Included(start) => *start,
            std::ops::Bound::Unbounded => 0,
            std::ops::Bound::Excluded(_) => unreachable!(), // I think?
        };
        if start > end {
            panic!("range's start point ({start}) is greater than its end point {end}");
        }
        start..end
    }
}

impl<T> Default for ImmutableVector<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> FromIterator<Rc<T>> for ImmutableVector<T> {
    fn from_iter<A: IntoIterator<Item = Rc<T>>>(iter: A) -> Self {
        let mut items = Vec::new();
        let mut piter = iter.into_iter().peekable();
        while piter.peek().is_some() {
            let mut values = Vec::new();
            for _ in 0..ARITY {
                match piter.next() {
                    Some(value) => values.push(value),
                    None => break,
                }
            }
            items.push(Item::new_leaf(values));
        }
        if items.is_empty() {
            return ImmutableVector::new();
        }
        while items.len() != 1 {
            let mut new_items = Vec::new();
            let mut piter = items.into_iter().peekable();
            while piter.peek().is_some() {
                let mut children = Vec::new();
                let mut len = 0;
                for _ in 0..ARITY {
                    match piter.next() {
                        Some(child) => {
                            len += child.len();
                            children.push(Rc::new(child));
                        }
                        None => break,
                    }
                }
                new_items.push(Item::new_internal(children, len));
            }
            items = new_items;
        }
        ImmutableVector {
            item: Rc::new(items.pop().unwrap()),
        }
    }
}

impl<T> FromIterator<T> for ImmutableVector<T> {
    fn from_iter<A: IntoIterator<Item = T>>(iter: A) -> Self {
        iter.into_iter().map(Rc::new).collect()
    }
}

impl<T> Debug for ImmutableVector<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (i, value) in self.into_iter().enumerate() {
            if i == 0 {
                write!(f, "{:?}", value)?;
            } else {
                write!(f, ", {:?}", value)?;
            }
        }
        write!(f, "]")
    }
}

impl<T> PartialEq for ImmutableVector<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() == other.len() {
            for (s, o) in self.into_iter().zip(other) {
                if s != o {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
}

impl<T> Eq for ImmutableVector<T> where T: Eq {}

impl<T, const N: usize> From<[T; N]> for ImmutableVector<T> {
    fn from(arr: [T; N]) -> Self {
        arr.into_iter().collect()
    }
}

impl<T> From<Vec<T>> for ImmutableVector<T> {
    fn from(vec: Vec<T>) -> Self {
        vec.into_iter().collect()
    }
}

impl<T> IntoIterator for ImmutableVector<T> {
    type IntoIter = IntoIter<T>;
    type Item = Rc<T>;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter { vector: self, i: 0 }
    }
}

pub struct IntoIter<T> {
    vector: ImmutableVector<T>,
    i: usize,
}

impl<T> Iterator for IntoIter<T> {
    type Item = Rc<T>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.i < self.vector.len() {
            self.i += 1;
            self.vector.get_rc(self.i - 1)
        } else {
            None
        }
    }
}

impl<'a, T> IntoIterator for &'a ImmutableVector<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;
    fn into_iter(self) -> Self::IntoIter {
        Iter { vector: self, i: 0 }
    }
}

pub struct Iter<'a, T: 'a> {
    vector: &'a ImmutableVector<T>,
    i: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.i < self.vector.len() {
            self.i += 1;
            self.vector.get(self.i - 1)
        } else {
            None
        }
    }
}

enum Item<T> {
    Internal {
        children: Vec<Rc<Item<T>>>,
        len: usize,
    },
    Leaf {
        values: Vec<Rc<T>>,
    },
}

impl<T> Item<T> {
    fn new() -> Item<T> {
        Self::new_leaf(Vec::new())
    }

    fn new_internal(children: Vec<Rc<Item<T>>>, len: usize) -> Item<T> {
        Self::Internal { children, len }
    }

    fn new_leaf(values: Vec<Rc<T>>) -> Item<T> {
        Self::Leaf { values }
    }

    fn nested_leaf(value: Rc<T>, depth: usize) -> Item<T> {
        let mut item = Self::new_leaf(vec![value]);
        for _ in 0..depth {
            item = Self::new_internal(vec![Rc::new(item)], 1);
        }
        item
    }

    fn get(&self, index: usize) -> Option<&T> {
        match self {
            Self::Internal { children, .. } => {
                let mut index = index;
                for child in children {
                    if index < child.len() {
                        return child.get(index);
                    }
                    index -= child.len();
                }
                None
            }
            Self::Leaf { values } => values.get(index).map(Rc::as_ref),
        }
    }

    fn get_rc(&self, index: usize) -> Option<Rc<T>> {
        match self {
            Self::Internal { children, .. } => {
                let mut index = index;
                for child in children {
                    if index < child.len() {
                        return child.get_rc(index);
                    }
                    index -= child.len();
                }
                None
            }
            Self::Leaf { values } => values.get(index).map(Rc::clone),
        }
    }

    fn push(&self, value: T) -> Item<T> {
        self.push_rec(value, self.depth())
    }

    fn push_rec(&self, value: T, depth: usize) -> Item<T> {
        match self {
            Self::Leaf { values } => {
                if values.len() == ARITY {
                    Self::new_internal(
                        vec![
                            Rc::new(Self::new_leaf(values.to_vec())),
                            Rc::new(Self::new_leaf(vec![Rc::new(value)])),
                        ],
                        ARITY + 1,
                    )
                } else {
                    Self::Leaf {
                        values: values.iter().cloned().chain(Some(Rc::new(value))).collect(),
                    }
                }
            }
            Self::Internal { children, len } => {
                if children
                    .last()
                    .map(Rc::as_ref)
                    .map(Self::can_append)
                    .unwrap_or(true)
                {
                    match children.split_last() {
                        None => Item::new_leaf(vec![Rc::new(value)]),
                        Some((last, others)) => Self::new_internal(
                            others
                                .iter()
                                .cloned()
                                .chain(Some(Rc::new(last.push_rec(value, depth.saturating_sub(1)))))
                                .collect(),
                            len + 1,
                        ),
                    }
                } else if children.len() < ARITY {
                    Self::new_internal(
                        children
                            .iter()
                            .cloned()
                            .chain(Some(Rc::new(Self::nested_leaf(Rc::new(value), depth))))
                            .collect(),
                        len + 1,
                    )
                } else {
                    Self::new_internal(
                        vec![
                            Rc::new(Self::new_internal(children.to_vec(), *len)),
                            Rc::new(Self::new_leaf(vec![Rc::new(value)])),
                        ],
                        len + 1,
                    )
                }
            }
        }
    }

    fn remove(&self, index: usize) -> Item<T> {
        if index >= self.len() {
            panic!(
                "index out of bounds: the len is {} but the index is {index}",
                self.len()
            );
        }
        self.remove_rec(index)
    }

    fn remove_rec(&self, index: usize) -> Item<T> {
        match self {
            Self::Internal { children, len } => {
                let mut new_children = Vec::with_capacity(children.len());
                let mut index = index;
                let mut citer = children.iter();
                for child in citer.by_ref() {
                    if index < child.len() {
                        new_children.push(Rc::new(child.remove_rec(index)));
                        break;
                    } else {
                        new_children.push(child.clone());
                    }
                    index -= child.len();
                }
                new_children.extend(citer.cloned());
                Self::new_internal(new_children, len - 1)
            }
            Self::Leaf { values } => Self::new_leaf(
                values
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != index)
                    .map(|(_, value)| value)
                    .cloned()
                    .collect(),
            ),
        }
    }

    fn replace(&self, index: usize, value: T) -> Item<T> {
        if index >= self.len() {
            panic!(
                "index out of bounds: the len is {} but the index is {index}",
                self.len()
            );
        }
        self.replace_rec(index, value)
    }

    fn replace_rec(&self, index: usize, value: T) -> Item<T> {
        let mut value = Some(value);
        match self {
            Self::Internal { children, len } => {
                let mut new_children = Vec::with_capacity(children.len());
                let mut index = index;
                let mut citer = children.iter();
                for child in citer.by_ref() {
                    if index < child.len() {
                        new_children.push(Rc::new(child.replace_rec(index, value.unwrap())));
                        break;
                    } else {
                        new_children.push(child.clone());
                    }
                    index -= child.len();
                }
                new_children.extend(citer.cloned());
                Self::new_internal(new_children, *len)
            }
            Self::Leaf { values } => Self::new_leaf(
                values
                    .iter()
                    .enumerate()
                    .map(|(i, old_value)| {
                        if i == index {
                            Rc::new(value.take().unwrap())
                        } else {
                            old_value.clone()
                        }
                    })
                    .collect(),
            ),
        }
    }

    fn len(&self) -> usize {
        match self {
            Self::Internal { len, .. } => *len,
            Self::Leaf { values } => values.len(),
        }
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn can_append(&self) -> bool {
        match self {
            Self::Internal { children, .. } => {
                if let Some(last) = children.last() {
                    children.len() < ARITY || last.can_append()
                } else {
                    true
                }
            }
            Self::Leaf { values } => values.len() < ARITY,
        }
    }

    fn depth(&self) -> usize {
        match self {
            Self::Internal { children, .. } => {
                children
                    .get(0)
                    .map(Rc::as_ref)
                    .map(Self::depth)
                    .unwrap_or(0)
                    + 1
            }
            Self::Leaf { .. } => 0,
        }
    }
}

#[cfg(test)]
mod test {
    use super::ImmutableVector;
    #[test]
    fn test() {
        let vector = ImmutableVector::new();
        // Each time we push a value, the original vector doesn't change.
        let vector1 = vector.push(1);
        let vector2 = vector1.push(2);
        let vector3 = vector2.push(3);

        println!("{:?}", vector);
        println!("{:?}", vector1);
        println!("{:?}", vector2);
        println!("{:?}", vector3);

        println!();

        let v: ImmutableVector<i32> = ImmutableVector::from([]);
        println!("{:?}", v);
        println!("{:?}", ImmutableVector::from([1]));
        println!("{:?}", ImmutableVector::from([1, 2]));
        println!("{:?}", ImmutableVector::from([1, 2, 3]));

        println!();

        let v = ImmutableVector::from([1, 2, 3, 4, 5, 6, 7]);
        println!("{:?}", v);
        println!("{:?}", v.remove(2));
    }
}
