use std::alloc::{alloc, dealloc, Layout};
use std::mem;
use std::ptr::NonNull;

/// A bump allocator for type `T`.
///
/// # Example
/// ```
/// use rust_dsa::BumpAlloc;
///
/// // First, we create a new bump allocator.
/// let mut arena: BumpAlloc<i32> = BumpAlloc::new(3);
///
/// // We can allocate pointers.
/// let ptr1 = arena.alloc().unwrap();
/// let ptr2 = arena.alloc().unwrap();
/// let ptr3 = arena.alloc().unwrap();
///
/// // Eventually, we run out of room.
/// assert_eq!(arena.alloc(), None);
/// assert_eq!(arena.available_slots(), 0);
///
/// // We can free allocations to make more room.
/// arena.free(ptr1);
/// arena.free(ptr2);
/// arena.free(ptr3);
/// assert!(arena.can_alloc());
/// assert!(arena.alloc().is_some());
/// assert!(arena.alloc().is_some());
///
/// // We can iterate over existing allocations.
/// assert_eq!(arena.allocations().count(), 2);
///
/// // Finally, we can free everything.
/// arena.free_all();
/// ```
pub struct BumpAlloc<T> {
    n: usize,
    queue: Vec<usize>,
    buffer: NonNull<T>,
    free: Vec<bool>,
}

impl<T> BumpAlloc<T> {
    /// Creates a new allocator.
    ///
    /// # Panics
    /// Panics if the allocation fails or if `size_of::<T>()` is zero.
    pub fn new(n: usize) -> BumpAlloc<T> {
        let buffer = if n == 0 {
            NonNull::dangling()
        } else if mem::size_of::<T>() == 0 {
            panic!("`T` has size 0");
        } else {
            let layout = Layout::array::<T>(n).expect("alloction is too big");
            let ptr = unsafe { alloc(layout) as *mut T };
            NonNull::new(ptr).expect("allocation failed")
        };

        BumpAlloc {
            n,
            queue: (0..n).collect(),
            buffer,
            free: vec![true; n],
        }
    }

    /// Allocates a slot, if one is available.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BumpAlloc;
    ///
    /// let mut arena: BumpAlloc<char> = BumpAlloc::new(3);
    ///
    /// assert!(arena.alloc().is_some());
    /// assert!(arena.alloc().is_some());
    /// assert!(arena.alloc().is_some());
    /// assert!(arena.alloc().is_none());
    /// ```
    pub fn alloc(&mut self) -> Option<NonNull<T>> {
        let slot = self.queue.pop()?;
        self.free[slot] = false;
        unsafe { NonNull::new(self.buffer.as_ptr().offset(slot as isize)) }
    }

    /// Frees a slot.
    ///
    /// # Panics
    /// Panics if the pointer was not allocated by this `BumpAlloc` struct.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BumpAlloc;
    ///
    /// let mut arena: BumpAlloc<String> = BumpAlloc::new(10);
    ///
    /// let ptr = arena.alloc().unwrap();
    /// assert_eq!(arena.available_slots(), 9);
    ///
    /// arena.free(ptr);
    ///
    /// assert_eq!(arena.available_slots(), 10);
    /// ```
    pub fn free(&mut self, ptr: NonNull<T>) {
        if ptr.as_ptr().align_offset(mem::align_of::<T>()) != 0 {
            panic!("invalid pointer");
        }

        let slot: usize = unsafe {
            ptr.as_ptr()
                .offset_from(self.buffer.as_ptr())
                .try_into()
                .expect("invalid pointer")
        };

        if self.free.get(slot) != Some(&false) {
            panic!("invalid pointer");
        }

        self.free[slot] = true;
        self.queue.push(slot);
    }

    /// Returns an interator over the currently allocated pointers.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BumpAlloc;
    ///
    /// let mut arena: BumpAlloc<u8> = BumpAlloc::new(100);
    /// arena.alloc();
    /// arena.alloc();
    /// arena.alloc();
    /// assert_eq!(arena.available_slots(), 97);
    ///
    /// let allocations: Vec<_> = arena.allocations().collect();
    /// for ptr in allocations {
    ///     arena.free(ptr);
    /// }
    ///
    /// assert_eq!(arena.available_slots(), 100);
    /// ```
    pub fn allocations(&self) -> Allocations<'_, T> {
        Allocations { ba: &self, n: 0 }
    }

    /// Frees all the currently allocated pointers.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BumpAlloc;
    ///
    /// let mut arena: BumpAlloc<i32> = BumpAlloc::new(10);
    /// arena.alloc();
    /// arena.alloc();
    /// arena.alloc();
    /// assert_eq!(arena.available_slots(), 7);
    ///
    /// arena.free_all();
    ///
    /// assert_eq!(arena.available_slots(), 10);
    /// ```
    pub fn free_all(&mut self) {
        self.free = vec![true; self.n];
        self.queue = (0..self.n).collect();
    }

    /// Returns the number of available slots that can be allocated.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BumpAlloc;
    ///
    /// let mut arena: BumpAlloc<i32> = BumpAlloc::new(10);
    /// assert_eq!(arena.available_slots(), 10);
    ///
    /// arena.alloc();
    /// arena.alloc();
    /// arena.alloc();
    /// assert_eq!(arena.available_slots(), 7);
    /// ```
    pub fn available_slots(&self) -> usize {
        self.queue.len()
    }

    /// Returns `true` if [`BumpAlloc::alloc`] will return `Some`.
    ///
    /// # Example
    /// ```
    /// use rust_dsa::BumpAlloc;
    ///
    /// let mut arena: BumpAlloc<bool> = BumpAlloc::new(1);
    /// assert!(arena.can_alloc());
    ///
    /// arena.alloc();
    ///
    /// assert!(!arena.can_alloc());
    /// ```
    pub fn can_alloc(&self) -> bool {
        self.available_slots() > 0
    }
}

impl<T> Drop for BumpAlloc<T> {
    fn drop(&mut self) {
        mem::take(&mut self.queue);
        mem::take(&mut self.free);
        let layout = Layout::array::<T>(self.n).unwrap();
        unsafe {
            dealloc(self.buffer.as_ptr() as *mut u8, layout);
        }
    }
}

pub struct Allocations<'a, T> {
    ba: &'a BumpAlloc<T>,
    n: usize,
}

impl<'a, T> Iterator for Allocations<'a, T> {
    type Item = NonNull<T>;
    fn next(&mut self) -> Option<NonNull<T>> {
        while self.ba.free.get(self.n) == Some(&true) {
            self.n += 1;
        }

        if self.ba.free.get(self.n).is_some() {
            let ptr = unsafe { self.ba.buffer.as_ptr().offset(self.n as isize) };
            self.n += 1;
            NonNull::new(ptr)
        } else {
            None
        }
    }
}
