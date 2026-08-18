use core::iter::Rev;

use crate::scan::{self, Cursor};

/// Search for the first occurrence of a byte in a slice.
///
/// This returns the index corresponding to the first occurrence of `needle` in
/// `haystack`, or `None` if one is not found. If an index is returned, it is
/// guaranteed to be less than `haystack.len()`.
///
/// # Example
///
/// ```
/// use memchr::memchr;
///
/// let haystack = b"the quick brown fox";
/// assert_eq!(memchr(b'k', haystack), Some(8));
/// ```
#[inline]
pub fn memchr(needle: u8, haystack: &[u8]) -> Option<usize> {
    let end = haystack.len();
    scan::find1(haystack, 0, end, needle)
}

/// Search for the last occurrence of a byte in a slice.
///
/// This returns the index corresponding to the last occurrence of `needle` in
/// `haystack`, or `None` if one is not found. If an index is returned, it is
/// guaranteed to be less than `haystack.len()`.
///
/// # Example
///
/// ```
/// use memchr::memrchr;
///
/// let haystack = b"the quick brown fox";
/// assert_eq!(memrchr(b'o', haystack), Some(17));
/// ```
#[inline]
pub fn memrchr(needle: u8, haystack: &[u8]) -> Option<usize> {
    let end = haystack.len();
    scan::rfind1(haystack, 0, end, needle)
}

/// Search for the first occurrence of two possible bytes in a haystack.
///
/// This returns the index corresponding to the first occurrence of one of the
/// needle bytes in `haystack`, or `None` if one is not found. If an index is
/// returned, it is guaranteed to be less than `haystack.len()`.
///
/// # Example
///
/// ```
/// use memchr::memchr2;
///
/// let haystack = b"the quick brown fox";
/// assert_eq!(memchr2(b'k', b'q', haystack), Some(4));
/// ```
#[inline]
pub fn memchr2(needle1: u8, needle2: u8, haystack: &[u8]) -> Option<usize> {
    let end = haystack.len();
    scan::find2(haystack, 0, end, needle1, needle2)
}

/// Search for the last occurrence of two possible bytes in a haystack.
///
/// This returns the index corresponding to the last occurrence of one of the
/// needle bytes in `haystack`, or `None` if one is not found. If an index is
/// returned, it is guaranteed to be less than `haystack.len()`.
///
/// # Example
///
/// ```
/// use memchr::memrchr2;
///
/// let haystack = b"the quick brown fox";
/// assert_eq!(memrchr2(b'k', b'o', haystack), Some(17));
/// ```
#[inline]
pub fn memrchr2(needle1: u8, needle2: u8, haystack: &[u8]) -> Option<usize> {
    let end = haystack.len();
    scan::rfind2(haystack, 0, end, needle1, needle2)
}

/// Search for the first occurrence of three possible bytes in a haystack.
///
/// This returns the index corresponding to the first occurrence of one of the
/// needle bytes in `haystack`, or `None` if one is not found. If an index is
/// returned, it is guaranteed to be less than `haystack.len()`.
///
/// # Example
///
/// ```
/// use memchr::memchr3;
///
/// let haystack = b"the quick brown fox";
/// assert_eq!(memchr3(b'k', b'q', b'u', haystack), Some(4));
/// ```
#[inline]
pub fn memchr3(
    needle1: u8,
    needle2: u8,
    needle3: u8,
    haystack: &[u8],
) -> Option<usize> {
    let end = haystack.len();
    scan::find3(haystack, 0, end, needle1, needle2, needle3)
}

/// Search for the last occurrence of three possible bytes in a haystack.
///
/// This returns the index corresponding to the last occurrence of one of the
/// needle bytes in `haystack`, or `None` if one is not found. If an index is
/// returned, it is guaranteed to be less than `haystack.len()`.
///
/// # Example
///
/// ```
/// use memchr::memrchr3;
///
/// let haystack = b"the quick brown fox";
/// assert_eq!(memrchr3(b'k', b'o', b'n', haystack), Some(17));
/// ```
#[inline]
pub fn memrchr3(
    needle1: u8,
    needle2: u8,
    needle3: u8,
    haystack: &[u8],
) -> Option<usize> {
    let end = haystack.len();
    scan::rfind3(haystack, 0, end, needle1, needle2, needle3)
}

/// Returns an iterator over all occurrences of the needle in a haystack.
///
/// The iterator returned implements `DoubleEndedIterator`. This means it
/// can also be used to find occurrences in reverse order.
#[inline]
pub fn memchr_iter<'h>(needle: u8, haystack: &'h [u8]) -> Memchr<'h> {
    let end = haystack.len();
    Memchr { needle1: needle, it: Cursor { haystack, start: 0, end } }
}

/// Returns an iterator over all occurrences of the needle in a haystack, in
/// reverse.
#[inline]
pub fn memrchr_iter(needle: u8, haystack: &[u8]) -> Rev<Memchr<'_>> {
    let end = haystack.len();
    let it = Memchr { needle1: needle, it: Cursor { haystack, start: 0, end } };
    it.rev()
}

/// Returns an iterator over all occurrences of the needles in a haystack.
///
/// The iterator returned implements `DoubleEndedIterator`. This means it
/// can also be used to find occurrences in reverse order.
#[inline]
pub fn memchr2_iter<'h>(
    needle1: u8,
    needle2: u8,
    haystack: &'h [u8],
) -> Memchr2<'h> {
    let end = haystack.len();
    Memchr2 { needle1, needle2, it: Cursor { haystack, start: 0, end } }
}

/// Returns an iterator over all occurrences of the needles in a haystack, in
/// reverse.
#[inline]
pub fn memrchr2_iter(
    needle1: u8,
    needle2: u8,
    haystack: &[u8],
) -> Rev<Memchr2<'_>> {
    let end = haystack.len();
    let it = Memchr2 { needle1, needle2, it: Cursor { haystack, start: 0, end } };
    it.rev()
}

/// Returns an iterator over all occurrences of the needles in a haystack.
///
/// The iterator returned implements `DoubleEndedIterator`. This means it
/// can also be used to find occurrences in reverse order.
#[inline]
pub fn memchr3_iter<'h>(
    needle1: u8,
    needle2: u8,
    needle3: u8,
    haystack: &'h [u8],
) -> Memchr3<'h> {
    let end = haystack.len();
    Memchr3 { needle1, needle2, needle3, it: Cursor { haystack, start: 0, end } }
}

/// Returns an iterator over all occurrences of the needles in a haystack, in
/// reverse.
#[inline]
pub fn memrchr3_iter(
    needle1: u8,
    needle2: u8,
    needle3: u8,
    haystack: &[u8],
) -> Rev<Memchr3<'_>> {
    let end = haystack.len();
    let it =
        Memchr3 { needle1, needle2, needle3, it: Cursor { haystack, start: 0, end } };
    it.rev()
}

/// An iterator over all occurrences of a single byte in a haystack.
///
/// This iterator implements `DoubleEndedIterator`, which means it can also be
/// used to find occurrences in reverse order.
///
/// This iterator is created by the [`memchr_iter`] or [`memrchr_iter`]
/// functions. It can also be created with the [`Memchr::new`] method.
///
/// The lifetime parameter `'h` refers to the lifetime of the haystack being
/// searched.
#[derive(Clone, Debug)]
pub struct Memchr<'h> {
    needle1: u8,
    it: Cursor<'h>,
}

impl<'h> Memchr<'h> {
    /// Returns an iterator over all occurrences of the needle byte in the
    /// given haystack.
    ///
    /// The iterator returned implements `DoubleEndedIterator`. This means it
    /// can also be used to find occurrences in reverse order.
    #[inline]
    pub fn new(needle1: u8, haystack: &'h [u8]) -> Memchr<'h> {
        let end = haystack.len();
        Memchr { needle1, it: Cursor { haystack, start: 0, end } }
    }
}

impl<'h> Iterator for Memchr<'h> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        match scan::find1(haystack, start, end, self.needle1) {
            None => None,
            Some(at) => {
                self.it.start = scan::step_past(at);
                Some(at)
            }
        }
    }

    #[inline]
    fn count(self) -> usize {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        scan::count1(haystack, start, end, self.needle1)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        scan::cursor_size_hint(self.it.start, self.it.end)
    }
}

impl<'h> DoubleEndedIterator for Memchr<'h> {
    #[inline]
    fn next_back(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        match scan::rfind1(haystack, start, end, self.needle1) {
            None => None,
            Some(at) => {
                self.it.end = at;
                Some(at)
            }
        }
    }
}

impl<'h> core::iter::FusedIterator for Memchr<'h> {}

/// An iterator over all occurrences of two possible bytes in a haystack.
///
/// This iterator implements `DoubleEndedIterator`, which means it can also be
/// used to find occurrences in reverse order.
///
/// This iterator is created by the [`memchr2_iter`] or [`memrchr2_iter`]
/// functions. It can also be created with the [`Memchr2::new`] method.
///
/// The lifetime parameter `'h` refers to the lifetime of the haystack being
/// searched.
#[derive(Clone, Debug)]
pub struct Memchr2<'h> {
    needle1: u8,
    needle2: u8,
    it: Cursor<'h>,
}

impl<'h> Memchr2<'h> {
    /// Returns an iterator over all occurrences of the needle bytes in the
    /// given haystack.
    ///
    /// The iterator returned implements `DoubleEndedIterator`. This means it
    /// can also be used to find occurrences in reverse order.
    #[inline]
    pub fn new(needle1: u8, needle2: u8, haystack: &'h [u8]) -> Memchr2<'h> {
        let end = haystack.len();
        Memchr2 { needle1, needle2, it: Cursor { haystack, start: 0, end } }
    }
}

impl<'h> Iterator for Memchr2<'h> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        match scan::find2(haystack, start, end, self.needle1, self.needle2) {
            None => None,
            Some(at) => {
                self.it.start = scan::step_past(at);
                Some(at)
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        scan::cursor_size_hint(self.it.start, self.it.end)
    }
}

impl<'h> DoubleEndedIterator for Memchr2<'h> {
    #[inline]
    fn next_back(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        match scan::rfind2(haystack, start, end, self.needle1, self.needle2) {
            None => None,
            Some(at) => {
                self.it.end = at;
                Some(at)
            }
        }
    }
}

impl<'h> core::iter::FusedIterator for Memchr2<'h> {}

/// An iterator over all occurrences of three possible bytes in a haystack.
///
/// This iterator implements `DoubleEndedIterator`, which means it can also be
/// used to find occurrences in reverse order.
///
/// This iterator is created by the [`memchr3_iter`] or [`memrchr3_iter`]
/// functions. It can also be created with the [`Memchr3::new`] method.
///
/// The lifetime parameter `'h` refers to the lifetime of the haystack being
/// searched.
#[derive(Clone, Debug)]
pub struct Memchr3<'h> {
    needle1: u8,
    needle2: u8,
    needle3: u8,
    it: Cursor<'h>,
}

impl<'h> Memchr3<'h> {
    /// Returns an iterator over all occurrences of the needle bytes in the
    /// given haystack.
    ///
    /// The iterator returned implements `DoubleEndedIterator`. This means it
    /// can also be used to find occurrences in reverse order.
    #[inline]
    pub fn new(
        needle1: u8,
        needle2: u8,
        needle3: u8,
        haystack: &'h [u8],
    ) -> Memchr3<'h> {
        let end = haystack.len();
        Memchr3 { needle1, needle2, needle3, it: Cursor { haystack, start: 0, end } }
    }
}

impl<'h> Iterator for Memchr3<'h> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        let found = scan::find3(
            haystack,
            start,
            end,
            self.needle1,
            self.needle2,
            self.needle3,
        );
        match found {
            None => None,
            Some(at) => {
                self.it.start = scan::step_past(at);
                Some(at)
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        scan::cursor_size_hint(self.it.start, self.it.end)
    }
}

impl<'h> DoubleEndedIterator for Memchr3<'h> {
    #[inline]
    fn next_back(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        let found = scan::rfind3(
            haystack,
            start,
            end,
            self.needle1,
            self.needle2,
            self.needle3,
        );
        match found {
            None => None,
            Some(at) => {
                self.it.end = at;
                Some(at)
            }
        }
    }
}

impl<'h> core::iter::FusedIterator for Memchr3<'h> {}
