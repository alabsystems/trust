/*!
Provides architecture independent implementations of `memchr` and friends.

Upstream this module is the word-at-a-time (SWAR) fallback and additionally
exposes `*_raw` pointer-range entry points. The raw entry points are absent
here: they cannot exist in a crate that carries `#![forbid(unsafe_code)]`, and
nothing outside memchr itself has ever called them.
*/

use crate::scan::{self, Cursor};

/// Finds all occurrences of a single byte in a haystack.
#[derive(Clone, Copy, Debug)]
pub struct One {
    needle: u8,
}

impl One {
    /// Create a new searcher that finds occurrences of the byte given.
    #[inline]
    pub fn new(needle: u8) -> One {
        One { needle }
    }

    /// Return the first occurrence of the needle in the given haystack. If no
    /// such occurrence exists, then `None` is returned.
    ///
    /// The occurrence is reported as an offset into `haystack`. Its maximum
    /// value for a non-empty haystack is `haystack.len() - 1`.
    #[inline]
    pub fn find(&self, haystack: &[u8]) -> Option<usize> {
        let end = haystack.len();
        scan::find1(haystack, 0, end, self.needle)
    }

    /// Return the last occurrence of the needle in the given haystack. If no
    /// such occurrence exists, then `None` is returned.
    ///
    /// The occurrence is reported as an offset into `haystack`. Its maximum
    /// value for a non-empty haystack is `haystack.len() - 1`.
    #[inline]
    pub fn rfind(&self, haystack: &[u8]) -> Option<usize> {
        let end = haystack.len();
        scan::rfind1(haystack, 0, end, self.needle)
    }

    /// Counts all occurrences of this byte in the given haystack.
    #[inline]
    pub fn count(&self, haystack: &[u8]) -> usize {
        let end = haystack.len();
        scan::count1(haystack, 0, end, self.needle)
    }

    /// Returns an iterator over all occurrences of the needle byte in the
    /// given haystack.
    ///
    /// The iterator returned implements `DoubleEndedIterator`. This means it
    /// can also be used to find occurrences in reverse order.
    #[inline]
    pub fn iter<'a, 'h>(&'a self, haystack: &'h [u8]) -> OneIter<'a, 'h> {
        let end = haystack.len();
        OneIter { searcher: self, it: Cursor { haystack, start: 0, end } }
    }
}

/// An iterator over all occurrences of a single byte in a haystack.
///
/// This iterator implements `DoubleEndedIterator`, which means it can also be
/// used to find occurrences in reverse order.
///
/// This iterator is created by the [`One::iter`] method.
///
/// The lifetime parameters are as follows:
///
/// * `'a` refers to the lifetime of the underlying [`One`] searcher.
/// * `'h` refers to the lifetime of the haystack being searched.
#[derive(Clone, Debug)]
pub struct OneIter<'a, 'h> {
    searcher: &'a One,
    it: Cursor<'h>,
}

impl<'a, 'h> Iterator for OneIter<'a, 'h> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        match scan::find1(haystack, start, end, self.searcher.needle) {
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
        scan::count1(haystack, start, end, self.searcher.needle)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        scan::cursor_size_hint(self.it.start, self.it.end)
    }
}

impl<'a, 'h> DoubleEndedIterator for OneIter<'a, 'h> {
    #[inline]
    fn next_back(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        match scan::rfind1(haystack, start, end, self.searcher.needle) {
            None => None,
            Some(at) => {
                self.it.end = at;
                Some(at)
            }
        }
    }
}

/// Finds all occurrences of two bytes in a haystack.
///
/// That is, this reports matches of one of two possible bytes. For example,
/// searching for `a` or `b` in `afoobar` would report matches at offsets `0`,
/// `4` and `5`.
#[derive(Clone, Copy, Debug)]
pub struct Two {
    needle1: u8,
    needle2: u8,
}

impl Two {
    /// Create a new searcher that finds occurrences of the bytes given.
    #[inline]
    pub fn new(needle1: u8, needle2: u8) -> Two {
        Two { needle1, needle2 }
    }

    /// Return the first occurrence of one of the needle bytes in the given
    /// haystack. If no such occurrence exists, then `None` is returned.
    ///
    /// The occurrence is reported as an offset into `haystack`. Its maximum
    /// value for a non-empty haystack is `haystack.len() - 1`.
    #[inline]
    pub fn find(&self, haystack: &[u8]) -> Option<usize> {
        let end = haystack.len();
        scan::find2(haystack, 0, end, self.needle1, self.needle2)
    }

    /// Return the last occurrence of one of the needle bytes in the given
    /// haystack. If no such occurrence exists, then `None` is returned.
    ///
    /// The occurrence is reported as an offset into `haystack`. Its maximum
    /// value for a non-empty haystack is `haystack.len() - 1`.
    #[inline]
    pub fn rfind(&self, haystack: &[u8]) -> Option<usize> {
        let end = haystack.len();
        scan::rfind2(haystack, 0, end, self.needle1, self.needle2)
    }

    /// Returns an iterator over all occurrences of one of the needle bytes in
    /// the given haystack.
    ///
    /// The iterator returned implements `DoubleEndedIterator`. This means it
    /// can also be used to find occurrences in reverse order.
    #[inline]
    pub fn iter<'a, 'h>(&'a self, haystack: &'h [u8]) -> TwoIter<'a, 'h> {
        let end = haystack.len();
        TwoIter { searcher: self, it: Cursor { haystack, start: 0, end } }
    }
}

/// An iterator over all occurrences of two possible bytes in a haystack.
///
/// This iterator implements `DoubleEndedIterator`, which means it can also be
/// used to find occurrences in reverse order.
///
/// This iterator is created by the [`Two::iter`] method.
///
/// The lifetime parameters are as follows:
///
/// * `'a` refers to the lifetime of the underlying [`Two`] searcher.
/// * `'h` refers to the lifetime of the haystack being searched.
#[derive(Clone, Debug)]
pub struct TwoIter<'a, 'h> {
    searcher: &'a Two,
    it: Cursor<'h>,
}

impl<'a, 'h> Iterator for TwoIter<'a, 'h> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        let n1 = self.searcher.needle1;
        let n2 = self.searcher.needle2;
        match scan::find2(haystack, start, end, n1, n2) {
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

impl<'a, 'h> DoubleEndedIterator for TwoIter<'a, 'h> {
    #[inline]
    fn next_back(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        let n1 = self.searcher.needle1;
        let n2 = self.searcher.needle2;
        match scan::rfind2(haystack, start, end, n1, n2) {
            None => None,
            Some(at) => {
                self.it.end = at;
                Some(at)
            }
        }
    }
}

/// Finds all occurrences of three bytes in a haystack.
///
/// That is, this reports matches of one of three possible bytes. For example,
/// searching for `a`, `b` or `o` in `afoobar` would report matches at offsets
/// `0`, `2`, `3`, `4` and `5`.
#[derive(Clone, Copy, Debug)]
pub struct Three {
    needle1: u8,
    needle2: u8,
    needle3: u8,
}

impl Three {
    /// Create a new searcher that finds occurrences of the bytes given.
    #[inline]
    pub fn new(needle1: u8, needle2: u8, needle3: u8) -> Three {
        Three { needle1, needle2, needle3 }
    }

    /// Return the first occurrence of one of the needle bytes in the given
    /// haystack. If no such occurrence exists, then `None` is returned.
    ///
    /// The occurrence is reported as an offset into `haystack`. Its maximum
    /// value for a non-empty haystack is `haystack.len() - 1`.
    #[inline]
    pub fn find(&self, haystack: &[u8]) -> Option<usize> {
        let end = haystack.len();
        let n1 = self.needle1;
        let n2 = self.needle2;
        let n3 = self.needle3;
        scan::find3(haystack, 0, end, n1, n2, n3)
    }

    /// Return the last occurrence of one of the needle bytes in the given
    /// haystack. If no such occurrence exists, then `None` is returned.
    ///
    /// The occurrence is reported as an offset into `haystack`. Its maximum
    /// value for a non-empty haystack is `haystack.len() - 1`.
    #[inline]
    pub fn rfind(&self, haystack: &[u8]) -> Option<usize> {
        let end = haystack.len();
        let n1 = self.needle1;
        let n2 = self.needle2;
        let n3 = self.needle3;
        scan::rfind3(haystack, 0, end, n1, n2, n3)
    }

    /// Returns an iterator over all occurrences of one of the needle bytes in
    /// the given haystack.
    ///
    /// The iterator returned implements `DoubleEndedIterator`. This means it
    /// can also be used to find occurrences in reverse order.
    #[inline]
    pub fn iter<'a, 'h>(&'a self, haystack: &'h [u8]) -> ThreeIter<'a, 'h> {
        let end = haystack.len();
        ThreeIter { searcher: self, it: Cursor { haystack, start: 0, end } }
    }
}

/// An iterator over all occurrences of three possible bytes in a haystack.
///
/// This iterator implements `DoubleEndedIterator`, which means it can also be
/// used to find occurrences in reverse order.
///
/// This iterator is created by the [`Three::iter`] method.
///
/// The lifetime parameters are as follows:
///
/// * `'a` refers to the lifetime of the underlying [`Three`] searcher.
/// * `'h` refers to the lifetime of the haystack being searched.
#[derive(Clone, Debug)]
pub struct ThreeIter<'a, 'h> {
    searcher: &'a Three,
    it: Cursor<'h>,
}

impl<'a, 'h> Iterator for ThreeIter<'a, 'h> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        let n1 = self.searcher.needle1;
        let n2 = self.searcher.needle2;
        let n3 = self.searcher.needle3;
        match scan::find3(haystack, start, end, n1, n2, n3) {
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

impl<'a, 'h> DoubleEndedIterator for ThreeIter<'a, 'h> {
    #[inline]
    fn next_back(&mut self) -> Option<usize> {
        let haystack = self.it.haystack;
        let start = self.it.start;
        let end = self.it.end;
        let n1 = self.searcher.needle1;
        let n2 = self.searcher.needle2;
        let n3 = self.searcher.needle3;
        match scan::rfind3(haystack, start, end, n1, n2, n3) {
            None => None,
            Some(at) => {
                self.it.end = at;
                Some(at)
            }
        }
    }
}
