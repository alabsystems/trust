/*!
This module provides forward and reverse substring search routines.

Unlike the standard library's substring search routines, these work on
arbitrary bytes. For all non-empty needles, these routines will report exactly
the same values as the corresponding routines in the standard library. For
the empty needle, the standard library reports matches only at valid UTF-8
boundaries, where as these routines will report matches at every position.

# Example: iterating over substring matches

```
use memchr::memmem;

let haystack = b"foo bar foo baz foo";

let mut it = memmem::find_iter(haystack, "foo");
assert_eq!(Some(0), it.next());
assert_eq!(Some(8), it.next());
assert_eq!(Some(16), it.next());
assert_eq!(None, it.next());
```

# Example: iterating over substring matches in reverse

**NOTE:** This module does not implement double ended iterators, so reverse
searches aren't done by calling `rev` on a forward iterator.

```
use memchr::memmem;

let haystack = b"foo bar foo baz foo";

let mut it = memmem::rfind_iter(haystack, "foo");
assert_eq!(Some(16), it.next());
assert_eq!(Some(8), it.next());
assert_eq!(Some(0), it.next());
assert_eq!(None, it.next());
```

# Example: repeating a search for the same needle

```
use memchr::memmem;

let finder = memmem::Finder::new("foo");

assert_eq!(Some(4), finder.find(b"baz foo quux"));
assert_eq!(None, finder.find(b"quux baz bar"));
```
*/

use crate::arch::all::packedpair::HeuristicFrequencyRank;
use crate::cow::{self, CowBytes};
use crate::scan;

/// Prefilter controls whether heuristics are used to accelerate prefix
/// matching.
///
/// A prefilter is a fast, approximate scan for a rare byte of the needle,
/// used to skip ahead before running a full match. This crate's substring
/// search does not use one — see [`crate::arch::all::packedpair`] — so this
/// setting is accepted and has no effect. It is retained because it is public
/// API, and because a caller that disables prefilters is asking for behavior
/// this crate already has.
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum Prefilter {
    /// Never use a prefilter in substring search.
    None,
    /// Automatically detect whether a heuristic prefilter should be used. If
    /// it is used, then heuristics will be used to dynamically disable the
    /// prefilter if it is believed to not be carrying its weight.
    Auto,
}

impl Default for Prefilter {
    fn default() -> Prefilter {
        Prefilter::Auto
    }
}

/// Returns an iterator over all non-overlapping occurrences of a substring in
/// a haystack.
///
/// # Examples
///
/// ```
/// use memchr::memmem;
///
/// let haystack = b"foo bar foo baz foo";
/// let mut it = memmem::find_iter(haystack, b"foo");
/// assert_eq!(Some(0), it.next());
/// assert_eq!(Some(8), it.next());
/// assert_eq!(Some(16), it.next());
/// assert_eq!(None, it.next());
/// ```
#[inline]
pub fn find_iter<'h, 'n, N: 'n + ?Sized + AsRef<[u8]>>(
    haystack: &'h [u8],
    needle: &'n N,
) -> FindIter<'h, 'n> {
    let finder = Finder { needle: cow::borrowed(needle.as_ref()) };
    FindIter { haystack, finder, pos: 0 }
}

/// Returns a reverse iterator over all non-overlapping occurrences of a
/// substring in a haystack.
///
/// # Examples
///
/// ```
/// use memchr::memmem;
///
/// let haystack = b"foo bar foo baz foo";
/// let mut it = memmem::rfind_iter(haystack, b"foo");
/// assert_eq!(Some(16), it.next());
/// assert_eq!(Some(8), it.next());
/// assert_eq!(Some(0), it.next());
/// assert_eq!(None, it.next());
/// ```
#[inline]
pub fn rfind_iter<'h, 'n, N: 'n + ?Sized + AsRef<[u8]>>(
    haystack: &'h [u8],
    needle: &'n N,
) -> FindRevIter<'h, 'n> {
    let finder = FinderRev { needle: cow::borrowed(needle.as_ref()) };
    let pos = Some(haystack.len());
    FindRevIter { haystack, finder, pos }
}

/// Returns the index of the first occurrence of the given needle.
///
/// Note that if you're are searching for the same needle in many different
/// small haystacks, it may be faster to initialize a [`Finder`] once,
/// and reuse it for each search.
///
/// # Examples
///
/// ```
/// use memchr::memmem;
///
/// let haystack = b"foo bar baz";
/// assert_eq!(Some(0), memmem::find(haystack, b"foo"));
/// assert_eq!(Some(4), memmem::find(haystack, b"bar"));
/// assert_eq!(None, memmem::find(haystack, b"quux"));
/// ```
#[inline]
pub fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    scan::find_substring(haystack, needle)
}

/// Returns the index of the last occurrence of the given needle.
///
/// Note that if you're are searching for the same needle in many different
/// small haystacks, it may be faster to initialize a [`FinderRev`] once,
/// and reuse it for each search.
///
/// # Examples
///
/// ```
/// use memchr::memmem;
///
/// let haystack = b"foo bar baz";
/// assert_eq!(Some(0), memmem::rfind(haystack, b"foo"));
/// assert_eq!(Some(4), memmem::rfind(haystack, b"bar"));
/// assert_eq!(Some(8), memmem::rfind(haystack, b"ba"));
/// assert_eq!(None, memmem::rfind(haystack, b"quux"));
/// ```
#[inline]
pub fn rfind(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    scan::rfind_substring(haystack, needle)
}

/// An iterator over non-overlapping substring matches.
///
/// Matches are reported by the byte offset at which they begin.
///
/// `'h` is the lifetime of the haystack while `'n` is the lifetime of the
/// needle.
#[derive(Debug, Clone)]
pub struct FindIter<'h, 'n> {
    haystack: &'h [u8],
    finder: Finder<'n>,
    pos: usize,
}

impl<'h, 'n> FindIter<'h, 'n> {
    /// Convert this iterator into its owned variant, such that it no longer
    /// borrows the finder and needle.
    ///
    /// If this is already an owned iterator, then this is a no-op. Otherwise,
    /// this copies the needle.
    ///
    /// This is only available when the `alloc` feature is enabled.
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn into_owned(self) -> FindIter<'h, 'static> {
        let finder = Finder { needle: cow::into_owned(self.finder.needle) };
        FindIter { haystack: self.haystack, finder, pos: self.pos }
    }
}

impl<'h, 'n> Iterator for FindIter<'h, 'n> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        let needle = cow::as_slice(&self.finder.needle);
        let haystack = self.haystack.get(self.pos..)?;
        let idx = scan::find_substring(haystack, needle)?;

        let pos = scan::add_saturating(self.pos, idx);
        // Hand-inlined `needle.len().max(1)`: an empty needle still has to
        // advance, or the iterator never terminates.
        let needle_len = needle.len();
        let step = if needle_len == 0 { 1 } else { needle_len };
        self.pos = scan::add_saturating(pos, step);

        Some(pos)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // The largest possible number of non-overlapping matches is the
        // quotient of the haystack and the needle (or the length of the
        // haystack, if the needle is empty)
        match self.haystack.len().checked_sub(self.pos) {
            None => (0, Some(0)),
            Some(haystack_len) => match cow::as_slice(&self.finder.needle).len() {
                // Empty needles always succeed and match at every point
                // (including the very end)
                0 => (haystack_len.saturating_add(1), haystack_len.checked_add(1)),
                needle_len => (0, Some(haystack_len / needle_len)),
            },
        }
    }
}

/// An iterator over non-overlapping substring matches in reverse.
///
/// Matches are reported by the byte offset at which they begin.
///
/// `'h` is the lifetime of the haystack while `'n` is the lifetime of the
/// needle.
#[derive(Clone, Debug)]
pub struct FindRevIter<'h, 'n> {
    haystack: &'h [u8],
    finder: FinderRev<'n>,
    /// When searching with an empty needle, this gets set to `None` after
    /// we've yielded the last element at `0`.
    pos: Option<usize>,
}

impl<'h, 'n> FindRevIter<'h, 'n> {
    /// Convert this iterator into its owned variant, such that it no longer
    /// borrows the finder and needle.
    ///
    /// If this is already an owned iterator, then this is a no-op. Otherwise,
    /// this copies the needle.
    ///
    /// This is only available when the `alloc` feature is enabled.
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn into_owned(self) -> FindRevIter<'h, 'static> {
        let finder = FinderRev { needle: cow::into_owned(self.finder.needle) };
        FindRevIter { haystack: self.haystack, finder, pos: self.pos }
    }
}

impl<'h, 'n> Iterator for FindRevIter<'h, 'n> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        let pos = match self.pos {
            None => return None,
            Some(pos) => pos,
        };
        // `pos` is only ever set to a match offset or to `haystack.len()`, so
        // this slice always exists; `get` rather than `[..pos]` keeps the
        // method panic-free by construction rather than by argument.
        let haystack = match self.haystack.get(..pos) {
            None => return None,
            Some(haystack) => haystack,
        };
        let needle = cow::as_slice(&self.finder.needle);
        let result = scan::rfind_substring(haystack, needle);
        match result {
            None => None,
            Some(i) => {
                if pos == i {
                    self.pos = pos.checked_sub(1);
                } else {
                    self.pos = Some(i);
                }
                Some(i)
            }
        }
    }
}

/// A single substring searcher fixed to a particular needle.
///
/// The purpose of this type is to permit callers to construct a substring
/// searcher that can be used to search haystacks without the overhead of
/// constructing the searcher in the first place.
///
/// When the `alloc` feature is enabled, then this type has an `into_owned`
/// version which permits building a `Finder` that is not connected to
/// the lifetime of its needle.
#[derive(Clone, Debug)]
pub struct Finder<'n> {
    needle: CowBytes<'n>,
}

impl<'n> Finder<'n> {
    /// Create a new finder for the given needle.
    #[inline]
    pub fn new<B: ?Sized + AsRef<[u8]>>(needle: &'n B) -> Finder<'n> {
        Finder { needle: cow::borrowed(needle.as_ref()) }
    }

    /// Returns the index of the first occurrence of this needle in the given
    /// haystack.
    ///
    /// # Examples
    ///
    /// ```
    /// use memchr::memmem::Finder;
    ///
    /// let haystack = b"foo bar baz";
    /// assert_eq!(Some(0), Finder::new("foo").find(haystack));
    /// assert_eq!(Some(4), Finder::new("bar").find(haystack));
    /// assert_eq!(None, Finder::new("quux").find(haystack));
    /// ```
    #[inline]
    pub fn find(&self, haystack: &[u8]) -> Option<usize> {
        let needle = cow::as_slice(&self.needle);
        scan::find_substring(haystack, needle)
    }

    /// Returns an iterator over all occurrences of a substring in a haystack.
    ///
    /// # Examples
    ///
    /// ```
    /// use memchr::memmem::Finder;
    ///
    /// let haystack = b"foo bar foo baz foo";
    /// let finder = Finder::new(b"foo");
    /// let mut it = finder.find_iter(haystack);
    /// assert_eq!(Some(0), it.next());
    /// assert_eq!(Some(8), it.next());
    /// assert_eq!(Some(16), it.next());
    /// assert_eq!(None, it.next());
    /// ```
    #[inline]
    pub fn find_iter<'a, 'h>(&'a self, haystack: &'h [u8]) -> FindIter<'h, 'a> {
        let finder = Finder { needle: cow::borrowed(cow::as_slice(&self.needle)) };
        FindIter { haystack, finder, pos: 0 }
    }

    /// Convert this finder into its owned variant, such that it no longer
    /// borrows the needle.
    ///
    /// If this is already an owned finder, then this is a no-op. Otherwise,
    /// this copies the needle.
    ///
    /// This is only available when the `alloc` feature is enabled.
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn into_owned(self) -> Finder<'static> {
        Finder { needle: cow::into_owned(self.needle) }
    }

    /// Convert this finder into its borrowed variant.
    ///
    /// This is primarily useful if your finder is owned and you'd like to
    /// store its borrowed variant in some intermediate data structure.
    ///
    /// Note that the lifetime parameter of the returned finder is tied to the
    /// lifetime of `self`, and may be shorter than the `'n` lifetime of the
    /// needle itself.
    #[inline]
    pub fn as_ref(&self) -> Finder<'_> {
        Finder { needle: cow::borrowed(cow::as_slice(&self.needle)) }
    }

    /// Returns the needle that this finder searches for.
    ///
    /// Note that the lifetime of the needle returned is tied to the lifetime
    /// of the finder, and may be shorter than the `'n` lifetime.
    #[inline]
    pub fn needle(&self) -> &[u8] {
        cow::as_slice(&self.needle)
    }
}

/// A single substring reverse searcher fixed to a particular needle.
///
/// The purpose of this type is to permit callers to construct a substring
/// searcher that can be used to search haystacks without the overhead of
/// constructing the searcher in the first place.
///
/// When the `alloc` feature is enabled, then this type has an `into_owned`
/// version which permits building a `FinderRev` that is not connected to
/// the lifetime of its needle.
#[derive(Clone, Debug)]
pub struct FinderRev<'n> {
    needle: CowBytes<'n>,
}

impl<'n> FinderRev<'n> {
    /// Create a new reverse finder for the given needle.
    #[inline]
    pub fn new<B: ?Sized + AsRef<[u8]>>(needle: &'n B) -> FinderRev<'n> {
        FinderRev { needle: cow::borrowed(needle.as_ref()) }
    }

    /// Returns the index of the last occurrence of this needle in the given
    /// haystack.
    ///
    /// The haystack may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str` and `&[u8]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use memchr::memmem::FinderRev;
    ///
    /// let haystack = b"foo bar baz";
    /// assert_eq!(Some(0), FinderRev::new("foo").rfind(haystack));
    /// assert_eq!(Some(4), FinderRev::new("bar").rfind(haystack));
    /// assert_eq!(None, FinderRev::new("quux").rfind(haystack));
    /// ```
    pub fn rfind<B: AsRef<[u8]>>(&self, haystack: B) -> Option<usize> {
        let needle = cow::as_slice(&self.needle);
        scan::rfind_substring(haystack.as_ref(), needle)
    }

    /// Returns a reverse iterator over all occurrences of a substring in a
    /// haystack.
    ///
    /// # Examples
    ///
    /// ```
    /// use memchr::memmem::FinderRev;
    ///
    /// let haystack = b"foo bar foo baz foo";
    /// let finder = FinderRev::new(b"foo");
    /// let mut it = finder.rfind_iter(haystack);
    /// assert_eq!(Some(16), it.next());
    /// assert_eq!(Some(8), it.next());
    /// assert_eq!(Some(0), it.next());
    /// assert_eq!(None, it.next());
    /// ```
    #[inline]
    pub fn rfind_iter<'a, 'h>(&'a self, haystack: &'h [u8]) -> FindRevIter<'h, 'a> {
        let finder = FinderRev { needle: cow::borrowed(cow::as_slice(&self.needle)) };
        let pos = Some(haystack.len());
        FindRevIter { haystack, finder, pos }
    }

    /// Convert this finder into its owned variant, such that it no longer
    /// borrows the needle.
    ///
    /// If this is already an owned finder, then this is a no-op. Otherwise,
    /// this copies the needle.
    ///
    /// This is only available when the `alloc` feature is enabled.
    #[cfg(feature = "alloc")]
    #[inline]
    pub fn into_owned(self) -> FinderRev<'static> {
        FinderRev { needle: cow::into_owned(self.needle) }
    }

    /// Convert this finder into its borrowed variant.
    ///
    /// This is primarily useful if your finder is owned and you'd like to
    /// store its borrowed variant in some intermediate data structure.
    ///
    /// Note that the lifetime parameter of the returned finder is tied to the
    /// lifetime of `self`, and may be shorter than the `'n` lifetime of the
    /// needle itself.
    #[inline]
    pub fn as_ref(&self) -> FinderRev<'_> {
        FinderRev { needle: cow::borrowed(cow::as_slice(&self.needle)) }
    }

    /// Returns the needle that this finder searches for.
    ///
    /// Note that the lifetime of the needle returned is tied to the lifetime
    /// of the finder, and may be shorter than the `'n` lifetime.
    #[inline]
    pub fn needle(&self) -> &[u8] {
        cow::as_slice(&self.needle)
    }
}

/// A builder for constructing non-default forward or reverse memmem finders.
///
/// A builder is primarily useful for configuring a substring searcher.
/// Currently, the only configuration exposed is the ability to disable
/// heuristic prefilters used to speed up certain searches.
#[derive(Clone, Debug, Default)]
pub struct FinderBuilder {
    prefilter: Prefilter,
}

impl FinderBuilder {
    /// Create a new finder builder with default settings.
    pub fn new() -> FinderBuilder {
        FinderBuilder { prefilter: Prefilter::Auto }
    }

    /// Build a forward finder using the given needle from the current
    /// settings.
    pub fn build_forward<'n, B: ?Sized + AsRef<[u8]>>(&self, needle: &'n B) -> Finder<'n> {
        let _ = self.prefilter;
        Finder { needle: cow::borrowed(needle.as_ref()) }
    }

    /// Build an owned forward finder using the given needle from the current
    /// settings.
    #[cfg(feature = "alloc")]
    pub fn build_forward_owned<B: Into<alloc::boxed::Box<[u8]>>>(
        &self,
        needle: B,
    ) -> Finder<'static> {
        Finder { needle: cow::owned(needle.into()) }
    }

    /// Build a forward finder using the given needle and a custom heuristic
    /// for determining the frequency of a given byte in the dataset. See
    /// [`HeuristicFrequencyRank`] for more details.
    pub fn build_forward_with_ranker<'n, R: HeuristicFrequencyRank, B: ?Sized + AsRef<[u8]>>(
        &self,
        _ranker: R,
        needle: &'n B,
    ) -> Finder<'n> {
        // Read, not applied: there is one search strategy here and it has no
        // prefilter, so both settings describe the same searcher.
        let _ = self.prefilter;
        Finder { needle: cow::borrowed(needle.as_ref()) }
    }

    /// Build an owned forward finder using the given needle and a custom
    /// heuristic for determining the frequency of a given byte in the dataset.
    /// See [`HeuristicFrequencyRank`] for more details.
    #[cfg(feature = "alloc")]
    pub fn build_forward_with_ranker_owned<
        R: HeuristicFrequencyRank,
        B: Into<alloc::boxed::Box<[u8]>>,
    >(
        &self,
        _ranker: R,
        needle: B,
    ) -> Finder<'static> {
        Finder { needle: cow::owned(needle.into()) }
    }

    /// Build a reverse finder using the given needle from the current
    /// settings.
    pub fn build_reverse<'n, B: ?Sized + AsRef<[u8]>>(&self, needle: &'n B) -> FinderRev<'n> {
        FinderRev { needle: cow::borrowed(needle.as_ref()) }
    }

    /// Build an owned reverse finder using the given needle from the current
    /// settings.
    #[cfg(feature = "alloc")]
    pub fn build_reverse_owned<B: Into<alloc::boxed::Box<[u8]>>>(
        &self,
        needle: B,
    ) -> FinderRev<'static> {
        FinderRev { needle: cow::owned(needle.into()) }
    }

    /// Configure the prefilter setting for the finder.
    ///
    /// See the documentation for [`Prefilter`] for more discussion on why
    /// you might want to configure this.
    pub fn prefilter(&mut self, prefilter: Prefilter) -> &mut FinderBuilder {
        self.prefilter = prefilter;
        self
    }
}
