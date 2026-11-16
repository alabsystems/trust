/*!
The scalar scanning core. Every search in this crate bottoms out here.

Everything is a plain index loop over a `&[u8]` in a free function. That is not
a stylistic choice; it is the shape Trust proves. The constraints below were
each measured against `trustc` with verification on (the default), and the
probes that established them are recorded next to the rule:

* **Hoist the length into a local and bound the loop by it.** A loop that
  re-reads `self.field.len()` in its own condition does not prove.
* **A helper must be a free function.** A call to a free function — private,
  `pub`, or `#[inline]` — lowers into the caller's bundle and costs nothing. A
  call to an *inherent associated constructor* (`Cursor::new(..)`) does not: it
  resurfaces in the caller as an absent callee whose panic path stays
  reachable, which is a hard error under the fail-closed default. So there are
  no constructor methods here, and callers build [`Cursor`] as a struct
  literal.
* **Give the reverse scans an explicit in-bounds guard.** In a descending loop
  the only condition is the *lower* bound (`while i > start`), so the upper
  bound is a loop invariant the solver does not rediscover, and the bounds
  check is refuted — with a counterexample that is not even reachable. The
  redundant `if i < len` restores it, and the check then proves.
* **Bound a compound scan by subtraction computed up front** (`let last = h - n;
  while i <= last`), never by addition in the condition (`while i + n <= h`),
  which raises an unprovable `overflow:add`.
* **Walk a reverse compound scan by an ascending counter** (`let j = last - d`),
  not by decrementing the index itself: the descending form refutes `j + k`.
* **Never route a length or an index through a std call.** An absent callee's
  return value is opaque and the bound cannot be re-derived, so `min`/`max` are
  hand-inlined as an `if`.
* **Guard every `+ 1` on a value the solver cannot bound.** An offset that
  arrives as a bare `usize` really can be `usize::MAX`, and the overflow is a
  genuine refutation rather than a modelling artifact.
* **No `assert!`/`debug_assert!`.** They are provable only as runtime checks.
*/

/// A half-open `[start, end)` cursor into a haystack, shared by every
/// double-ended byte iterator in this crate.
///
/// `start` is where the next forward search begins and `end` is where the next
/// reverse search begins; they converge and the iterator is exhausted when they
/// meet. Offsets are always relative to the start of `haystack`, so a yielded
/// position is directly a valid index into it.
///
/// There is deliberately no `Cursor::new`: see the module docs.
#[derive(Clone, Debug)]
pub(crate) struct Cursor<'h> {
    pub(crate) haystack: &'h [u8],
    pub(crate) start: usize,
    pub(crate) end: usize,
}

/// `Iterator::size_hint` for a byte iterator: at most one match per remaining
/// byte, and no lower bound.
#[inline]
pub(crate) fn cursor_size_hint(start: usize, end: usize) -> (usize, Option<usize>) {
    #[expect(
        clippy::implicit_saturating_sub,
        reason = "the subtraction stays in this body, where trust check certifies it cannot \
                  overflow; end.saturating_sub(start) moves it into a trusted core call and \
                  leaves this function with no obligations (measured 2026-11-14)"
    )]
    let remaining = if end > start { end - start } else { 0 };
    (0, Some(remaining))
}

/// The offset just past `at`, saturating.
///
/// Hand-inlined `saturating_add(1)`. `at` is always a real offset into a live
/// slice, so the saturating branch is unreachable in practice — but `at`
/// arrives as an unconstrained `usize` and the solver is right to refuse the
/// bare `at + 1`.
#[inline]
pub(crate) fn step_past(at: usize) -> usize {
    if at < usize::MAX { at + 1 } else { usize::MAX }
}

/// `a + b`, saturating. Hand-inlined `saturating_add` for the same reason as
/// [`step_past`].
#[inline]
pub(crate) fn add_saturating(a: usize, b: usize) -> usize {
    let room = usize::MAX - b;
    if a > room { usize::MAX } else { a + b }
}

/// First offset in `[start, end)` whose byte is `n1`.
#[inline]
pub(crate) fn find1(haystack: &[u8], start: usize, end: usize, n1: u8) -> Option<usize> {
    let len = haystack.len();
    let stop = if end < len { end } else { len };
    let mut i = start;
    while i < stop {
        if haystack[i] == n1 {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Last offset in `[start, end)` whose byte is `n1`.
#[inline]
pub(crate) fn rfind1(haystack: &[u8], start: usize, end: usize, n1: u8) -> Option<usize> {
    let len = haystack.len();
    let stop = if end < len { end } else { len };
    let mut i = stop;
    while i > start {
        i -= 1;
        if i < len && haystack[i] == n1 {
            return Some(i);
        }
    }
    None
}

/// Number of offsets in `[start, end)` whose byte is `n1`.
#[inline]
pub(crate) fn count1(haystack: &[u8], start: usize, end: usize, n1: u8) -> usize {
    let len = haystack.len();
    let stop = if end < len { end } else { len };
    let mut found = 0usize;
    let mut i = start;
    while i < stop {
        if haystack[i] == n1 {
            found = step_past(found);
        }
        i += 1;
    }
    found
}

/// First offset in `[start, end)` whose byte is `n1` or `n2`.
#[inline]
pub(crate) fn find2(haystack: &[u8], start: usize, end: usize, n1: u8, n2: u8) -> Option<usize> {
    let len = haystack.len();
    let stop = if end < len { end } else { len };
    let mut i = start;
    while i < stop {
        let b = haystack[i];
        if b == n1 || b == n2 {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Last offset in `[start, end)` whose byte is `n1` or `n2`.
#[inline]
pub(crate) fn rfind2(haystack: &[u8], start: usize, end: usize, n1: u8, n2: u8) -> Option<usize> {
    let len = haystack.len();
    let stop = if end < len { end } else { len };
    let mut i = stop;
    while i > start {
        i -= 1;
        if i < len {
            let b = haystack[i];
            if b == n1 || b == n2 {
                return Some(i);
            }
        }
    }
    None
}

/// First offset in `[start, end)` whose byte is `n1`, `n2` or `n3`.
#[inline]
pub(crate) fn find3(
    haystack: &[u8],
    start: usize,
    end: usize,
    n1: u8,
    n2: u8,
    n3: u8,
) -> Option<usize> {
    let len = haystack.len();
    let stop = if end < len { end } else { len };
    let mut i = start;
    while i < stop {
        let b = haystack[i];
        if b == n1 || b == n2 || b == n3 {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Last offset in `[start, end)` whose byte is `n1`, `n2` or `n3`.
#[inline]
pub(crate) fn rfind3(
    haystack: &[u8],
    start: usize,
    end: usize,
    n1: u8,
    n2: u8,
    n3: u8,
) -> Option<usize> {
    let len = haystack.len();
    let stop = if end < len { end } else { len };
    let mut i = stop;
    while i > start {
        i -= 1;
        if i < len {
            let b = haystack[i];
            if b == n1 || b == n2 || b == n3 {
                return Some(i);
            }
        }
    }
    None
}

/// True when `needle` occurs in `haystack` at offset `at`.
///
/// `get` rather than indexing: the compound offset `at + k` carries no bound
/// the solver can re-derive across the two loops, and a `None` here is
/// unreachable but costs nothing to handle. The offset is added saturating for
/// the same reason `step_past` is — `at` arrives as an unconstrained `usize`.
#[inline]
fn matches_at(haystack: &[u8], needle: &[u8], at: usize, n: usize) -> bool {
    let mut k = 0usize;
    let mut equal = true;
    while equal && k < n {
        match (haystack.get(add_saturating(at, k)), needle.get(k)) {
            (Some(h), Some(x)) => {
                if *h == *x {
                    k += 1;
                } else {
                    equal = false;
                }
            }
            _ => equal = false,
        }
    }
    equal
}

/// Offset of the first occurrence of `needle` in `haystack`.
///
/// An empty needle matches at `0`, which is what upstream reports and what the
/// `memmem` iterators depend on.
///
/// # Complexity
///
/// `O(haystack.len() * needle.len())` worst case, constant space. Upstream is
/// Two-Way and guarantees `O(haystack.len() + needle.len())`. That is the one
/// documented property of upstream this crate does not yet reproduce; it is a
/// speed obligation, not a correctness one, and closing it is a separate,
/// separately-verified step. Correctness first.
#[inline]
pub(crate) fn find_substring(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    let n = needle.len();
    let h = haystack.len();
    if n == 0 {
        return Some(0);
    }
    if n > h {
        return None;
    }
    let last = h - n;
    let mut i = 0usize;
    while i <= last {
        if matches_at(haystack, needle, i, n) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Offset of the last occurrence of `needle` in `haystack`.
///
/// An empty needle matches at `haystack.len()`, which is what upstream reports
/// and what `FindRevIter` depends on to terminate.
///
/// The scan walks *down* from the last candidate but counts *up*, because a
/// decrementing index loses the bound that keeps `j + k` in range.
///
/// Same complexity note as [`find_substring`].
#[inline]
pub(crate) fn rfind_substring(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    let n = needle.len();
    let h = haystack.len();
    if n == 0 {
        return Some(h);
    }
    if n > h {
        return None;
    }
    let last = h - n;
    let mut d = 0usize;
    while d <= last {
        let j = last - d;
        if matches_at(haystack, needle, j, n) {
            return Some(j);
        }
        d += 1;
    }
    None
}

/// Byte-wise equality.
#[inline]
pub(crate) fn is_equal(x: &[u8], y: &[u8]) -> bool {
    let xlen = x.len();
    let ylen = y.len();
    if xlen != ylen {
        return false;
    }
    matches_at(x, y, 0, xlen)
}

/// True when `needle` is a prefix of `haystack`.
#[inline]
pub(crate) fn is_prefix(haystack: &[u8], needle: &[u8]) -> bool {
    let n = needle.len();
    let h = haystack.len();
    if n > h {
        return false;
    }
    matches_at(haystack, needle, 0, n)
}

/// True when `needle` is a suffix of `haystack`.
#[inline]
pub(crate) fn is_suffix(haystack: &[u8], needle: &[u8]) -> bool {
    let n = needle.len();
    let h = haystack.len();
    if n > h {
        return false;
    }
    let base = h - n;
    matches_at(haystack, needle, base, n)
}
