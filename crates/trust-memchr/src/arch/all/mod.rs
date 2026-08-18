/*!
Contains architecture independent routines.

In upstream memchr these are the "fallback" implementations used when no vector
instruction set is available. Here they are the only implementations.
*/

pub mod memchr;
pub mod packedpair;

use crate::scan;

/// Returns true if and only if `needle` is a prefix of `haystack`.
///
/// # Inlining
///
/// This routine is marked `inline(always)`. If you want to call this function
/// in a way that is not always inlined, you'll need to wrap a call to it in
/// another function that is marked as `inline(never)` or just `inline`.
#[inline(always)]
pub fn is_prefix(haystack: &[u8], needle: &[u8]) -> bool {
    scan::is_prefix(haystack, needle)
}

/// Returns true if and only if `needle` is a suffix of `haystack`.
///
/// # Inlining
///
/// This routine is marked `inline(always)`. If you want to call this function
/// in a way that is not always inlined, you'll need to wrap a call to it in
/// another function that is marked as `inline(never)` or just `inline`.
#[inline(always)]
pub fn is_suffix(haystack: &[u8], needle: &[u8]) -> bool {
    scan::is_suffix(haystack, needle)
}

/// Compare corresponding bytes in `x` and `y` for equality.
///
/// That is, this returns true if and only if `x.len() == y.len()` and
/// `x[i] == y[i]` for all `0 <= i < x.len()`.
///
/// # Inlining
///
/// This routine is marked `inline(always)`. If you want to call this function
/// in a way that is not always inlined, you'll need to wrap a call to it in
/// another function that is marked as `inline(never)` or just `inline`.
#[inline(always)]
pub fn is_equal(x: &[u8], y: &[u8]) -> bool {
    scan::is_equal(x, y)
}
