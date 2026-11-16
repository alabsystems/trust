//! The census's AUDITED effect-free lists for fd-inherit (Critique C-13: an
//! allowlist per property, each entry with its reason).
//!
//! A std / core / alloc call is translated only if it is a std-table row,
//! a `Command` builder method, or on one of these lists; anything else is a
//! named refusal (`PC-UNKNOWN-STD`). An entry here touches no descriptor,
//! description, process or limit, and runs no user code — EXCEPT through
//! the trait impls of its generic arguments where `dispatch` says so
//! (`Ord::cmp` for `min`, `PartialOrd` for `Range::contains`): such a call
//! is admitted only when the census sees every argument is an integer (a
//! user impl could run anything), else it is refused.
//!
//! A closure or fn item handed to any std / core / alloc / upstream callee
//! may be called by it: no entry here takes one, so such a call is never
//! admitted through these lists (Critique review F3: `for_each(|x| dup(x))`).
//! What a list entry's arguments DROP inside the callee (`unwrap_or` drops
//! the unused value) is the drop gate's business: the value is a local or a
//! temporary of the caller, which the gate sees.

use crate::sites::strip_generics_cow;

/// One audited entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pure {
    pub path: &'static str,
    pub why: &'static str,
    /// The call runs trait impls of its generic arguments: admitted only
    /// with integer arguments.
    pub dispatch: bool,
}

const fn pure(path: &'static str, why: &'static str) -> Pure {
    Pure { path, why, dispatch: false }
}

const fn dispatch(path: &'static str, why: &'static str) -> Pure {
    Pure { path, why, dispatch: true }
}

/// std (and the core/alloc items std re-exports; matched with `core::` /
/// `alloc::` read as `std::`).
pub const PURE_STD: &[Pure] = &[
    pure("std::io::Error::from_raw_os_error", "builds an error value"),
    pure("std::io::Error::raw_os_error", "reads an error value"),
    pure("std::io::Error::last_os_error", "reads errno"),
    pure("std::io::Error::other", "builds an error value (its payload's drop is the caller's)"),
    pure("std::io::Error::new", "builds an error value (its payload's drop is the caller's)"),
    pure("std::io::Error::kind", "reads an error value"),
    pure(
        "std::option::Option::unwrap_or",
        "moves a value out (the unused one's drop is the caller's)",
    ),
    pure(
        "std::result::Result::unwrap_or",
        "moves a value out (the unused one's drop is the caller's)",
    ),
    pure("std::option::Option::is_some", "reads a tag"),
    pure("std::option::Option::is_none", "reads a tag"),
    pure("std::result::Result::ok", "moves a value out (the error's drop is the caller's)"),
    pure("std::result::Result::is_ok", "reads a tag"),
    pure("std::result::Result::is_err", "reads a tag"),
    pure("std::mem::size_of", "a constant"),
    pure("std::mem::align_of", "a constant"),
    dispatch("std::ops::Range::contains", "compares through PartialOrd"),
    dispatch("std::cmp::min", "compares through Ord"),
    dispatch("std::cmp::max", "compares through Ord"),
    pure("std::ptr::null_mut", "a constant"),
    pure("std::ptr::null", "a constant"),
    pure("std::hint::must_use", "identity"),
    pure("std::hint::black_box", "identity"),
    pure("std::intrinsics::discriminant_value", "reads a tag"),
];

/// core / alloc items std does not re-export under the same path.
pub const PURE_CORE: &[Pure] = &[
    pure("alloc::boxed::Box::new", "moves a value to the heap (no user code)"),
    pure("core::slice::<impl [T]>::iter", "builds a slice iterator"),
    pure("core::slice::<impl [T]>::len", "reads a length"),
    pure("core::num::<impl i32>::unsigned_abs", "integer arithmetic"),
    pure("core::num::<impl i32>::wrapping_add", "integer arithmetic"),
    pure("core::num::<impl i32>::checked_add", "integer arithmetic"),
];

/// Whether `a` (a path, generics stripped) is entry `p` (with `core::` /
/// `alloc::` read as `std::` for std's re-exports).
fn matches(a: &str, p: &str) -> bool {
    if a == p || strip_generics_cow(p) == a {
        return true;
    }
    if let Some(rest) = a.strip_prefix("core::").or_else(|| a.strip_prefix("alloc::")) {
        return p.strip_prefix("std::") == Some(rest);
    }
    false
}

/// A `for` over an integer range: HIR desugars it into
/// `<Range<int> as IntoIterator>::into_iter` and `<Range<int> as
/// Iterator>::next` calls (`Step` for integers: no user code). Recognized
/// only with the concrete integer type in the path (the host's spelling);
/// a generic `Range<A>` is not.
pub const RANGE_ITERATION: Pure = pure(
    "<std::ops::Range<{integer}> as std::iter::{IntoIterator::into_iter,Iterator::next}>",
    "integer range iteration",
);

const INTEGERS: &[&str] =
    &["i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize"];

fn range_iteration(path: &str) -> bool {
    let Some(rest) = path.strip_prefix('<') else { return false };
    let Some((self_ty, method)) = rest.split_once(" as ") else { return false };
    let int_range =
        ["std::ops::Range<", "core::ops::Range<", "std::ops::RangeInclusive<"].iter().any(|pre| {
            self_ty
                .strip_prefix(pre)
                .and_then(|t| t.strip_suffix('>'))
                .is_some_and(|t| INTEGERS.contains(&t))
        });
    int_range
        && [
            "std::iter::IntoIterator>::into_iter",
            "core::iter::IntoIterator>::into_iter",
            "std::iter::Iterator>::next",
            "core::iter::Iterator>::next",
        ]
        .contains(&method)
}

/// The audited entry `path` names.
#[must_use]
pub fn lookup_str(path: &str) -> Option<&'static Pure> {
    if range_iteration(path) {
        return Some(&RANGE_ITERATION);
    }
    let stripped = strip_generics_cow(path);
    PURE_STD.iter().chain(PURE_CORE).find(|e| matches(&stripped, e.path))
}

/// The audited entry any of `paths` names.
#[must_use]
pub fn lookup(paths: &[String]) -> Option<&'static Pure> {
    if paths.iter().any(|p| range_iteration(p)) {
        return Some(&RANGE_ITERATION);
    }
    let stripped: Vec<_> = paths.iter().map(|p| strip_generics_cow(p)).collect();
    PURE_STD.iter().chain(PURE_CORE).find(|e| stripped.iter().any(|s| matches(s, e.path)))
}

/// Whether a path is a panic (the path ends; premise P-PANIC-ENDS-PATH).
#[must_use]
pub fn is_panic(path: &str) -> bool {
    let p = strip_generics_cow(path);
    p.contains("::panicking::")
        || p == "std::process::abort"
        || p == "core::intrinsics::abort"
        || p.ends_with("::unwrap_failed")
        || p.ends_with("::expect_failed")
        || p.ends_with("::begin_panic")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entries_match_their_reexports_and_generic_spellings() {
        let p = |s: &str| vec![s.to_string()];
        assert!(lookup(&p("std::option::Option::<T>::unwrap_or")).is_some());
        assert!(lookup(&p("core::ptr::null_mut")).is_some());
        assert!(lookup(&p("alloc::boxed::Box::new")).is_some());
        assert!(lookup(&p("std::ops::Range::<Idx>::contains")).is_some_and(|e| e.dispatch));
        // A `for` over an integer range, in the host's spelling; not a
        // generic or user iterator.
        assert!(lookup(&p("<std::ops::Range<i32> as std::iter::Iterator>::next")).is_some());
        assert!(
            lookup(&p("<std::ops::Range<i32> as std::iter::IntoIterator>::into_iter")).is_some()
        );
        assert!(lookup(&p("<std::ops::Range<A> as std::iter::Iterator>::next")).is_none());
        assert!(lookup(&p("<MyIter as std::iter::Iterator>::next")).is_none());
        // Closure-taking combinators are never on the lists.
        for path in [
            "core::iter::Iterator::for_each",
            "std::iter::Iterator::for_each",
            "std::option::Option::<T>::map",
            "std::option::Option::<T>::unwrap_or_else",
            "core::iter::Iterator::count",
        ] {
            assert!(lookup(&p(path)).is_none(), "{path}");
        }
    }

    #[test]
    fn every_entry_has_a_reason() {
        for e in PURE_STD.iter().chain(PURE_CORE) {
            assert!(!e.why.is_empty(), "{}", e.path);
        }
    }
}
