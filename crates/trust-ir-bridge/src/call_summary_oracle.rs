// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! # Bridge call-summary soundness + completeness oracle (rung-1 frontier)
//!
//! `total_no_panic_call_summary` decides which callees the bridge may lower to an
//! obligation-free `Inst::Undef` (treated as cannot-panic) instead of a real, may-panic
//! `Inst::Call`. Mis-including a callee that CAN panic is the exact false-proof class of
//! the 2026-06-19 sweep (HOLE-6C: a user type ending in a total suffix; hunt-9:
//! `saturating_div` still panics on div-by-zero). This is the bridge-domain analogue of
//! the trust-mc program-space oracle: it pins that soundness-critical string decision
//! against curated GROUND-TRUTH std semantics, in two directions:
//!
//!   * SOUNDNESS — every genuinely-panicking / user-code-dispatching callee, and every
//!     adversarial user type that merely *ends* in a total suffix, MUST be classified
//!     not-total. A regression that flips one to total is a false-proof; this test fails.
//!   * COMPLETENESS — of the genuinely-total std callees, how many does the allowlist
//!     recognize? Unrecognized totals are precision lost to conservatism — rung-1's
//!     target. Reported (not failed): it quantifies the bridge precision gap.

use crate::lower::{is_element_free_total_std_type, total_no_panic_call_summary};

/// Callees that GENUINELY PANIC or dispatch into user code (Hash/Eq/Ord/Display/Drop or
/// a closure) — every one MUST be classified not-total. Strings are realistic
/// monomorphized def-paths (the decision strips `<…>` generics, then anchors on
/// core/alloc/std and suffix-matches).
const PANICKING: &[&str] = &[
    "core::option::Option::<u32>::unwrap",     // panics on None
    "core::option::Option::<u32>::expect",     // panics on None
    "core::result::Result::<u32, ()>::unwrap", // panics on Err
    "core::result::Result::<u32, ()>::expect", // panics on Err
    "alloc::vec::Vec::<u32>::remove",          // panics on OOB index
    "alloc::vec::Vec::<u32>::insert",          // panics on OOB index
    "alloc::vec::Vec::<u32>::swap_remove",     // panics on OOB index
    "<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index", // Vec[i] OOB panic
    "<[u32] as core::ops::index::Index<usize>>::index", // slice[i] OOB panic
    "core::option::Option::<u32>::map",        // runs a user closure
    "core::option::Option::<u32>::unwrap_or_else", // runs a user closure
    "alloc::string::ToString::to_string",      // dispatches to Display::fmt (user)
    "std::collections::hash::map::HashMap::<u32, u32>::get", // Hash+Eq on key (user)
    "core::slice::<impl [u32]>::contains",     // Eq on elements (user)
    "core::num::<impl i32>::saturating_div",   // hunt-9: still panics on div-by-zero
    "core::num::<impl i32>::saturating_rem",   // hunt-9: still panics on rem-by-zero
    "core::num::<impl i32>::wrapping_div",     // wraps only MIN/-1; panics on div-by-zero
    "core::num::<impl i32>::wrapping_rem",     // wraps only MIN/-1; panics on rem-by-zero
    "core::num::<impl i64>::wrapping_div_euclid", // euclid twin: same zero-divisor panic
    "core::num::<impl i32>::overflowing_div",  // (val, bool) pair; panics on div-by-zero
    "core::num::<impl i32>::overflowing_rem",  // (val, bool) pair; panics on rem-by-zero
    // SUBTLE traps (the class that makes rung-1 recovery dangerous — encoded as guards so a
    // future "obviously total" addition that overlooks them is caught):
    "core::result::Result::<u32, ErrT>::unwrap_or", // consumes self; DROPS the Err payload
    // (a user Drop can panic) — unlike
    // Option::unwrap_or, whose None has no payload.
    "core::mem::take::<MyT>", // dispatches to Default::default() (user)
    "alloc::vec::Vec::<ElemT>::truncate", // DROPS removed elements (user Drop)
    "alloc::vec::Vec::<ElemT>::dedup", // PartialEq on elements (user)
    "alloc::vec::Vec::<ElemT>::retain", // runs a user closure
    "core::option::Option::<MyT>::map_or", // runs a user closure
    "core::option::Option::<MyT>::get_or_insert_with", // runs a user closure
    // NEAR-NEIGHBOR pins for the T3 aterm-scrollback totals (`Vec::shrink_to_fit` /
    // `BTreeMap::iter` / `MaybeUninit::new` / `RangeInclusive::new`): the closest
    // sibling of each new entry that must NOT ride it. Flipping any of these to
    // total is the regression this oracle exists to catch.
    "alloc::vec::Vec::<u32>::shrink_to", // DELIBERATE pin: the PARAMETERIZED
    // shrink sibling is kept unmodeled/
    // fail-closed — the exact `_fit`
    // suffix must never widen to it
    "alloc::collections::btree::map::BTreeMap::<UserOrdK, u32>::get", // Ord on the KEY
    // (user code can panic) — the keyed
    // lookup the iter-ctor entry must
    // never be confused with
    "core::mem::maybe_uninit::MaybeUninit::<u32>::assume_init", // the UNWRAP direction:
                                                                // init-validity is the unsafe
                                                                // caller's obligation (and
                                                                // assert_inhabited panics for
                                                                // uninhabited T); a total summary
                                                                // would silently drop it
];

/// Adversarial USER types whose path merely ENDS in a genuine total suffix — the HOLE-6C
/// / Attack-5 false-proof shape. None start with core/alloc/std, so all MUST be not-total.
const ADVERSARIAL: &[&str] = &[
    "mycrate::vec::Vec::<u32>::new", // ends in ::Vec::new but is a USER Vec
    "myapp::text::str::find",        // ends in ::str::find but is a USER str
    "userlib::Option::<u32>::is_some", // ends in ::Option::is_some but USER
    "company::collections::String::len", // ends in ::String::len but USER
    "mycrate::slice::first_mut",     // ends in ::slice::first_mut but USER (anchor must reject)
    "userlib::Vec::<u32>::as_mut_slice", // ends in ::Vec::as_mut_slice but USER
    "company::collections::String::from_utf16_lossy", // ends in the new total suffix but USER
    // The T3 aterm-scrollback additions' user-path twins (crate-origin anchor must
    // reject every one — HOLE-6C shape):
    "mycrate::vec::Vec::<u32>::shrink_to_fit", // USER Vec ending in the new suffix
    "mycrate::collections::BTreeMap::<String, u32>::iter", // USER BTreeMap
    "userlib::mem::MaybeUninit::<u32>::new",   // USER MaybeUninit
    "company::ops::RangeInclusive::<usize>::new", // USER RangeInclusive
];

/// GENUINELY-TOTAL std callees (no user code, cannot panic). Recognition rate = the
/// bridge's call-summary COMPLETENESS. Entries marked `// GAP` are total but currently
/// unrecognized — the precision rung-1 must reclaim.
const SHOULD_BE_TOTAL: &[&str] = &[
    "alloc::vec::Vec::<u32>::new",
    "alloc::vec::Vec::<u32>::push",
    "alloc::vec::Vec::<u32>::len",
    "alloc::vec::Vec::<u32>::is_empty",
    "alloc::vec::Vec::<u32>::capacity",
    "core::str::<impl str>::len",
    "core::str::<impl str>::is_empty",
    "core::str::<impl str>::find",
    "core::option::Option::<u32>::is_some",
    "core::option::Option::<u32>::is_none",
    "core::slice::<impl [u32]>::get",
    "core::slice::<impl [u32]>::len",
    "alloc::string::String::new",
    "alloc::string::String::len",
    // rung-1 recovery: the UTF-16 total pair. `str::encode_utf16` is a lazy iterator
    // factory (&self-only, no alloc, no user code); `String::from_utf16_lossy` decodes
    // `&[u16]` replacing ill-formed units with U+FFFD (no user code, no closure, never
    // panics — OOM excluded). Both abort whole-function lowering when unrecognized.
    "core::str::<impl str>::encode_utf16",
    "alloc::string::String::from_utf16_lossy",
    // GAP candidates — genuinely total (return Option, move out, run NO user code and
    // NO element Drop, cannot panic), currently NOT in the allowlist. The precision
    // rung-1 reclaims by adding them.
    "alloc::vec::Vec::<u32>::pop",
    "alloc::string::String::pop",
    // rung-1 recovery: the `&mut` structural-accessor twins of already-recognized total
    // accessors (`first`/`last`/`get_mut`/`as_slice`). Bounds-checked, return Option<&mut T> /
    // &mut [T], run NO element user code, cannot panic — same soundness class as their `&` twins.
    "core::slice::<impl [u32]>::first_mut",
    "core::slice::<impl [u32]>::last_mut",
    "alloc::vec::Vec::<u32>::as_mut_slice",
    // rung-1 recovery: the integer endian/bit-twiddling family (`core::num` inherent
    // const fns). Copy scalar operands by value, no user code, no Drop, panic-free
    // (fixed-length byte arrays => no bounds check; rotate shift masked mod BITS;
    // is_multiple_of is the panic-free divisibility predicate). Same soundness class
    // as the recognized checked_*/saturating_* arithmetic.
    // The wrapping_/overflowing_ non-division families: defined wraparound on
    // Copy scalars (or the `(value, overflowed)` pair), no user code, no panic
    // — the checked_/saturating_ soundness class. The DIVISION members are in
    // PANICKING above (zero divisor still panics).
    "core::num::<impl i128>::wrapping_neg",
    "core::num::<impl u32>::wrapping_add",
    "core::num::<impl u64>::wrapping_sub",
    "core::num::<impl i64>::wrapping_mul",
    "core::num::<impl u32>::wrapping_shl",
    "core::num::<impl i32>::overflowing_add",
    "core::num::<impl u64>::overflowing_mul",
    "core::num::<impl u32>::from_le_bytes",
    "core::num::<impl u32>::from_be_bytes",
    "core::num::<impl u32>::from_ne_bytes",
    "core::num::<impl u32>::to_le_bytes",
    "core::num::<impl u32>::to_be_bytes",
    "core::num::<impl u32>::to_ne_bytes",
    "core::num::<impl u32>::to_le",
    "core::num::<impl u32>::to_be",
    "core::num::<impl u32>::to_ne",
    "core::num::<impl u32>::trailing_zeros",
    "core::num::<impl u32>::leading_zeros",
    "core::num::<impl u32>::count_ones",
    "core::num::<impl u64>::rotate_left",
    "core::num::<impl u64>::rotate_right",
    "core::num::<impl u32>::swap_bytes",
    "core::num::<impl usize>::is_multiple_of",
    // Orca autoformalization rung: the infallible conversion trait methods. TOTAL by
    // the `From`/`Into` contract (fallible conversion is `TryFrom`/`TryInto`); the
    // single largest native-incomplete cluster (`.into()`, `String::from`, integer
    // widening, struct-field conversions).
    "core::convert::From::from",
    "core::convert::Into::into",
    // T3 rung-1 recovery (aterm-scrollback batch): realloc-shrink with no element
    // drops (`shrink_to_fit`), the zero-comparison in-order iterator ctor
    // (`BTreeMap::iter`), the const union wrap (`MaybeUninit::new`), and the const
    // struct ctor (`RangeInclusive::new`) — see the allowlist entries' per-entry
    // justifications; their panicking/parameterized near-neighbors are pinned in
    // PANICKING above.
    "alloc::vec::Vec::<u32>::shrink_to_fit",
    "alloc::collections::btree::map::BTreeMap::<alloc::string::String, u32>::iter",
    "core::mem::maybe_uninit::MaybeUninit::<u32>::new",
    "core::ops::range::RangeInclusive::<usize>::new",
];

#[test]
fn call_summary_oracle_soundness() {
    let mut violations: Vec<String> = Vec::new();
    for &callee in PANICKING.iter().chain(ADVERSARIAL.iter()) {
        if total_no_panic_call_summary(callee) {
            violations.push(format!(
                "FALSE PROVE source: `{callee}` is classified cannot-panic (total), but it \
                 panics or dispatches into user code — its panic obligation would be dropped"
            ));
        }
    }
    assert!(
        violations.is_empty(),
        "bridge call-summary SOUNDNESS violations ({} of {}):\n{}",
        violations.len(),
        PANICKING.len() + ADVERSARIAL.len(),
        violations.join("\n")
    );
    eprintln!(
        "bridge call-summary oracle: {} panicking + {} adversarial callees, all correctly \
         classified not-total (no false-proof source)",
        PANICKING.len(),
        ADVERSARIAL.len()
    );
}

/// K-PARAMETERIZED std types: their derived Clone/PartialEq/Default/Ord/Hash dispatch
/// INTO the element/payload type `K` (whose user impl we cannot see and which can panic).
/// The Attack-5 contract: every one MUST be classified NOT element-free-total, so the
/// call fails closed. `def_path_str` carries no generics, so each name is bare.
const K_PARAMETERIZED: &[&str] = &[
    "alloc::vec::Vec",
    "alloc::boxed::Box",
    "core::option::Option",
    "core::result::Result",
    "std::collections::hash::map::HashMap",
    "alloc::collections::btree::map::BTreeMap",
    "alloc::rc::Rc",
    "alloc::sync::Arc",
    "alloc::collections::vec_deque::VecDeque",
    "core::cell::RefCell",
    "core::cmp::Reverse",
    // THE HOLE this oracle found: `Wrapping<T>` is an UNBOUNDED transparent newtype
    // (unlike `NonZero<T>`, whose `ZeroablePrimitive` bound is sealed to primitives), so
    // `Wrapping<UserType>`'s derived Clone/eq/cmp dispatch into the user type — exactly
    // the Attack-5 shape closed for Vec/Box. Must be NOT element-free.
    "core::num::Wrapping",
    "mycrate::domain::MyAdt", // a user ADT
];

/// Genuinely ELEMENT-FREE total std leaves: parameter-free (String bottoms out in u8;
/// Ordering/Duration have no element) or sealed-to-primitive (NonZero). MUST be total.
const ELEMENT_FREE: &[&str] = &[
    "alloc::string::String",
    "std::string::String",
    "core::cmp::Ordering",
    "core::time::Duration",
    "std::time::Duration",
    "core::num::NonZeroU32",
    "core::num::NonZeroI64",
];

#[test]
fn element_free_oracle_soundness() {
    let mut violations: Vec<String> = Vec::new();
    for &name in K_PARAMETERIZED {
        if is_element_free_total_std_type(name) {
            violations.push(format!(
                "FALSE PROVE source: `{name}` is classified element-free-total, but it is \
                 K-parameterized — its Clone/eq/cmp dispatches into the element type, which \
                 can panic (Attack-5 shape); the panic obligation would be dropped"
            ));
        }
    }
    assert!(
        violations.is_empty(),
        "element-free SOUNDNESS violations ({} of {}):\n{}",
        violations.len(),
        K_PARAMETERIZED.len(),
        violations.join("\n")
    );
    // And the genuine element-free leaves must still be recognized (no over-removal).
    let missing: Vec<&str> =
        ELEMENT_FREE.iter().copied().filter(|n| !is_element_free_total_std_type(n)).collect();
    assert!(
        missing.is_empty(),
        "element-free leaves wrongly rejected (precision regression): {}",
        missing.join(", ")
    );
    eprintln!(
        "element-free oracle: {} K-parameterized types all not-total (no Attack-5 source), \
         {} element-free leaves all total",
        K_PARAMETERIZED.len(),
        ELEMENT_FREE.len()
    );
}

#[test]
fn call_summary_oracle_completeness() {
    let recognized: Vec<&str> =
        SHOULD_BE_TOTAL.iter().copied().filter(|c| total_no_panic_call_summary(c)).collect();
    let gaps: Vec<&str> =
        SHOULD_BE_TOTAL.iter().copied().filter(|c| !total_no_panic_call_summary(c)).collect();
    eprintln!(
        "bridge call-summary COMPLETENESS: {}/{} genuinely-total callees recognized ({}%)",
        recognized.len(),
        SHOULD_BE_TOTAL.len(),
        recognized.len() * 100 / SHOULD_BE_TOTAL.len().max(1)
    );
    if !gaps.is_empty() {
        eprintln!("  precision GAPS (total but unrecognized — rung-1 target): {}", gaps.join(", "));
    }
    // Non-vacuity: the allowlist must recognize a solid base of total callees.
    assert!(
        recognized.len() >= 8,
        "expected the allowlist to recognize the common total std callees, got {}",
        recognized.len()
    );
}
