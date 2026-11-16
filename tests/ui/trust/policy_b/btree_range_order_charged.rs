//@ needs-trust-verify
//@ edition: 2021
//@ revisions: refused guarded guarded_debug_std
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[refused] check-fail
//@[guarded] check-pass
//@[guarded] ignore-std-debug-assertions (pinned by `guarded_debug_std`)
//@[guarded_debug_std] check-fail
//@[guarded_debug_std] needs-std-debug-assertions
//! `BTreeMap::range` / `BTreeSet::range` ON OUT-OF-ORDER BOUNDS (measured
//! 2026-09-25 on stage-1 `ab7e41892`): a FALSE ACCEPT class. `m.range(a..b)`
//! with `a > b` built rc=0 with a single advisory for the bundled member, and
//! panicked "range start is greater than range end in BTreeMap" as soon as the
//! map was non-empty. `(Excluded(x), Excluded(x))` panics too ("range start and
//! end are equal and excluded").
//!
//! The call now joins the call-site panic family (`slice_method_panic`):
//!
//!   * `refused` — an unguarded `a..b`, `a..=b`, `(Included(a), Excluded(b))`,
//!     `(Excluded(a), Excluded(b))`, a range handed in whole (its bounds are
//!     untraceable, so the row fails closed), and `range_mut`.
//!   * `guarded` — the same calls under a guard that orders the bounds, and the
//!     families that cannot panic (`a..`, `..b`, `..`, an `Unbounded` side).
//!     Runs where std is built WITHOUT debug assertions — the sealed channel's
//!     std and `scripts/recreate_bootstrap.py`'s `debug-assertions-std = false`.
//!   * `guarded_debug_std` — the same seven functions where std IS built with
//!     debug assertions (a `compiler`-profile `bootstrap.toml` without
//!     `debug-assertions-std = false`; docs/KNOWN_HAZARDS.md, "A std built with
//!     debug assertions ..."). The bound row is charged and the guard still
//!     proves it (`1 proved, 0 failed` for the three ordered ranges; the
//!     open-ended ranges mint none), but six of the seven are refused on the
//!     ITERATION, not on the range: with that std the call to
//!     `alloc::collections::btree::mem::replace::<_, _, {closure@LeafRange::
//!     perform_next_checked ..}>` is charged as an absent callee, and a sysroot
//!     routine instantiated at a closure is not a vanilla sysroot callee
//!     (`callee_is_vanilla_sysroot`: `ty::Closure` is never foundational), so
//!     the row is a generic absent callee and fail-closed (`TRUST_VANILLA_DEBUG=1`
//!     prints it NOT-VANILLA for each of the six). Nor would that closure meet
//!     the standard a sysroot fn ITEM in a type argument meets
//!     (`foreign_fn_item_type_arg_is_accounted`): its body is
//!     `front.next_kv().ok().unwrap()` and more, so it can panic and sits in
//!     vcgen's `unwrap` call-site family. Measured 2026-09-30 at origin/main
//!     `f2e5ebbc0fa` and `1f880965f1b`. Until 2026-09-29 the bundled std-member
//!     tolerance accepted them: the `Iterator::count` closure's `Overflow(Add)`
//!     member discarded the whole bundle, this absent callee included. That
//!     member is now a `runtime_checked` row and is NOT the refusal:
//!     `map_range_mut_ordered` carries the same two kinds of member row and
//!     builds. An accepted capability loss of that fix (docs/DECISION_QUEUE.md,
//!     row "Bundled std-member losses"). When that call is judged like any other
//!     vanilla sysroot call these verify again: fold this revision back into
//!     `guarded` then, with the measurement.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::{Bound, Range};

// ---- refused ----

#[cfg(refused)]
pub fn map_range_unordered(m: &BTreeMap<u32, u32>, a: u32, b: u32) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `btree_range_order_charged::map_range_unordered`
    m.range(a..b).count()
}

#[cfg(refused)]
pub fn set_range_inclusive(s: &BTreeSet<u32>, a: u32, b: u32) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `btree_range_order_charged::set_range_inclusive`
    s.range(a..=b).count()
}

#[cfg(refused)]
pub fn map_range_both_excluded(m: &BTreeMap<u32, u32>, a: u32, b: u32) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `btree_range_order_charged::map_range_both_excluded`
    m.range((Bound::Excluded(a), Bound::Excluded(b))).count()
}

#[cfg(refused)]
pub fn map_range_bound_pair(m: &BTreeMap<u32, u32>, a: u32, b: u32) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `btree_range_order_charged::map_range_bound_pair`
    m.range((Bound::Included(a), Bound::Excluded(b))).count()
}

#[cfg(refused)]
pub fn map_range_passed_in(m: &BTreeMap<u32, u32>, r: Range<u32>) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `btree_range_order_charged::map_range_passed_in`
    m.range(r).count()
}

/// `range_mut` runs the same bound check.
#[cfg(refused)]
pub fn map_range_mut_unordered(m: &mut BTreeMap<u32, u32>, a: u32, b: u32) -> usize {
    //[refused]~^ ERROR Trust Level 0 safety verification incomplete for `btree_range_order_charged::map_range_mut_unordered`
    m.range_mut(a..b).count()
}

// ---- guarded: must still verify (`guarded_debug_std`: six are refused) ----

#[cfg(any(guarded, guarded_debug_std))]
pub fn map_range_ordered(m: &BTreeMap<u32, u32>, a: u32, b: u32) -> usize {
    //[guarded_debug_std]~^ ERROR Trust strict verification failed for `btree_range_order_charged::map_range_ordered`
    //[guarded_debug_std]~| NOTE Trust verification: 1 proved, 0 failed
    //[guarded_debug_std]~| NOTE an unproved assumption-panic row — a generic absent callee — keeps the function fail-closed
    if a <= b { m.range(a..b).count() } else { 0 }
}

#[cfg(any(guarded, guarded_debug_std))]
pub fn set_range_inclusive_ordered(s: &BTreeSet<u32>, a: u32, b: u32) -> usize {
    //[guarded_debug_std]~^ ERROR Trust strict verification failed for `btree_range_order_charged::set_range_inclusive_ordered`
    //[guarded_debug_std]~| NOTE Trust verification: 1 proved, 0 failed
    //[guarded_debug_std]~| NOTE an unproved assumption-panic row — a generic absent callee — keeps the function fail-closed
    if a <= b { s.range(a..=b).count() } else { 0 }
}

#[cfg(any(guarded, guarded_debug_std))]
pub fn map_range_both_excluded_ordered(m: &BTreeMap<u32, u32>, a: u32, b: u32) -> usize {
    //[guarded_debug_std]~^ ERROR Trust strict verification failed for `btree_range_order_charged::map_range_both_excluded_ordered`
    //[guarded_debug_std]~| NOTE Trust verification: 1 proved, 0 failed
    //[guarded_debug_std]~| NOTE an unproved assumption-panic row — a generic absent callee — keeps the function fail-closed
    if a < b { m.range((Bound::Excluded(a), Bound::Excluded(b))).count() } else { 0 }
}

#[cfg(any(guarded, guarded_debug_std))]
pub fn map_range_from(m: &BTreeMap<u32, u32>, a: u32) -> usize {
    //[guarded_debug_std]~^ ERROR Trust strict verification failed for `btree_range_order_charged::map_range_from`
    //[guarded_debug_std]~| NOTE Trust verification: 0 proved, 0 failed
    //[guarded_debug_std]~| NOTE an unproved assumption-panic row — a generic absent callee — keeps the function fail-closed
    m.range(a..).count()
}

#[cfg(any(guarded, guarded_debug_std))]
pub fn map_range_to(m: &BTreeMap<u32, u32>, b: u32) -> usize {
    //[guarded_debug_std]~^ ERROR Trust strict verification failed for `btree_range_order_charged::map_range_to`
    //[guarded_debug_std]~| NOTE Trust verification: 0 proved, 0 failed
    //[guarded_debug_std]~| NOTE an unproved assumption-panic row — a generic absent callee — keeps the function fail-closed
    m.range(..b).count()
}

#[cfg(any(guarded, guarded_debug_std))]
pub fn map_range_unbounded_end(m: &BTreeMap<u32, u32>, a: u32) -> usize {
    //[guarded_debug_std]~^ ERROR Trust strict verification failed for `btree_range_order_charged::map_range_unbounded_end`
    //[guarded_debug_std]~| NOTE Trust verification: 0 proved, 0 failed
    //[guarded_debug_std]~| NOTE an unproved assumption-panic row — a generic absent callee — keeps the function fail-closed
    m.range((Bound::Excluded(a), Bound::Unbounded)).count()
}

/// Builds with a debug std too, beside its own two `runtime_checked`
/// `Iterator::count` member rows (the closure and its `call_mut`), as the six
/// refused functions have.
#[cfg(any(guarded, guarded_debug_std))]
pub fn map_range_mut_ordered(m: &mut BTreeMap<u32, u32>, a: u32, b: u32) -> usize {
    //[guarded_debug_std]~^ NOTE Trust verification: 1 proved, 0 failed
    if a <= b { m.range_mut(a..b).count() } else { 0 }
}
