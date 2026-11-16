//@ needs-trust-verify
//@ edition: 2021
//@ revisions: insert insert_owned swap range range_mut index index_mut total_members swap_remove_back swap_remove_front insert_guarded insert_front
//@ revisions: fnitem_insert fnitem_swap fnitem_range fnitem_opt_rotate fnitem_u64_insert fnitem_range_mut fnitem_trait_index fnitem_trait_index_mut
//@ revisions: fnitem_split_off fnitem_drain fnitem_rotate_left fnitem_collections_insert fnitem_neg_index
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[insert] check-fail
//@[insert_owned] check-fail
//@[swap] check-fail
//@[range] check-fail
//@[range_mut] check-fail
//@[index] check-fail
//@[index_mut] check-fail
//@[total_members] check-pass
//@[swap_remove_back] check-pass
//@[swap_remove_front] check-pass
//@[insert_guarded] check-fail
//@[insert_front] check-fail
//@[fnitem_insert] check-fail
//@[fnitem_swap] check-fail
//@[fnitem_range] check-fail
//@[fnitem_opt_rotate] check-fail
//@[fnitem_u64_insert] check-fail
//@[fnitem_range_mut] check-fail
//@[fnitem_trait_index] check-fail
//@[fnitem_trait_index_mut] check-fail
//@[fnitem_split_off] check-fail
//@[fnitem_drain] check-fail
//@[fnitem_rotate_left] check-fail
//@[fnitem_collections_insert] check-fail
//@[fnitem_neg_index] check-fail
//! **`VecDeque`'s members that panic on a caller-supplied index or range are not
//! "std's own defined behaviour" (W4 fix round 1, Trust 2026-09-25).**
//!
//! The vanilla-sysroot tolerance admits a sysroot callee at foundational types
//! because its panic, if any, is std reacting to the environment — and it carves out
//! the callees whose panic is about the CALLER's own value
//! (`trust_vcgen::callee_is_known_caller_value_panic`: the division family, the
//! `Vec`/`String` index mutators, `char::encode_utf8`). The `Vec`/`String`
//! recognizer excludes `collections::` wholesale, to keep the TOTAL
//! `VecDeque::remove` and the map/set methods out — and with them every `VecDeque`
//! member that DOES panic on a caller value. `split_off`, `rotate_*` and `drain` were
//! refused by a different lane (`is_bounds_panicking_slice_mutator`'s `collections::`
//! fallback); the members below were not.
//!
//! # Before (stage 1 `0.10.0+gc2e3daed7`, `origin/main`, 2026-09-25)
//!
//! Every check-fail revision except the two pinned over-refusals built rc=0 with one
//! runtime-checked row, and panics when driven: `insert` (probe r08) and
//! `insert_owned` with "index out of bounds" at `i = 5` on a 2-element deque, `swap`
//! at `j = 7`, `range`/`range_mut` at `0..9` on a 2-element deque, `index`/`index_mut`
//! at `9` ("Out of bounds access"). `TRUST_VANILLA_DEBUG=1` shows the root ledger admitting each as
//! `vanilla=true`: the callee itself (`insert`), or its bundled std body's own
//! `core::panicking::panic` (`swap`, `range`, `Index::index`).
//!
//! # After
//!
//! `unwrap_panic::is_caller_value_panicking_deque_method` (audited against
//! `library/alloc/src/collections/vec_deque/mod.rs`) joins the caller-value family:
//! the compiler withholds the vanilla tolerance and vcgen emits the fail-closed
//! `Call::<m>::panic-freedom-unverified` row. The TOTAL members (`remove`,
//! `swap_remove_back`/`_front`, `get`, `push_back`/`pop_front`) are untouched.
//!
//! # Reconciled with `origin/main` 92e7829ca5 (W4 salvage, 2026-09-28)
//!
//! Main's `generate/collection_range.rs` charges `swap`, `range`, `range_mut`,
//! `insert_mut` and `d[i]`/`d[i] = x` at the call site, precisely over a stable deque
//! length (so the GUARDED forms prove — `policy_b/std_index_range_panics_charged.rs`),
//! fail-honest otherwise. Those members left the name carve-out, whose row no guard
//! discharges; their revisions here (`swap`, `range`, `range_mut`, `index`,
//! `index_mut` and the matching `fnitem_*`) now pin the refusal main's rows give
//! (`ERROR ... verification incomplete`), not the carve-out's note. `insert` stays on
//! the carve-out: main has no row for it.
//!
//! The compiler asks the new predicate of the ROOT body's own call sites only
//! (`trust_vcgen::callee_is_root_call_caller_value_panic`), never in the bundle walk:
//! std calls these members with its OWN validated arguments, and a first cut that
//! put them in the shared carve-out refused the TOTAL `swap_remove_back` /
//! `swap_remove_front` through their bundled bodies' `self.swap(index, len - 1)`
//! (measured: both rc=1). The `swap_remove_back`/`swap_remove_front` revisions pin
//! that, one member each — `total_members` alone did not catch it.
//!
//! # Over-refusals kept, on purpose
//!
//! No guard discharges the `insert` row (`insert` RESIZES its receiver, and main's
//! deque length model, `deque_receiver_len`, is only a stable length):
//! `insert_guarded` (`if i <= d.len() { d.insert(i, 0) }`) and `insert_front`
//! (`d.insert(0, 0)`, which can never panic) are refused. Both built rc=0 before,
//! correctly for these two programs, but by the same tolerance that admitted the
//! unguarded `insert`. Lifting them needs `VecDeque` in the VEC-INSERT region lane
//! (`vec_region.rs`), not a wider tolerance.
//!
//! # Fn-item element types (W4 fix round 2, 2026-09-26)
//!
//! The `fnitem_*` revisions are the same members at an element type that is a
//! sysroot fn ITEM. Its type renders with an ARROW and a `core::num::` path, e.g.
//! `VecDeque::<fn(u32) -> u32 {core::num::<impl u32>::count_ones}>::insert`, and
//! three name parses failed on it:
//!
//! * `callee_without_turbofish_args` counted the arrow's `>` as a bracket, so the
//!   receiver spine came back as `VecDeque:: u32 {..}>::insert`, and neither the
//!   vcgen row nor the compiler's root-call carve-out recognized the member
//!   (`fnitem_insert`, `fnitem_swap`, `fnitem_range`, `fnitem_u64_insert`,
//!   `fnitem_range_mut`, `fnitem_collections_insert`);
//! * the `Index`/`IndexMut` arm split the qualified path at the FIRST ` as `, which
//!   sits inside a trait-method fn item's type (`fn(u32) -> <u32 as Not>::Output
//!   {<u32 as Not>::not}`) — `fnitem_trait_index`, `fnitem_trait_index_mut`,
//!   `fnitem_neg_index`;
//! * `is_bounds_panicking_slice_mutator` excluded any callee CONTAINING `::num::` or
//!   `<impl u` as an integer method, and the element type contains both
//!   (`fnitem_opt_rotate`, `fnitem_split_off`, `fnitem_drain`, `fnitem_rotate_left`).
//!
//! BEFORE: every `fnitem_*` revision built rc=0 on stage 1 `0.10.0+g6a3460983` (the
//! round-1 compiler) and on `0.10.0+gc2e3daed7` (`origin/main`), and panicked when
//! driven past the deque's length (adversarial probes d01 d02 d03 d20 d23 d24 d25
//! d26, and p04 p05 p06 p13 p15). AFTER: each is refused — `insert`/`rotate_*`/
//! `split_off`/`drain` on the `Call::<m>::panic-freedom-unverified` row, `swap`/
//! `range`/`range_mut`/`d[i]` on main's `collection_range` row (the deque is pushed
//! to in the body, so its length is not stable and that row is fail-honest).
//! `fnitem_drain` pins the ERROR rather than the row's NOTE: its `.count()` stops main's
//! native lowering at `Iterator::count::{closure#0}`, and the native full verifier's
//! note for the unknown `Call::drain::panic-freedom-unverified` row then names that
//! instead of the row (the row is still minted and alone refuses: main's stage 1
//! `0.10.0+g296873da6` builds this body rc=0; W4 salvage rebase, 2026-09-29).

use std::collections::VecDeque;

#[cfg(insert)]
pub fn insert_at(d: &mut VecDeque<u32>, i: usize) {
    //[insert]~^ NOTE panic-freedom-unverified
    d.insert(i, 0);
}

#[cfg(insert_owned)]
pub fn insert_owned(mut d: VecDeque<u32>, i: usize) -> usize {
    //[insert_owned]~^ NOTE panic-freedom-unverified
    d.insert(i, 0);
    d.len()
}

#[cfg(swap)]
pub fn swap_at(d: &mut VecDeque<u32>, i: usize, j: usize) {
    //[swap]~^ ERROR Trust Level 0 safety verification incomplete for
    d.swap(i, j);
}

#[cfg(range)]
pub fn any_in_range(d: &VecDeque<u32>, a: usize, b: usize) -> bool {
    //[range]~^ ERROR Trust Level 0 safety verification incomplete for
    d.range(a..b).next().is_some()
}

#[cfg(range_mut)]
pub fn any_in_range_mut(d: &mut VecDeque<u32>, a: usize, b: usize) -> bool {
    //[range_mut]~^ ERROR Trust Level 0 safety verification incomplete for
    d.range_mut(a..b).next().is_some()
}

#[cfg(index)]
pub fn read_at(d: &VecDeque<u32>, i: usize) -> u32 {
    //[index]~^ ERROR Trust Level 0 safety verification incomplete for
    d[i]
}

#[cfg(index_mut)]
pub fn write_at(d: &mut VecDeque<u32>, i: usize) {
    //[index_mut]~^ ERROR Trust Level 0 safety verification incomplete for
    d[i] = 3;
}

// The TOTAL members: each returns `Option` (or cannot panic on its argument).
#[cfg(total_members)]
pub fn total(d: &mut VecDeque<u32>, i: usize) -> u32 {
    let a = d.remove(i).unwrap_or(0);
    let b = d.swap_remove_back(i).unwrap_or(0);
    let c = d.swap_remove_front(i).unwrap_or(0);
    let e = d.get(i).copied().unwrap_or(0);
    d.push_back(1);
    let f = d.pop_front().unwrap_or(0);
    a ^ b ^ c ^ e ^ f
}

// TOTAL, and its bundled body calls `self.swap(index, len - 1)` after its own check.
#[cfg(swap_remove_back)]
pub fn take_back(d: &mut VecDeque<u32>, i: usize) -> Option<u32> {
    d.swap_remove_back(i)
}

// TOTAL, and its bundled body calls `self.swap(index, 0)` after its own check.
#[cfg(swap_remove_front)]
pub fn take_front(d: &mut VecDeque<u32>, i: usize) -> Option<u32> {
    d.swap_remove_front(i)
}

// OVER-REFUSAL, pinned: guarded, cannot panic, refused (no `VecDeque` length model).
#[cfg(insert_guarded)]
pub fn insert_guarded(d: &mut VecDeque<u32>, i: usize) {
    //[insert_guarded]~^ NOTE panic-freedom-unverified
    if i <= d.len() {
        d.insert(i, 0);
    }
}

// OVER-REFUSAL, pinned: `insert(0, _)` never panics.
#[cfg(insert_front)]
pub fn insert_front(d: &mut VecDeque<u32>) {
    //[insert_front]~^ NOTE panic-freedom-unverified
    d.insert(0, 0);
}

// ── Fn-item element types (W4 fix round 2) ────────────────────────────────────

#[cfg(fnitem_insert)]
pub fn fnitem_insert(i: usize) -> usize {
    //[fnitem_insert]~^ NOTE panic-freedom-unverified
    let mut d = VecDeque::new();
    d.push_back(u32::count_ones);
    d.insert(i, u32::count_ones);
    d.len()
}

#[cfg(fnitem_swap)]
pub fn fnitem_swap(i: usize, j: usize) -> usize {
    //[fnitem_swap]~^ ERROR Trust Level 0 safety verification incomplete for
    let mut d = VecDeque::new();
    d.push_back(u32::count_ones);
    d.push_back(u32::count_ones);
    d.swap(i, j);
    d.len()
}

#[cfg(fnitem_range)]
pub fn fnitem_range(a: usize, b: usize) -> usize {
    //[fnitem_range]~^ ERROR Trust Level 0 safety verification incomplete for
    let mut d = VecDeque::new();
    d.push_back(u32::count_ones);
    d.range(a..b).count()
}

#[cfg(fnitem_opt_rotate)]
pub fn fnitem_opt_rotate(n: usize) -> usize {
    //[fnitem_opt_rotate]~^ NOTE panic-freedom-unverified
    let mut d = VecDeque::new();
    d.push_back(Some(u8::count_zeros));
    d.rotate_right(n);
    d.len()
}

#[cfg(fnitem_u64_insert)]
pub fn fnitem_u64_insert(i: usize) -> usize {
    //[fnitem_u64_insert]~^ NOTE panic-freedom-unverified
    let mut q = VecDeque::new();
    q.push_back(u64::leading_zeros);
    q.insert(i, u64::leading_zeros);
    q.len()
}

#[cfg(fnitem_range_mut)]
pub fn fnitem_range_mut(b: usize) -> usize {
    //[fnitem_range_mut]~^ ERROR Trust Level 0 safety verification incomplete for
    let mut d = VecDeque::new();
    d.push_back(i32::signum);
    d.range_mut(0..b).count()
}

#[cfg(fnitem_trait_index)]
pub fn fnitem_trait_index(i: usize) -> u32 {
    //[fnitem_trait_index]~^ ERROR Trust Level 0 safety verification incomplete for
    use std::ops::Not;
    let mut d = VecDeque::new();
    d.push_back(<u32 as Not>::not);
    (d[i])(7)
}

#[cfg(fnitem_trait_index_mut)]
pub fn fnitem_trait_index_mut(i: usize) -> usize {
    //[fnitem_trait_index_mut]~^ ERROR Trust Level 0 safety verification incomplete for
    use std::ops::Not;
    let mut d = VecDeque::new();
    d.push_back(<u32 as Not>::not);
    d[i] = <u32 as Not>::not;
    d.len()
}

#[cfg(fnitem_split_off)]
pub fn fnitem_split_off(n: usize) -> usize {
    //[fnitem_split_off]~^ NOTE panic-freedom-unverified
    let mut d = VecDeque::new();
    d.push_back(u32::count_ones);
    d.split_off(n).len()
}

#[cfg(fnitem_drain)]
pub fn fnitem_drain(a: usize, b: usize) -> usize {
    //[fnitem_drain]~^ ERROR Trust Level 0 safety verification incomplete for
    let mut d = VecDeque::new();
    d.push_back(u32::count_ones);
    d.drain(a..b).count()
}

#[cfg(fnitem_rotate_left)]
pub fn fnitem_rotate_left(n: usize) -> usize {
    //[fnitem_rotate_left]~^ NOTE panic-freedom-unverified
    let mut d = VecDeque::new();
    d.push_back(u32::count_ones);
    d.rotate_left(n);
    d.len()
}

// The element's fn item is itself rooted under `collections::` and carries a turbofish.
#[cfg(fnitem_collections_insert)]
pub fn fnitem_collections_insert(i: usize) -> usize {
    //[fnitem_collections_insert]~^ NOTE panic-freedom-unverified
    let mut d = VecDeque::new();
    d.push_back(VecDeque::<u32>::len);
    d.insert(i, VecDeque::<u32>::len);
    d.len()
}

#[cfg(fnitem_neg_index)]
pub fn fnitem_neg_index(i: usize) -> i32 {
    //[fnitem_neg_index]~^ ERROR Trust Level 0 safety verification incomplete for
    use std::ops::Neg;
    let mut d = VecDeque::new();
    d.push_back(<i32 as Neg>::neg);
    (d[i])(7)
}
