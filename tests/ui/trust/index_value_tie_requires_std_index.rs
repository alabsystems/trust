//@ revisions: default strict certify memsafe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@[certify] compile-flags: -Ztrust-policy=certify
//@[memsafe] compile-flags: -Ztrust-policy=memory-safe
//@ check-fail
//@ dont-check-compiler-stderr
//! IDX-TIE-1 (docs/KNOWN_HAZARDS.md, "FIX PREPARED 2026-10-03 — the index value
//! tie trusted any method named `index`"; docs/DECISION_QUEUE.md IDX-TIE-1).
//!
//! `build_vec_index_dest_value_tie_facts` (trust-vcgen `value_facts.rs`) states
//! that two `index` calls on one unchanged slice, at equal indices, read equal
//! elements. That is a theorem about std's `Index<usize>` for `[T]`, `[T; N]` and
//! `Vec<T>`. The builder recognized the callee by its method NAME only, so it
//! also tied the results of:
//!  * two user traits whose method is named `index` (`two_user_traits`);
//!  * two user `impl Index<Key> for [u32]` with local key types
//!    (`two_user_index_keys`). The trait there IS core's: the same impl in a
//!    dependency is named `<[u32] as core::ops::index::Index<dep::K>>::index`,
//!    which a crate-root anchor admits, so the trait argument must be `usize`.
//!
//! Here each pair returns `&0` and `&u32::MAX`. With the false tie, `a == 0`
//! made `b == 0`, so `b + 1` was proved and its overflow check was removed:
//! the program returned 0 where vanilla Rust panics.
//!
//! BEFORE the fix, on stage1-w10 (the stage 1 of `1ab78ed8e8`, main with
//! waves 7–10), every revision's compile line exited 0 with no error and no
//! warning, and `TRUST_ELIDE_DEBUG=1` printed `elided 1 kernel-certified overflow
//! checks` for both functions (measured 2026-10-03). AFTER, each function's
//! `overflow:add` row must be refused. The expected diagnostics are the ones the
//! same compiler prints for this file with the tie removed by hand (the methods
//! renamed, the second key read through a plain function), measured the same
//! day: `default`, `strict` and `certify` print the two errors below,
//! `memory-safe` prints the warning and the memory-safe error. That prediction
//! held on the stage 1 of `936573497e` (2026-10-04), which this file passes.
//!
//! `std_index_twice` is the honest control: std `v[i]` read twice under the same
//! guard. It stays proved under every revision (no annotation, and no diagnostic
//! may appear for it). The std explicit-call control, which goes through this
//! builder, is `index_value_tie_std_index_call_still_proves.rs`.

use core::ops::Index;

static ZERO: u32 = 0;
static MAX: u32 = u32::MAX;

pub trait Lo {
    fn index(&self, i: usize) -> &u32;
}
pub trait Hi {
    fn index(&self, i: usize) -> &u32;
}
impl Lo for [u32] {
    fn index(&self, _i: usize) -> &u32 {
        &ZERO
    }
}
impl Hi for [u32] {
    fn index(&self, _i: usize) -> &u32 {
        &MAX
    }
}

pub struct A;
pub struct B;
impl Index<A> for [u32] {
    type Output = u32;
    fn index(&self, _k: A) -> &u32 {
        &ZERO
    }
}
impl Index<B> for [u32] {
    type Output = u32;
    fn index(&self, _k: B) -> &u32 {
        &MAX
    }
}

pub fn two_user_traits(v: &[u32], i: usize) -> u32 {
    //[default,strict,certify]~^ ERROR Trust Level 0 safety verification incomplete for `index_value_tie_requires_std_index::two_user_traits`
    //[default,strict,certify]~| ERROR Trust strict verification failed for `index_value_tie_requires_std_index::two_user_traits`
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `index_value_tie_requires_std_index::two_user_traits`
    //[memsafe]~| ERROR Trust memory-safe verification failed for `index_value_tie_requires_std_index::two_user_traits`
    let a = *Lo::index(v, i);
    let b = *Hi::index(v, i);
    if a == 0 { b + 1 } else { 0 }
}

pub fn two_user_index_keys(v: &[u32]) -> u32 {
    //[default,strict,certify]~^ ERROR Trust Level 0 safety verification incomplete for `index_value_tie_requires_std_index::two_user_index_keys`
    //[default,strict,certify]~| ERROR Trust strict verification failed for `index_value_tie_requires_std_index::two_user_index_keys`
    //[memsafe]~^^^ WARN Trust Level 0 safety verification incomplete for `index_value_tie_requires_std_index::two_user_index_keys`
    //[memsafe]~| ERROR Trust memory-safe verification failed for `index_value_tie_requires_std_index::two_user_index_keys`
    let a = v[A];
    let b = v[B];
    if a == 0 { b + 1 } else { 0 }
}

pub fn std_index_twice(v: &[u32], i: usize) -> u32 {
    if i < v.len() && v[i] < 10 { v[i] + 1 } else { 0 }
}
