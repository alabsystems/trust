//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@[on] check-pass
//@[off] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! D2 tier 1 (2026-09-24): every other admitted adapter over a constant-size
//! slice receiver. `chunks(3)` yields length in `[1, 3]` (so `c[0]` only);
//! `fold`'s item is its SECOND closure parameter (`_3`); `find` passes the
//! item behind `&`; `map` is lazy and is consumed by core's `Iterator::last`
//! (no generic parameters of its own).
//!
//! BEFORE (stage-1 snapshot 4e9fe36bf = the `off` revision): every closure
//! below is refused on its own root with `[slice] FAILED`.

pub fn any_eq(v: &[u32]) -> bool {
    v.windows(3).any(|w| w[0] == w[2])
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::any` over `<[T]>::windows(3)`
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `slice_adapters::any_eq::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `slice_adapters::any_eq::{closure#0}`
    //[off]~^^^^ NOTE [slice] FAILED
}

pub fn position_zero(v: &[u32]) -> Option<usize> {
    v.windows(3).position(|w| w[2] == 0)
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::position` over `<[T]>::windows(3)`
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `slice_adapters::position_zero::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `slice_adapters::position_zero::{closure#0}`
    //[off]~^^^^ NOTE [slice] FAILED
}

pub fn find_zero(v: &[u32]) -> Option<&[u32]> {
    v.windows(2).find(|w| w[1] == 0)
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::find` over `<[T]>::windows(2)` invokes this closure only on items it yields; assumed: item parameter `*_2` has slice length 2
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `slice_adapters::find_zero::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `slice_adapters::find_zero::{closure#0}`
    //[off]~^^^^ NOTE [slice] FAILED
}

pub fn last_xor(v: &[u32]) -> Option<u32> {
    v.windows(2).map(|w| w[0] ^ w[1]).last()
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::map` over `<[T]>::windows(2)`
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `slice_adapters::last_xor::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `slice_adapters::last_xor::{closure#0}`
    //[off]~^^^^ NOTE [slice] FAILED
}

pub fn first_positive(v: &[u32]) -> bool {
    v.chunks(3).all(|c| c[0] > 0)
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::all` over `<[T]>::chunks(3)` invokes this closure only on items it yields; assumed: item parameter `_2` has slice length in [1, 3]
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `slice_adapters::first_positive::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `slice_adapters::first_positive::{closure#0}`
    //[off]~^^^^ NOTE [slice] FAILED
}

pub fn fold_last(v: &[u32]) -> u32 {
    v.chunks_exact(4).fold(0u32, |acc, c| acc.wrapping_add(c[3]))
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::fold` over `<[T]>::chunks_exact(4)` invokes this closure only on items it yields; assumed: item parameter `_3` has slice length 4
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `slice_adapters::fold_last::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `slice_adapters::fold_last::{closure#0}`
    //[off]~^^^^ NOTE [slice] FAILED
}

pub fn xor_lasts(v: &[u32], out: &mut u32) {
    v.chunks_exact(4).for_each(|c| *out ^= c[3])
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::for_each` over `<[T]>::chunks_exact(4)`
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `slice_adapters::xor_lasts::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `slice_adapters::xor_lasts::{closure#0}`
    //[off]~^^^^ NOTE [slice] FAILED
}
