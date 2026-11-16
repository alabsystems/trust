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
//! D2 tier 1: a lazy `map` over `windows(2)` keeps its premise under the core
//! consumers ordinary code writes after it — a GENERIC one (`fold` takes `B`
//! and `G`) and one taking `&mut self` (`any`), which reaches the adapter
//! through one `&mut` conduit.
//!
//! BEFORE (2026-09-29, the ordinary-Rust sweep): the premise demanded a
//! by-value consumer with no generics of its own, so each map closure below was
//! refused on its own root with `[slice] FAILED`, while `.map(..).last()`
//! (`slice_adapters.rs`) proved. Neither restriction reached the closure: the
//! map is still consumed exactly once, and a generic argument that does not
//! mention the closure cannot carry it.

fn xor(a: u8, b: u8) -> u8 {
    a ^ b
}

pub fn fold_second(v: &[u8]) -> u8 {
    v.windows(2).map(|w| w[1]).fold(0u8, |a, b| a ^ b)
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::map` over `<[T]>::windows(2)`
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `lazy_adapter_consumers::fold_second::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `lazy_adapter_consumers::fold_second::{closure#0}`
    //[off]~^^^^ NOTE [slice] FAILED
}

pub fn fold_with_fn_item(v: &[u8]) -> u8 {
    v.windows(2).map(|w| w[1]).fold(0u8, xor)
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::map` over `<[T]>::windows(2)`
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `lazy_adapter_consumers::fold_with_fn_item::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `lazy_adapter_consumers::fold_with_fn_item::{closure#0}`
    //[off]~^^^^ NOTE [slice] FAILED
}

pub fn any_zero_second(v: &[u8]) -> bool {
    v.windows(2).map(|w| w[1]).any(|x| x == 0)
    //[on]~^ NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::map` over `<[T]>::windows(2)`
    //[off]~^^ ERROR Trust Level 0 safety verification incomplete for `lazy_adapter_consumers::any_zero_second::{closure#0}`
    //[off]~^^^ ERROR Trust strict verification failed for `lazy_adapter_consumers::any_zero_second::{closure#0}`
    //[off]~^^^^ NOTE [slice] FAILED
}
