//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! `auxiliary/requires_callee_dep.rs`'s `add1`, built with verification OFF: the
//! overflow check the verified build elides under the `requires` is still here,
//! so an out-of-contract argument panics instead of wrapping. The witness
//! `foreign_requires_callee_as_value_really_overflows.rs` calls it through a fn
//! pointer.

pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}
