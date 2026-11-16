//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_dyn_f2_trait_and_fn_at_one_path_collapse.rs` (review 6
//! of the review-14 build): a trait and a fn at ONE path, `k::Keep`, which Rust
//! keeps apart (the type namespace and the value namespace). The fn swaps.
//! Safe and sound.
#![forbid(unsafe_code)]
#![allow(non_snake_case)]
pub mod k {
    /// A component trait: a `dyn` of it may be kept.
    pub trait Keep: std::any::Any { fn label(&self) -> u8 { 0 } }
    /// A fn of the same name, which swaps.
    pub fn Keep<T>(a: &mut T, b: &mut T) { core::mem::swap(a, b) }
}
