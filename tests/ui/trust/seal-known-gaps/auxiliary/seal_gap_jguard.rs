//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_const_f3_trusted_abstract_foreign_item_covers_this_crates_impl_beneath.rs`
//! (review 6 of the review-14 build), shape 2: a guard whose `Drop` runs its
//! hook. Sound.
#![forbid(unsafe_code)]
pub trait Hook { fn on_drop(&mut self); }
pub struct Guard<X: Hook>(pub X);
impl<X: Hook> Drop for Guard<X> { fn drop(&mut self) { self.0.on_drop() } }
