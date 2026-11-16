//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_const_f3_trusted_abstract_foreign_item_covers_this_crates_impl_beneath.rs`
//! (review 6 of the review-14 build), shape 3: `HasSw` over an associated
//! type, whose only impl is a blanket one over `Base`, which it calls. Sound.
#![forbid(unsafe_code)]
pub trait Base { type Item; fn base_sw(a: &mut Self::Item, b: &mut Self::Item); }
pub trait HasSw { type Item; fn sw(a: &mut Self::Item, b: &mut Self::Item); }
impl<X: Base> HasSw for X { type Item = X::Item; fn sw(a: &mut X::Item, b: &mut X::Item) { X::base_sw(a, b) } }
