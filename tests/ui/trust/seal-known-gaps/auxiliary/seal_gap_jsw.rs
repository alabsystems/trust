//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_const_f3_trusted_abstract_foreign_item_covers_this_crates_impl_beneath.rs`
//! (review 6 of the review-14 build), shape 1: a trait `HasSw` whose only impl is
//! a blanket one over another trait, `Base`, that it calls. Sound.
#![forbid(unsafe_code)]
pub trait Base { fn base_sw(a: &mut Self, b: &mut Self); const BASE_SW: fn(&mut Self, &mut Self); }
pub trait HasSw { fn sw(a: &mut Self, b: &mut Self); const SW: fn(&mut Self, &mut Self); }
impl<X: Base> HasSw for X {
    fn sw(a: &mut X, b: &mut X) { X::base_sw(a, b) }
    const SW: fn(&mut X, &mut X) = X::BASE_SW;
}
