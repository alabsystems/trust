//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `r6_dyn_f3_upcast_to_dyn_any_in_unread_dep_fn.rs` (review 6
//! of the review-14 build): a component trait whose `dyn` may be downcast
//! (`Any` is its supertrait), and a fn that is not generic which upcasts a
//! boxed component to a `Box<dyn Any>` (trait upcasting). Safe and sound;
//! nothing is replaced here.
#![forbid(unsafe_code)]
pub trait Component: std::any::Any {
    fn label(&self) -> u8 { 0 }
}
pub fn into_any(b: Box<dyn Component>) -> Box<dyn std::any::Any> { b }
