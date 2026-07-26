//@ known-bug: #148727
//@ check-pass
// Trust: Regression test for rust-lang#148727
// DispatchFromDyn on references must validate that the inner (pointee) types
// also implement DispatchFromDyn. Without this check, bogus impls on references
// to multi-field structs are accepted, causing ICE or UB at codegen.

#![feature(dispatch_from_dyn, arbitrary_self_types)]

use std::ops::DispatchFromDyn;

// A struct with multiple non-ZST fields — NOT a valid dispatch wrapper.
pub struct Ptr<T: ?Sized>(Box<T>, Box<T>);

// This impl is bogus: &Ptr<T> -> &Ptr<U> should not be allowed because
// Ptr<T> does not implement DispatchFromDyn<Ptr<U>> (it has two Box fields).
impl<'a, T: ?Sized, U: ?Sized> DispatchFromDyn<&'a Ptr<U>> for &'a Ptr<T> {}
// [pending soundness check] ERROR

fn main() {}
