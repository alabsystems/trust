//@ known-bug: #141713
//@ check-pass
// Trust: regression test for rust-lang#141713
// Part of #859
//
// Incoherent lifetime HRTB on associated types allows unsoundness in
// safe stable Rust. When a trait bound `for<'a> Producer<&'a T>` is used
// (where Producer is a blanket-implemented supertrait of FnOnce),
// the associated type `P::Output` can be used to bypass lifetime checks.
// The type `P::Output` for `P: for<'a> Producer<&'a T>` behaves like
// a `for<'a> &'a T` which allows assignment to `&'static dyn Any`
// even when `T` is not `'static`.
//
// PoC from upstream issue: https://github.com/rust-lang/rust/issues/141713
// Affected since rustc 1.67.0.
//
// STATUS: This currently COMPILES on stable Rust (unsound). When fixed,
// the compiler should reject the incoherent associated type usage.

use std::any::Any;

// `for<'a> Producer<&'a T>` is equivalent to the (non-existent)
// `for<'a> FnOnce() -> &'a T`
pub trait Producer<T>: FnOnce() -> T {}
impl<T, F: FnOnce() -> T> Producer<T> for F {}

// `P::Output` here is incoherent: it seems to resemble `for<'a> &'a T`
// which should not exist as a type.
fn write_incoherent_p2<T, P: for<'a> Producer<&'a T>>(
    weird: P::Output,
    out: &mut &'static dyn Any,
) {
    // T is not 'static, but P::Output can be assigned to &'static dyn Any
    *out = weird;
}

fn write_incoherent_p1<T, P: for<'a> Producer<&'a T>>(p: P, out: &mut &'static dyn Any) {
    write_incoherent_p2::<T, P>(p(), out)
}

fn construct_implementor<T>(not_static: T, out: &mut &'static dyn Any) {
    write_incoherent_p1::<T, _>(|| Box::leak(Box::new(not_static)), out);
}

fn make_static_and_drop<T: 'static>(t: T) -> &'static T {
    let mut out: &'static dyn Any = &();
    construct_implementor::<&T>(&t, &mut out);
    *out.downcast_ref::<&T>().unwrap()
}

fn main() {
    // Use-after-free: t is dropped but the reference persists.
    println!("{:?}", make_static_and_drop(vec![vec![1]]));
}
