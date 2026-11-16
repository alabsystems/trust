//@ needs-trust-verify
//@ only-64bit
//@ edition: 2021
//@ revisions: position nested_any fold_ord_min find panicking_closure panicking_fn_item owning_receiver u128_position generic_parent_closure
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[position] check-pass
//@[nested_any] check-pass
//@[fold_ord_min] check-pass
//@[find] check-pass
//@[panicking_closure] check-fail
//@[panicking_fn_item] check-fail
//@[owning_receiver] check-fail
//@[u128_position] check-fail
//@[generic_parent_closure] check-fail
//! **A drive-only `Iterator` consumer whose callable is verified is total at the call
//! (Trust, 2026-09-28).**
//!
//! `v.iter().position(|x| *x == t)` panics only through `next`, the closure, a drop, or
//! its own counter. The compiler rules each out from `tcx` facts
//! (`collect_verified_callable_consumer_total_calls`):
//! * the method is drive-only;
//! * `Self` is a total std iterator, and neither it nor its items need drop;
//! * every integer range in `Self` fits `usize`;
//! * the callable is core's own total fn item, or a local closure or fn whose OWN
//!   verification discharged its panic-freedom.
//!
//! The callable's verdict is read through the shared bar the `dyn` lane uses. The
//! bridge then skips the closure-driving marker for the granted call key.
//!
//! * POSITIVE (the ordinary sweep's t21, t27 and s30, and a `find`):
//!   * `position` over a slice, with a capturing closure;
//!   * `nested_any`: a closure whose body is itself a granted `any`. The inner grant
//!     is collected while the closure is a bundled MEMBER of `f`'s module;
//!   * `fold_ord_min`: `fold(i32::MAX, i32::min)`, `Ord::min` resolved into core;
//!   * `find`, which drops the items it passes over. They are `&u32`, so no glue runs.
//! * NEGATIVE, each annotated on `f`, the discriminating row:
//!   * a closure that can panic;
//!   * a local fn item that can panic;
//!   * an owning receiver, whose drop frees through an allocator;
//!   * `position` over a `u128` range, whose counter can pass `usize::MAX`;
//!   * a closure defined in a GENERIC fn. One body is verified per item, and it does
//!     not cover every instantiation.

#[cfg(position)]
pub fn f(v: &[u8], t: u8) -> Option<usize> {
    v.iter().position(|x| *x == t)
}

#[cfg(nested_any)]
pub fn f(v: &[&str]) -> bool {
    v.iter().any(|s| s.chars().any(|c| c.is_uppercase()))
}

#[cfg(fold_ord_min)]
pub fn f(v: &[i32]) -> i32 {
    v.iter().copied().fold(i32::MAX, i32::min)
}

#[cfg(find)]
pub fn f(v: &[u32]) -> Option<&u32> {
    v.iter().find(|x| **x > 3)
}

#[cfg(panicking_closure)]
pub fn f(v: &[u32]) -> bool {
    //[panicking_closure]~^ ERROR Trust Level 0 safety verification incomplete for `iterator_consumer_with_verified_callable::f`
    v.iter().any(|x| {
        assert!(*x != 7);
        *x > 3
    })
}

#[cfg(panicking_fn_item)]
fn p(x: &u32) -> bool {
    assert!(*x != 7);
    *x > 3
}

#[cfg(panicking_fn_item)]
pub fn f(v: &[u32]) -> bool {
    //[panicking_fn_item]~^ ERROR Trust Level 0 safety verification incomplete for `iterator_consumer_with_verified_callable::f`
    v.iter().any(p)
}

#[cfg(owning_receiver)]
pub fn f(v: Vec<u32>) -> bool {
    //[owning_receiver]~^ ERROR Trust Level 0 safety verification incomplete for `iterator_consumer_with_verified_callable::f`
    v.into_iter().any(|x| x > 3)
}

#[cfg(u128_position)]
pub fn f(n: u128) -> Option<usize> {
    //[u128_position]~^ ERROR Trust Level 0 safety verification incomplete for `iterator_consumer_with_verified_callable::f`
    (0u128..n).position(|x| x == 5)
}

#[cfg(generic_parent_closure)]
fn mk<T>() -> impl Fn(&u32) -> bool {
    |x| {
        assert!(*x != 7);
        *x > 3
    }
}

#[cfg(generic_parent_closure)]
pub fn f(v: &[u32]) -> bool {
    //[generic_parent_closure]~^ ERROR Trust Level 0 safety verification incomplete for `iterator_consumer_with_verified_callable::f`
    v.iter().any(mk::<u8>())
}
