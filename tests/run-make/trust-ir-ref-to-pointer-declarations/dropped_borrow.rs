//! Trust (thir-generic-instance-callee, 2026-10-15): the 2026-09-15 adversarial review's
//! DROPPED-BORROW shapes, against the now-SIGNED reference-to-pointer declarations.
//!
//! `&P` and `P` both spell `ptr` when `P` is a thin pointer, so the validator's arg/param check
//! cannot see a call that passes `P` where `&P` is due. The review measured exactly that:
//! `take_raw(p: &*const u8)` called as `take_raw(&q)` was lowered as `take_raw(q)` and accepted.
//! The declaration guard that answered it is retired; what keeps these shapes faithful now is the
//! CALL SITE: every argument below either gets a REAL borrow (a slot holding `P`) or its body is
//! refused at its own call. `rmake.rs` asserts which, function by function. A body here that
//! splices with `P` itself as the argument is the measured unfaithful acceptance coming back.
#![crate_type = "lib"]
use std::fmt::Debug;

extern crate take_raw_dep;

pub trait Tr {
    fn m(&self) -> u8;
}

impl Tr for *const u8 {
    fn m(&self) -> u8 {
        unsafe { **self }
    }
}

pub struct Inner<'a> {
    pub q: *const u8,
    pub r: &'a u8,
    pub d: &'a dyn Debug,
    pub n: u32,
}

pub struct Outer<'a> {
    pub inner: Inner<'a>,
}

/// The review's exact shape: a raw-pointer PARAMETER borrowed for a verify-off dependency whose
/// parameter is `&*const u8`.
pub fn call_raw(q: *const u8) -> u8 {
    take_raw_dep::take_raw(&q)
}

/// The same borrow for a generic std instance (`size_of_val::<*const u8>`, parameter
/// `&*const u8`).
pub fn size_raw(q: *const u8) -> usize {
    std::mem::size_of_val(&q)
}

/// A method RECEIVER: `q.m()` is `Tr::m(&q)`, an auto-ref of a raw-pointer local.
pub fn recv_raw(q: *const u8) -> u8 {
    q.m()
}

/// A receiver PLACE: `Tr::m(&(*o).inner.q)`, a raw-pointer leaf under a deref.
pub fn recv_place_raw(o: &Outer) -> u8 {
    o.inner.q.m()
}

/// An explicit call's place argument with a thin-reference leaf (`&&u8`).
pub fn place_ref(o: &Outer) -> usize {
    std::mem::size_of_val(&o.inner.r)
}

/// An explicit call's place argument with a `&dyn` leaf (`&&dyn Debug`).
pub fn place_dyn(o: &Outer) -> usize {
    std::mem::size_of_val(&o.inner.d)
}

/// CONTROL: a genuine borrow of a thin-reference parameter. It must splice, and the argument
/// must be the address of a slot holding `r`, never `r`.
pub fn borrow_ref_param(r: &u8) -> usize {
    std::mem::size_of_val(&r)
}

/// CONTROL: a reborrow `&*rr` IS `rr` at the identical type (`&&u8`), so passing `rr` is
/// faithful.
pub fn reborrow_param(rr: &&u8) -> usize {
    std::mem::size_of_val(&*rr)
}
