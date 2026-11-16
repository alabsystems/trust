//@ revisions: at at_strict
//@ needs-trust-verify
//@ edition: 2024
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=0
//@[at_strict] compile-flags: -Ztrust-policy=strict
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]
//! Trust (2026-10-14, INSTANCE-WALK-1): the CONTROLS for
//! `unverified_edge_generic_instance.rs`. The instance walk substitutes a local
//! generic body's MIR at its concrete arguments and counts every edge it finds as
//! the caller's; where each dispatch lands in a LOCAL impl (a body this crate holds)
//! there is no edge, and every `#[trust::assume_total]` body here keeps its skip.
//! WARN annotations are REQUIRED in this file on purpose: the "`assume_total` ...
//! does not cover ..." revocation warning appearing here would fail the test. Each
//! shape is a refusal's twin with its dependency trait replaced by the local `Ok1`.
//! The one warning each generic helper carries is the existing per-instance
//! hypothesis advisory of its own polymorphic body, annotated below. (The closure
//! twin of `closuremap` is not here: `Some(x).map(|y| y.o())` in a generic body fails
//! that body's own verification, before and after this change.)

pub trait Ok1 {
    fn o(&self) -> u32;
}

impl Ok1 for u32 {
    fn o(&self) -> u32 {
        *self / 2
    }
}

fn gc<T: Ok1>(x: &T) -> u32 {
    //~^ WARN instance hypothesis row(s)
    x.o()
}

// A generic dispatching into a local impl for a foundational type.
#[trust::assume_total]
#[inline(never)]
pub fn t_generic() -> u32 {
    gc(&5u32)
}

// A transitive generic, still landing in the local impl.
fn hc<T: Ok1>(x: &T) -> u32 {
    //~^ WARN instance hypothesis row(s)
    gc(x)
}

#[trust::assume_total]
#[inline(never)]
pub fn t_transitive() -> u32 {
    hc(&5u32)
}

// A local blanket impl over a LOCAL trait.
pub trait L2 {
    fn l2(&self) -> u32;
}

impl<T: Ok1> L2 for T {
    fn l2(&self) -> u32 {
        //~^ WARN instance hypothesis row(s)
        self.o()
    }
}

#[trust::assume_total]
#[inline(never)]
pub fn t_local_blanket() -> u32 {
    5u32.l2()
}

// An inherent method and a trait impl of a local generic ADT.
pub struct Lw<T>(T);

impl<T: Ok1> Lw<T> {
    fn go(&self) -> u32 {
        //~^ WARN instance hypothesis row(s)
        self.0.o()
    }
}

impl<T: Ok1> Iterator for Lw<T> {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        //~^ WARN instance hypothesis row(s)
        Some(self.0.o())
    }
}

#[trust::assume_total]
#[inline(never)]
pub fn t_inherent() -> u32 {
    Lw(5u32).go()
}

#[trust::assume_total]
#[inline(never)]
pub fn t_adt_impl() -> u32 {
    Lw(5u32).take(1).count() as u32
}

// A local generic ADT's destructor, bare and inside an `Option` and a tuple.
pub struct DG<T: Ok1>(T);

impl<T: Ok1> Drop for DG<T> {
    fn drop(&mut self) {
        //~^ WARN instance hypothesis row(s)
        let _ = self.0.o();
    }
}

#[trust::assume_total]
#[inline(never)]
pub fn t_drop() -> u32 {
    let _a = DG(5u32);
    let _b = Some(DG(6u32));
    let _c = (DG(7u32), 1u8);
    0
}
