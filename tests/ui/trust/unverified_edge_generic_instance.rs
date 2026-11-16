//@ revisions: blanket u32impl u32impl_strict unit strref fnptr localblanket atgen transitive adtimpl
//@ revisions: inherent dropdirect dropopt dropbox droptuple droparr dropvec fnitem closuremap
//@ revisions: ms_u32impl
//@ needs-trust-verify
//@ edition: 2024
//@ aux-build: unverified_edge_instance_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Copt-level=0
//@[u32impl_strict] compile-flags: -Ztrust-policy=strict
//@[ms_u32impl] compile-flags: -Ztrust-policy=memory-safe
//@[blanket] check-fail
//@[u32impl] check-fail
//@[u32impl_strict] check-fail
//@[unit] check-fail
//@[strref] check-fail
//@[fnptr] check-fail
//@[localblanket] check-fail
//@[atgen] check-fail
//@[transitive] check-fail
//@[adtimpl] check-fail
//@[inherent] check-fail
//@[dropdirect] check-fail
//@[dropopt] check-fail
//@[dropbox] check-fail
//@[droptuple] check-fail
//@[droparr] check-fail
//@[dropvec] check-fail
//@[fnitem] check-fail
//@[closuremap] check-fail
//@[ms_u32impl] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN
#![feature(register_tool)]
#![register_tool(trust)]
#![allow(dead_code)]
//! Trust (2026-10-14, INSTANCE-WALK-1): the ONE enumeration of a body's edges into
//! code this compilation does not verify (`trust_verify/unverified_edges.rs`) held a
//! LOCAL GENERIC callee at every instantiation whose type arguments reach no foreign
//! code (`local_instance_args_reach_foreign`), without asking which impl the
//! instance CALLS at those arguments. `u32`, `()` and `&str` are foundational, so
//! `g2::<u32>`, whose `x.a2()` resolves to the verify-off dependency's `impl Act2
//! for u32`, was held, and an `#[trust::assume_total]` caller kept its skip. The
//! dependency here (`auxiliary/unverified_edge_instance_dep.rs`) is ordinary code
//! returning constants; the point is only that nothing verified it.
//!
//! MEASURED BEFORE on stage 1 `d28d17dc2` (the same shapes, with a dependency whose
//! impls write through null): every `assume_total` revision below built rc=0 in the
//! default and strict lanes and the binary died with SIGSEGV (139); this file's own
//! revisions, run on that compiler, emitted no revocation warning (see the commit).
//!
//! AFTER: the instance's MIR is substituted at its concrete arguments and walked
//! (calls, drops, casts and constants resolved there, transitively), and any edge is
//! an edge of the caller: the `assume_total` skip is revoked with the warning naming
//! it (and `t`, verified in full, is then refused on its own rows), and the
//! memory-safe skip is withheld (`ms_u32impl`: before, `skipped` was recorded as an
//! `addr-of-field` assumption and only `g2`'s own memory-safe failure refused it). Shapes: a dependency blanket impl, an
//! impl for `u32` (default and strict), for `()`, for `str`; a fn pointer to `T::a2`
//! minted in the generic; a local blanket impl over a dependency trait; a generic
//! `assume_total` callee; a transitive generic; a local generic ADT's trait impl run
//! by `Iterator::count` (`local_impl_surface`); an inherent method of a local generic
//! ADT; a local generic ADT's `Drop` bare, in an `Option`, a `Box`, a tuple, an
//! array and a `Vec`; a generic fn item and a generic body's closure handed to
//! `Option::map`. Each helper exists only in the revisions that use it, so a
//! revision's refusal is its own. The controls (dispatch landing in a LOCAL impl keeps the skip) are
//! in `unverified_edge_generic_instance_controls.rs`.
extern crate unverified_edge_instance_dep as dep;
#[allow(unused_imports)]
use dep::{Act2, Act3, Blanket};

#[cfg(ms_u32impl)]
pub struct S {
    pub a: u32,
}

#[cfg(any(blanket))]
fn g_blanket<T: Blanket>(x: &T) -> u32 {
    x.bl()
}

#[cfg(any(u32impl, u32impl_strict, transitive, fnitem, ms_u32impl))]
fn g2<T: Act2>(x: &T) -> u32 {
    x.a2()
}

#[cfg(any(unit))]
fn g3<T: Act3>() -> u32 {
    T::a3()
}

#[cfg(any(strref))]
fn g4<T: Act2 + ?Sized>(x: &T) -> u32 {
    x.a2()
}

#[cfg(any(fnptr))]
fn g5<T: Act2>(x: &T) -> u32 {
    let f: fn(&T) -> u32 = T::a2;
    f(x)
}

#[cfg(any(localblanket))]
trait L {
    fn l(&self) -> u32;
}

#[cfg(any(localblanket))]
impl<T: Act2> L for T {
    fn l(&self) -> u32 {
        self.a2()
    }
}

#[cfg(any(atgen))]
#[trust::assume_total]
fn ga<T: Act2>(x: &T) -> u32 {
    x.a2()
}

#[cfg(any(transitive))]
fn h<T: Act2>(x: &T) -> u32 {
    g2(x)
}

#[cfg(any(adtimpl, inherent))]
struct Lw<T>(T);

#[cfg(any(adtimpl))]
impl<T: Act2> Iterator for Lw<T> {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        Some(self.0.a2())
    }
}

#[cfg(any(inherent))]
impl<T: Act2> Lw<T> {
    fn go(&self) -> u32 {
        self.0.a2()
    }
}

#[cfg(any(dropdirect, dropopt, dropbox, droptuple, droparr, dropvec))]
struct DG<T: Act2>(T);

#[cfg(any(dropdirect, dropopt, dropbox, droptuple, droparr, dropvec))]
impl<T: Act2> Drop for DG<T> {
    fn drop(&mut self) {
        let _ = self.0.a2();
    }
}

#[cfg(any(closuremap))]
fn gm<T: Act2 + Copy>(x: T) -> u32 {
    Some(x).map(|y| y.a2()).unwrap_or(0)
}

#[cfg(blanket)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[blanket]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[blanket]~| NOTE `g_blanket` in bb
    g_blanket(&5u32)
}

#[cfg(u32impl)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[u32impl]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[u32impl]~| NOTE `g2` in bb
    g2(&5u32)
}

#[cfg(u32impl_strict)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[u32impl_strict]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[u32impl_strict]~| NOTE `g2` in bb
    g2(&5u32)
}

#[cfg(unit)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[unit]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[unit]~| NOTE `g3` in bb
    g3::<()>()
}

#[cfg(strref)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[strref]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[strref]~| NOTE `g4` in bb
    g4("hi")
}

#[cfg(fnptr)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[fnptr]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[fnptr]~| NOTE `g5` in bb
    g5(&5u32)
}

#[cfg(localblanket)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[localblanket]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[localblanket]~| NOTE `L::l` in bb
    5u32.l()
}

#[cfg(atgen)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[atgen]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[atgen]~| NOTE `ga` in bb
    ga(&5u32)
}

#[cfg(transitive)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[transitive]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[transitive]~| NOTE `h` in bb
    h(&5u32)
}

#[cfg(adtimpl)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[adtimpl]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[adtimpl]~| NOTE `std::iter::Iterator::count` in bb
    Lw(5u32).take(1).count() as u32
}

#[cfg(inherent)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[inherent]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[inherent]~| NOTE `Lw::<T>::go` in bb
    Lw(5u32).go()
}

#[cfg(dropdirect)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[dropdirect]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[dropdirect]~| NOTE the drop glue of `DG<u32>`
    let _d = DG(5u32);
    0
}

#[cfg(dropopt)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[dropopt]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[dropopt]~| NOTE the drop glue of `std::option::Option<DG<u32>>`
    let _d = Some(DG(5u32));
    0
}

#[cfg(dropbox)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[dropbox]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[dropbox]~| NOTE DG<u32>
    let _d = Box::new(DG(5u32));
    0
}

#[cfg(droptuple)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[droptuple]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[droptuple]~| NOTE the drop glue of `(DG<u32>, u8)`
    let _d = (DG(5u32), 1u8);
    0
}

#[cfg(droparr)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[droparr]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[droparr]~| NOTE the drop glue of `[DG<u32>; 1]`
    let _d = [DG(5u32)];
    0
}

#[cfg(dropvec)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[dropvec]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[dropvec]~| NOTE DG<u32>
    let _d = vec![DG(5u32)];
    0
}

#[cfg(fnitem)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[fnitem]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[fnitem]~| NOTE `std::option::Option::<T>::map` in bb
    Some(&5u32).map(g2).unwrap_or(0)
}

#[cfg(closuremap)]
#[trust::assume_total]
#[inline(never)]
pub fn t() -> u32 {
    //[closuremap]~^ WARN does not cover its unsafe operations or its edges into code this compilation does not verify
    //[closuremap]~| NOTE `gm` in bb
    gm(5u32)
}

#[cfg(ms_u32impl)]
pub fn skipped(s: &S) -> u32 {
    //[ms_u32impl]~^ ERROR Trust full verification skipped `unverified_edge_generic_instance::skipped`
    //[ms_u32impl]~| NOTE has no edge out of the verified closure
    let _q = &raw const s.a;
    g2(&5u32)
}
