//@ revisions: default lower off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: --crate-type lib
//@[default] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict
//@[lower] compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on
//@[off] compile-flags: -Ztrust-verify=off
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: E0391
//@ forbid-output: cycle detected
//@ forbid-output: error[E
//! OPAQUE-IMPL-WHERE-LEAK-1 residual (b), the WRITE side: a leak-free answer must not reach the
//! old solver's GLOBAL caches, which stock typeck reads.
//!
//! Drop-in (release gate): `nightly-2026-04-20` accepts this crate, and so must every lane.
//! `leak`'s typeck leaks `define_rpit`'s auto traits (`need_send`), which borrow-checks and so
//! builds `define_rpit`; inside that `mir_built` the producer asks `needs_drop(C)` leak-free, and
//! its walk asks `Wrap<u8>: Copy`, whose impl's where-clause `Wrap2<u8>: Send` reaches `Tait`
//! through a field: AMBIGUOUS with every local opaque definable. The old solver keys its global
//! evaluation cache by the typing mode with the defining set ERASED, so that ambiguity was
//! stored under the very key `caller`'s typeck then reads `Wrap2<u8>: Send` from: specialization
//! winnowing could not drop the specializing `Pick` impl, kept both candidates, and reported
//! E0283 ("type annotations needed: cannot satisfy `Wrap<u8>: Pick`") under `default` and
//! `lower` on the stage 1 of main `3ce41aa8e`; `off` never asks. Stock rejects the specializing
//! impl (`Tait` is a raw pointer, so `Wrap2<u8>: Send` is false) and selects the blanket one.
//! Every leak-free question is now asked in an environment carrying an inference region
//! (`trust_mir_extract::ctfe_reentrancy::leak_free_infcx`), which keeps it to its own caches.

#![feature(type_alias_impl_trait, specialization)]
#![allow(incomplete_features, dead_code, unused)]

pub type Tait = impl Sized;
#[define_opaque(Tait)]
pub fn define_tait() -> Tait {
    0usize as *const u8
}

pub struct Wrap2<T> { t: T, x: Tait }
#[derive(Clone)]
pub struct Wrap<T>(pub T);
// Never holds: `Tait` is `*const u8`, so `Wrap2<u8>: Send` is false.
impl<T: Copy> Copy for Wrap<T> where Wrap2<T>: Send {}

pub trait Pick { fn pick(&self) -> u8; }
impl<T> Pick for T { default fn pick(&self) -> u8 { 1 } }
impl<T> Pick for Wrap<T> where Wrap2<T>: Send { fn pick(&self) -> u8 { 2 } }

pub struct C { w: Wrap<u8>, n: u32 }
fn need_send<T: Send>(_: &T) {}
pub fn define_rpit(c: &C) -> impl Sized { c.n }

pub fn leak() {
    let c = C { w: Wrap(0u8), n: 1 };
    need_send(&define_rpit(&c));
}

fn need_pick<T: Pick>(_: &T) {}

pub fn caller() {
    need_pick(&Wrap(0u8));
}
