//@ check-fail
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ forbid-output: final Trust-IR module validation failed
//@ forbid-output: CallArgTypeMismatch
//! Trust (thir-generic-instance-callee): the NEGATIVE half of signing a reference to a pointer.
//! A parameter `&P` whose pointee `P` is a thin pointer is now SIGNED `ptr`, which is also how
//! `P` spells, so the validator cannot tell a genuine `&P` from a `P` passed in its place. Every
//! call below has NO genuine borrow for its `&P` argument (a raw-pointer local or a field place
//! has no slot to point at), so each body must be refused at its OWN call site, where strict
//! reports it, and never answered by passing `P`, which would splice a program that is not this
//! one. The annotated errors ARE the pin: compiletest fails when an expected error is missing.
//!
//! MEASURED 2026-10-15 (docs/DECISION_QUEUE.md, REF-TO-PTR-SIGN-1) on stage-1 builds of this
//! tree with the call-site checks removed:
//!   * with BOTH the `ref_arg_pointee_may_be_pointer` carrier checks and the 611f4f9086
//!     `arg_is_reference` gate removed, `recv_raw`, `recv_place_raw` and `size_raw` LOWER and
//!     splice with the dropped borrow (`call @m(%0)` for `Tr::m(&q)`, `size_of_val(q)` for
//!     `size_of_val(&q)`, the field VALUE for `&(*o).inner.q`) and their three errors go missing,
//!     so this file fails;
//!   * with only the 611f4f9086 gate removed, the carrier checks alone keep all four refused.
//!
//! `chain_set` is the third carrier, the bottom hop of the `DerefMut` chain
//! (`lower_deref_mut_chain_ptr`): `s.inner.d.f = 5` through `D: DerefMut` is
//! `(*DerefMut::deref_mut(&mut (*s).inner.d)).f = 5`, and that hop would pass the leaf VALUE where
//! `&mut D` is due, which for `D = &mut Pair` is itself a `ptr` against `<&mut Pair as
//! DerefMut>::deref_mut`'s now-signed `&mut &mut Pair`. Measured: refused with the chain check in
//! place; with the carrier checks removed its body LOWERS through the chain instead (a generic
//! body, not spliced on the default lane, so this pin is what keeps that lane honest).
//! `through_carrier` (a `&&dyn` place) is refused at its call site in every one of those
//! builds: no carrier can lower a `&dyn` leaf VALUE either, so it pins the end state for that
//! shape rather than a check. The forbid-outputs keep a module-wide refusal from standing in for
//! the one-body refusals, and the controls (genuine borrows of a thin `&r`, the DB-L slot, and a
//! fat `&s`, the wave-AR2 snapshot) lower and are not refused.
use std::fmt::Debug;

pub trait Tr {
    fn m(&self) -> u8;
}

impl Tr for *const u8 {
    fn m(&self) -> u8 {
        7
    }
}

pub struct Inner {
    pub d: &'static dyn Debug,
    pub q: *const u8,
    pub n: u32,
}

pub struct Outer {
    pub inner: Inner,
}

pub struct Pair {
    pub f: u8,
    pub g: u32,
}

pub struct ChainInner<D> {
    pub d: D,
    pub n: u32,
}

pub struct Chain<D> {
    pub inner: ChainInner<D>,
}

/// A method RECEIVER: `q.m()` is `Tr::m(&q)`, an auto-ref of a raw-pointer local.
pub fn recv_raw(q: *const u8) -> u8 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    q.m()
}

/// A receiver PLACE: `Tr::m(&(*o).inner.q)`, a raw-pointer leaf under a deref.
pub fn recv_place_raw(o: &Outer) -> u8 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    o.inner.q.m()
}

/// An explicit call: `size_of_val::<*const u8>(&q)`, parameter `&*const u8`.
pub fn size_raw(q: *const u8) -> usize {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    std::mem::size_of_val(&q)
}

/// A `&&dyn Debug` place argument.
pub fn through_carrier(o: &Outer) -> usize {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    std::mem::size_of_val(&o.inner.d)
}

/// The `DerefMut` chain's bottom hop: `&mut (*s).inner.d` with `d: D`, a pointer for
/// `D = &mut Pair` (see `chain_caller`).
pub fn chain_set<D: std::ops::DerefMut<Target = Pair>>(s: &mut Chain<D>) {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    s.inner.d.f = 5;
}

pub fn chain_caller(s: &mut Chain<&mut Pair>) {
    chain_set(s)
}

pub fn thin_control(r: &u8) -> usize {
    std::mem::size_of_val(&r)
}

pub fn fat_control(s: &str) -> usize {
    std::mem::size_of_val(&s)
}
