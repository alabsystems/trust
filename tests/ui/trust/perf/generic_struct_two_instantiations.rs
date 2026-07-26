//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust: regression for the trust-ir producer's per-instantiation struct
//! identity (totality Batch B). The registration ledger deduped by bare
//! `DefId` while field types were substituted per-instantiation — so
//! `Pair<u8>` and `Pair<u32>` aliased to whichever registered first,
//! mis-typing the second's fields in the recorded `StructDef` (a confirmed
//! latent field-type bug), and the DefId-keyed cycle guard false-positived
//! on nested DISTINCT instantiations (`Outer<Inner>` wrapping `Inner`:
//! typenum's whole `UInt<UInt<..>>` vocabulary), tagging finite DAG walks
//! as `Ty(recursive adt)`.
//!
//! Both shapes below must lower under `-Z trust-ir-lower` without aborting
//! (check-pass), with distinct instantiations getting distinct StructDefs
//! (asserted by the coverage/artifact validation in the batch protocol —
//! this fixture locks the compile-level behavior).
pub struct Pair<T> {
    pub a: T,
    pub b: T,
}

pub struct Inner {
    pub x: u32,
}

pub struct Outer {
    pub inner: Inner,
    pub tag: u8,
}

pub fn use_u8(p: Pair<u8>) -> u8 {
    p.a
}

pub fn use_u32(p: Pair<u32>) -> u32 {
    p.b
}

pub fn nest(o: Outer) -> u32 {
    o.inner.x
}

fn main() {}
