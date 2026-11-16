//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type=lib -Copt-level=0
//@ rustc-env:TRUST_DYN_RELIANCE_PROBE=1
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//~? RAW C-FLOW declined: trait Emit poisoned
//~? RAW cast Transmute: `*const &dyn Emit<u8>` -> `core::ptr::NonNull<&dyn Emit<u16>>`
//~? RAW origin-preserving cast in `total` at bb0: Transmute `core::ptr::NonNull<&dyn Emit<u16>>` -> `*mut &dyn Emit<u16>`
#![no_std]
#![allow(dead_code)]
// Same trait DefId with different type arguments must not count as equal pointees.
pub trait Emit<T> { fn emit(&self) -> u32; }
pub struct A;
impl Emit<u8> for A { fn emit(&self) -> u32 { 1 } }
impl Emit<u16> for A { fn emit(&self) -> u32 { 2 } }
pub fn total() -> (u32, usize) {
    let a = A;
    let source: &dyn Emit<u8> = &a;
    let target: &dyn Emit<u16> = &a;
    let p = &source as *const &dyn Emit<u8>;
    let n: core::ptr::NonNull<&dyn Emit<u16>> = unsafe { core::mem::transmute(p) };
    let retag: *mut &dyn Emit<u16> = unsafe { core::mem::transmute(n) };
    (target.emit(), retag as usize)
}
