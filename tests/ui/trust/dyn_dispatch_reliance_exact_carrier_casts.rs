//@ needs-trust-verify
//@ edition: 2021
//@ revisions: raw non_null fake integer mismatch fabricated
//@ compile-flags: -Ztrust-verify=on --crate-type=lib -Copt-level=0
//@ rustc-env:TRUST_DYN_RELIANCE_PROBE=1
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//[raw,non_null]~? RAW C-FLOW admitted 1 target(s)
//[raw]~? RAW origin-preserving cast in `total` at bb0: PtrToPtr
//[non_null]~? RAW origin-preserving cast in `total` at bb0: Transmute
//[fake,integer,mismatch,fabricated]~? RAW C-FLOW declined: trait Emit poisoned
//[fake,integer,mismatch,fabricated]~? RAW poison from a non-`Unsize` CAST target: Emit
//[integer,mismatch,fabricated]~? RAW origin-preserving cast in `total` at bb0: Transmute
// Exact operation probes establish that every intended cast reached the analysis.
// The positive origin cases still owe unsafe/expose obligations; no validity
// credit is granted. Negative origins must remain poisoned after legal retags.
#![no_std]
#![allow(dead_code)]
pub trait Emit { fn emit(&self) -> u32; }
pub struct A;
impl Emit for A { fn emit(&self) -> u32 { 1 } }
#[repr(transparent)]
struct NonNull<T: ?Sized> { pointer: *mut T }
pub fn total() -> u32 {
 let a = A;
 let d: &dyn Emit = &a;
 #[cfg(raw)] { let p = &d as *const &dyn Emit as *mut &dyn Emit as *const &dyn Emit; let _ = p as usize; }
 #[cfg(non_null)] { let p = &d as *const &dyn Emit; let n: core::ptr::NonNull<&dyn Emit> = unsafe { core::mem::transmute(p) }; let p: *mut &dyn Emit = unsafe { core::mem::transmute(n) }; let _ = p as usize; }
 #[cfg(fake)] { let p = &d as *const &dyn Emit; let n: NonNull<&dyn Emit> = unsafe { core::mem::transmute(p) }; let p: *mut &dyn Emit = unsafe { core::mem::transmute(n) }; let _ = p as usize; }
 #[cfg(integer)] { let n: core::ptr::NonNull<&dyn Emit> = unsafe { core::mem::transmute(0xdeadusize) }; let p: *mut &dyn Emit = unsafe { core::mem::transmute(n) }; let _ = p as usize; }
 #[cfg(mismatch)] { let pair = (d, 0xdeadusize); let p = &pair as *const (&dyn Emit, usize); let n: core::ptr::NonNull<&dyn Emit> = unsafe { core::mem::transmute(p) }; let p: *mut &dyn Emit = unsafe { core::mem::transmute(n) }; let _ = p as usize; }
 #[cfg(fabricated)] { let p: *mut &dyn Emit = unsafe { core::mem::transmute(0xdeadusize) }; let n: core::ptr::NonNull<&dyn Emit> = unsafe { core::mem::transmute(p) }; let p: *const &dyn Emit = unsafe { core::mem::transmute(n) }; let _ = p as usize; }
 d.emit()
}
