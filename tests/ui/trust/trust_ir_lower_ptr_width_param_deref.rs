//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-PWP): the `&`-pattern param bind covers POINTER-WIDTH ints.
//!
//! `pointee_scalar` silently returned `None` for `isize`/`usize`, so the bind
//! never happened and every USE of the local reported the cascade
//! `VarRef(unbound)` — a tag with 134 touches whose root here was two missing
//! match arms. The ORACLE already mints the pair (`trust-ir-bridge` maps
//! `Ty::PtrSizedInt{signed}` to `Isize`/`Usize`), so the producer was the only
//! refuser and the differential could never have compared them.
//!
//! The classification arms are a read of ground truth; the 64-bit ADMISSION
//! gate lives at the single production call site, which has the `TyCtxt` the
//! classifier deliberately does not — and NOT threaded through
//! `deref_param_scalar_admits`, whose signature nine in-file tests call
//! (widening it is the arity churn that broke main's test target once already).
//! `map_ty` degrades `isize`/`usize` off 64-bit, so mirroring that condition
//! keeps the lane from ever being ahead of the mapper.

pub fn sum_isize(v: &[isize]) -> isize {
    v.iter().map(|&b| b + 1).sum()
}

pub fn sum_usize(v: &[usize]) -> usize {
    v.iter().map(|&b| b * 2).sum()
}

fn main() {
    assert_eq!(sum_isize(&[1, 2, 3]), 9);
    assert_eq!(sum_usize(&[1, 2, 3]), 12);
}
