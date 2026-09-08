//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (wave-ITP): an UNSIGNED-INTEGER -> THIN RAW-POINTER `as` cast is
//! `CastOp::IntToPtr` — the exact inverse of the shipped wave-PTI arm, and the
//! one op in this family whose spelling the MIR ORACLE has minted all along
//! (`trust-ir-bridge`'s lowerer answers `IntToPtr` for this very MIR cast, and
//! the trust-ir frontend's own MIR lowerer does too). Same shape as wave-DNP:
//! one side of the pair already had the mint and the producer was the only
//! refuser.
//!
//! It needs no new carrier and no layout evidence: the op exists, the reference
//! interpreter executes it (resolving to a first-class no-provenance value), it
//! is in the conformance subset with no exclusion, and the layout-sensitive
//! cast list names PtrToPtr/Bitcast/Transmute/ReifyFnPointer — not this.
//!
//! `ref_dest_declines` is the fence: a reference has provenance obligations an
//! integer cannot supply, so only a RAW destination is admitted.

pub fn int_to_ptr(n: usize) -> *const isize {
    n as *const isize
}

pub fn round_trip(x: &isize) -> isize {
    let n = x as *const isize as usize;
    let p = n as *const isize;
    unsafe { *p }
}

fn main() {
    let p = int_to_ptr(0);
    assert!(p.is_null());
    let v: isize = 41;
    assert_eq!(round_trip(&v), 41);
}
