//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! Trust (wave-CP): the REFUSAL half of `trust_ir_lower_ptr_ptr_cast.rs`.
//!
//! The thin raw-ptr -> raw-ptr lane is a GATE, and each conjunct of that gate
//! is a soundness claim. Under `strict` a refusal is a compile error, so the
//! refusals cannot share a file with the check-pass admissions — they are
//! pinned here, one function per conjunct, and every error annotation below must
//! survive every future widening of the lane.
//!
//! `frame_addr_launder` is the witness that matters. Its operand is a LEDGERED
//! frame snapshot: returning it UNCAST is already refused
//! (`Return(borrow ptr escapes tail)`), and admitting the cast without the
//! `is_borrow_ptr` guard would launder it into an unledgered `Ty::Ptr`, which
//! neither return-escape guard recognises — a dangling frame address returned
//! from a body the census calls clean. Delete the guard and this line stops
//! erroring; nothing else in the tree would say so.
//!
//! The tag each body carries is deliberately NOT asserted here, only that the
//! body still refuses: `frame_addr_launder` and `ref_chain` move from
//! `Cast(ptr source)` to the more precise `Cast(borrow ptr operand)` when the
//! lane lands, which is the intended outcome, not a regression.

#![allow(dead_code)]

// The ledger guard: a frame-derived address must never leave `borrow_ptrs`.
pub fn frame_addr_launder() -> *const u8 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    let x = 5u32;
    core::ptr::addr_of!(x) as *const u8
}

// RE-PINNED 2026-09-14: `ptr -> int` and `int -> ptr` are ADMITTED since wave-ITP
// (fa3dc5cef0, 2026-09-02) — the producer was the only refuser of a cast its own oracle
// already mints: trust-ir-bridge answers `CastOp::PtrToInt` / `CastOp::IntToPtr` for the
// same MIR casts, the reference interpreter executes them as first-class no-provenance
// values, and the result joins no ledger. Measured on the 4d972edcfd stage1: both bodies
// lower under `strict`. The conjuncts below (frame-address launder, thin<->fat, a
// `ty::Ref` root) are still refused and stay pinned. The mut->const coercion once pinned
// here is admitted since 94502e4acc6 and moved to `trust_ir_lower_ptr_ptr_cast.rs`.
pub fn ptr_to_int(p: *const u8) -> usize {
    p as usize
}

pub fn int_to_ptr(a: usize) -> *const u8 {
    a as *const u8
}

// THIN -> FAT: synthesises a metadata lane.
pub fn thin_to_fat(p: *const [u8; 1]) -> *const [u8] {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    p as *const [u8]
}

// FAT -> THIN: drops a metadata lane.
pub fn fat_to_thin(p: *const [u8]) -> *const u8 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    p as *const u8
}

// A `ty::Ref` at the root of the chain: the value is ledgered, so re-typing it
// would launder it out of `borrow_ptrs` exactly as `frame_addr_launder` would.
pub fn ref_chain(r: &u32) -> *const u8 {
    //~^ ERROR -Ztrust-ir-lower=strict: the direct trust-ir producer could not fully lower this body
    r as *const u32 as *const u8
}

fn main() {}
