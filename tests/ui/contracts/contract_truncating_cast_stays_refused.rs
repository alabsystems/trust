//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ proc-macro: trust.rs
//@ edition: 2021
//! Trust D3 (cast half) — THE ADVERSARIAL FIXTURE. A truncating cast lowered as
//! identity is the canonical false-proof bug, and this is the case that would
//! expose it.
//!
//! The contract formula is over MATHEMATICAL integers: every integer
//! proposition domain maps to `Sort::Int`, so `+`/`*` never wrap at a machine
//! width. That is exactly why a VALUE-PRESERVING cast may be dropped (`x as
//! u64` denotes the same mathematical value as `x`) and exactly why a
//! TRUNCATING one may not.
//!
//! `x as u8 == 0` is true iff x = 0 (mod 256). x = 256 satisfies it while
//! `x == 0` is FALSE. So if `x as u8` were lowered as the bare `x`, the
//! verifier would assume `x == 0` and the body's `assert!(x == 0)` would be
//! PROVED — a proof of something the program does not guarantee. The assert
//! must therefore stay unproved, and the build must fail.
//!
//! The three refused neighbours below are the rest of the boundary: narrowing
//! (`u64 as u32`), sign-changing (`i32 as u32`), and the unsigned->signed case
//! that needs a strictly wider target (`u8 as i8`, where 255 becomes -1). None
//! of them may lower. Their value-preserving counterparts are the subject of
//! `contract_widening_cast_lowers.rs`.


// x = 256 satisfies the precondition but not the assert.
#[trust::requires(x as u8 == 0)]
pub fn truncating(x: u32) -> u32 { //~ WARN `#[trust::requires]` on `truncating` is not assumed
    assert!(x == 0);
    x
}

// u64 -> u32 truncates.
#[trust::requires(a as u32 == 0)]
pub fn narrowing(a: u64) -> u64 { //~ WARN `#[trust::requires]` on `narrowing` is not assumed
    assert!(a == 0);
    a
}

// i32 -> u32 does not preserve negatives: -1i32 as u32 is 4294967295.
#[trust::requires(a as u32 == 0)]
pub fn sign_changing(a: i32) -> i32 { //~ WARN `#[trust::requires]` on `sign_changing` is not assumed
    assert!(a == 0);
    a
}

// u8 -> i8 needs a STRICTLY wider target: 255u8 as i8 is -1.
#[trust::requires(a as i8 == 0)]
pub fn unsigned_to_same_width_signed(a: u8) -> u8 { //~ WARN `#[trust::requires]` on `unsigned_to_same_width_signed` is not assumed
    assert!(a == 0);
    a
}

fn main() {
    let _ = truncating(0);
    let _ = narrowing(0);
    let _ = sign_changing(0);
    let _ = unsigned_to_same_width_signed(0);
}
