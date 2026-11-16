//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ proc-macro: trust.rs
//@ edition: 2021
//! Trust D3 (cast half), pointer-sized lane. `u32::MAX as usize` is the real
//! guard ay could not write, and it was refused for TWO independent reasons:
//! the associated constant did not resolve, and `usize`/`isize` were excluded
//! from the cast rule WHOLESALE.
//!
//! The exclusion was conservative rather than wrong — `fixed_int_bits_signed`
//! returned `None` for `usize` because "a spec must not silently bake in a
//! target word size". But this boundary is inside rustc, where the width is not
//! a guess: `tcx.data_layout.pointer_size()` is the same authority
//! `proposition_domain_from_ty` already uses to build the
//! `PointerSizedInt { width }` domain that the contract's own free-variable
//! sidecar carries. Deciding the cast with it is therefore exactly as
//! target-specific as the proposition it feeds, and nothing is baked in: a
//! cross-compile to a 16-bit target RE-DECIDES `u32 as usize` and refuses it
//! there, because there it truncates.
//!
//! WHAT THIS ASSERTS IS THE OBLIGATION. Each precondition is assumed only if
//! the clause lowered, so each body assert discharges only on that condition,
//! and `off_by_one` — one tighter than its precondition — must stay REFUTED.
//!
//! `main`'s PINS RE-MEASURED 2026-09-16. It carried two WARN annotations —
//! `Trust Level 0 safety verification incomplete` and `Trust verification
//! advisory` — recording that the harness body itself had an unproved row. It
//! does not any more: `main` now reports `1 proved, 0 failed, 0 unknown, 0 timed
//! out, 0 runtime-checked out of 1 obligation(s)` and emits no warning at all.
//!
//! The pins are REPLACED by that line rather than deleted. `main` exists here
//! only to instantiate the functions above, so a silent `main` is indistinguishable
//! from a `main` that was never verified; pinning the count keeps the harness
//! itself measured. Every ERROR this file is actually about is unchanged and
//! still covered by `dont-require-annotations: ERROR`.


// ay's real contract: u32 -> usize, value-preserving on a 64-bit target.
#[trust::requires(idx <= u32::MAX as usize)]
pub fn from_index(idx: usize) -> usize {
    assert!(idx <= 4294967295);
    idx
}

// EXACTNESS GUARD: one tighter than the precondition -> must NOT discharge.
#[trust::requires(idx <= u32::MAX as usize)]
pub fn off_by_one(idx: usize) -> usize {
    assert!(idx <= 4294967294);
    idx
}

// usize -> u64 is the identity on a 64-bit target.
#[trust::requires(n as u64 <= 10)]
pub fn pointer_sized_to_fixed(n: usize) -> usize {
    assert!(n <= 10);
    n
}

// u8 -> i16: unsigned to a STRICTLY wider signed target keeps every value.
#[trust::requires(b as i16 <= 10)]
pub fn unsigned_to_wider_signed(b: u8) -> u8 {
    assert!(b <= 10);
    b
}

fn main() { //~ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    let _ = from_index(0);
    let _ = off_by_one(0);
    let _ = pointer_sized_to_fixed(0);
    let _ = unsigned_to_wider_signed(0);
}
