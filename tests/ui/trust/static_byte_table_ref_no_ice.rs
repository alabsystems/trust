//@ dont-check-compiler-stderr
//@ check-pass
//! Regression for the trust-mir-extract ICE "expected memory, got Static(..)"
//! (`convert.rs` `array_ref_u8_const_bytes`): a `&[u8; N]` MIR constant may
//! point into a NAMED `static` (ryu's `DIGIT_TABLE`, webpki's `ID_CE` OID),
//! whose `GlobalAlloc` is `Static(..)`, not inline `Memory(..)` —
//! `unwrap_memory()` aborted the whole compile (exit 101) on any crate
//! referencing a static byte table under default-on verification. The reader
//! is a diagnostics-only exact-or-`None` helper, so the fix bails gracefully
//! (`GlobalAlloc::Memory` let-else → `None`) instead of ICEing.
//!
//! Salvaged from the 2026-07-15 audit-agent patch, landed with this test.
//! The guarded indexing keeps every Level-0 obligation provable, so the
//! compile must simply pass — before the fix it ICE'd.
static DIGIT_TABLE: [u8; 8] = [48, 49, 50, 51, 52, 53, 54, 55];

pub fn digit(i: usize) -> u8 {
    if i < 8 { DIGIT_TABLE[i] } else { 0 }
}

pub fn pair(i: usize) -> (u8, u8) {
    let t: &[u8; 8] = &DIGIT_TABLE;
    if i + 1 < 8 { (t[i], t[i + 1]) } else { (0, 0) }
}

fn main() {}
