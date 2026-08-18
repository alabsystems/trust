//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
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
//! VACUOUS until 2026-08: it shipped with no verify directives, and
//! compiletest injects `-Ztrust-verify=off` into every managed compile
//! (`TRUST_VANILLA_RUSTC_FLAG`), so the extractor never ran and the test
//! stayed green against a compiler that still had the ICE. Verification must
//! be ON for this pin to bite; `needs-trust-verify` makes the mode explicit.
//!
//! Advisory policy, not strict: `pair` computes `i + 1`, whose add-overflow
//! obligation is genuinely refutable (`i == usize::MAX`), so strict Level-0
//! verification rejects this crate even with the ICE fixed. The pin is that
//! verification RUNS and the compile survives — before the fix it ICE'd.
static DIGIT_TABLE: [u8; 8] = [48, 49, 50, 51, 52, 53, 54, 55];

pub fn digit(i: usize) -> u8 {
    if i < 8 { DIGIT_TABLE[i] } else { 0 }
}

pub fn pair(i: usize) -> (u8, u8) {
    let t: &[u8; 8] = &DIGIT_TABLE;
    if i + 1 < 8 { (t[i], t[i + 1]) } else { (0, 0) }
}

fn main() {}
