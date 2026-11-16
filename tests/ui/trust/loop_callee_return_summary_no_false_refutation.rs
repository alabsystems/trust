//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! A same-crate callee's RETURN SUMMARY must reach a LOOP BODY (TRUST-10).
//!
//! `reverse_bits` is bit-vec 0.9.1's (`src/lib.rs:206`), verbatim, with its
//! `BitBlock` impl for `u8` reduced to the one method it calls. It was reported
//!
//!     [overflow:sub] FAILED (ay-in-process); counterexample: … _17 = 0, …
//!     [shift:left]   FAILED (trust-bitmask-refute)
//!     [shift:right]  FAILED (ay-in-process); counterexample: … _5 = 9, …
//!
//! although `u8::bits()` is 8 on every call and the function panics on none of
//! its 256 inputs. The callee's const-set summary `{8}` was applied only as a
//! PATH fact at each call, and a path fact does not survive the loop-header
//! join, so the loop body saw both call results as free variables.
//!
//! THE STRICT BUILD IS THE ASSERTION. Under the default policy a refuted row is
//! fatal, while a row that keeps rustc's runtime check is reported and tolerated
//! (policy B) — two of `reverse_bits`' rows are still runtime-checked, which is
//! why warnings are allowed here. So this file compiles exactly when no row is
//! refuted. The paired `loop_callee_return_summary_real_overflow_still_refutes.rs`
//! plants a real overflow through a summarised callee and must keep failing.
pub trait Bits {
    fn bits() -> usize;
}
impl Bits for u8 {
    #[inline]
    fn bits() -> usize {
        8
    }
}

fn eight() -> usize {
    8
}

pub fn reverse_bits(byte: u8) -> u8 {
    let mut result = 0;
    for i in 0..u8::bits() {
        result |= ((byte >> i) & 1) << (u8::bits() - 1 - i);
    }
    result
}

pub fn lsb_fold(byte: u8) -> u8 {
    let mut r = 0;
    for i in 0..eight() {
        r |= (byte >> i) & 1;
    }
    r
}
