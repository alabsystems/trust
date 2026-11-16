//@ revisions: default certify safe
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-fail
//@[certify] check-fail
//@[safe] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! WRAPPING-SUB-AND-INTERVAL-NEG-1 (2026-11-09): two independent false proofs of the
//! 128-bit negation `-(1i128 << amt)`, each enough on its own to report a row that
//! panics as proved.
//!
//! * THE WRAPPING SUBTRACTION (`w`, `w_method`). trust-vcgen's shift-amount bound
//!   (`overflow_vc.rs`, `v2_amount_sub_source_at_use`) read a bare `BinaryOp(Sub)`
//!   as mathematical subtraction: from `src < 4294967210` and
//!   `amt = src.wrapping_sub(4294967200)` it derived `amt < 10`, though `src = 31`
//!   gives `amt = 127` and `w(31)` panics ("attempt to negate with overflow"). The
//!   bound is now derived only when a dominating `src >= MIN + c` proves the
//!   subtraction cannot wrap (`w_safe`).
//! * THE UNSIGNED INTERVAL (`g`). trust-router's interval lane
//!   (`interval_backend.rs`, `prove_neg_no_overflow`) compared the SIGNED `i128::MIN`
//!   with the UNSIGNED interval of the bit-vector operand `bvshl(1, amt)`, `[0, ∞)`,
//!   and proved `if amt < 128 { -(1i128 << amt) }` although `g(127)` panics. The
//!   interval lane runs before ay, so ay's refutation never ran. A bit-vector
//!   operand is now never evaluated; the obligation's Int-sorted subject is.
//!
//! The binary was never wrong: no check was elided (neither proof carried kernel or
//! native authority, so both rows kept rustc's own overflow check). The lie is the
//! default lane ACCEPTING `w` and `g` on a proof that does not hold.
//!
//! BEFORE (stage 1 of `0bed4bba00`, each revision's flags, `--emit=metadata`,
//! measured 2026-11-09): under `default`, `w`, `w_method` and `g` each exit with
//! warnings only, their negation row reading `[negation] runtime-checked: solver
//! interval reported Proved without exact kernel/native proof authority`; under
//! `certify` the same row is an error for lack of authority, not a refutation. No
//! `[negation] FAILED` note appears for any of the three in either revision, so
//! every annotation below is absent before the fix.
//!
//! AFTER (stage 1 of this change, the same flags): each of the three reports
//! `[negation] FAILED (ay-in-process)` under both policies. `w_add` reads
//! `[overflow:add] FAILED` before and after: the false bound reached its add
//! formula (trust-vcgen's `signed_128_overflow_tests` pin that it no longer does),
//! but ay refuted the row regardless, so its end-to-end verdict does not move.
//! `w_safe` builds under `default` before and after, its rows `runtime-checked`;
//! the `safe` revision pins that the cannot-wrap case is not refuted.

#![feature(core_intrinsics)]
#![allow(internal_features)]

#[cfg(not(safe))]
pub fn w(src: u32) -> i128 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE [negation] FAILED
    if src < 4294967210 {
        let amt = core::intrinsics::wrapping_sub(src, 4294967200u32);
        if amt < 128 {
            return -(1i128 << amt);
        }
    }
    0
}

// The stable spelling reaches the same bare `Sub`.
#[cfg(not(safe))]
pub fn w_method(src: u32) -> i128 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE [negation] FAILED
    if src < 4294967210 {
        let amt = src.wrapping_sub(4294967200);
        if amt < 128 {
            return -(1i128 << amt);
        }
    }
    0
}

// The same false bound reached the signed 128-bit ADD lane: `w_add(30)` gives
// `amt = 126` and `2^126 + 2^126` overflows.
#[cfg(not(safe))]
pub fn w_add(src: u32) -> i128 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE [overflow:add] FAILED
    if src < 4294967210 {
        let amt = core::intrinsics::wrapping_sub(src, 4294967200u32);
        if amt < 128 {
            return (1i128 << amt) + (1i128 << 126);
        }
    }
    0
}

#[cfg(not(safe))]
pub fn g(amt: u32) -> i128 {
    //[default,certify]~^ ERROR Trust Level 0 safety verification incomplete
    //[default,certify]~| ERROR Trust strict verification failed
    //[default,certify]~| NOTE [negation] FAILED
    if amt < 128 { -(1i128 << amt) } else { 0 }
}

// The designed case the bound is kept for: behind `src >= 4294967200` the wrapping
// subtraction cannot wrap, so `amt < 10` holds and `-(1i128 << amt)` is safe.
#[cfg(safe)]
pub fn w_safe(src: u32) -> i128 {
    if src < 4294967210 && src >= 4294967200 {
        let amt = core::intrinsics::wrapping_sub(src, 4294967200u32);
        return -(1i128 << amt);
    }
    0
}
