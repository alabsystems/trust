//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! §13.1 of `docs/STRICT_VERIFICATION_FRAGMENT.md`, pinned: a numeric literal
//! in a contract predicate may be written the way Rust writes one.
//!
//! Measured 2026-08-29 before the fix, every function below except `bare`
//! reported `SpecEnsuresUnparseable` and TWO UNKNOWN rows — with no diagnostic
//! naming the literal, while the identical constant in the same function's
//! BODY was fine. The failure was in the SPELLING, not the magnitude: a
//! separator in the two-digit `1_0` was as fatal as one in `999_999_999`.
//!
//! This fixture is `check-pass` under `-Ztrust-verify=on`, so it is not merely
//! asserting that the clauses parse: an unproved obligation is an error on this
//! lane, so every function here must actually DISCHARGE its postcondition. That
//! is the property that regressed silently and the only one worth pinning —
//! "the clause was accepted" and "the clause was proved" are exactly the two
//! things §13.1 shows can come apart without a word of output.
//!
//! `bare` is the control. It passed before the fix and must keep passing; if it
//! ever fails alongside the others, the cause is the lane and not the lexer.

pub fn bare(x: u32) -> u32 ensures result <= 999999999 {
    if x > 999999999 { return 999999999; }
    x
}

pub fn separators(x: u32) -> u32 ensures result <= 999_999_999 {
    if x > 999999999 { return 999999999; }
    x
}

pub fn hexadecimal(x: u32) -> u32 ensures result <= 0x3B9AC9FF {
    if x > 999999999 { return 999999999; }
    x
}

pub fn type_suffix(x: u32) -> u32 ensures result <= 999999999u32 {
    if x > 999999999 { return 999999999; }
    x
}

/// The separator is fatal at any width, so the small case is pinned too.
pub fn separator_in_a_two_digit_literal(x: u32) -> u32 ensures result <= 1_0 {
    if x > 10 { return 10; }
    x
}

pub fn binary(x: u32) -> u32 ensures result <= 0b111 {
    if x > 7 { return 7; }
    x
}

pub fn octal(x: u32) -> u32 ensures result <= 0o17 {
    if x > 15 { return 15; }
    x
}

/// `requires` reaches the same grammar down a different road — `trust-types`'
/// `spec_parse`, not the compiler's snippet tokenizer — and it used to refuse a
/// separator with "trailing tokens after expression", a message that names
/// everything except the separator.
///
/// Measured 2026-08-29, this function's rows are IDENTICAL to those of the
/// same function spelled `requires x <= 1000`: one `assumption:requires`
/// `skipped` (the standard callee-side treatment of a precondition, unrelated
/// to the literal) and two `postcond` `proved`. Recorded so the `skipped` row
/// is not read as something this fixture is claiming.
pub fn precondition_separator(x: u32) -> u32 requires x <= 1_000 ensures result <= 1000 {
    x
}
