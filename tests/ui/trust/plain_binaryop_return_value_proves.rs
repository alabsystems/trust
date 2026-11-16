//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! ORDINARY Rust: a plain `if`/`else` whose taken arm divides, with a
//! postcondition that is obviously true. This must PROVE, with no annotation
//! beyond the contract itself.
//!
//! It did not. The emitted query named the division's temporary and never said
//! what it was, so the solver could assign it anything and the negated clause
//! stayed satisfiable. The row came back `unknown` and the build was refused.
//!
//! The defect was operator-shaped, which is a strange thing for a verifier to
//! be. `+`, `-` and `*` lower to `CheckedBinaryOp`, whose value is a field the
//! arm's assert-passed semantic guard pins — a lane that survives the branch
//! merge. Division, remainder and the shifts are plain `BinaryOp`, so their
//! value equation exists only as a block definition, and the block definitions
//! were being offered to the relevance filter BEFORE the return pin introduced
//! the name that would have made them relevant.
//!
//! `plain_binaryop_return_value_refutes.rs` is the other half: the same body
//! under a FALSE clause must still be refused. A fix that proves both is not a
//! fix.

pub fn half_nonneg(x: i32) -> i32
    requires x >= 0
    ensures result >= 0
{
    if x < 0 { 0 } else { x / 2 }
}

pub fn remainder_is_bounded(x: i32) -> i32
    requires x >= 0
    ensures result >= 0
{
    if x < 0 { 0 } else { x % 7 }
}

// The fix is not division-specific, so pin the rest of the plain-`BinaryOp`
// family here. Each of these produces a temporary whose defining equation was
// dropped before the return pin introduced its name, and each is a shape an
// ordinary program writes without thinking about it. Checked arithmetic is
// deliberately absent: `+`, `-` and `*` never had the bug.

pub fn masked_is_nonnegative(x: i32) -> i32
    // CAPABILITY RETURNED on the 1.101 toolchain (2026-10-18, measured: all
    // three body rows prove, and `plain_binaryop_return_value_refutes.rs`
    // still refuses the false clause, so the return is discriminating).
    // Was: CAPABILITY LOSS, re-pinned 2026-10-15 (the merge of 2026-10-14;
    // docs/KNOWN_HAZARDS.md "OPEN 2026-10-15 — correct programs the merge of
    // 2026-10-14 refuses", DECISION_QUEUE D103(i)): the `ensures result >= 0`
    // row of the `x & 1023` return path was `unknown`.
    ensures result >= 0
{
    if x < 0 { 0 } else { x & 1023 }
}

// Both widths, deliberately, because for a while only one of them worked and
// the reason was not the one it looked like. rustc routed the `i64` body through
// a temporary and wrote the `i32` one straight into the return slot; the direct
// form's defining equation was then pruned on a token mismatch against the
// return block's merged token, the row had no pin, and the tripwire failed it
// closed. It read exactly like a solver declining a 32-bit query. It was not.
pub fn shifted_is_nonnegative_i32(x: i32) -> i32
    requires x >= 0
    ensures result >= 0
{
    if x < 0 { 0 } else { x >> 1 }
}

pub fn shifted_is_nonnegative_i64(x: i64) -> i64
    requires x >= 0
    ensures result >= 0
{
    if x < 0 { 0 } else { x >> 1 }
}

pub fn ored_is_nonnegative(x: i32) -> i32
    // See `masked_is_nonnegative`: returned with it on 1.101 (the `x | 1` path
    // proves; measured 2026-10-18).
    requires x >= 0
    ensures result >= 0
{
    if x < 0 { 0 } else { x | 1 }
}
