//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **W5 (Lean-calls-Rust) — A CLEAN `def` CALLS A SIBLING RUST `fn`, AND RUNS.**
//! (`docs/design/2026-09-13-lean-calls-rust-lane.md`, increments 1 and 2; the
//! battery row `tests/two-language-programs/r18_lean_calls_rust` is the same
//! program with one callee.)
//!
//! What IS claimed: each island `def` elaborated against a kernel `Opaque`
//! the compiler declared for the sibling `fn` (increment 1), the emitter
//! produced a linear call chain to the REGISTERED callee `DefId`s, and the
//! faithfulness gate identified that chain with the island's own application
//! term by kernel definitional equality before anything linked (increment 2).
//! Every value asserted below distinguishes the emitted semantics from a
//! plausible mistranslation: the nested chain from a single call, the
//! two-callee chain from either callee alone, the swapped-argument twin of
//! `sub2`, and the `bool` and `u32` carriers from the `u64` one.
//!
//! What is NOT claimed, stated per the design's SOUNDNESS charges: nothing
//! about the CALLEES. `-Z trust-verify=off` is the point — the compiler
//! asserts that the constant `inc` DENOTES `fn inc` (a `docs/TCB.md` row),
//! the kernel proved nothing about `inc` beyond its type, and whether `inc`
//! panics or returns is an ordinary obligation of `inc` that verification ON
//! (increment 3) charges. No panic-free registration and no caller-side
//! summary are minted for these defs.

// The `dead_code` lint could not see a call that exists only in a Clean-origin
// body (the MIR is synthesized after the lint walks HIR). Since 2026-09-28 it
// follows the resolver's island use edges instead; see
// `clean_origin_rust_callee_not_dead_code.rs`. The `allow` is kept so this
// fixture keeps pinning the call lane alone.
#![allow(dead_code)]

fn inc(x: u64) -> u64 {
    x.wrapping_add(1)
}

fn dbl(x: u64) -> u64 {
    x.wrapping_mul(2)
}

fn sub2(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
}

fn half32(x: u32) -> u32 {
    x / 2
}

fn is_small(x: u32) -> bool {
    x < 10
}

clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
    def inc_dbl (x : UInt64) : UInt64 := dbl (inc x)
    def dbl_inc (x : UInt64) : UInt64 := inc (dbl x)
    def diff (a b : UInt64) : UInt64 := sub2 a b
    def minus5 (x : UInt64) : UInt64 := sub2 x 5
    def quarter (x : UInt32) : UInt32 := half32 (half32 x)
    def small_half (x : UInt32) : Bool := is_small (half32 x)
}

fn main() {
    let v = twice_inc(5);
    println!("twice_inc(5) = {v}");
    assert_eq!(v, 7, "two applications of `inc`; a single one would give 6");
    assert_eq!(twice_inc(u64::MAX), 1, "the chain wraps through the intermediate");

    // Two DIFFERENT callees in one chain, in both orders: the order is the
    // tree, and the tree is what the gate compared.
    assert_eq!(inc_dbl(5), 12, "dbl (inc 5) = (5 + 1) * 2");
    assert_eq!(dbl_inc(5), 11, "inc (dbl 5) = 5 * 2 + 1");

    // A two-argument callee: the argument ORDER is the swapped-argument
    // mutation `control_23::half_2` measures the kernel refusing.
    assert_eq!(diff(10, 3), 7, "sub2 a b, not sub2 b a (which would wrap)");
    assert_eq!(diff(3, 10), 3u64.wrapping_sub(10), "and in the other order");
    assert_eq!(minus5(12), 7, "a numeral operand at the callee's carrier");

    // Other carriers: `u32` and `bool`.
    assert_eq!(quarter(40), 10);
    assert!(small_half(18), "half32 18 = 9 < 10");
    assert!(!small_half(20), "half32 20 = 10, not small");
}
