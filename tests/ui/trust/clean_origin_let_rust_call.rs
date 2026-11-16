//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off -C overflow-checks=on
//@ dont-check-compiler-stderr
//! **W5 increment 7 — A `let`-BOUND RUST CALL IS ONE VALUE TEMPORARY, EVALUATED ONCE.**
//! (`docs/design/2026-09-13-lean-calls-rust-lane.md`, "Increment 7"; battery
//! row `tests/two-language-programs/r24_clean_pure_callee_let` is the two-def
//! version of this program.)
//!
//! What IS claimed: a `let y := f x; …` on the spine of a Clean `def`, with `f`
//! a PURE sibling `fn`, is emitted as ONE `Call` into a temporary that the body
//! reads any number of times — zero (`dead`, `dead_panics`), one
//! (`once_pure_let`), two (`dup_pure_let`), through another binding (`nested`,
//! `chain_val`) — in binding order, before the body. Every value asserted
//! below distinguishes that from the zeta-substituted twin: `dup_pure_let(5)`
//! is `0` either way, so `dead_panics` is the load-bearing witness — its
//! binding is never read, the substituted body would drop the call, and the
//! call PANICS at `0` (`dec(0)` overflows under `-C overflow-checks=on`, an
//! `Assert` terminator the purity guard admits). A zero-use binding that
//! still panics is the once-evaluation the kernel cannot see.
//!
//! What is NOT claimed: nothing about the callees beyond purity (the guard's
//! MIR walk), and nothing about Lean fidelity — Lean's compiler drops dead
//! lets; Trust's strict reading evaluates them, as `docs/TCB.md`'s
//! "let-temp ONCE-EVALUATION" row discloses.

#![allow(dead_code)]

fn inc(x: u64) -> u64 {
    x.wrapping_add(1)
}

fn dbl(x: u64) -> u64 {
    x.wrapping_add(x)
}

fn sub2(a: u64, b: u64) -> u64 {
    a.wrapping_sub(b)
}

// PURE, and PANICS at 0: `0 - 1` is an `Assert` terminator under overflow checks.
fn dec(x: u64) -> u64 {
    x - 1
}

clean {
    def dup_pure_let (x : UInt64) : UInt64 := let y := dbl x; sub2 y y
    def once_pure_let (x : UInt64) : UInt64 := let y := dbl x; sub2 y x
    def dead (x : UInt64) : UInt64 := let y := dbl x; sub2 x x
    def nested (x : UInt64) : UInt64 := let a := dbl x; let b := dbl a; sub2 b a
    def tail (x : UInt64) : UInt64 := let y := dbl x; y
    def chain_val (x : UInt64) : UInt64 := let y := inc (dbl x); sub2 y y
    def dead_panics (x : UInt64) : UInt64 := let y := dec x; sub2 x x
}

fn main() {
    assert_eq!(dup_pure_let(5), 0); // sub2(10, 10)
    assert_eq!(once_pure_let(4), 4); // sub2(8, 4)
    assert_eq!(dead(7), 0); // sub2(7, 7); `dbl 7` evaluated and unread
    assert_eq!(nested(3), 6); // a = 6, b = 12, sub2(12, 6)
    assert_eq!(tail(7), 14); // identity let: one call
    assert_eq!(chain_val(1), 0); // y = inc(dbl 1) = 3, sub2(3, 3)
    assert_eq!(dead_panics(3), 0); // dec(3) evaluated and unread
    // The dead binding is EVALUATED: dec(0) panics before sub2 runs.
    assert!(std::panic::catch_unwind(|| dead_panics(0)).is_err());
    println!("let-temp: once-evaluation holds, dead binding panics");
}
