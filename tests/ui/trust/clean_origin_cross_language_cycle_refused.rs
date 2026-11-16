//@ needs-trust-verify
//@ revisions: verifyoff verifyon
//@[verifyoff] compile-flags: -Ztrust-verify=off
//@[verifyon] compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

//! **CROSS-LANGUAGE CYCLE — the designed refusal, not `E0391`.**
//! (`compiler/rustc_mir_transform/src/clean_origin_mir.rs`,
//! `callee_reaches_a_gate_on_this_stack`; 2026-09-25.)
//!
//! `fn inc` calls `def twice_inc` calls `inc`. The Clean-origin gate models a Rust
//! callee as a pure value the kernel already checked; a callee whose own body
//! depends on THIS declaration has no such value, so the cycle must be refused —
//! with a cause naming both languages.
//!
//! WHAT THIS PINS, and why it is not decoration. Before the guard this program
//! reported `error[E0391]: cycle detected when optimizing MIR for twice_inc`: a
//! query-engine internal that names no Clean declaration, offers no remedy, and
//! reads as a compiler bug rather than a refused program. Reproduce by making
//! `callee_reaches_a_gate_on_this_stack` return `false` and rebuilding — measured
//! 2026-09-25, E0391 at both revisions.
//!
//! BOTH REVISIONS ARE LOAD-BEARING. The two lanes reach the cycle by different
//! demand orders, and the FIRST version of this guard fixed only `verifyoff`
//! while `verifyon` still emitted E0391 — measured. A guard tested in one lane is
//! not a guard.
//!
//! The acyclic companion is `clean_origin_acyclic_nesting_still_compiles.rs`: the
//! refusal must not cost the legal nesting it resembles.

fn inc(x: u64) -> u64 {
    if x == 0 { 0 } else { twice_inc(x - 1) }
}

clean {
    def twice_inc (x : UInt64) : UInt64 := inc (inc x)
}
//~^^ ERROR cannot be called from Rust
//~| NOTE CROSS-LANGUAGE CYCLE

fn main() {
    let _v = twice_inc(5);
}
