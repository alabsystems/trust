//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ build-pass
//! Regression: a contract quantifier whose binder SHADOWS an in-scope variable
//! of a DIFFERENT sort must degrade to an ordinary undischarged obligation, not
//! ICE the compiler.
//!
//! The parameter `x: u64` reaches the in-process ay backend as the escaped
//! symbol `__trust_u_x` with sort Int. The `ensures forall x: bool, ...` binder
//! escapes to the SAME name (the namespace map is injective on source names,
//! applied to binders and occurrences alike) with sort Bool.
//! `translate_quantifier` (ay-bindings `execute_direct/translate.rs`) declared
//! its bound variables through the PANICKING `Solver::declare_const`, whose
//! collision refusal —
//!
//! ```text
//! invalid argument to declare_const: constant '__trust_u_x' is already
//! declared with sort Int, not Bool
//! ```
//!
//! is not an ay-classified panic reason, so it resumed through every unwind
//! boundary and aborted the crate with a full ICE report. The fix routes the
//! binder declaration through `try_declare_const`, so the collision arrives as
//! an `ExecuteError` and the backend degrades the obligation to Unknown; under
//! the advisory policy the crate then compiles with a warning.
//!
//! Requires the stage2 `trustc` toolchain (verify runs in the compiler) with
//! the first-party/ay pin carrying the `translate_quantifier` fix: against the
//! unfixed pin this exact file ICEs, and with `-Ztrust-verify=off` it compiles
//! cleanly, so the verify directives above are load-bearing.

pub fn shadowed_binder(x: u64) -> u64
    requires x > 0
    ensures forall x: bool, x || !x
{
    x
}

fn main() {}
