//@ revisions: assume assume_certify callsite callsite_certify callsite_nan signzero
//@ revisions: signzero_certify ensures ensures_certify ensures_cost
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[assume_certify] compile-flags: -Ztrust-policy=certify
//@[callsite_certify] compile-flags: -Ztrust-policy=certify
//@[signzero_certify] compile-flags: -Ztrust-policy=certify
//@[ensures_certify] compile-flags: -Ztrust-policy=certify
//@[assume] check-pass
//@[assume_certify] check-pass
//@[callsite] check-fail
//@[callsite_certify] check-fail
//@[callsite_nan] check-fail
//@[signzero] check-pass
//@[signzero_certify] check-fail
//@[ensures] check-fail
//@[ensures_certify] check-fail
//@[ensures_cost] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! A contract `==` between floats is Rust `PartialEq`: IEEE equality, under
//! which `NaN == NaN` is false and `0.0 == -0.0` is true
//! (SPEC-FLOAT-EQ-STRUCTURAL-1, docs/KNOWN_HAZARDS.md).
//!
//! The spec parser spelled every `==` as `Formula::Eq`, which every solver lane
//! reads as SMT-LIB `=`: structural, so `NaN = NaN` holds and `+0 = -0` fails.
//! Four consequences, one per case below:
//!
//! * `callsite`: `requires x == y` at a call. The callee's `x`/`y` are replaced
//!   by the actuals' bit patterns, so the obligation became bit equality.
//!   `c_xy(f64::NAN, f64::NAN)` was PROVED (native trust_mc typed CHC/PDR, a
//!   `PdrInvariant`), and the binary broke the clause
//!   (`spec_float_eq_ieee_run.rs`); `c_xy(0.0, -0.0)`, which the clause admits,
//!   was REFUTED.
//! * `assume`: the assumption gate evaluated `Eq` only over bools and integers,
//!   so `requires x == 1.0` had "no satisfiable witness" and the gate dropped the
//!   WHOLE precondition set, `requires i < 4` included: correct code was refuted
//!   with `i = 4`.
//! * `signzero`: the trap the obvious gate fix would spring. Assumed as
//!   structural `=`, `requires x == 0.0` excludes `-0.0`, which Rust's `==`
//!   admits, and would prove the `is_sign_negative()` branch into `a[10]`
//!   unreachable.
//! * `ensures`: the most severe reach of the lie, and the one `certify`
//!   accepted. A float postcondition `==` was PROVED by the same lane (native
//!   trust_mc typed CHC/PDR, a `PdrInvariant`), so `ensures result == result` on
//!   an `f64` identity, and on a body that returns `f64::NAN`, was a proved row
//!   and the crate built rc 0 under every policy, `certify` included. For
//!   `result = NaN` the clause is false; `spec_float_eq_ieee_ensures_run.rs` is
//!   the program that verdict certified. `ensures_cost` pins what the fix costs on
//!   this path: the structural reading also proved a TRUE float postcondition
//!   (the tautology `result == result || result != result`) and correctly refuted
//!   `result != result` on an identity; both are declined now.
//!
//! BEFORE (`scratchpad/stage1-w18b`, the stage 1 of 4ccd862830; each revision's
//! flags plus `--cfg <revision> -Zui-testing -Zdeduplicate-diagnostics=no -A unused
//! --emit=metadata`, measured 2026-10-06):
//! * `assume`/`assume_certify`: exit 1. `mix_eq` and `mix_ne` each get the
//!   "not assumed ... no satisfiable witness" WARN and two ERRORs
//!   (`[bounds] FAILED`, counterexample `i = 4`).
//! * `callsite`: exit 1, but `k_xy_nan` and `k_xy_33` have their precondition
//!   PROVED (`k_xy_nan` reports only the runtime-checked panic-freedom WARNs),
//!   and `k_xy_zeros`/`k_xy_12` are `[precond] FAILED`.
//!   `callsite_certify`: the same rows.
//! * `callsite_nan` (`c_xy` and `k_xy_nan` alone, default policy): exit 0 — the
//!   crate was ACCEPTED with a call that breaks its callee's `requires`.
//! * `signzero`: exit 1 — the vacuity WARN, then `[bounds] FAILED` and two
//!   ERRORs (the refutation is right only by accident: the clause was dropped).
//!   `signzero_certify`: the same.
//! * `ensures`/`ensures_certify` (added 2026-10-10 after the wave-20 review; the
//!   same flags, measured on that stage 1 and on main's, `912bbdf300`): exit 0
//!   under both policies, every function `2 proved, 0 failed, 0 unknown, 0 timed
//!   out, 0 runtime-checked out of 2`; both postcondition rows (`obligation:…` from
//!   trust-exact-source-clause-discharge, `vc:…` from trust-full-verifier) proved.
//!   `ensures_cost`: exit 1; `e_taut`'s two rows proved, `e_ne_self`'s two rows
//!   FAILED (`[postcond] FAILED`, trust-full-verifier).
//!
//! AFTER (predicted, not built). Every producer of a contract formula spells a
//! float `==` as IEEE `FpEq`; the gate evaluates it in f64; no consumer proves it
//! structurally. The annotations were derived on the BEFORE compiler from a twin
//! of this file in which each float `==` clause is replaced by an IEEE-equivalent
//! ordering clause the BEFORE compiler already reads correctly — `x == 1.0` by
//! `x >= 1.0 && x <= 1.0`, `x != 0.0` by `!(x >= 0.0 && x <= 0.0)`, `x == y` by
//! `x <= y && y <= x`, `x == 0.0` by `x >= 0.0 && x <= 0.0` (each pair admits the
//! same f64 values) — with the same flags:
//! * `assume`/`assume_certify`: exit 0, nothing reported. The clauses are
//!   assumed, `i < 4` with them, and every `[bounds]` row proves.
//! * `callsite`/`callsite_certify`/`callsite_nan`: every call's precondition row is
//!   `[precond] UNKNOWN` — neither the `NaN` lie nor the `-0.0` refutation. The
//!   callsite obligation substitutes the actuals' bit patterns into an IEEE
//!   comparison, which no lane models, so it is declined; that the correct calls
//!   `k_xy_zeros` and `k_xy_33` are now refused rather than decided is the
//!   recorded capability cost (docs/DECISION_QUEUE.md SPEC-FLOAT-EQ-STRUCTURAL-1).
//!   Under the default policy an unmonitored unknown precondition fails the
//!   build, so `callsite_nan` now exits 1.
//! * `signzero`: exit 0 with two WARNs: the clause is assumed (no vacuity WARN)
//!   and the bounds row stays runtime-checked — `-0.0 == 0.0`, so the negative
//!   branch is NOT proved unreachable. `signzero_certify`: the same two rows as
//!   ERRORs.
//! Checked the way compiletest checks (expected annotations against the JSON
//! diagnostics), the twin matches every revision's annotations and this file fails
//! every revision's on the BEFORE compiler.
//! * `ensures`/`ensures_certify`/`ensures_cost` (MEASURED, not predicted: the
//!   wave-20 stage 1 `8f3584d2fe`): exit 1. Each function reports `0 proved, 0
//!   failed, 2 unknown` with `[postcond] UNKNOWN` from both lanes and the ERROR
//!   `Trust strict verification failed`. No row is refuted: the solver's NaN model
//!   of the encoded VC is withheld, as an unattested refutation always is, so the
//!   verdict on the false clauses is "not proved", not "false".

#[cfg(any(assume, assume_certify))]
pub mod assume_case {
    // Control: the integer clause alone.
    pub fn only_i(x: f64, i: usize, a: &[u8; 4]) -> u8
        requires i < 4
    {
        if x > 0.0 { a[i] } else { a[i] }
    }

    // `x == 1.0` has the witness `x = 1.0`; dropping it took `i < 4` with it.
    pub fn mix_eq(x: f64, i: usize, a: &[u8; 4]) -> u8
        requires x == 1.0
        requires i < 4
    {
        if x > 0.0 { a[i] } else { a[i] }
    }

    // Control: the same values, spelled as an ordering.
    pub fn mix_rng(x: f64, i: usize, a: &[u8; 4]) -> u8
        requires x >= 1.0 && x <= 1.0
        requires i < 4
    {
        if x > 0.0 { a[i] } else { a[i] }
    }

    // `x != 0.0` is the negation of IEEE equality; `x = 1.0` satisfies it.
    pub fn mix_ne(x: f64, i: usize, a: &[u8; 4]) -> u8
        requires x != 0.0
        requires i < 4
    {
        if x > 0.0 { a[i] } else { a[i] }
    }

    // Control: two float parameters. Admitted before (as an integer equation)
    // and after (as IEEE equality, witness `x = y = 0.0`).
    pub fn mix_xy(x: f64, y: f64, i: usize, a: &[u8; 4]) -> u8
        requires x == y
        requires i < 4
    {
        if x > y { a[i] } else { a[i] }
    }
}

#[cfg(any(callsite, callsite_certify, callsite_nan))]
pub mod callsite_case {
    pub fn c_xy(x: f64, y: f64) -> f64
        requires x == y
    {
        x
    }

    // Rust: `NaN == NaN` is false, so this call VIOLATES the clause. It must not
    // be proved. Alone (`callsite_nan`) it was the whole lie: the crate was
    // accepted with the precondition row proved.
    pub fn k_xy_nan() -> f64 {
        //[callsite,callsite_nan]~^ WARN Trust Level 0 safety verification incomplete
        //[callsite,callsite_nan]~| ERROR Trust strict verification failed
        //[callsite_certify]~^^^ ERROR Trust Level 0 safety verification incomplete
        //[callsite_certify]~| ERROR Trust strict verification failed
        //[callsite,callsite_certify,callsite_nan]~| NOTE [precond] UNKNOWN
        c_xy(f64::NAN, f64::NAN)
    }

    // Rust: `0.0 == -0.0` is true, so this call SATISFIES the clause. It must not
    // be refuted.
    #[cfg(any(callsite, callsite_certify))]
    pub fn k_xy_zeros() -> f64 {
        //[callsite]~^ WARN Trust Level 0 safety verification incomplete
        //[callsite]~| ERROR Trust strict verification failed
        //[callsite_certify]~^^^ ERROR Trust Level 0 safety verification incomplete
        //[callsite_certify]~| ERROR Trust strict verification failed
        //[callsite,callsite_certify]~| NOTE [precond] UNKNOWN
        c_xy(0.0, -0.0)
    }

    // Controls: `1.0 == 2.0` is false and `3.0 == 3.0` true, under either
    // reading. Both are declined now, as the ordering spelling of the same
    // clause already was.
    #[cfg(any(callsite, callsite_certify))]
    pub fn k_xy_12() -> f64 {
        //[callsite]~^ WARN Trust Level 0 safety verification incomplete
        //[callsite]~| ERROR Trust strict verification failed
        //[callsite_certify]~^^^ ERROR Trust Level 0 safety verification incomplete
        //[callsite_certify]~| ERROR Trust strict verification failed
        //[callsite,callsite_certify]~| NOTE [precond] UNKNOWN
        c_xy(1.0, 2.0)
    }

    #[cfg(any(callsite, callsite_certify))]
    pub fn k_xy_33() -> f64 {
        //[callsite]~^ WARN Trust Level 0 safety verification incomplete
        //[callsite]~| ERROR Trust strict verification failed
        //[callsite_certify]~^^^ ERROR Trust Level 0 safety verification incomplete
        //[callsite_certify]~| ERROR Trust strict verification failed
        //[callsite,callsite_certify]~| NOTE [precond] UNKNOWN
        c_xy(3.0, 3.0)
    }
}

#[cfg(any(signzero, signzero_certify))]
pub mod signzero_case {
    // `-0.0 == 0.0`, and `-0.0` is sign-negative: `a[10]` is reachable under the
    // clause. Assumed, the clause must not prove that branch dead.
    pub fn r_eq0(x: f64, a: &[u8; 4]) -> u8
        requires x == 0.0
    {
        //[signzero]~^^^ WARN Trust Level 0 safety verification incomplete
        //[signzero]~| WARN Trust verification advisory
        //[signzero_certify]~^^^^^ ERROR Trust Level 0 safety verification incomplete
        //[signzero_certify]~| ERROR Trust strict verification failed
        //[signzero,signzero_certify]~| NOTE [bounds] runtime-checked
        let i: usize = if x.is_sign_negative() { 10 } else { 0 };
        a[i]
    }
}

#[cfg(any(ensures, ensures_certify))]
pub mod ensures_case {
    // `e(f64::NAN)` returns NaN, and `NaN == NaN` is false: the clause can fail.
    // It was PROVED before the fix, under `certify` too.
    pub fn e(x: f64) -> f64
        ensures result == result
    {
        //[ensures,ensures_certify]~^^^ ERROR Trust strict verification failed
        //[ensures,ensures_certify]~| NOTE [postcond] UNKNOWN
        x
    }

    // The body returns NaN on every call, so the clause never holds. Proved before.
    pub fn e_nan() -> f64
        ensures result == result
    {
        //[ensures,ensures_certify]~^^^ ERROR Trust strict verification failed
        //[ensures,ensures_certify]~| NOTE [postcond] UNKNOWN
        f64::NAN
    }

    // The `f32` twin.
    pub fn e32(x: f32) -> f32
        ensures result == result
    {
        //[ensures,ensures_certify]~^^^ ERROR Trust strict verification failed
        //[ensures,ensures_certify]~| NOTE [postcond] UNKNOWN
        x
    }

    // The same clause through `!=`, which is the negation of IEEE `==`.
    pub fn e_ne(x: f64) -> f64
        ensures !(result != result)
    {
        //[ensures,ensures_certify]~^^^ ERROR Trust strict verification failed
        //[ensures,ensures_certify]~| NOTE [postcond] UNKNOWN
        x
    }
}

#[cfg(ensures_cost)]
pub mod ensures_cost_case {
    // TRUE under either reading (a propositional tautology): proved before the fix,
    // declined now. The recorded cost.
    pub fn e_taut(x: f64) -> f64
        ensures result == result || result != result
    {
        //[ensures_cost]~^^^ ERROR Trust strict verification failed
        //[ensures_cost]~| NOTE [postcond] UNKNOWN
        x
    }

    // FALSE for every non-NaN result, and refuted before the fix (structurally,
    // `r != r` never holds). Declined now: still refused, no longer refuted.
    pub fn e_ne_self(x: f64) -> f64
        ensures result != result
    {
        //[ensures_cost]~^^^ ERROR Trust strict verification failed
        //[ensures_cost]~| NOTE [postcond] UNKNOWN
        x
    }
}
