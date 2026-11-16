//@ revisions: force_o0_certify force_o0_advisory
//@ revisions: map_o0
//@ revisions: force_guarded_default force_guarded_strict force_guarded_certify
//@ revisions: force_twin_o0_certify
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: requires_callee_inlinable_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ rustc-env:TRUST_MIR_INLINE_TRACE=1
//@[force_o0_certify] compile-flags: -Ztrust-policy=certify
//@[force_o0_advisory] compile-flags: -Ztrust-policy=advisory
//@[force_guarded_strict] compile-flags: -Ztrust-policy=strict
//@[force_guarded_certify] compile-flags: -Ztrust-policy=certify
//@[force_twin_o0_certify] compile-flags: -Ztrust-policy=certify
//@[force_o0_certify] check-fail
//@[force_o0_advisory] check-pass
//@[force_guarded_default] check-fail
//@[force_guarded_strict] check-fail
//@[force_guarded_certify] check-fail
//@[force_twin_o0_certify] check-pass
//@[map_o0] check-fail
//@[force_o0_certify] forbid-output: inlined `requires_callee_erased_by_mir_inliner::add1_forced`
//@[force_o0_advisory] forbid-output: [TRUST_MIR_INLINE] kept call
//@[force_guarded_default] forbid-output: [TRUST_MIR_INLINE] inlined
//@[force_guarded_default] forbid-output: [precond] FAILED
//@[force_guarded_strict] forbid-output: [TRUST_MIR_INLINE] inlined
//@[force_guarded_strict] forbid-output: [precond] FAILED
//@[force_guarded_certify] forbid-output: [TRUST_MIR_INLINE] inlined
//@[force_guarded_certify] forbid-output: [precond] FAILED
//@[force_twin_o0_certify] forbid-output: [TRUST_MIR_INLINE] kept call
//@[map_o0] forbid-output: [TRUST_MIR_INLINE]
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Residual L3 of the fn-pointer `requires` fix (docs/KNOWN_HAZARDS.md, "FIX
//! PREPARED 2026-09-30 … — under an explicit `-Zmir-opt-level=2` …"): the MIR
//! inliner ERASED the call that is the only place a `requires` is charged, and
//! copied in the callee's `optimized_mir`, whose overflow check its own
//! verification had already elided under that `requires`.
//!
//! `add1` is verified UNDER `requires x < 100` (the overflow row is kernel-certified
//! with the clause as the entry hypothesis, and the check is elided). Each caller
//! below reaches it with an unconstrained `y`.
//!
//! BEFORE (a stage 1 of `fbc6068e3`, measured 2026-09-30 by compiling each revision
//! as below, without the trace): every check-fail revision except `map_o0` built
//! exit 0 — `certify`, the default policy and memory-safe alike — with NO row for
//! `f` (its JSON is one `no_obligations` row): at `-Copt-level=3 -Zmir-opt-level=2`
//! `f`'s MIR is `AddWithOverflow(copy _1, const 1_u32)` under
//! `scope (inlined add1)`, with no `Call` for the direct-call lane, no reified
//! constant or callable type argument for the value-use gate, and no `Assert`.
//! `map_o3_certify`'s library, linked into a verify-off `main`, RETURNED
//! `f(u32::MAX) = Some(0)`; `let_o3_certify`'s and `identity_o3_certify`'s returned
//! 0 (the witness, `requires_callee_erased_by_mir_inliner_really_overflows.rs`, is
//! the build that keeps the check and panics). `closure_o3_certify` is the closure
//! the value-use gate's own note recommends: the closure's `optimized_mir` inlined
//! `add1` first. `force_o0_certify` and `force_o0_advisory` need no flag at all:
//! `ForceInline` runs at every opt-level (both built exit 0, advisory with no
//! warning about the clause). `map_level0_inline_certify` also built exit 0.
//! `map_o0` (no inliner in a verifying session at `-O0`, ruling R1) was refused by
//! the gate with the `requires` note; the twins and `guarded_o3_certify` built
//! exit 0.
//!
//! AFTER (predicted — no stage 1 with the fix was built for this commit; the
//! verdicts were MEASURED on the same stage 1 with `#[inline(never)]` on the callee,
//! or `-Zinline-mir=no` for the `dep_direct` shape, standing in for the rule, which
//! makes the inliner decline the same callee at the same point): in a verifying
//! session the inliner keeps a call whose callee owes its caller a `requires`
//! (`trust_verify/requires_callee_inlining.rs`). What wraps the call is still
//! inlined, so each shape's `f` holds `add1(move _1)` and is refused by the
//! direct-call lane's `[precond] FAILED` (counterexample `y = 100`), exactly as at
//! `-O0`; memory-safe refuses the same row. `dep_map_o3` was measured a second way,
//! with the aux's `#[inline]` MIR exported as here: `f` written as the match the
//! inlined `map` leaves (`Some(x) => Some(dep::add1(x))`) under `-Zinline-mir=no`
//! was refused by the same `[precond] FAILED`. `map_level0_inline_certify` is the
//! one shape the rule keeps without a `[precond]` row: at `-Zmir-opt-level=0`
//! `RemoveZsts` does not run, so the kept call is `move _8(..)` through a fn-item
//! local, which the direct-call lane does not charge, and the lowering refuses it as
//! `Call(indirect)` (fail-closed; MEASURED with the stand-in). `force_o0_certify`
//! gets `ForceInline`'s own "could not be inlined" error, with the Trust reason;
//! `force_o0_advisory` is still inlined, since advisory may not fail a build over a
//! Trust rule, and warns that the call is not charged for the clause (both
//! predicted only: `#[rustc_force_inline]` has no stand-in).
//!
//! MERGED onto main (integ/stage1-batch4, 2026-10-02), which landed the same fix as
//! W5 (4d80508166; `w5_requires_callee_not_mir_inlined.rs`): W5 declines the callee
//! in `inline::resolve_callsite`, before this rule, silently and under every
//! policy. The kept-call trace is printed at W5's sites too, so every non-force pin
//! is unchanged.
//!
//! W5's silent decline ICEd on a `#[rustc_force_inline]` callee (2026-10-02): the
//! forced call was kept with no `ForceInline` error, and `validate.rs` panicked
//! ("`#[rustc_force_inline]`-annotated function not inlined") whenever the caller's
//! verification raised no error first. MEASURED on a stage 1 of integ/stage1-batch4
//! with `-Ztrust-verify=on --crate-type lib --emit=metadata`: the guarded caller
//! (`force_guarded_*`) exited 101 under the default policy, strict and certify, and
//! so did `force_o0_advisory`. FIX: W5 lets a forced callee through to this rule,
//! which decides it as it did before the merge. Expected, not run (no stage 1 of
//! the fix was built):
//! * `force_guarded_{default,strict,certify}`: `ForceInline`'s "could not be
//!   inlined" error, with the Trust reason, and nothing else. The kept call is
//!   charged and PROVED (as in `guarded_o3_certify`), so no `[precond] FAILED`.
//! * `force_o0_certify`: the same `ForceInline` error, then `[precond] FAILED`. The
//!   kept call is the same `Call` W5 kept, and `TrustVerify` still runs after the
//!   `ForceInline` error.
//! * `force_o0_advisory`: inlined, with the advisory warning that this call is not
//!   charged for the clause. No kept-call line.
//! * `force_twin_o0_certify`: a requires-free `#[rustc_force_inline]` callee is
//!   still inlined, and the build passes.
//!
//! PINNED, not just claimed, under `TRUST_MIR_INLINE_TRACE=1`: the rule prints
//! `[TRUST_MIR_INLINE] kept call to <callee>` when it declines, and every inline of
//! a verifying session prints `[TRUST_MIR_INLINE] inlined <callee>`, each item
//! spelled by `trust_mir_extract::safe_def_path_str` (crate-prefixed, and a
//! dependency by its crate name, not the `dep` alias). Each refused
//! revision requires the kept-call line (a `~? RAW` annotation) and forbids an
//! inlined line for its callee. `guarded_o3_certify` requires the kept-call line
//! and still builds under certify: the kept call is charged and PROVED, so no
//! correct caller is lost. The requires-free twins (`half`) forbid any kept-call line
//! and require `half`'s inlined line: the rule costs them nothing, and they are
//! still inlined (`twin_map_o3_certify` builds only because `Option::map` is
//! inlined too — at `-O0` its generic-absent-callee row refuses it). `map_o0`
//! forbids every trace line: at `-O0` a verifying session runs no MIR inliner.

#![cfg_attr(
    any(
        force_o0_certify,
        force_o0_advisory,
        force_guarded_default,
        force_guarded_strict,
        force_guarded_certify,
        force_twin_o0_certify
    ),
    feature(rustc_attrs),
    allow(internal_features)
)]

// Not in the `dep_*` revisions: under memory-safe a local `requires` function is
// refused by its own `assumption:requires` row, which would mask `f`'s verdict.
pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}

#[cfg(map_o0)]
pub fn f(y: u32) -> Option<u32> {
    //[map_o0]~^ ERROR Trust strict verification failed for `requires_callee_erased_by_mir_inliner::f`
    //[map_o0]~| NOTE `add1` carries a `requires` its callers owe
    Some(y).map(add1)
}

#[cfg(any(
    force_o0_certify,
    force_o0_advisory,
    force_guarded_default,
    force_guarded_strict,
    force_guarded_certify
))]
#[rustc_force_inline]
pub fn add1_forced(x: u32) -> u32
    requires x < 100
{
    x + 1
}
#[cfg(any(force_o0_certify, force_o0_advisory))]
pub fn f(y: u32) -> u32 {
    //[force_o0_certify]~^ ERROR Trust strict verification failed for `requires_callee_erased_by_mir_inliner::f`
    //[force_o0_certify]~| NOTE [precond] FAILED
    add1_forced(y)
    //[force_o0_certify]~^ ERROR `add1_forced` could not be inlined into `f` but is required to be inlined
    //[force_o0_certify]~| NOTE could not be inlined due to: the callee owes its caller a Trust `requires`
    //[force_o0_advisory]~^^^ WARN `#[rustc_force_inline]` inlines `requires_callee_erased_by_mir_inliner::add1_forced`, which owes its caller a `requires`, so this call is not charged for it
}

// The ICE repro: the guarded call is charged and proved, so before the W5 exemption
// no verification error preceded the validator's "not inlined" panic.
#[cfg(any(force_guarded_default, force_guarded_strict, force_guarded_certify))]
pub fn f(y: u32) -> u32 {
    if y < 100 { add1_forced(y) } else { 0 }
    //[force_guarded_default,force_guarded_strict,force_guarded_certify]~^ ERROR `add1_forced` could not be inlined into `f` but is required to be inlined
    //[force_guarded_default,force_guarded_strict,force_guarded_certify]~| NOTE could not be inlined due to: the callee owes its caller a Trust `requires`
}

#[cfg(force_twin_o0_certify)]
#[rustc_force_inline]
pub fn half_forced(x: u32) -> u32 {
    x / 2
}
#[cfg(force_twin_o0_certify)]
pub fn f(y: u32) -> u32 {
    half_forced(y)
}

//[force_o0_certify,force_guarded_default,force_guarded_strict,force_guarded_certify]~? RAW [TRUST_MIR_INLINE] kept call to `requires_callee_erased_by_mir_inliner::add1_forced`
//[force_o0_advisory]~? RAW [TRUST_MIR_INLINE] inlined `requires_callee_erased_by_mir_inliner::add1_forced`
//[force_twin_o0_certify]~? RAW [TRUST_MIR_INLINE] inlined `requires_callee_erased_by_mir_inliner::half_forced`
