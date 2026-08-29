//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ check-fail
//! ADVERSARIAL CONTROL for the memory-safe demotion. This body MUST stay refused.
//!
//! It is, verbatim, the counterexample that refuted the second attempt at greening
//! `demote_explicit_lowering_gap.rs` (reports/2026-08-20-r2-campaign-plan.md,
//! §"REFUTED A SECOND TIME"), pinned as a fixture so a fourth attempt cannot
//! silently re-open the hole it found.
//!
//! There is no `unsafe` here, so `memory_safe_demotion_applies` holds and every
//! demotion leg is live. And yet the guarded exit is a DIVERGING CALL: MIR lowers
//! `std::process::exit` to `Call { target: None }`, which `rustc_codegen_ssa`
//! finishes with a bare `unreachable` in THIS function's own frame (`mir/block.rs`,
//! the `else { bx.unreachable(); }` after the call) — with ZERO
//! `TerminatorKind::Unreachable` anywhere in the MIR to scan for. The REQUIRED
//! `LintAndRemoveUninhabited` pass additionally rewrites `Call { target: Some(bb) }`
//! into exactly this form and lets the `Unreachable` successor be DCE'd, so the
//! marker a body scan would hunt is erased ~500 passes before `TrustVerify` looks.
//!
//! MEASURED on `trustc 1.99.0-dev (8d592268f 2026-08-24)`, three rows:
//!
//! ```text
//! …:bounds_check:0       (kernel-certified)                        proved
//! …:arithmetic_safety:1  ArithmeticOverflow                        failed  -> demotes
//! …:custom:2             UnsupportedMir{"Call::std::process::exit"} unknown -> REFUSES
//! ```
//!
//! The `v[i] + 1` rows are deliberately kept: one proves, one is an ordinary
//! memory-safe panic that DOES demote, so this fixture also pins that a demotable
//! row cannot carry the whole function. What refuses the build is row 3 — an
//! unmodeled diverging call, which `vc_kind_is_memory_safe_panic` correctly declines
//! (not a known-panicking call, not an `ArithmeticSafety`/`BoundsCheck` round-trip).
//! An unmodeled diverging call is not a safe panic, and that is the whole point:
//! this is the hazard class that mints no demotable constituent row of its own.
//!
//! IF THIS FILE EVER GOES GREEN, STOP. It does not matter that the refusal is
//! delivered today by the native lowering declining the opaque
//! `Call::std::process::exit` terminator rather than by a demotion gate — a change
//! that teaches the bridge to lower diverging calls must keep the REFUSAL, and this
//! fixture is what forces a human to re-derive why. The rule it guards is
//! unconditional: a row whose body can reach a bare `unreachable` may never pass as
//! monitored.
pub fn pick(v: &[u32], i: usize) -> u32 {
    //~^ ERROR Trust memory-safe verification failed for `reject_diverging_call_gap::pick`
    //~| WARN Trust Level 0 safety verification incomplete for `reject_diverging_call_gap::pick`
    if i >= v.len() {
        std::process::exit(1);
    }
    v[i] + 1
}
