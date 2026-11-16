//@ build-pass
//@ compile-flags: -Ztrust-verify=off -Ztrust-ir-lower=on -Ztrust-ir-lower-mutate-finalization
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE

//! **`-Ztrust-verify=off` is the master off-switch: a producer-side invalid
//! module must not kill a lane that claims nothing.**
//!
//! `advisory_invalid_module_is_a_warning.rs` established that
//! `trust_ir_crate_finalize`'s `semantic finalization failed` is a loss of
//! COVERAGE — an invalid module proves nothing, so nothing unproved can be
//! smuggled through it — and routed it as a warning under `advisory`. But the
//! routing read `trust_policy.is_advisory()` ALONE, so the off lane, which runs
//! the direct frontend only as a diagnostic opt-in (`-Ztrust-ir-lower=on`),
//! inherited the DEFAULT policy's fatal. No `-Ztrust-policy` is passed here on
//! purpose: the default is `strict`, and the off-switch has to win over it.
//!
//! MEASURED 2026-09-22: ay's everyday lane (`targo --unverified`, its config
//! putting `-Ztrust-ir-lower=strict` on every unit) died in `autocfg 1.5.1` and
//! `cc 1.2.64` on `StructLayoutInconsistent { reason: "fields overlap" }` — a
//! producer defect in two registry crates, on a compile that verifies nothing.
//!
//! The routing now consults `Session::trust_proof_claimed` (verification on AND
//! a fail-closed policy), pinned pure in `rustc_session`
//! (`proof_claim_requires_verification_and_a_fail_closed_policy`). The
//! manufactured refusal comes from the same TEST-ONLY knob the advisory fixture
//! uses, so this file does not ride a live producer gap either.
//! `advisory_invalid_module_strict_control.rs` remains the control that the
//! fail-closed lanes under verification still refuse.

fn main() {}
