//@ ignore-test (RED ON PURPOSE — greening the blocking row provably greens a `*p` deref; see below)
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: -Ztrust-policy=memory-safe --crate-type=lib
//@ dont-check-compiler-stderr
//@ build-pass
//! A known panic-capable safe call whose body cannot be lowered is meant to be an
//! explicit, authenticated memory-safe assumption: visible and unproved, but the raw
//! compiler agreeing with Targo that this narrow row may conditionally compile.
//!
//! It does not, and after two refuted attempts and a third investigation the honest
//! disposition is that this fixture is a CAPABILITY ALARM, not a bug report against
//! the demotion. It is ignored rather than deleted so the target state stays
//! recorded, and ignored rather than left red so the suite is honest instead of
//! noisy. Three records back that, and all three must be read before it is touched:
//! commit `c93aabc77f`; the §"REFUTED …" sections of
//! reports/2026-08-20-r2-campaign-plan.md; and
//! reports/memory-safe-demote-is-unfixable-at-this-seam-2026-08-23.md.
//!
//! WHAT THE COMPILER ACTUALLY PRODUCES (measured on `trustc 1.99.0-dev
//! (8d592268f 2026-08-24)`, this exact file, `-Ztrust-verify-output=json`): TWO
//! obligations, not one.
//!
//! ```text
//! vc:…:assertion:0                  Assertion{"Call::unwrap::panic-freedom"}   failed
//! vc:…:assertion:panic-freedom:0    Assertion{"panic freedom: no assertion, …"} runtime_checked
//! ```
//!
//! Row 1 demotes exactly as intended — `rewrite_memory_safe_panic_refutation_rows`
//! turns it into `assumption:memory-safe-panic`. Row 2 is the blocker, and the error
//! says so: "effective transport rows: 2 total, 1 authenticated memory-safe
//! assumption(s)". Row 2 is the compiler-SYNTHESIZED whole-function panic-freedom
//! AGGREGATE (minted in `trust_verify.rs`, whole-fn span, no originating MIR block).
//! It reports `runtime_checked` only because `VcKind::Assertion::has_runtime_fallback`
//! is `true` — a per-KIND property.
//!
//! ATTEMPT 1 — widen the demotion to RUNTIME-CHECKED rows. REFUTED, commit
//! `c93aabc77f` and reports/2026-08-20-r2-campaign-plan.md §"REFUTED AND NOT LANDED".
//! `has_runtime_fallback` is a static per-kind answer, not evidence a check was
//! emitted; the leg also ran before the extern-call gate and manufactured
//! `others_all_proved`.
//!
//! ATTEMPT 2 — exclude bodies containing `TerminatorKind::Unreachable`. REFUTED with a
//! built counterexample, §"REFUTED A SECOND TIME" in the same report. `Call { target:
//! None }` emits a bare `unreachable` in the CALLER's frame with no `Unreachable`
//! terminator anywhere in the MIR, and the REQUIRED `LintAndRemoveUninhabited` pass
//! rewrites the caught form into the missed one. A MIR scan cannot establish "every
//! exit traps", because codegen decides some exits after `TrustVerify` has run.
//!
//! AND THE DECISIVE ONE, which subsumes both:
//! reports/memory-safe-demote-is-unfixable-at-this-seam-2026-08-23.md proves the
//! disposition rather than arguing it. Row 2 is BYTE-IDENTICAL, in every field any
//! gate reads, between this fixture and `app::read_any` — a crate with no `unsafe`
//! token anywhere that calls an `#[inline(always)]` `*p` deref out of a dependency
//! compiled `-Ztrust-verify=off` (which is how Targo compiles EVERY dependency unit,
//! per `trust_verify.rs`). `function_uses_unsafe` cannot see the inlined callee, so
//! row 2 is today the single load-bearing fail-closed row keeping that build red.
//! **Any rule that demotes row 2 for this fixture demotes it for that exploit**, and
//! the fact that would separate them — *was the bundled callee independently
//! verified?* — is not in the transport rows the gate reads. Read that report before
//! touching anything here.
//!
//! The second refutation named the only two acceptable shapes for a third attempt:
//! (i) derive the fact WHERE CODEGEN MAKES IT, or (ii) narrow the demotion to rows
//! carrying positive evidence a check was EMITTED. BOTH WERE INVESTIGATED AND BOTH
//! ANSWER "NO CHECK" FOR ROW 2 — which is why this file is ignored and not fixed:
//!
//! * (ii) is CONSTRUCTIBLE but INAPPLICABLE. The tree does hold exactly one per-row
//!   "a check was emitted" oracle: `OverflowCheckOrigins` (trust_verify.rs), built from
//!   `trust_vcgen::overflow_vc_block_origins` and re-confirmed against the LIVE
//!   `TerminatorKind::Assert` by `elide_kernel_certified_checks`. It is filtered to
//!   `VcKind::ArithmeticOverflow { Add | Sub | Mul }`. Generalizing it to every
//!   physical Assert still answers NO here, because this function HAS NO ASSERT.
//!   Measured optimized MIR of `unwrap_opt`:
//!
//!   ```text
//!   bb0: { _0 = Option::<u32>::unwrap(copy _1) -> [return: bb1, unwind continue]; }
//!   bb1: { return; }
//!   ```
//!
//!   Zero `Assert` terminators. The panic branch this fixture wants credit for is
//!   emitted in the CALLEE's frame, in another crate, and row 2 is a synthetic
//!   whole-function aggregate for which no physical check exists or can exist.
//!   The other per-row evidence field, `TransportObligationResult::monitor`
//!   (`TransportMonitorEvidence`), is about kernel-certified runtime decision
//!   procedures for CONTRACT clauses, never rustc panic branches; its honest value
//!   for row 2 is `Unmonitored`, which the type's own doc says "must never be
//!   interpreted as a successful check".
//!
//!   The `overflow_guard_targets`-shaped sets in trust-vcgen
//!   (`v2_overflow_guard_targets`, which is `#[cfg(test)]`, and its live sibling
//!   `v2_sole_bounds_assert_by_target`) are NOT this oracle either, in either
//!   direction: they bind an `Assert` to a row in order to SUPPRESS the row during
//!   generation, and a suppressed row is one the verifier never grades — the
//!   opposite end of the pipeline from grading a row on evidence its check
//!   survived. Neither says anything about a synthesized whole-function aggregate.
//!
//! * (i) is NOT REACHABLE in this slice. This verdict is emitted from inside
//!   `TrustVerify` during `optimized_mir` — it is a fatal diagnostic raised long
//!   before codegen runs, and a metadata-only compile never reaches codegen at all,
//!   so a codegen-derived fact would make the memory-safe gate depend on the emit
//!   mode. `rustc_codegen_ssa` has exactly one Trust seam
//!   (`mir/mod.rs`, the per-instance trust-ir flip) and it SELECTS a body; nothing
//!   there records "a check was emitted for obligation X", and there is no channel
//!   back into a verdict already issued.
//!
//!   That same seam also retires, independently, the premise attempt 2 was built on
//!   ("TrustVerify is the last pass of the optimized pipeline, so its `Body` is what
//!   `rustc_codegen_ssa` lowers"). For a GENERIC body the codegen root can be MIR
//!   re-derived from the trust-ir Module (`tcx.trust_instance_flip_body`), which is
//!   not the `optimized_mir` body `TrustVerify` scanned at all.
//!
//! So the correct oracle answers NO for row 2, and any demotion that admits it is
//! asserting a monitor that was never emitted. A red fixture with a known root cause
//! beats a green build resting on a false safety claim.
//!
//! WHAT UN-IGNORES THIS FILE — a CAPABILITY, never a widening, and it is the SAME
//! capability the indistinguishability proof names. Row 2 is unproved because
//! `Call::unwrap::panic-freedom` is unproved, and the gate cannot tell an unproved
//! TOTAL-and-verified callee from an unverified one. Give it that fact — a real
//! interprocedural callee panic-freedom summary, an authenticated callee-totality
//! assumption on the existing `assumed_total_callee` seam, or the dependency-
//! verification status of the bundled callee — and row 2 has nothing left to be
//! unproved about while `read_any` stays red, with no edit to any demotion leg.
//! Delete the `ignore-test` line in the same commit that lands it. If this file is
//! still red then, the capability did not take — and it, not this file, is wrong.
//!
//! DO NOT "fix" this by admitting `runtime_checked` rows, by scanning the body for
//! `TerminatorKind::Unreachable`, or by folding the aggregate into its constituents
//! (the aggregate also covers hazards that mint NO constituent row: drop glue,
//! unmodeled diverging calls, post-mono-unreached blocks). The adversarial control for
//! the third of those is `reject_diverging_call_gap.rs` in this directory — the
//! `std::process::exit` body from the second refutation, which MUST stay refused.
pub fn unwrap_opt(o: Option<u32>) -> u32 {
    //~^ WARN Trust Level 0 safety verification incomplete for `demote_explicit_lowering_gap::unwrap_opt`
    o.unwrap()
}
