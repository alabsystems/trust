//@ needs-trust-verify
//@ revisions: no_census census
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[no_census] rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@[no_census] check-fail
//@[census] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! THE SOUNDNESS HALF of `float_exact_intrinsic_methods_are_panic_free.rs`.
//!
//! These are panic-free, so it would be easy to read their refusal as the same
//! gap the exact methods had. It is not. The `@trust-rustc-intrinsic::` marker
//! is read by the facet gates (`trust-vcgen`'s `facets.rs`, `trust-types`'
//! `facet_inference.rs`) as a claim that the callee is pure, total, panic-free
//! AND DETERMINISTIC. `library/std/src/num/f64.rs` documents these as failing
//! the last one in its own words: "The precision of this function is
//! non-deterministic. This means it varies by platform, Rust version, and can
//! even differ within the same execution from one invocation to the next."
//!
//! `powi` is in that list too, which is the trap — it looks like an exact
//! integer-exponent power and is not. `sqrt` and `mul_add` are pointedly NOT in
//! it, because IEEE-754 requires both to be correctly rounded, which is why
//! they are admitted next door.
//!
//! Marking these with the deterministic marker would be a false determinism
//! claim, so they never take it. The `no_census` revision used to FAIL for that
//! reason: with the sysroot panic census withheld (`TRUST_NO_SYSROOT_CENSUS=1`),
//! nothing but the intrinsic marker could discharge these calls.
//!
//! Trust (std-call-summaries P2, 2026-10-11): the revision now PASSES, and not
//! because anyone marked them deterministic. The intrinsics inside the wrappers'
//! bundled bodies (`expf64`, `powif64`) now take the separate PANIC-FREEDOM-ONLY
//! stamp `@trust-rustc-panic-free-intrinsic::` (`tcx_marked_panic_free_intrinsic_path`),
//! which the facet and determinism gates never read and which grants no value
//! fact. This revision is STILL an end-to-end tripwire for the deterministic
//! marker: the bridge's deterministic list holds none of the panic-freedom-only
//! names (pinned by trust-ir-bridge's
//! `saturating_intrinsics_are_total_but_unchecked_ones_are_not`), so if the
//! extractor stamped `expf64`/`powif64` with `@trust-rustc-intrinsic::` the calls
//! would take the absent-callee arm again and this check-pass revision goes red
//! (mutation-checked on a stage 1, std-call-summaries P2 review). The marker is
//! also named directly at the unit level: trust-mir-extract's
//! `exact_ieee754_intrinsics_are_marked_and_the_inexact_siblings_are_not` (these
//! names stay off the deterministic marker) and the facet tests
//! `a_panic_free_only_intrinsic_stamp_grants_no_facet` (trust-types) and
//! `panic_free_only_intrinsic_stamp_grants_no_facet` (trust-vcgen). MEASURED: the
//! `no_census` command exits 1 on the stage 1 of `e4fdcde2f9` and 0 with P2.
//!
//! RE-PINNED 2026-10-18 (the 1.101 toolchain migration): upstream replaced
//! the sized float intrinsics with generic ones whose fallback bodies
//! dispatch into `libm`; the stamp's pin cannot follow that dispatch, so
//! the panic-freedom stamp is LOST for `exp` (only the body-less
//! `powif64` keeps it) and `no_census` FAILS again on `exponential`
//! (docs/DECISION_QUEUE.md, "transcendental panic-free stamp lost"). The
//! deterministic-marker tripwire above is thereby weaker end-to-end — the
//! revision is red for a second reason now — and the direct unit-level
//! pins named above are what still guard the marker. `census` passed then:
//! nothing here was ever marked deterministic (see the 2026-11-12 re-pin below).
//!
//! The `census` revision (2026-09-26) is the other half of the same fact: these
//! calls ARE panic-free, and the sysroot panic census now DERIVES that from std's
//! own MIR (`f64::exp` is one `#[rustc_nounwind]` intrinsic; docs/design/
//! trust-std-design.md, amendment 2026-09-26). That grant is panic-freedom ONLY:
//! it rides the bridge's compiler-total channel, which leaves the call's result a
//! fresh havoc per call and adds no `@trust-rustc-intrinsic::` marker, so no facet
//! gate reads it as a purity or determinism claim.
//!
//! RE-PINNED 2026-11-12 (POISON-EVICTION-FALSE-PROOF-1): `census` FAILS on
//! `exponential`. That grant reached the call only after the poison loop evicted
//! `f64::exp`'s bundled body, which calls the generic intrinsic
//! `core::intrinsics::exp::<f64>` (absent since the 1.101 migration above). An evicted
//! body is a withdrawn call, and a withdrawn call takes no credit in any lane,
//! compiler-total included (docs/DECISION_QUEUE.md CALL-REACH-POISON-1). The loop now
//! keeps a member that a retained call still names, so the body stays and its generic
//! absent callee keeps the default policy fail-closed. `integer_power` still builds:
//! `powi::<f64>`'s absent row is runtime-checked. The lost admission is
//! docs/DECISION_QUEUE.md POISON-EVICTION-KEEP-1. MEASURED on this branch's stage 1 with
//! `TRUST_MEMBER_PANIC_CENSUS=1`: before, `evicting=["std::f64::<impl f64>::exp"]` and
//! with the withdrawal skipped the revision exits 0; now the loop keeps it, `called by`
//! `exponential`, and the revision exits 1.

pub fn exponential(x: f64) -> f64 {
    //[no_census,census]~^ ERROR Trust strict verification failed for `float_inexact_intrinsic_methods_stay_refused::exponential`
    //[census]~| NOTE a generic absent callee — keeps the function fail-closed
    x.exp()
}

pub fn integer_power(x: f64) -> f64 { x.powi(3) }
