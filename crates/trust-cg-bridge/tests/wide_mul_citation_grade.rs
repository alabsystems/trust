//! The wide-`Mul` CITATION path and the grade it produces.
//!
//! # What the grade claims, and what it does not
//!
//! A `Mul` wider than `MAX_RECHECKABLE_MUL_WIDTH` cannot carry a re-checkable
//! refutation: measured at that guard, width 8 alone is 1_759_704 resolution
//! steps and 24.3s to EXPORT, before the kernel re-check begins, growing ~16x
//! per +2 bits. The structured multiplier theorem in
//! `proofs/codegen-equivalence/g16_multiplier_equivalence.lean` covers those
//! widths GENERICALLY, so the obligation can be discharged by CITING it.
//!
//! That is a real discharge and it is strictly weaker than [PROVED]:
//!
//!   * the kernel checked `G16Mul.blast_equals_ir` — once, width-generically,
//!     axiom-free;
//!   * the kernel did NOT check `G16Mul.AyBlastAgrees`, that ay's Rust encoder
//!     emits the model's multiplier. That correspondence is machine-checked
//!     (`ay_blast_agrees_differential.rs`: exhaustive to width 8, sampled at
//!     16/32/64) but is not provable inside clean, because the encoder is Rust.
//!
//! So the grade must never read as `Certified`, and a cited function must never
//! ship where only kernel-[PROVED] may. Both are pinned below.
//!
//! # Why it is opt-in
//!
//! Enabling this changes what a verdict MEANS for every wide multiply. That is
//! an owner decision, not a build-time default — so the path is gated behind
//! `TCG_CITE_WIDE_MUL=1` and the default surface is byte-identical to before.
//! `citation_is_off_by_default` is the regression guard for that.

#![cfg(feature = "ay-proofs")]

use trust_types::grade::{AxiomClosure, GradeRecord, ProofValidation};
use trust_types::AssuranceLevel;

const THEOREM: &str = "G16Mul.blast_equals_ir";
const RESIDUAL: &str = "G16Mul.AyBlastAgrees";

/// The ceiling. A citation is not a per-instance kernel re-check, so it must
/// project to `Trusted` — never `Certified` — however it is built.
#[test]
fn citation_grade_can_never_be_certified() {
    let g = GradeRecord::cited_kernel_theorem(THEOREM, RESIDUAL);
    assert_eq!(g.to_legacy(), AssuranceLevel::Trusted);
    assert!(!g.is_certified());
    assert_eq!(g.validation, ProofValidation::CitedKernelTheorem);

    // Even with the closure forcibly emptied, the ceiling holds: the guarantee
    // does not depend on a constructor remembering to record the residual.
    let mut forced = g.clone();
    forced.axiom_closure = AxiomClosure::Empty;
    assert_eq!(
        forced.to_legacy(),
        AssuranceLevel::Trusted,
        "the citation ceiling must not depend on a non-empty closure"
    );
}

/// The residual must travel WITH the verdict. A citation whose unproved
/// correspondence is not named would claim more than it has.
#[test]
fn citation_grade_names_both_the_theorem_and_the_residual() {
    let g = GradeRecord::cited_kernel_theorem(THEOREM, RESIDUAL);
    let AxiomClosure::Named(names) = &g.axiom_closure else {
        panic!("a citation must carry a NAMED closure; got {:?}", g.axiom_closure);
    };
    assert!(
        names.iter().any(|n| n.contains(THEOREM)),
        "the cited theorem must be recorded; got {names:?}"
    );
    assert!(
        names.iter().any(|n| n.starts_with("residual:") && n.contains(RESIDUAL)),
        "the UNPROVED correspondence must be recorded as a residual; got {names:?}"
    );
}

/// The citation path is ON by default (owner decision, 2026-08-16), with
/// `TCG_CITE_WIDE_MUL=0` as the escape hatch.
///
/// Defaulting it on is safe ONLY because it raises no claim — the citation is
/// classified with [VALIDATED], caps at `Trusted`, and `StrictProvenOnly`
/// refuses it. Those three are pinned by the other tests here; if any of them
/// regresses, defaulting on would start meaning something it does not mean now.
#[test]
fn citation_is_on_by_default_with_an_escape_hatch() {
    let src = include_str!("../src/verify_output.rs");
    assert!(
        src.contains("fn cite_wide_mul_enabled_from"),
        "the policy must stay a pure, testable predicate"
    );
    assert!(
        src.contains(r#"v != Some("0")"#),
        "absent must mean ON and `0` must be the escape hatch"
    );
    assert!(
        src.contains("TCG_CITE_WIDE_MUL"),
        "the escape hatch must remain reachable without a rebuild"
    );
}

/// A citation must be counted with the [VALIDATED] surface and REFUSED under
/// StrictProvenOnly — never counted as `proved`. Pinned against the source so a
/// future edit that quietly promotes it fails here.
#[test]
fn citation_is_not_counted_as_proved() {
    for src in [
        include_str!("../src/verify_output.rs"),
        include_str!("../src/verify_output_trust_ir.rs"),
    ] {
        let proved_arm = src
            .split("=> report.proved += 1")
            .next()
            .expect("a proved-counting arm must exist");
        // The LAST proved arm before the counter must not mention the citation.
        let tail = &proved_arm[proved_arm.len().saturating_sub(400)..];
        assert!(
            !tail.contains("StructuralCitation"),
            "a StructuralCitation must NOT be counted as proved — the kernel never \
             re-checked a term for the instance:\n{tail}"
        );
        assert!(
            src.contains("ProvenEvidence::StructuralCitation { .. }\n                | ProvenEvidence::AyValidated"),
            "a citation must be grouped with the [VALIDATED] surface, so \
             StrictProvenOnly refuses it"
        );
    }
}
