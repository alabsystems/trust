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

use trust_cg_bridge::verify_output::{OutputVerdict, ProvenEvidence, verify_output_preserved};
use trust_types::grade::{AxiomClosure, GradeRecord, ProofValidation};
use trust_types::{
    AssuranceLevel, BasicBlock, BinOp, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

const THEOREM: &str = "G16Mul.blast_equals_ir";
const RESIDUAL: &str = "G16Mul.AyBlastAgrees";

/// `wide_mul(a: i32, b: i32) -> i32 { a * b }` — width 32 is past
/// `MAX_RECHECKABLE_MUL_WIDTH` (8), so the slow bit-blast path declines and the
/// citation path is what the live gate reaches.
fn make_wide_mul_fn() -> VerifiableFunction {
    VerifiableFunction {
        name: "cite_wide_mul".to_string(),
        def_path: "test::cite_wide_mul".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Mul,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

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

/// THE PIPELINE ASSERTION (2026-08-20 carrier increment): drive the REAL gate —
/// emit `a * b: i32` to machine bytes, decode, discharge through ay — and
/// require the resulting `StructuralCitation` verdict to CARRY a
/// `GradeRecord::cited_kernel_theorem` that names the theorem and the residual
/// and is not `Certified` by construction. This is the first production
/// constructor of that record whose output survives past its own statement.
///
/// Exact-evidence form runs without `kernel-recheck`: with that feature on, a
/// 32-bit mul is discharged KERNEL-[PROVED] by O(1) instantiation before the
/// citation path is consulted, so the citation is not what the gate returns.
/// (Relies on the default-ON citation policy; do not set `TCG_CITE_WIDE_MUL=0`
/// in the environment of this test run.)
#[cfg(not(feature = "kernel-recheck"))]
#[test]
fn pipeline_wide_mul_verdict_carries_the_citation_grade_record() {
    let func = make_wide_mul_fn();
    let verdict = verify_output_preserved(&func);
    let OutputVerdict::Proven { evidence } = &verdict else {
        panic!("the gate must prove the wide mul (got {verdict:?})");
    };
    let ProvenEvidence::StructuralCitation { theorem, residual, width, grade } = evidence else {
        panic!("a >8-bit mul must be discharged by citation on this path (got {evidence:?})");
    };

    // The named fields and the carried record cannot drift apart: the record
    // IS the constructor applied to those same names.
    assert_eq!(*theorem, THEOREM);
    assert_eq!(*residual, RESIDUAL);
    assert_eq!(*width, 32, "the citation must record the width the guard measured");
    assert_eq!(grade, &GradeRecord::cited_kernel_theorem(theorem, residual));

    // The carried grade names BOTH the theorem and the residual...
    let AxiomClosure::Named(names) = &grade.axiom_closure else {
        panic!("a carried citation grade must have a NAMED closure; got {:?}", grade.axiom_closure);
    };
    assert!(names.contains(&format!("cites:{THEOREM}")));
    assert!(names.contains(&format!("residual:{RESIDUAL}")));

    // ...and is not Certified, by construction, projecting to Trusted.
    assert!(!grade.is_certified(), "a citation is not a per-instance kernel re-check");
    assert_eq!(grade.to_legacy(), AssuranceLevel::Trusted);
    assert_eq!(grade.validation, ProofValidation::CitedKernelTheorem);

    // The pipeline read side: the carried record is reachable from the verdict
    // without matching the evidence shape.
    assert_eq!(verdict.carried_grade(), Some(grade));
}

/// NEGATIVE: no non-citation evidence carries a grade record this increment —
/// in particular the ay-only ([VALIDATED] / smt-backed) surface must never
/// present a record that could be mistaken for a kernel-theorem citation. A
/// grade is CARRIED from a mint site or it is absent; accessors never derive
/// one.
#[test]
fn non_citation_evidence_carries_no_grade_record() {
    assert_eq!(ProvenEvidence::AyValidated.carried_grade(), None);
    assert_eq!(
        ProvenEvidence::KernelInstantiated { theorem: "bvf_mul_cong".into() }.carried_grade(),
        None
    );
    assert_eq!(
        OutputVerdict::Proven { evidence: ProvenEvidence::AyValidated }.carried_grade(),
        None
    );
    assert_eq!(OutputVerdict::Unknown { reason: "r".into() }.carried_grade(), None);
    assert_eq!(OutputVerdict::Refuted { detail: "d".into() }.carried_grade(), None);
}

/// The mint site must stay SINGLE: the variant is built only through
/// `structural_citation_evidence`, whose grade field applies the record's own
/// constructor to the same constants as the string fields. Pinned against the
/// source so a second, drift-capable construction site fails here.
#[test]
fn citation_grade_is_minted_once_at_the_citation_site() {
    let src = include_str!("../src/verify_output.rs");
    assert!(src.contains("fn structural_citation_evidence"), "the single mint helper must exist");
    assert!(
        src.contains("return Some(structural_citation_evidence(width))"),
        "the citation path must mint through the helper"
    );
    assert!(
        src.contains(
            "grade: GradeRecord::cited_kernel_theorem(CITED_MUL_THEOREM, CITED_MUL_RESIDUAL)"
        ),
        "the carried record must be built from the SAME constants as the string fields"
    );
    assert_eq!(
        src.matches("ProvenEvidence::StructuralCitation {\n        theorem:").count(),
        1,
        "exactly one construction site may exist"
    );
}

/// A citation must be counted with the [VALIDATED] surface and REFUSED under
/// StrictProvenOnly — never counted as `proved`. Pinned against the source so a
/// future edit that quietly promotes it fails here.
#[test]
fn citation_is_not_counted_as_proved() {
    for src in
        [include_str!("../src/verify_output.rs"), include_str!("../src/verify_output_trust_ir.rs")]
    {
        let proved_arm =
            src.split("=> report.proved += 1").next().expect("a proved-counting arm must exist");
        // The LAST proved arm before the counter must not mention the citation.
        let tail = &proved_arm[proved_arm.len().saturating_sub(400)..];
        assert!(
            !tail.contains("StructuralCitation"),
            "a StructuralCitation must NOT be counted as proved — the kernel never \
             re-checked a term for the instance:\n{tail}"
        );
        // Trust: check the GROUPING, not its formatting.
        //
        // This pinned an exact multi-line spelling — `StructuralCitation { .. }`,
        // a newline, sixteen spaces, then `| ProvenEvidence::AyValidated`. rustfmt
        // has since joined that match arm onto ONE line, so the substring stopped
        // matching while the property it guards was completely intact. The test
        // was reporting a formatting change as a soundness failure.
        //
        // Collapsing whitespace keeps the real assertion — the two variants share
        // a match arm, which is what puts a citation on the [VALIDATED] surface
        // and makes StrictProvenOnly refuse it — and survives the next reflow.
        let collapsed: String = src.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(
            collapsed.contains(
                "ProvenEvidence::StructuralCitation { .. } | ProvenEvidence::AyValidated"
            ),
            "a citation must be grouped with the [VALIDATED] surface, so \
             StrictProvenOnly refuses it"
        );
    }
}
