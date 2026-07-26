use trust_backprop::{
    BinaryBackpropEvidence, GovernancePolicy, RewriteEngine, RewriteError,
    apply_binary_derived_plan, proposals_to_plan,
};
use trust_strengthen::{Proposal, ProposalKind};
use trust_types::{BinarySourceProvenanceSummary, BinaryVerificationSummary};

const FLAWED_SOURCE: &str = include_str!("fixtures/deterministic_feedback_loop/flawed.rs");
const REPAIRED_SOURCE: &str = include_str!("fixtures/deterministic_feedback_loop/repaired.rs");

#[derive(Debug, Clone, PartialEq, Eq)]
struct FakeBackpropDiagnostic {
    code: &'static str,
    function_name: &'static str,
    counterexample: &'static str,
    required_strengthening: &'static str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum FakeVerifierOutcome {
    BackpropDiagnostic(FakeBackpropDiagnostic),
    Passed { proof: &'static str },
}

struct FakeVerifier;

impl FakeVerifier {
    fn verify(source: &str) -> FakeVerifierOutcome {
        if source.contains("(a + b) / 2") {
            return FakeVerifierOutcome::BackpropDiagnostic(FakeBackpropDiagnostic {
                code: "verifier.arithmetic_overflow",
                function_name: "midpoint",
                counterexample: "a = u64::MAX, b = 1 overflows before division",
                required_strengthening: "a <= u64::MAX - b",
            });
        }

        // A precondition only reaches the verifier as a native signature
        // clause: it must appear before the body brace, where trustc lowers it
        // into `body.contract`.
        let signature_requires = source
            .find("requires a <= u64::MAX - b")
            .is_some_and(|clause| source.find('{').is_some_and(|brace| clause < brace));
        if signature_requires
            && source.contains("a.checked_add(b).expect(\"midpoint addition overflow\")")
        {
            return FakeVerifierOutcome::Passed {
                proof: "overflow VC discharged by precondition plus checked_add repair",
            };
        }

        FakeVerifierOutcome::BackpropDiagnostic(FakeBackpropDiagnostic {
            code: "backprop.incomplete_repair",
            function_name: "midpoint",
            counterexample: "repair did not preserve the strengthening expected by the verifier",
            required_strengthening: "a <= u64::MAX - b",
        })
    }
}

#[derive(Debug, Clone)]
struct FakeProposalBatch {
    accepted: Vec<Proposal>,
    rejected: Vec<Proposal>,
}

struct DeterministicFakeProposalSource;

impl DeterministicFakeProposalSource {
    fn propose(diagnostic: &FakeBackpropDiagnostic, source_path: &str) -> FakeProposalBatch {
        assert_eq!(diagnostic.code, "verifier.arithmetic_overflow");
        assert_eq!(diagnostic.function_name, "midpoint");

        FakeProposalBatch {
            accepted: vec![
                Proposal {
                    function_path: source_path.into(),
                    function_name: "midpoint".into(),
                    kind: ProposalKind::AddPrecondition {
                        spec_body: diagnostic.required_strengthening.into(),
                    },
                    confidence: 1.0,
                    rationale: format!(
                        "proof strengthening from deterministic verifier diagnostic: {}",
                        diagnostic.counterexample
                    ),
                },
                Proposal {
                    function_path: source_path.into(),
                    function_name: "midpoint".into(),
                    kind: ProposalKind::SafeArithmetic {
                        original: "a + b".into(),
                        replacement: "a.checked_add(b).expect(\"midpoint addition overflow\")"
                            .into(),
                    },
                    confidence: 1.0,
                    rationale: "repair raw addition before midpoint division".into(),
                },
            ],
            rejected: vec![Proposal {
                function_path: "binary:fixture@0x401000".into(),
                function_name: "midpoint".into(),
                kind: ProposalKind::SafeArithmetic {
                    original: "a + b".into(),
                    replacement: "unsafe { std::hint::unreachable_unchecked() }".into(),
                },
                confidence: 1.0,
                rationale:
                    "unsafe binary-derived replacement without exact source provenance is rejected"
                        .into(),
            }],
        }
    }
}

#[test]
fn deterministic_backprop_ai_feedback_loop_fixture() {
    let temp = tempfile::tempdir().expect("create deterministic fixture temp root");
    let fixture_path = temp.path().join("flawed.rs");
    std::fs::write(&fixture_path, FLAWED_SOURCE).expect("write flawed source fixture");

    let diagnostic = match FakeVerifier::verify(FLAWED_SOURCE) {
        FakeVerifierOutcome::BackpropDiagnostic(diagnostic) => diagnostic,
        FakeVerifierOutcome::Passed { proof } => {
            panic!("flawed fixture unexpectedly verified: {proof}")
        }
    };
    assert_eq!(diagnostic.counterexample, "a = u64::MAX, b = 1 overflows before division");

    let proposal_batch = DeterministicFakeProposalSource::propose(&diagnostic, "flawed.rs");
    assert_eq!(proposal_batch.accepted.len(), 2);
    assert_eq!(proposal_batch.rejected.len(), 1);

    let plan = proposals_to_plan(&proposal_batch.accepted, temp.path())
        .expect("accepted fake proposals should convert to a source rewrite plan");
    assert_eq!(plan.len(), 2);

    let repaired = RewriteEngine::new()
        .apply_plan_to_source(FLAWED_SOURCE, &plan)
        .expect("accepted fake proposals should apply cleanly");
    assert_eq!(repaired, REPAIRED_SOURCE);
    assert!(!repaired.contains("unreachable_unchecked"));

    let proof = match FakeVerifier::verify(&repaired) {
        FakeVerifierOutcome::Passed { proof } => proof,
        FakeVerifierOutcome::BackpropDiagnostic(diagnostic) => {
            panic!("repaired fixture did not verify: {diagnostic:?}")
        }
    };
    assert_eq!(proof, "overflow VC discharged by precondition plus checked_add repair");

    let invalid_provenance = BinarySourceProvenanceSummary::default();
    let invalid_verification = BinaryVerificationSummary::default();
    let invalid_evidence = BinaryBackpropEvidence::new(&invalid_provenance, &invalid_verification);
    let rejection = apply_binary_derived_plan(
        &proposal_batch.rejected,
        &GovernancePolicy::default(),
        invalid_evidence,
    )
    .expect_err("provenance-invalid unsafe fake proposal must fail closed");

    let RewriteError::UnsafeProvenance { function, reason } = rejection else {
        panic!("expected unsafe provenance rejection");
    };
    assert_eq!(function, "midpoint");
    assert!(reason.contains("exact-source-provenance-missing"), "{reason}");
    assert!(reason.contains("proof-grade-binary-verification-missing"), "{reason}");
    assert!(reason.contains("source_backpropagation_gate=missing"), "{reason}");
}
