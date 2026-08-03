// trust-types/annotation.rs: Proof annotations for proof-carrying MIR
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};

use crate::formula::{ProofLevel, VcKind, VerificationCondition};
use crate::model::{BinOp, SourceSpan};
use crate::result::{Counterexample, ProofStrength, VerificationResult};

/// Per-function proof annotation for proof-carrying MIR.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofAnnotation {
    pub function_name: String,
    pub function_path: String,
    pub obligations: Vec<ObligationAnnotation>,
    pub summary: AnnotationSummary,
    pub certificate: Option<ProofCertificateRef>,
}

impl ProofAnnotation {
    /// Returns true when every obligation was statically proved.
    #[must_use]
    pub fn is_fully_verified(&self) -> bool {
        !self.obligations.is_empty()
            && self
                .obligations
                .iter()
                .all(|obligation| obligation.status == AnnotationStatus::Proved)
    }

    /// Returns true when any obligation fell back to a runtime check.
    #[must_use]
    pub fn has_runtime_checks(&self) -> bool {
        self.obligations
            .iter()
            .any(|obligation| obligation.status == AnnotationStatus::RuntimeChecked)
    }

    /// Count obligations proved statically.
    #[must_use]
    pub fn proved_count(&self) -> usize {
        self.obligations
            .iter()
            .filter(|obligation| obligation.status == AnnotationStatus::Proved)
            .count()
    }

    /// Iterate only over failed obligations.
    pub fn failed_obligations(&self) -> impl Iterator<Item = &ObligationAnnotation> + '_ {
        self.obligations.iter().filter(|obligation| obligation.status == AnnotationStatus::Failed)
    }
}

/// Per-obligation detail for proof-carrying MIR consumers.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ObligationAnnotation {
    pub description: String,
    pub kind: String,
    pub proof_level: ProofLevel,
    pub status: AnnotationStatus,
    pub strength: Option<ProofStrength>,
    pub solver: String,
    pub time_ms: u64,
    pub location: Option<SourceSpan>,
    pub counterexample: Option<Counterexample>,
    pub fingerprint: [u64; 2],
}

/// Verification outcome for a single obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum AnnotationStatus {
    Proved,
    Failed,
    Unknown,
    RuntimeChecked,
    Timeout,
}

/// Aggregated counts for all obligations in a function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnnotationSummary {
    pub total: usize,
    pub proved: usize,
    pub failed: usize,
    /// Includes obligations reported as `Unknown` or `Timeout`.
    pub unknown: usize,
    pub runtime_checked: usize,
    pub max_level: Option<ProofLevel>,
}

/// Reference to an external proof certificate.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofCertificateRef {
    pub prover: String,
    pub vc_fingerprint: [u64; 2],
    pub prover_version: String,
}

/// Build a ProofAnnotation from raw verification pipeline output.
///
/// Converts paired (VerificationCondition, VerificationResult) tuples from trust-router
/// into the serde-serializable ProofAnnotation format. This is the bridge between the
/// compiler-internal verification pipeline and the external annotation world.
pub fn build_proof_annotation(
    function_name: &str,
    function_path: &str,
    results: &[(VerificationCondition, VerificationResult)],
) -> ProofAnnotation {
    let obligations: Vec<_> = results
        .iter()
        .enumerate()
        .map(|(idx, (vc, result))| {
            let (status, strength, counterexample) = match result {
                VerificationResult::Proved { strength, .. } => {
                    (AnnotationStatus::Proved, Some(strength.clone()), None)
                }
                VerificationResult::Failed { counterexample, .. } => {
                    (AnnotationStatus::Failed, None, counterexample.clone())
                }
                VerificationResult::Unknown { .. } => (AnnotationStatus::Unknown, None, None),
                VerificationResult::Timeout { .. } => (AnnotationStatus::Timeout, None, None),
            };

            ObligationAnnotation {
                description: vc.kind.description(),
                kind: vc_kind_tag(&vc.kind),
                proof_level: vc.kind.proof_level(),
                status,
                strength,
                solver: result.solver_name().to_string(),
                time_ms: result.time_ms(),
                location: (!source_span_is_default(&vc.location)).then(|| vc.location.clone()),
                counterexample,
                fingerprint: [0, idx as u64],
            }
        })
        .collect();

    let mut proved = 0usize;
    let mut failed = 0usize;
    let mut unknown = 0usize;
    let mut runtime_checked = 0usize;
    let mut max_level: Option<ProofLevel> = None;

    for obligation in &obligations {
        match obligation.status {
            AnnotationStatus::Proved => proved += 1,
            AnnotationStatus::Failed => failed += 1,
            AnnotationStatus::Unknown | AnnotationStatus::Timeout => unknown += 1,
            AnnotationStatus::RuntimeChecked => runtime_checked += 1,
        }

        max_level = Some(match max_level {
            Some(current) => current.max(obligation.proof_level),
            None => obligation.proof_level,
        });
    }

    ProofAnnotation {
        function_name: function_name.to_string(),
        function_path: function_path.to_string(),
        summary: AnnotationSummary {
            total: obligations.len(),
            proved,
            failed,
            unknown,
            runtime_checked,
            max_level,
        },
        obligations,
        certificate: None,
    }
}

fn vc_kind_tag(kind: &VcKind) -> String {
    #[allow(unreachable_patterns)] // wildcard kept for #[non_exhaustive] forward compat
    match kind {
        VcKind::ArithmeticOverflow { op, .. } => format!("arithmetic_overflow_{}", op_tag(op)),
        VcKind::ShiftOverflow { op, .. } => format!("shift_overflow_{}", op_tag(op)),
        VcKind::DivisionByZero => "division_by_zero".to_string(),
        VcKind::RemainderByZero => "remainder_by_zero".to_string(),
        VcKind::IndexOutOfBounds => "index_out_of_bounds".to_string(),
        VcKind::SliceBoundsCheck => "slice_bounds_check".to_string(),
        VcKind::CastOverflow { .. } => "cast_overflow".to_string(),
        VcKind::NegationOverflow { .. } => "negation_overflow".to_string(),
        VcKind::Assertion { .. } => "assertion".to_string(),
        VcKind::Precondition { .. } => "precondition".to_string(),
        VcKind::Postcondition => "postcondition".to_string(),
        VcKind::Unreachable => "unreachable".to_string(),
        VcKind::DeadState { .. } => "dead_state".to_string(),
        VcKind::Deadlock => "deadlock".to_string(),
        VcKind::Temporal { .. } => "temporal".to_string(),
        VcKind::Liveness { .. } => "liveness".to_string(),
        VcKind::Fairness { .. } => "fairness".to_string(),
        VcKind::TaintViolation { .. } => "taint_violation".to_string(),
        VcKind::RefinementViolation { .. } => "refinement_violation".to_string(),
        VcKind::ResilienceViolation { .. } => "resilience_violation".to_string(),
        VcKind::ProtocolViolation { .. } => "protocol_violation".to_string(),
        VcKind::NonTermination { .. } => "non_termination".to_string(),
        // Data race and memory ordering tags.
        VcKind::DataRace { .. } => "data_race".to_string(),
        VcKind::InsufficientOrdering { .. } => "insufficient_ordering".to_string(),
        // Translation validation.
        VcKind::TranslationValidation { .. } => "translation_validation".to_string(),
        // Floating-point operation tags.
        VcKind::FloatDivisionByZero => "float_division_by_zero".to_string(),
        VcKind::FloatOverflowToInfinity { .. } => "float_overflow_to_infinity".to_string(),
        // Rvalue safety VCs.
        VcKind::InvalidDiscriminant { .. } => "invalid_discriminant".to_string(),
        VcKind::AggregateArrayLengthMismatch { .. } => {
            "aggregate_array_length_mismatch".to_string()
        }
        // Unsafe operation tag.
        VcKind::UnsafeOperation { .. } => "unsafe_operation".to_string(),
        VcKind::SavedReturnAddressOverwrite { .. } => "saved_return_address_overwrite".to_string(),
        VcKind::FormatStringViolation { .. } => "format_string_violation".to_string(),
        VcKind::TaintedIndirectBranch { .. } => "tainted_indirect_branch".to_string(),
        VcKind::BinaryAbiContradiction { .. } => "binary_abi_contradiction".to_string(),
        VcKind::BinaryCopySinkLengthViolation { .. } => {
            VcKind::BINARY_COPY_SINK_LENGTH_FAMILY.to_string()
        }
        // FFI boundary violation tag.
        VcKind::FfiBoundaryViolation { .. } => "ffi_boundary_violation".to_string(),
        // Ownership VcKind tags.
        VcKind::UseAfterFree => "use_after_free".to_string(),
        VcKind::DoubleFree => "double_free".to_string(),
        VcKind::AliasingViolation { .. } => "aliasing_violation".to_string(),
        VcKind::LifetimeViolation => "lifetime_violation".to_string(),
        VcKind::SendViolation => "send_violation".to_string(),
        VcKind::SyncViolation => "sync_violation".to_string(),
        // Functional correctness tag.
        VcKind::FunctionalCorrectness { .. } => "functional_correctness".to_string(),
        // Loop invariant VcKind tags.
        VcKind::LoopInvariantInitiation { .. } => "loop_invariant_initiation".to_string(),
        VcKind::LoopInvariantConsecution { .. } => "loop_invariant_consecution".to_string(),
        VcKind::LoopInvariantSufficiency { .. } => "loop_invariant_sufficiency".to_string(),
        // trust_wp contract VcKind tags.
        VcKind::TypeRefinementViolation { .. } => "type_refinement_violation".to_string(),
        VcKind::FrameConditionViolation { .. } => "frame_condition_violation".to_string(),
        // Catch-all for future #[non_exhaustive] variants.
        _ => "unknown".to_string(),
    }
}

fn op_tag(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::Div => "div",
        BinOp::Rem => "rem",
        BinOp::Shl => "shl",
        BinOp::Shr => "shr",
        BinOp::Eq => "eq",
        BinOp::Ne => "ne",
        BinOp::Lt => "lt",
        BinOp::Le => "le",
        BinOp::Gt => "gt",
        BinOp::Ge => "ge",
        BinOp::BitAnd => "bitand",
        BinOp::BitOr => "bitor",
        BinOp::BitXor => "bitxor",
        BinOp::Cmp => "cmp",
    }
}

fn source_span_is_default(span: &SourceSpan) -> bool {
    span.file.is_empty()
        && span.line_start == 0
        && span.col_start == 0
        && span.line_end == 0
        && span.col_end == 0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::{Formula, VcKind, VerificationCondition};
    use crate::model::{BinOp, Ty};
    use crate::result::CounterexampleValue;

    fn sample_obligation(status: AnnotationStatus, description: &str) -> ObligationAnnotation {
        ObligationAnnotation {
            description: description.to_string(),
            kind: "arithmetic_overflow_add".to_string(),
            proof_level: ProofLevel::L0Safety,
            status,
            strength: matches!(status, AnnotationStatus::Proved)
                .then_some(ProofStrength::smt_unsat()),
            solver: "ay".into(),
            time_ms: 12,
            location: Some(SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 5,
                line_end: 10,
                col_end: 15,
            }),
            counterexample: matches!(status, AnnotationStatus::Failed).then(|| {
                Counterexample::new(vec![("x".to_string(), CounterexampleValue::Int(-1))])
            }),
            fingerprint: [0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210],
        }
    }

    fn sample_annotation(statuses: &[AnnotationStatus]) -> ProofAnnotation {
        let obligations: Vec<_> = statuses
            .iter()
            .enumerate()
            .map(|(index, status)| sample_obligation(*status, &format!("obligation-{index}")))
            .collect();

        let proved = obligations
            .iter()
            .filter(|obligation| obligation.status == AnnotationStatus::Proved)
            .count();
        let failed = obligations
            .iter()
            .filter(|obligation| obligation.status == AnnotationStatus::Failed)
            .count();
        let unknown = obligations
            .iter()
            .filter(|obligation| {
                matches!(obligation.status, AnnotationStatus::Unknown | AnnotationStatus::Timeout)
            })
            .count();
        let runtime_checked = obligations
            .iter()
            .filter(|obligation| obligation.status == AnnotationStatus::RuntimeChecked)
            .count();

        ProofAnnotation {
            function_name: "checked_add".to_string(),
            function_path: "crate::math::checked_add".to_string(),
            obligations,
            summary: AnnotationSummary {
                total: statuses.len(),
                proved,
                failed,
                unknown,
                runtime_checked,
                max_level: Some(ProofLevel::L0Safety),
            },
            certificate: Some(ProofCertificateRef {
                prover: "clean".to_string(),
                vc_fingerprint: [7, 11],
                prover_version: "5.1.0".to_string(),
            }),
        }
    }

    #[test]
    fn construction_and_field_access() {
        let annotation = sample_annotation(&[
            AnnotationStatus::Proved,
            AnnotationStatus::Failed,
            AnnotationStatus::RuntimeChecked,
        ]);

        assert_eq!(annotation.function_name, "checked_add");
        assert_eq!(annotation.function_path, "crate::math::checked_add");
        assert_eq!(annotation.summary.total, 3);
        assert_eq!(annotation.summary.proved, 1);
        assert_eq!(annotation.summary.failed, 1);
        assert_eq!(annotation.summary.runtime_checked, 1);
        assert!(annotation.has_runtime_checks());
        assert_eq!(annotation.proved_count(), 1);
        assert_eq!(
            annotation.certificate.as_ref().map(|certificate| certificate.prover.as_str()),
            Some("clean")
        );
        assert_eq!(annotation.obligations[1].description, "obligation-1");
        assert!(matches!(
            annotation.obligations[1].counterexample,
            Some(ref counterexample) if counterexample.to_string() == "x = -1"
        ));
    }

    #[test]
    fn is_fully_verified_returns_true_only_when_all_proved() {
        let proved = sample_annotation(&[
            AnnotationStatus::Proved,
            AnnotationStatus::Proved,
            AnnotationStatus::Proved,
        ]);
        assert!(proved.is_fully_verified());

        let failed = sample_annotation(&[AnnotationStatus::Proved, AnnotationStatus::Failed]);
        assert!(!failed.is_fully_verified());

        let unknown = sample_annotation(&[AnnotationStatus::Proved, AnnotationStatus::Unknown]);
        assert!(!unknown.is_fully_verified());

        let runtime_checked =
            sample_annotation(&[AnnotationStatus::Proved, AnnotationStatus::RuntimeChecked]);
        assert!(!runtime_checked.is_fully_verified());

        let timed_out = sample_annotation(&[AnnotationStatus::Proved, AnnotationStatus::Timeout]);
        assert!(!timed_out.is_fully_verified());

        let empty = sample_annotation(&[]);
        assert!(!empty.is_fully_verified());
    }

    #[test]
    fn serialization_roundtrip() {
        let annotation = sample_annotation(&[
            AnnotationStatus::Proved,
            AnnotationStatus::Failed,
            AnnotationStatus::Timeout,
        ]);

        let json = serde_json::to_string(&annotation).expect("serialize annotation");
        let roundtrip: ProofAnnotation =
            serde_json::from_str(&json).expect("deserialize annotation");

        assert_eq!(roundtrip.function_name, annotation.function_name);
        assert_eq!(roundtrip.function_path, annotation.function_path);
        assert_eq!(roundtrip.summary.total, annotation.summary.total);
        assert_eq!(roundtrip.summary.failed, annotation.summary.failed);
        assert_eq!(roundtrip.summary.unknown, annotation.summary.unknown);
        assert_eq!(roundtrip.proved_count(), annotation.proved_count());
        assert!(matches!(roundtrip.obligations[0].status, AnnotationStatus::Proved));
        assert!(matches!(
            roundtrip.obligations[1].counterexample,
            Some(ref counterexample) if counterexample.to_string() == "x = -1"
        ));
        assert!(matches!(roundtrip.obligations[2].status, AnnotationStatus::Timeout));
        assert_eq!(
            roundtrip.certificate.as_ref().map(|certificate| certificate.vc_fingerprint),
            Some([7, 11])
        );
    }

    #[test]
    fn failed_obligations_iterator_filters_correctly() {
        let annotation = sample_annotation(&[
            AnnotationStatus::Failed,
            AnnotationStatus::Proved,
            AnnotationStatus::Failed,
            AnnotationStatus::RuntimeChecked,
        ]);

        let failed: Vec<_> = annotation
            .failed_obligations()
            .map(|obligation| obligation.description.as_str())
            .collect();

        assert_eq!(failed, vec!["obligation-0", "obligation-2"]);
    }

    #[test]
    fn test_build_proof_annotation_mixed() {
        let proved_vc = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::u32(), Ty::u32()),
            },
            function: "checked_add".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        };
        let failed_vc = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "checked_add".into(),
            location: SourceSpan {
                file: "src/math.rs".to_string(),
                line_start: 42,
                col_start: 9,
                line_end: 42,
                col_end: 18,
            },
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };

        let results = vec![
            (
                proved_vc,
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 17,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
            (
                failed_vc,
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 31,
                    counterexample: Some(Counterexample::new(vec![(
                        "denominator".to_string(),
                        CounterexampleValue::Int(0),
                    )])),
                },
            ),
        ];

        let annotation =
            build_proof_annotation("checked_add", "crate::math::checked_add", &results);

        assert_eq!(annotation.function_name, "checked_add");
        assert_eq!(annotation.function_path, "crate::math::checked_add");
        assert_eq!(annotation.summary.total, 2);
        assert_eq!(annotation.summary.proved, 1);
        assert_eq!(annotation.summary.failed, 1);
        assert_eq!(annotation.summary.unknown, 0);
        assert_eq!(annotation.summary.runtime_checked, 0);
        assert_eq!(annotation.summary.max_level, Some(ProofLevel::L0Safety));
        assert!(annotation.certificate.is_none());

        assert_eq!(annotation.obligations[0].description, "arithmetic overflow (Add)");
        assert_eq!(annotation.obligations[0].kind, "arithmetic_overflow_add");
        assert_eq!(annotation.obligations[0].status, AnnotationStatus::Proved);
        assert_eq!(annotation.obligations[0].strength, Some(ProofStrength::smt_unsat()));
        assert_eq!(annotation.obligations[0].solver, "ay");
        assert_eq!(annotation.obligations[0].time_ms, 17);
        assert!(annotation.obligations[0].location.is_none());
        assert!(annotation.obligations[0].counterexample.is_none());
        assert_eq!(annotation.obligations[0].fingerprint, [0, 0]);

        assert_eq!(annotation.obligations[1].description, "division by zero");
        assert_eq!(annotation.obligations[1].kind, "division_by_zero");
        assert_eq!(annotation.obligations[1].status, AnnotationStatus::Failed);
        assert_eq!(annotation.obligations[1].strength, None);
        assert_eq!(annotation.obligations[1].solver, "ay");
        assert_eq!(annotation.obligations[1].time_ms, 31);
        assert_eq!(
            annotation.obligations[1].location.as_ref().map(|span| span.file.as_str()),
            Some("src/math.rs")
        );
        assert!(matches!(
            annotation.obligations[1].counterexample,
            Some(ref counterexample) if counterexample.to_string() == "denominator = 0"
        ));
        assert_eq!(annotation.obligations[1].fingerprint, [0, 1]);
    }

    #[test]
    fn test_build_proof_annotation_empty() {
        let annotation = build_proof_annotation("empty", "crate::empty", &[]);

        assert_eq!(annotation.function_name, "empty");
        assert_eq!(annotation.function_path, "crate::empty");
        assert!(annotation.obligations.is_empty());
        assert_eq!(annotation.summary.total, 0);
        assert_eq!(annotation.summary.proved, 0);
        assert_eq!(annotation.summary.failed, 0);
        assert_eq!(annotation.summary.unknown, 0);
        assert_eq!(annotation.summary.runtime_checked, 0);
        assert_eq!(annotation.summary.max_level, None);
        assert!(annotation.certificate.is_none());
    }
}
