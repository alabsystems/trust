// trust-transval: Conservative reconstructed-output validation
//
// This is intentionally a thin scaffold over the existing translation
// validator. Reconstructed source or converted artifacts only become
// validation candidates when a caller supplies a structured TrustIr body to
// compare against the lifted binary TrustIr.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    DecompileTarget, DecompiledFunction, DecompiledOutput, ReconstructionCandidateKind,
    ReconstructionValidationDirection, ReconstructionValidationDirectionRecord,
    ReconstructionValidationEvidence, ReconstructionValidationRecord,
    ReconstructionValidationStatus, TrustLevel, VerifiableFunction,
};

use crate::ay_validator::{SmtValidationResult, TranslationValidator};
use crate::error::TransvalError;

/// Conservative validator for reconstructed or converted outputs.
///
/// The lifted binary TrustIr is treated as the reference. A decompiler/converter
/// output must provide a comparable `VerifiableFunction` body before this API
/// can attempt validation. Text-only outputs, pre-existing validation labels,
/// and presentation artifacts are never upgraded to `Validated` by themselves.
pub struct ReconstructionOutputValidator {
    validator: TranslationValidator,
}

impl Default for ReconstructionOutputValidator {
    fn default() -> Self {
        Self::new()
    }
}

impl ReconstructionOutputValidator {
    /// Create a validator backed by the default translation validator.
    #[must_use]
    pub fn new() -> Self {
        Self { validator: TranslationValidator::new() }
    }

    /// Create a validator backed by a caller-provided translation validator.
    #[must_use]
    pub fn with_translation_validator(validator: TranslationValidator) -> Self {
        Self { validator }
    }

    /// Validate a structured reconstructed/conversion TrustIr body against lifted
    /// binary TrustIr.
    ///
    /// This checks both refinement directions. `Validated` is returned only
    /// when both directions are equivalent. Any definite divergence is
    /// `Refuted`; solver/modeling gaps are `Unknown`.
    #[must_use]
    pub fn validate_pair(
        &self,
        lifted_binary_trust_ir: &VerifiableFunction,
        reconstructed_trust_ir: &VerifiableFunction,
    ) -> ReconstructionOutputValidation {
        self.validate_output(Some(lifted_binary_trust_ir), Some(reconstructed_trust_ir), None)
    }

    /// Validate a decompiler/converter output against lifted binary TrustIr.
    ///
    /// `output` supplies metadata only. `reconstructed_trust_ir` is the comparable
    /// semantic body for the output; if it is absent, validation is not
    /// attempted or remains unknown, never `Validated`.
    #[must_use]
    pub fn validate_output(
        &self,
        lifted_binary_trust_ir: Option<&VerifiableFunction>,
        reconstructed_trust_ir: Option<&VerifiableFunction>,
        output: Option<&DecompiledOutput>,
    ) -> ReconstructionOutputValidation {
        let target = output.map_or(DecompileTarget::TrustIr, |output| output.target.clone());
        let candidate = candidate_kind(reconstructed_trust_ir, output);
        let lifted_function = lifted_binary_trust_ir.map(|func| func.name.clone());
        let reconstructed_function = reconstructed_trust_ir.map(|func| func.name.clone());
        let mut diagnostics = output_diagnostics(output);

        let (Some(lifted), Some(reconstructed)) = (lifted_binary_trust_ir, reconstructed_trust_ir)
        else {
            diagnostics.push(missing_comparable_reason(
                lifted_binary_trust_ir,
                reconstructed_trust_ir,
                output,
            ));

            let status =
                missing_comparable_status(output, lifted_binary_trust_ir, reconstructed_trust_ir);
            return ReconstructionOutputValidation::new(
                status,
                target,
                candidate,
                lifted_function,
                reconstructed_function,
                diagnostics,
                None,
                None,
            );
        };

        if let Some(report) = preflight_report(
            lifted,
            reconstructed,
            &mut diagnostics,
            target.clone(),
            candidate.clone(),
        ) {
            return report.with_functions(lifted_function, reconstructed_function);
        }

        let forward = match self.validator.validate_refinement(lifted, reconstructed) {
            Ok(result) => result,
            Err(err) => {
                diagnostics.push(format!("lifted-to-output refinement could not complete: {err}"));
                return ReconstructionOutputValidation::new(
                    status_for_error(&err),
                    target,
                    candidate,
                    lifted_function,
                    reconstructed_function,
                    diagnostics,
                    None,
                    None,
                );
            }
        };

        diagnostics.extend(result_diagnostics("lifted-to-output", &forward));
        if matches!(status_for_result(&forward), ReconstructionValidationStatus::Refuted) {
            return ReconstructionOutputValidation::new(
                ReconstructionValidationStatus::Refuted,
                target,
                candidate,
                lifted_function,
                reconstructed_function,
                diagnostics,
                Some(forward),
                None,
            );
        }

        let reverse = match self.validator.validate_refinement(reconstructed, lifted) {
            Ok(result) => result,
            Err(err) => {
                diagnostics.push(format!("output-to-lifted refinement could not complete: {err}"));
                return ReconstructionOutputValidation::new(
                    status_for_error(&err),
                    target,
                    candidate,
                    lifted_function,
                    reconstructed_function,
                    diagnostics,
                    Some(forward),
                    None,
                );
            }
        };

        diagnostics.extend(result_diagnostics("output-to-lifted", &reverse));
        let status =
            merge_direction_statuses(status_for_result(&forward), status_for_result(&reverse));

        ReconstructionOutputValidation::new(
            status,
            target,
            candidate,
            lifted_function,
            reconstructed_function,
            diagnostics,
            Some(forward),
            Some(reverse),
        )
    }

    /// Validate a recovered binary function with an optional structured output
    /// body.
    ///
    /// The `DecompiledFunction` carries the lifted TrustIr reference. The
    /// reconstructed TrustIr must still be supplied separately because
    /// `DecompiledOutput` is presentation metadata/text, not a semantic body.
    #[must_use]
    pub fn validate_decompiled_function(
        &self,
        function: &DecompiledFunction,
        reconstructed_trust_ir: Option<&VerifiableFunction>,
    ) -> ReconstructionOutputValidation {
        let mut report = self.validate_output(
            function.lifted.as_ref(),
            reconstructed_trust_ir,
            function.output.as_ref(),
        );

        if report.lifted_function.is_none() && !function.name.is_empty() {
            report.lifted_function = Some(function.name.clone());
        }

        report
    }
}

/// Result of reconstructed/conversion-output validation.
#[derive(Debug, Clone)]
pub struct ReconstructionOutputValidation {
    /// Output target whose reconstruction/conversion is being checked.
    pub target: DecompileTarget,
    /// Semantic candidate available to this validation attempt.
    pub candidate: ReconstructionCandidateKind,
    /// Conservative validation status for the output.
    pub status: ReconstructionValidationStatus,
    /// Trust level justified by this validation result alone.
    ///
    /// A successful reconstruction check establishes consistency with lifted
    /// TrustIr, but does not by itself prove lift coverage or binary modeling
    /// soundness, so `Validated` maps to `Partial`.
    pub trust_level: TrustLevel,
    /// Name of the lifted binary TrustIr function, when known.
    pub lifted_function: Option<String>,
    /// Name of the reconstructed/conversion TrustIr function, when supplied.
    pub reconstructed_function: Option<String>,
    /// Human-readable conservative diagnostics.
    pub diagnostics: Vec<String>,
    /// Result for lifted-binary-TrustIr -> reconstructed-output refinement.
    pub forward: Option<SmtValidationResult>,
    /// Result for reconstructed-output -> lifted-binary-TrustIr refinement.
    pub reverse: Option<SmtValidationResult>,
}

impl ReconstructionOutputValidation {
    #[allow(clippy::too_many_arguments)] // validation row captures every facet of one reconstruction outcome
    fn new(
        status: ReconstructionValidationStatus,
        target: DecompileTarget,
        candidate: ReconstructionCandidateKind,
        lifted_function: Option<String>,
        reconstructed_function: Option<String>,
        diagnostics: Vec<String>,
        forward: Option<SmtValidationResult>,
        reverse: Option<SmtValidationResult>,
    ) -> Self {
        let has_complete_direction_evidence = has_complete_direction_evidence(&forward, &reverse);
        Self {
            target,
            candidate: candidate.clone(),
            status,
            trust_level: trust_level_for_status(
                status,
                &candidate,
                has_complete_direction_evidence,
            ),
            lifted_function,
            reconstructed_function,
            diagnostics,
            forward,
            reverse,
        }
    }

    fn with_functions(
        mut self,
        lifted_function: Option<String>,
        reconstructed_function: Option<String>,
    ) -> Self {
        self.lifted_function = lifted_function;
        self.reconstructed_function = reconstructed_function;
        self
    }

    /// Reconstruction validation alone is never proof-grade evidence.
    #[must_use]
    pub fn is_proof_grade(&self) -> bool {
        false
    }

    /// Convert this validation outcome into the serializable decompilation
    /// artifact record.
    #[must_use]
    pub fn to_record(&self) -> ReconstructionValidationRecord {
        let status = record_status(self.status, &self.candidate, &self.forward, &self.reverse);
        let trust_level = record_trust_level(status, &self.candidate, &self.forward, &self.reverse);
        ReconstructionValidationRecord {
            target: self.target.clone(),
            function: self.lifted_function.clone().or_else(|| self.reconstructed_function.clone()),
            lifted_function: self.lifted_function.clone(),
            reconstructed_function: self.reconstructed_function.clone(),
            candidate: self.candidate.clone(),
            status,
            trust_level,
            forward: self.forward.as_ref().map(|result| {
                direction_record(ReconstructionValidationDirection::LiftedToOutput, result)
            }),
            reverse: self.reverse.as_ref().map(|result| {
                direction_record(ReconstructionValidationDirection::OutputToLifted, result)
            }),
            evidence: record_evidence(
                status,
                &self.candidate,
                self.lifted_function.is_some() && self.reconstructed_function.is_some(),
                self.forward.is_some(),
                self.reverse.is_some(),
            ),
            diagnostics: self.diagnostics.clone(),
        }
    }
}

fn has_complete_direction_evidence(
    forward: &Option<SmtValidationResult>,
    reverse: &Option<SmtValidationResult>,
) -> bool {
    forward.is_some() && reverse.is_some()
}

fn record_status(
    status: ReconstructionValidationStatus,
    candidate: &ReconstructionCandidateKind,
    forward: &Option<SmtValidationResult>,
    reverse: &Option<SmtValidationResult>,
) -> ReconstructionValidationStatus {
    if !matches!(status, ReconstructionValidationStatus::Validated) {
        return status;
    }

    if matches!(candidate, ReconstructionCandidateKind::StructuredTrustIr)
        && has_complete_direction_evidence(forward, reverse)
    {
        return ReconstructionValidationStatus::Validated;
    }

    ReconstructionValidationStatus::Unknown
}

fn record_trust_level(
    status: ReconstructionValidationStatus,
    candidate: &ReconstructionCandidateKind,
    forward: &Option<SmtValidationResult>,
    reverse: &Option<SmtValidationResult>,
) -> TrustLevel {
    trust_level_for_status(status, candidate, has_complete_direction_evidence(forward, reverse))
}

fn record_evidence(
    status: ReconstructionValidationStatus,
    candidate: &ReconstructionCandidateKind,
    has_comparable_functions: bool,
    has_forward: bool,
    has_reverse: bool,
) -> Vec<ReconstructionValidationEvidence> {
    let mut evidence = Vec::new();
    match candidate {
        ReconstructionCandidateKind::StructuredTrustIr => {
            if has_forward && has_reverse {
                evidence.push(ReconstructionValidationEvidence::BidirectionalTrustIrRefinement);
            } else if !has_comparable_functions {
                evidence.push(ReconstructionValidationEvidence::MissingComparableTrustIr);
            }
            evidence.push(ReconstructionValidationEvidence::NoCheckedProofCertificate);
            evidence.push(ReconstructionValidationEvidence::NoBinaryProofObligation);
        }
        ReconstructionCandidateKind::ValidatedRustStrictSubset => {
            evidence.push(ReconstructionValidationEvidence::StrictRustSubsetEligible);
            evidence.push(ReconstructionValidationEvidence::NoCheckedProofCertificate);
            evidence.push(ReconstructionValidationEvidence::NoBinaryProofObligation);
        }
        ReconstructionCandidateKind::TextOnly => {
            evidence.push(ReconstructionValidationEvidence::TextOnlyCandidateRejected);
            evidence.push(ReconstructionValidationEvidence::MissingComparableTrustIr);
        }
        ReconstructionCandidateKind::Missing => {
            evidence.push(ReconstructionValidationEvidence::MissingComparableTrustIr);
        }
        ReconstructionCandidateKind::Other(_) => {}
        _ => {}
    }

    if matches!(status, ReconstructionValidationStatus::Validated) {
        evidence.retain(|item| {
            !matches!(item, ReconstructionValidationEvidence::MissingComparableTrustIr)
        });
    }
    evidence
}

fn output_diagnostics(output: Option<&DecompiledOutput>) -> Vec<String> {
    output
        .map(|output| {
            vec![format!(
                "output metadata: target={:?}, prior_validation={:?}, prior_trust={:?}",
                output.target, output.validation, output.trust_level
            )]
        })
        .unwrap_or_default()
}

fn candidate_kind(
    reconstructed_trust_ir: Option<&VerifiableFunction>,
    output: Option<&DecompiledOutput>,
) -> ReconstructionCandidateKind {
    if reconstructed_trust_ir.is_some() {
        return ReconstructionCandidateKind::StructuredTrustIr;
    }

    if output.is_some_and(has_strict_rust_subset_candidate) {
        return ReconstructionCandidateKind::ValidatedRustStrictSubset;
    }

    if output.is_some_and(|output| output.text.is_some() || output.artifact_path.is_some()) {
        return ReconstructionCandidateKind::TextOnly;
    }

    ReconstructionCandidateKind::Missing
}

fn has_strict_rust_subset_candidate(output: &DecompiledOutput) -> bool {
    output.validated_rust.as_ref().is_some_and(|validated| {
        validated.eligibility.iter().any(|eligibility| eligibility.eligible)
            || validated.validation_records.iter().any(|record| {
                matches!(record.candidate, ReconstructionCandidateKind::ValidatedRustStrictSubset)
            })
    })
}

fn missing_comparable_reason(
    lifted_binary_trust_ir: Option<&VerifiableFunction>,
    reconstructed_trust_ir: Option<&VerifiableFunction>,
    output: Option<&DecompiledOutput>,
) -> String {
    match (lifted_binary_trust_ir.is_some(), reconstructed_trust_ir.is_some(), output) {
        (false, false, _) => {
            "missing lifted binary TrustIr reference and reconstructed TrustIr body".to_string()
        }
        (false, true, _) => "missing lifted binary TrustIr reference".to_string(),
        (true, false, Some(output))
            if matches!(output.validation, ReconstructionValidationStatus::Validated) =>
        {
            "output metadata claims validation, but no comparable reconstructed TrustIr body was supplied"
                .to_string()
        }
        (true, false, _) => {
            "no comparable reconstructed TrustIr body was supplied for this output".to_string()
        }
        (true, true, _) => "unreachable comparable-state fallback".to_string(),
    }
}

fn missing_comparable_status(
    output: Option<&DecompiledOutput>,
    lifted_binary_trust_ir: Option<&VerifiableFunction>,
    reconstructed_trust_ir: Option<&VerifiableFunction>,
) -> ReconstructionValidationStatus {
    if lifted_binary_trust_ir.is_some()
        && reconstructed_trust_ir.is_none()
        && output.is_some_and(has_strict_rust_subset_candidate)
    {
        return ReconstructionValidationStatus::Unknown;
    }

    if lifted_binary_trust_ir.is_some()
        && reconstructed_trust_ir.is_none()
        && output.is_some_and(|output| {
            !matches!(output.validation, ReconstructionValidationStatus::NotAttempted)
        })
    {
        return ReconstructionValidationStatus::Unknown;
    }

    if lifted_binary_trust_ir.is_none() && reconstructed_trust_ir.is_some() {
        return ReconstructionValidationStatus::Unknown;
    }

    ReconstructionValidationStatus::NotAttempted
}

fn preflight_report(
    lifted: &VerifiableFunction,
    reconstructed: &VerifiableFunction,
    diagnostics: &mut Vec<String>,
    target: DecompileTarget,
    candidate: ReconstructionCandidateKind,
) -> Option<ReconstructionOutputValidation> {
    if lifted.body.blocks.is_empty() {
        diagnostics.push("lifted binary TrustIr body is empty".to_string());
        return Some(ReconstructionOutputValidation::new(
            ReconstructionValidationStatus::Unknown,
            target,
            candidate,
            None,
            None,
            diagnostics.clone(),
            None,
            None,
        ));
    }

    if reconstructed.body.blocks.is_empty() {
        diagnostics.push("reconstructed output TrustIr body is empty".to_string());
        return Some(ReconstructionOutputValidation::new(
            ReconstructionValidationStatus::Unknown,
            target,
            candidate,
            None,
            None,
            diagnostics.clone(),
            None,
            None,
        ));
    }

    if lifted.body.arg_count != reconstructed.body.arg_count {
        diagnostics.push(format!(
            "argument count mismatch: lifted has {}, reconstructed output has {}",
            lifted.body.arg_count, reconstructed.body.arg_count
        ));
        return Some(ReconstructionOutputValidation::new(
            ReconstructionValidationStatus::Refuted,
            target,
            candidate,
            None,
            None,
            diagnostics.clone(),
            None,
            None,
        ));
    }

    if lifted.body.return_ty != reconstructed.body.return_ty {
        diagnostics.push(format!(
            "return type mismatch: lifted has {:?}, reconstructed output has {:?}",
            lifted.body.return_ty, reconstructed.body.return_ty
        ));
        return Some(ReconstructionOutputValidation::new(
            ReconstructionValidationStatus::Unknown,
            target,
            candidate,
            None,
            None,
            diagnostics.clone(),
            None,
            None,
        ));
    }

    None
}

fn status_for_error(err: &TransvalError) -> ReconstructionValidationStatus {
    match err {
        TransvalError::SignatureMismatch { .. } => ReconstructionValidationStatus::Refuted,
        TransvalError::EmptyBody(_)
        | TransvalError::UnmappedBlock(_)
        | TransvalError::InvalidRelation(_)
        | TransvalError::SolverError(_)
        | TransvalError::UnsupportedOptimization(_) => ReconstructionValidationStatus::Unknown,
    }
}

fn status_for_result(result: &SmtValidationResult) -> ReconstructionValidationStatus {
    match result {
        SmtValidationResult::Equivalent { .. } => ReconstructionValidationStatus::Validated,
        SmtValidationResult::Divergent { .. } => ReconstructionValidationStatus::Refuted,
        SmtValidationResult::Inconclusive { .. } => ReconstructionValidationStatus::Unknown,
    }
}

fn merge_direction_statuses(
    forward: ReconstructionValidationStatus,
    reverse: ReconstructionValidationStatus,
) -> ReconstructionValidationStatus {
    if matches!(forward, ReconstructionValidationStatus::Refuted)
        || matches!(reverse, ReconstructionValidationStatus::Refuted)
    {
        return ReconstructionValidationStatus::Refuted;
    }

    if matches!(forward, ReconstructionValidationStatus::Validated)
        && matches!(reverse, ReconstructionValidationStatus::Validated)
    {
        return ReconstructionValidationStatus::Validated;
    }

    ReconstructionValidationStatus::Unknown
}

fn trust_level_for_status(
    status: ReconstructionValidationStatus,
    candidate: &ReconstructionCandidateKind,
    has_direction_evidence: bool,
) -> TrustLevel {
    let has_structured_candidate =
        matches!(candidate, ReconstructionCandidateKind::StructuredTrustIr);
    match status {
        ReconstructionValidationStatus::NotAttempted => TrustLevel::Exploratory,
        ReconstructionValidationStatus::Validated
            if has_structured_candidate && has_direction_evidence =>
        {
            TrustLevel::Partial
        }
        ReconstructionValidationStatus::Validated => TrustLevel::Exploratory,
        ReconstructionValidationStatus::Refuted | ReconstructionValidationStatus::Failed => {
            TrustLevel::Rejected
        }
        ReconstructionValidationStatus::Unknown
            if has_structured_candidate && has_direction_evidence =>
        {
            TrustLevel::Partial
        }
        ReconstructionValidationStatus::Unknown => TrustLevel::Exploratory,
        _ if has_structured_candidate && has_direction_evidence => TrustLevel::Partial,
        _ => TrustLevel::Exploratory,
    }
}

fn direction_record(
    direction: ReconstructionValidationDirection,
    result: &SmtValidationResult,
) -> ReconstructionValidationDirectionRecord {
    let direction_name = match direction {
        ReconstructionValidationDirection::LiftedToOutput => "lifted-to-output",
        ReconstructionValidationDirection::OutputToLifted => "output-to-lifted",
        _ => "unknown-direction",
    };

    let (vc_count, counterexamples, proof_certificates) = match result {
        SmtValidationResult::Equivalent { proof_certificates, .. } => {
            (0, 0, proof_certificates.len())
        }
        SmtValidationResult::Divergent { counterexamples, .. } => (0, counterexamples.len(), 0),
        SmtValidationResult::Inconclusive { partial_results, .. } => (partial_results.len(), 0, 0),
    };

    ReconstructionValidationDirectionRecord {
        direction,
        status: status_for_result(result),
        vc_count,
        counterexamples,
        proof_certificates,
        diagnostics: result_diagnostics(direction_name, result),
    }
}

fn result_diagnostics(direction: &str, result: &SmtValidationResult) -> Vec<String> {
    match result {
        SmtValidationResult::Equivalent { .. } => vec![],
        SmtValidationResult::Divergent { counterexamples, .. } => {
            vec![format!(
                "{direction} refinement was refuted with {} counterexample(s)",
                counterexamples.len()
            )]
        }
        SmtValidationResult::Inconclusive { reason, .. } => {
            vec![format!("{direction} refinement is unknown: {reason}")]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_router::Router;
    use trust_types::{
        BasicBlock, BinOp, BlockId, DecompileTarget, LocalDecl, Operand, Place,
        ReconstructionCandidateKind, ReconstructionValidationDirection,
        ReconstructionValidationEvidence, ReconstructionValidationRecord,
        ReconstructionValidationStatus, RustReconstructionEligibility, Rvalue, SourceSpan,
        Statement, Terminator, Ty, ValidatedRustReconstruction, VerifiableBody,
    };

    fn simple_binop(name: &str, op: BinOp) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                op,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn rust_output(validation: ReconstructionValidationStatus) -> DecompiledOutput {
        DecompiledOutput {
            target: DecompileTarget::Rust,
            text: Some("pub fn f() { todo!() }".to_string()),
            validation,
            trust_level: TrustLevel::Exploratory,
            ..DecompiledOutput::default()
        }
    }

    fn equivalent_result() -> SmtValidationResult {
        SmtValidationResult::Equivalent { proof_time_ms: 1, proof_certificates: vec![] }
    }

    fn assert_non_proof_record(
        report: &ReconstructionOutputValidation,
        record: &ReconstructionValidationRecord,
        trust_level: TrustLevel,
    ) {
        assert!(!report.is_proof_grade());
        assert_eq!(record.trust_level, trust_level);
        assert_ne!(record.trust_level, TrustLevel::ProofGrade);
    }

    #[test]
    fn unvalidated_output_without_comparable_trust_ir_is_not_attempted() {
        let lifted = simple_binop("lifted", BinOp::Add);
        let function = DecompiledFunction {
            name: "binary_fn".to_string(),
            lifted: Some(lifted),
            output: Some(rust_output(ReconstructionValidationStatus::NotAttempted)),
            ..DecompiledFunction::default()
        };

        let report =
            ReconstructionOutputValidator::new().validate_decompiled_function(&function, None);

        assert_eq!(report.status, ReconstructionValidationStatus::NotAttempted);
        assert_eq!(report.candidate, ReconstructionCandidateKind::TextOnly);
        assert_eq!(report.trust_level, TrustLevel::Exploratory);
        assert!(!report.is_proof_grade());
        assert_ne!(report.trust_level, TrustLevel::ProofGrade);
        assert!(report.forward.is_none());
        assert!(report.reverse.is_none());

        let record = report.to_record();
        assert_eq!(record.candidate, ReconstructionCandidateKind::TextOnly);
        assert_eq!(record.status, ReconstructionValidationStatus::NotAttempted);
        assert_eq!(record.trust_level, TrustLevel::Exploratory);
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::TextOnlyCandidateRejected)
        );
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::MissingComparableTrustIr)
        );
        assert!(record.forward.is_none());
        assert_non_proof_record(&report, &record, TrustLevel::Exploratory);
    }

    #[test]
    fn claimed_validated_output_without_comparable_trust_ir_is_unknown_not_proof_grade() {
        let lifted = simple_binop("lifted", BinOp::Add);
        let mut output = rust_output(ReconstructionValidationStatus::Validated);
        output.trust_level = TrustLevel::ProofGrade;

        let report = ReconstructionOutputValidator::new().validate_output(
            Some(&lifted),
            None,
            Some(&output),
        );

        assert_eq!(report.status, ReconstructionValidationStatus::Unknown);
        assert_eq!(report.candidate, ReconstructionCandidateKind::TextOnly);
        assert_eq!(report.trust_level, TrustLevel::Exploratory);
        assert!(!report.is_proof_grade());
        assert_ne!(report.trust_level, TrustLevel::ProofGrade);
        assert!(report.diagnostics.iter().any(|msg| msg.contains("no comparable")));

        let record = report.to_record();
        assert_eq!(record.status, ReconstructionValidationStatus::Unknown);
        assert_eq!(record.candidate, ReconstructionCandidateKind::TextOnly);
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::TextOnlyCandidateRejected)
        );
        assert_non_proof_record(&report, &record, TrustLevel::Exploratory);
    }

    #[test]
    fn missing_lifted_trust_ir_reference_is_never_validated() {
        let reconstructed = simple_binop("candidate", BinOp::Add);

        let report =
            ReconstructionOutputValidator::new().validate_output(None, Some(&reconstructed), None);

        assert_eq!(report.status, ReconstructionValidationStatus::Unknown);
        assert_eq!(report.candidate, ReconstructionCandidateKind::StructuredTrustIr);
        assert_eq!(report.trust_level, TrustLevel::Exploratory);
        assert!(!report.is_proof_grade());
        assert!(report.forward.is_none());
    }

    #[test]
    fn matching_structured_output_can_validate_but_does_not_raise_binary_trust() {
        let lifted = simple_binop("lifted", BinOp::Add);
        let reconstructed = simple_binop("candidate", BinOp::Add);

        let validator = ReconstructionOutputValidator::with_translation_validator(
            TranslationValidator::with_router(Router::new()),
        );
        let report = validator.validate_pair(&lifted, &reconstructed);

        assert_eq!(report.status, ReconstructionValidationStatus::Validated);
        assert_eq!(report.candidate, ReconstructionCandidateKind::StructuredTrustIr);
        assert_eq!(report.trust_level, TrustLevel::Partial);
        assert!(!report.is_proof_grade());
        assert!(report.forward.is_some());
        assert!(report.reverse.is_some());

        let record = report.to_record();
        assert_eq!(record.candidate, ReconstructionCandidateKind::StructuredTrustIr);
        assert_eq!(record.status, ReconstructionValidationStatus::Validated);
        assert_eq!(record.trust_level, TrustLevel::Partial);
        assert!(
            record
                .evidence
                .contains(&ReconstructionValidationEvidence::BidirectionalTrustIrRefinement)
        );
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::NoCheckedProofCertificate)
        );
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::NoBinaryProofObligation)
        );
        assert!(
            !record.evidence.contains(&ReconstructionValidationEvidence::MissingComparableTrustIr)
        );
        assert_non_proof_record(&report, &record, TrustLevel::Partial);
        assert_eq!(
            record.forward.as_ref().map(|forward| forward.direction),
            Some(ReconstructionValidationDirection::LiftedToOutput)
        );
        assert_eq!(
            record.reverse.as_ref().map(|reverse| reverse.direction),
            Some(ReconstructionValidationDirection::OutputToLifted)
        );
    }

    #[test]
    fn default_validator_does_not_validate_matching_structured_output() {
        let lifted = simple_binop("lifted", BinOp::Add);
        let reconstructed = simple_binop("candidate", BinOp::Add);

        let report = ReconstructionOutputValidator::new().validate_pair(&lifted, &reconstructed);

        assert_eq!(report.status, ReconstructionValidationStatus::Unknown);
        assert_eq!(report.candidate, ReconstructionCandidateKind::StructuredTrustIr);
        assert_eq!(report.trust_level, TrustLevel::Partial);
        assert!(!report.is_proof_grade());
        assert!(report.forward.is_some());
        assert!(
            report.diagnostics.iter().any(|msg| msg.contains("no trusted solver router supplied"))
        );
    }

    #[test]
    fn mismatched_function_summary_is_refuted_before_solver_dispatch() {
        let lifted = simple_binop("lifted", BinOp::Add);
        let mut reconstructed = simple_binop("candidate", BinOp::Add);
        reconstructed.body.arg_count = 1;

        let report = ReconstructionOutputValidator::new().validate_pair(&lifted, &reconstructed);

        assert_eq!(report.status, ReconstructionValidationStatus::Refuted);
        assert_eq!(report.candidate, ReconstructionCandidateKind::StructuredTrustIr);
        assert_eq!(report.trust_level, TrustLevel::Rejected);
        assert!(report.forward.is_none());
        assert!(report.diagnostics.iter().any(|msg| msg.contains("argument count mismatch")));

        let record = report.to_record();
        assert_eq!(record.status, ReconstructionValidationStatus::Refuted);
        assert_eq!(record.trust_level, TrustLevel::Rejected);
        assert_non_proof_record(&report, &record, TrustLevel::Rejected);
    }

    #[test]
    fn mismatched_refinement_is_not_validated() {
        let lifted = simple_binop("lifted", BinOp::Add);
        let reconstructed = simple_binop("candidate", BinOp::Sub);

        let validator = ReconstructionOutputValidator::with_translation_validator(
            TranslationValidator::with_router(Router::new()),
        );
        let report = validator.validate_pair(&lifted, &reconstructed);

        assert_eq!(report.status, ReconstructionValidationStatus::Refuted);
        assert_eq!(report.candidate, ReconstructionCandidateKind::StructuredTrustIr);
        assert_eq!(report.trust_level, TrustLevel::Rejected);
        assert!(!report.is_proof_grade());
        assert!(report.diagnostics.iter().any(|msg| msg.contains("refuted")));

        let record = report.to_record();
        assert_eq!(record.status, ReconstructionValidationStatus::Refuted);
        assert_eq!(record.trust_level, TrustLevel::Rejected);
        assert_non_proof_record(&report, &record, TrustLevel::Rejected);
    }

    #[test]
    fn text_only_claimed_validated_record_is_exploratory_non_proof() {
        let report = ReconstructionOutputValidation {
            target: DecompileTarget::Rust,
            candidate: ReconstructionCandidateKind::TextOnly,
            status: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            lifted_function: Some("lifted".to_string()),
            reconstructed_function: None,
            diagnostics: vec!["external metadata claimed validation".to_string()],
            forward: None,
            reverse: None,
        };

        let record = report.to_record();
        assert_eq!(record.status, ReconstructionValidationStatus::Unknown);
        assert_eq!(record.candidate, ReconstructionCandidateKind::TextOnly);
        assert!(record.forward.is_none());
        assert!(record.reverse.is_none());
        assert_non_proof_record(&report, &record, TrustLevel::Exploratory);
    }

    #[test]
    fn missing_direction_evidence_cannot_be_partial_or_proof_grade() {
        let report = ReconstructionOutputValidation {
            target: DecompileTarget::Rust,
            candidate: ReconstructionCandidateKind::StructuredTrustIr,
            status: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            lifted_function: Some("lifted".to_string()),
            reconstructed_function: Some("candidate".to_string()),
            diagnostics: vec!["incomplete direction evidence".to_string()],
            forward: Some(equivalent_result()),
            reverse: None,
        };

        let record = report.to_record();
        assert_eq!(record.status, ReconstructionValidationStatus::Unknown);
        assert_eq!(record.candidate, ReconstructionCandidateKind::StructuredTrustIr);
        assert!(
            !record
                .evidence
                .contains(&ReconstructionValidationEvidence::BidirectionalTrustIrRefinement)
        );
        assert!(
            !record.evidence.contains(&ReconstructionValidationEvidence::MissingComparableTrustIr)
        );
        assert!(record.forward.is_some());
        assert!(record.reverse.is_none());
        assert_non_proof_record(&report, &record, TrustLevel::Exploratory);
    }

    #[test]
    fn validated_rust_subset_candidate_is_not_validated_without_direction_evidence() {
        let report = ReconstructionOutputValidation {
            target: DecompileTarget::Rust,
            candidate: ReconstructionCandidateKind::ValidatedRustStrictSubset,
            status: ReconstructionValidationStatus::Validated,
            trust_level: TrustLevel::ProofGrade,
            lifted_function: Some("lifted".to_string()),
            reconstructed_function: Some("candidate".to_string()),
            diagnostics: vec!["strict subset preflight only".to_string()],
            forward: None,
            reverse: None,
        };

        let record = report.to_record();
        assert_eq!(record.status, ReconstructionValidationStatus::Unknown);
        assert_eq!(record.trust_level, TrustLevel::Exploratory);
        assert_eq!(record.candidate, ReconstructionCandidateKind::ValidatedRustStrictSubset);
        assert!(record.forward.is_none());
        assert!(record.reverse.is_none());
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::StrictRustSubsetEligible)
        );
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::NoCheckedProofCertificate)
        );
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::NoBinaryProofObligation)
        );
        assert_non_proof_record(&report, &record, TrustLevel::Exploratory);
    }

    #[test]
    fn strict_subset_output_metadata_is_classified_but_not_validated_without_compile_back_trust_ir()
    {
        let lifted = simple_binop("lifted", BinOp::Add);
        let output = DecompiledOutput {
            target: DecompileTarget::Rust,
            text: Some("pub fn add(a: i32, b: i32) -> i32 { a + b }".to_string()),
            validated_rust: Some(ValidatedRustReconstruction {
                status: ReconstructionValidationStatus::Unknown,
                trust_level: TrustLevel::Exploratory,
                eligibility: vec![RustReconstructionEligibility {
                    function: Some("add".to_string()),
                    eligible: true,
                    evidence: vec![ReconstructionValidationEvidence::StrictRustSubsetEligible],
                    ..Default::default()
                }],
                validation_records: vec![ReconstructionValidationRecord {
                    target: DecompileTarget::Rust,
                    function: Some("add".to_string()),
                    candidate: ReconstructionCandidateKind::ValidatedRustStrictSubset,
                    status: ReconstructionValidationStatus::Unknown,
                    trust_level: TrustLevel::Exploratory,
                    evidence: vec![ReconstructionValidationEvidence::StrictRustSubsetEligible],
                    ..Default::default()
                }],
                diagnostics: vec![],
            }),
            ..Default::default()
        };

        let report = ReconstructionOutputValidator::new().validate_output(
            Some(&lifted),
            None,
            Some(&output),
        );
        let record = report.to_record();

        assert_eq!(report.status, ReconstructionValidationStatus::Unknown);
        assert_eq!(record.candidate, ReconstructionCandidateKind::ValidatedRustStrictSubset);
        assert_eq!(record.status, ReconstructionValidationStatus::Unknown);
        assert_eq!(record.trust_level, TrustLevel::Exploratory);
        assert!(record.forward.is_none());
        assert!(record.reverse.is_none());
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::StrictRustSubsetEligible)
        );
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::NoCheckedProofCertificate)
        );
        assert!(
            record.evidence.contains(&ReconstructionValidationEvidence::NoBinaryProofObligation)
        );
    }

    #[test]
    fn records_keep_text_and_mismatches_unvalidated_while_structured_match_validates() {
        let lifted = simple_binop("lifted", BinOp::Add);
        let rust = rust_output(ReconstructionValidationStatus::NotAttempted);
        let validator = ReconstructionOutputValidator::with_translation_validator(
            TranslationValidator::with_router(Router::new()),
        );

        let text_only = validator.validate_output(Some(&lifted), None, Some(&rust)).to_record();
        assert_eq!(text_only.target, DecompileTarget::Rust);
        assert_eq!(text_only.candidate, ReconstructionCandidateKind::TextOnly);
        assert_eq!(text_only.status, ReconstructionValidationStatus::NotAttempted);
        assert_eq!(text_only.trust_level, TrustLevel::Exploratory);
        assert!(text_only.forward.is_none());
        assert!(text_only.reverse.is_none());

        let mismatched = validator
            .validate_output(
                Some(&lifted),
                Some(&simple_binop("candidate", BinOp::Sub)),
                Some(&rust),
            )
            .to_record();
        assert_eq!(mismatched.target, DecompileTarget::Rust);
        assert_eq!(mismatched.candidate, ReconstructionCandidateKind::StructuredTrustIr);
        assert_eq!(mismatched.status, ReconstructionValidationStatus::Refuted);
        assert_ne!(mismatched.status, ReconstructionValidationStatus::Validated);
        assert_eq!(mismatched.trust_level, TrustLevel::Rejected);

        let validated = validator
            .validate_output(
                Some(&lifted),
                Some(&simple_binop("candidate", BinOp::Add)),
                Some(&rust),
            )
            .to_record();
        assert_eq!(validated.target, DecompileTarget::Rust);
        assert_eq!(validated.candidate, ReconstructionCandidateKind::StructuredTrustIr);
        assert_eq!(validated.status, ReconstructionValidationStatus::Validated);
        assert_eq!(validated.trust_level, TrustLevel::Partial);
        assert!(
            validated
                .evidence
                .contains(&ReconstructionValidationEvidence::BidirectionalTrustIrRefinement)
        );
        assert!(validated.forward.is_some());
        assert!(validated.reverse.is_some());
        assert_ne!(validated.trust_level, TrustLevel::ProofGrade);
    }
}
