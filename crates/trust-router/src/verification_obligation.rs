// trust-router/verification_obligation.rs: Pipeline v2 obligation adapter
//
// Maps external tool results (trust-mc-lib, trust-wp-lib) back to
// per-obligation identities so the Trust report pipeline can attribute
// verification outcomes to specific source spans, VcKinds, and functions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Verification obligation adapter for Pipeline v2.
//!
//! The v1 pipeline produces `VerificationCondition` objects (with a `Formula`)
//! that flow through the `Router`. The v2 pipeline operates at the MIR level,
//! dispatching whole functions to trust-mc-lib or trust-wp-lib. These external tools
//! return their own result types (`TrustMcResult`, `TrustWpResult`), which need to
//! be mapped back to per-obligation identities for the report pipeline.
//!
//! `VerificationObligation` is the bridge: it captures the function identity,
//! source span, strategy used, and the resulting `VerificationResult` in a
//! single struct that the report pipeline can consume uniformly regardless
//! of which pipeline (v1 or v2) produced it.

use trust_types::fx::FxHashMap;
use trust_types::{SourceSpan, VcKind, VerificationResult};

use crate::mir_router::MirStrategy;
use crate::verifier_result::{
    ObligationDescriptor, ObligationEvidenceProvenance, ObligationProofEvidence,
    StableObligationId, VerifierFunctionResult, descriptors_for_vcs,
};

/// A verification obligation with its result, produced by the v2 pipeline.
///
/// Unlike the v1 `VerificationCondition` (which carries a `Formula` for the
/// solver), this type is result-oriented: it records what was verified, how,
/// and what the outcome was. It serves as the common output type for both
/// pipelines, enabling unified reporting and comparison.
#[derive(Debug, Clone)]
pub struct VerificationObligation {
    /// Stable per-obligation identity.
    pub id: StableObligationId,

    /// Fully qualified function path (e.g., `my_crate::my_module::my_fn`).
    pub def_path: String,

    /// Short function name for display.
    pub function_name: String,

    /// Source location of the function or obligation.
    pub span: SourceSpan,

    /// The kind of verification obligation (safety, contract, overflow, etc.).
    pub kind: VcKind,

    /// The MIR-level strategy that was used to verify this obligation.
    /// `None` if this obligation came from the v1 pipeline.
    pub strategy: Option<MirStrategy>,

    /// The verification result.
    result: VerificationResult,

    /// Proof evidence for this obligation only, when the result is proved.
    pub evidence: Option<ObligationProofEvidence>,
}

impl VerificationObligation {
    /// Create a new obligation without a result (defaults to Unknown).
    #[must_use]
    pub fn new(def_path: String, function_name: String, span: SourceSpan, kind: VcKind) -> Self {
        let id = StableObligationId::for_function_placeholder(&def_path, None, &kind);
        Self {
            id,
            def_path,
            function_name,
            span,
            kind,
            strategy: None,
            result: VerificationResult::Unknown {
                solver: "pending".into(),
                time_ms: 0,
                reason: "not yet dispatched".to_string(),
            },
            evidence: None,
        }
    }

    /// Attach a verification result to this obligation.
    #[must_use]
    pub fn with_result(mut self, result: VerificationResult) -> Self {
        self.evidence = ObligationProofEvidence::from_result(
            result.solver_name(),
            ObligationEvidenceProvenance::RouterAttributed,
            &result,
        );
        self.result = result;
        self
    }

    /// Attach a MIR strategy to this obligation.
    #[must_use]
    pub fn with_strategy(mut self, strategy: MirStrategy) -> Self {
        self.strategy = Some(strategy);
        self
    }

    /// Get the verification result.
    #[must_use]
    pub fn result(&self) -> &VerificationResult {
        &self.result
    }

    /// Get per-obligation proof evidence, if this obligation was proved.
    #[must_use]
    pub fn evidence(&self) -> Option<&ObligationProofEvidence> {
        self.evidence.as_ref()
    }

    /// Returns `true` if this obligation was proved.
    #[must_use]
    pub fn is_proved(&self) -> bool {
        self.result.is_proved()
    }

    /// Returns `true` if this obligation failed (counterexample found).
    #[must_use]
    pub fn is_failed(&self) -> bool {
        self.result.is_failed()
    }

    /// Returns the solver name from the result, if available.
    #[must_use]
    pub fn solver_name(&self) -> &str {
        match &self.result {
            VerificationResult::Proved { solver, .. }
            | VerificationResult::Failed { solver, .. }
            | VerificationResult::Unknown { solver, .. }
            | VerificationResult::Timeout { solver, .. } => solver.as_str(),
            _ => "unknown",
        }
    }

    /// Convert a batch of v2 MirRouter results into `VerificationObligation`s.
    ///
    /// Each tuple from `MirRouter::verify_all` is mapped to an obligation
    /// with the appropriate VcKind inferred from the MirStrategy.
    pub fn from_mir_results(
        results: Vec<(String, MirStrategy, VerificationResult)>,
        spans: &FxHashMap<String, SourceSpan>,
    ) -> Vec<Self> {
        results
            .into_iter()
            .map(|(name, strategy, result)| {
                let span = spans.get(&name).cloned().unwrap_or_default();
                let kind = vc_kind_for_strategy(&strategy);
                Self {
                    id: StableObligationId::for_function_placeholder(&name, Some(&strategy), &kind),
                    def_path: name.clone(),
                    function_name: short_name(&name),
                    span,
                    kind,
                    strategy: Some(strategy),
                    evidence: ObligationProofEvidence::from_result(
                        result.solver_name(),
                        ObligationEvidenceProvenance::RouterAttributed,
                        &result,
                    ),
                    result,
                }
            })
            .collect()
    }

    /// Convert a batch of v1 Router results into `VerificationObligation`s.
    ///
    /// Each `(VerificationCondition, VerificationResult)` pair from
    /// `Router::verify_all` is mapped to an obligation with no MirStrategy.
    pub fn from_v1_results(
        results: Vec<(trust_types::VerificationCondition, VerificationResult)>,
    ) -> Vec<Self> {
        let descriptors = descriptors_for_vcs(results.iter().map(|(vc, _)| vc), None);
        results
            .into_iter()
            .zip(descriptors)
            .map(|((_, result), descriptor)| {
                let evidence = ObligationProofEvidence::from_result(
                    result.solver_name(),
                    ObligationEvidenceProvenance::RouterAttributed,
                    &result,
                );
                Self::from_descriptor_result(descriptor, result, evidence)
            })
            .collect()
    }

    /// Convert native per-obligation function results into legacy obligations.
    #[must_use]
    pub fn from_verifier_function_result(function_result: VerifierFunctionResult) -> Vec<Self> {
        function_result
            .obligations
            .into_iter()
            .map(|obligation_result| {
                Self::from_descriptor_result(
                    obligation_result.obligation,
                    obligation_result.result,
                    obligation_result.evidence,
                )
            })
            .collect()
    }

    /// Convert multiple native function results into legacy obligations.
    #[must_use]
    pub fn from_verifier_function_results(
        function_results: Vec<VerifierFunctionResult>,
    ) -> Vec<Self> {
        function_results.into_iter().flat_map(Self::from_verifier_function_result).collect()
    }

    fn from_descriptor_result(
        descriptor: ObligationDescriptor,
        result: VerificationResult,
        evidence: Option<ObligationProofEvidence>,
    ) -> Self {
        Self {
            id: descriptor.id,
            def_path: descriptor.def_path,
            function_name: descriptor.function_name,
            span: descriptor.span,
            kind: descriptor.kind,
            strategy: descriptor.strategy,
            evidence,
            result,
        }
    }
}

/// Infer a VcKind from a MirStrategy (crate-internal).
///
/// Used by `Router::verify_function_v2` to map MirStrategy to VcKind.
pub(crate) fn vc_kind_for_mir_strategy(strategy: &MirStrategy) -> VcKind {
    vc_kind_for_strategy(strategy)
}

/// Internal helper: infer a VcKind from a MirStrategy.
///
/// Since v2 strategies operate at the function level rather than the formula
/// level, we map each strategy to the broadest applicable VcKind.
fn vc_kind_for_strategy(strategy: &MirStrategy) -> VcKind {
    match strategy {
        MirStrategy::BoundedModelCheck => {
            VcKind::Assertion { message: "bounded model check (trust-mc-lib)".to_string() }
        }
        MirStrategy::ContractVerification => VcKind::Postcondition,
        MirStrategy::UnsafeAudit => VcKind::UnsafeOperation {
            desc: "unsafe audit (trust-mc-lib + trust-wp-lib)".to_string(),
        },
        MirStrategy::SeparationLogic => {
            VcKind::Assertion { message: "separation logic safety".to_string() }
        }
        MirStrategy::DataRace => VcKind::DataRace {
            variable: String::new(),
            thread_a: String::new(),
            thread_b: String::new(),
        },
        MirStrategy::FFIBoundary => VcKind::FfiBoundaryViolation {
            callee: String::new(),
            desc: "FFI boundary verification".to_string(),
        },
        MirStrategy::Portfolio(_) => {
            VcKind::Assertion { message: "portfolio strategy".to_string() }
        }
        #[cfg(feature = "trust-cg-backend")]
        MirStrategy::TrustCgCodegen => {
            VcKind::Assertion { message: "trust-cg verified codegen".to_string() }
        }
        MirStrategy::V1Fallback => {
            VcKind::Assertion { message: "v1 pipeline fallback".to_string() }
        }
    }
}

/// Extract a short function name from a fully qualified path.
fn short_name(def_path: &str) -> String {
    def_path.rsplit("::").next().unwrap_or(def_path).to_string()
}

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;

    #[test]
    fn test_obligation_creation() {
        let ob = VerificationObligation::new(
            "test::my_fn".to_string(),
            "my_fn".to_string(),
            SourceSpan::default(),
            VcKind::Assertion { message: "safety check".to_string() },
        );
        assert!(!ob.is_proved());
        assert!(!ob.is_failed());
        assert_eq!(ob.solver_name(), "pending");
        assert!(ob.strategy.is_none());
    }

    #[test]
    fn test_obligation_with_result() {
        let ob = VerificationObligation::new(
            "test::proved_fn".to_string(),
            "proved_fn".to_string(),
            SourceSpan::default(),
            VcKind::DivisionByZero,
        )
        .with_result(VerificationResult::Proved {
            solver: "trust-mc-lib".into(),
            time_ms: 42,
            strength: ProofStrength::bounded(100),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        })
        .with_strategy(MirStrategy::BoundedModelCheck);

        assert!(ob.is_proved());
        assert!(!ob.is_failed());
        assert_eq!(ob.solver_name(), "trust-mc-lib");
        assert_eq!(ob.strategy, Some(MirStrategy::BoundedModelCheck));
        let evidence = ob.evidence().expect("proved obligation evidence");
        assert_eq!(evidence.strength, ProofStrength::bounded(100));
        assert_eq!(evidence.provenance, ObligationEvidenceProvenance::RouterAttributed);
    }

    #[test]
    fn test_obligation_failed() {
        let ob = VerificationObligation::new(
            "test::bad_fn".to_string(),
            "bad_fn".to_string(),
            SourceSpan::default(),
            VcKind::Postcondition,
        )
        .with_result(VerificationResult::Failed {
            solver: "trust-wp-lib".into(),
            time_ms: 10,
            counterexample: None,
        });

        assert!(!ob.is_proved());
        assert!(ob.is_failed());
        assert_eq!(ob.solver_name(), "trust-wp-lib");
    }

    #[test]
    fn test_from_v1_results() {
        let vc = trust_types::VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "v1::div_check".into(),
            location: SourceSpan::default(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let result = VerificationResult::Proved {
            solver: "constant-folder".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };

        let obligations = VerificationObligation::from_v1_results(vec![(vc, result)]);
        assert_eq!(obligations.len(), 1);
        assert!(obligations[0].is_proved());
        assert_eq!(obligations[0].function_name, "div_check");
        assert!(obligations[0].strategy.is_none());
        assert!(obligations[0].evidence().is_some());
    }

    #[test]
    fn test_from_mir_results() {
        let results = vec![
            (
                "test::loopy".to_string(),
                MirStrategy::BoundedModelCheck,
                VerificationResult::Proved {
                    solver: "trust-mc-lib".into(),
                    time_ms: 50,
                    strength: ProofStrength::bounded(100),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
            (
                "test::contracted".to_string(),
                MirStrategy::ContractVerification,
                VerificationResult::Failed {
                    solver: "trust-wp-lib".into(),
                    time_ms: 30,
                    counterexample: None,
                },
            ),
        ];

        let spans = FxHashMap::default();
        let obligations = VerificationObligation::from_mir_results(results, &spans);
        assert_eq!(obligations.len(), 2);
        assert!(obligations[0].is_proved());
        assert_eq!(obligations[0].strategy, Some(MirStrategy::BoundedModelCheck));
        assert!(obligations[0].evidence().is_some());
        assert!(obligations[1].is_failed());
        assert_eq!(obligations[1].strategy, Some(MirStrategy::ContractVerification));
        assert!(obligations[1].evidence().is_none());
    }

    #[test]
    fn native_evidence_survives_verifier_function_conversion() {
        let vc = trust_types::VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "native::div_check".into(),
            location: SourceSpan::default(),
            formula: trust_types::Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let descriptors = descriptors_for_vcs([&vc], Some(MirStrategy::BoundedModelCheck));
        let function_result = VerifierFunctionResult::from_function_level_result(
            "native::div_check".to_string(),
            "trust-mc-lib",
            descriptors,
            VerificationResult::Proved {
                solver: "trust-mc-lib".into(),
                time_ms: 11,
                strength: ProofStrength::bounded(12),
                proof_certificate: Some(vec![9]),
                solver_warnings: None,
                native_proof_envelope: None,
            },
        );

        let obligations = VerificationObligation::from_verifier_function_result(function_result);

        assert_eq!(obligations.len(), 1);
        let evidence = obligations[0].evidence().expect("native evidence");
        assert_eq!(evidence.strength, ProofStrength::bounded(12));
        assert_eq!(
            evidence.provenance,
            ObligationEvidenceProvenance::NativeBackend { verifier: "trust-mc-lib".to_string() }
        );
        assert_eq!(evidence.proof_certificate.as_deref(), Some(&[9][..]));
    }

    #[test]
    fn test_short_name() {
        assert_eq!(short_name("my_crate::my_mod::my_fn"), "my_fn");
        assert_eq!(short_name("simple"), "simple");
        assert_eq!(short_name("a::b::c::d"), "d");
    }

    #[test]
    fn test_vc_kind_for_strategy() {
        assert!(matches!(
            vc_kind_for_strategy(&MirStrategy::ContractVerification),
            VcKind::Postcondition
        ));
        assert!(matches!(
            vc_kind_for_strategy(&MirStrategy::BoundedModelCheck),
            VcKind::Assertion { .. }
        ));
        assert!(matches!(
            vc_kind_for_strategy(&MirStrategy::UnsafeAudit),
            VcKind::UnsafeOperation { .. }
        ));
        assert!(matches!(vc_kind_for_strategy(&MirStrategy::DataRace), VcKind::DataRace { .. }));
        assert!(matches!(
            vc_kind_for_strategy(&MirStrategy::FFIBoundary),
            VcKind::FfiBoundaryViolation { .. }
        ));
    }
}
