// trust-router/verifier_result.rs: Native verifier result adapter
//
// Common per-obligation result shape for Pipeline v2.

//! Native verifier result and obligation adapter.
//!
//! Pipeline v2 backends often start with a function-level result. This module
//! provides the per-obligation shape the rest of the router should use. When a
//! backend cannot identify which obligation its result belongs to, the adapter
//! keeps the backend artifact unattributed instead of copying the same result
//! onto every VC.

use std::collections::BTreeMap;
use std::fmt;

use sha2::{Digest, Sha256};
use trust_types::{
    ProofEvidence, ProofStrength, SourceSpan, VcKind, VerificationCondition, VerificationResult,
};

use crate::mir_router::MirStrategy;

/// Stable identity for a proof obligation within a function.
///
/// The fingerprint is derived from semantic VC content, not source locations.
/// The occurrence disambiguates repeated identical formulas in the same
/// function while keeping IDs stable for a deterministic VC generator.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StableObligationId {
    /// First 128 bits of SHA-256 over the canonical obligation payload.
    pub fingerprint: String,
    /// Zero-based occurrence of this fingerprint in the current function.
    pub occurrence: u32,
}

impl StableObligationId {
    /// Build a stable ID for a VC.
    #[must_use]
    pub fn for_vc(vc: &VerificationCondition, occurrence: u32) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(b"trust-router-obligation-v1\n");
        hasher.update(vc.function.as_str().as_bytes());
        hasher.update(b"\n");
        hasher.update(format!("{:?}", vc.kind).as_bytes());
        hasher.update(b"\n");
        hasher.update(vc.formula.to_smtlib().as_bytes());
        let digest = hasher.finalize();
        Self { fingerprint: hex_128(&digest[..16]), occurrence }
    }

    /// Build a stable function-level placeholder ID.
    ///
    /// This is used only when no VC-level obligations exist yet. It must not be
    /// used to attach one function-level backend verdict to multiple VCs.
    #[must_use]
    pub fn for_function_placeholder(
        def_path: &str,
        strategy: Option<&MirStrategy>,
        kind: &VcKind,
    ) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(b"trust-router-function-obligation-v1\n");
        hasher.update(def_path.as_bytes());
        hasher.update(b"\n");
        hasher.update(format!("{strategy:?}").as_bytes());
        hasher.update(b"\n");
        hasher.update(format!("{kind:?}").as_bytes());
        let digest = hasher.finalize();
        Self { fingerprint: hex_128(&digest[..16]), occurrence: 0 }
    }
}

impl fmt::Display for StableObligationId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.fingerprint, self.occurrence)
    }
}

/// Static metadata for an obligation before a verifier result is attached.
#[derive(Debug, Clone)]
pub struct ObligationDescriptor {
    /// Stable per-obligation identity.
    pub id: StableObligationId,
    /// Fully qualified function path.
    pub def_path: String,
    /// Short function name.
    pub function_name: String,
    /// Source location for diagnostics.
    pub span: SourceSpan,
    /// VC/property kind.
    pub kind: VcKind,
    /// MIR strategy that produced or handled this obligation.
    pub strategy: Option<MirStrategy>,
    /// Dense per-function order from the VC generator.
    pub ordinal: u32,
}

impl ObligationDescriptor {
    /// Create a descriptor from a VC and deterministic occurrence number.
    #[must_use]
    pub fn from_vc(vc: &VerificationCondition, occurrence: u32, ordinal: u32) -> Self {
        let def_path = vc.function.to_string();
        Self {
            id: StableObligationId::for_vc(vc, occurrence),
            function_name: short_name(&def_path),
            def_path,
            span: vc.location.clone(),
            kind: vc.kind.clone(),
            strategy: None,
            ordinal,
        }
    }

    /// Attach a MIR strategy.
    #[must_use]
    pub fn with_strategy(mut self, strategy: MirStrategy) -> Self {
        self.strategy = Some(strategy);
        self
    }
}

/// Where proof evidence attached to an obligation came from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObligationEvidenceProvenance {
    /// The v1 router or another per-VC path returned this result directly for
    /// the obligation.
    RouterAttributed,
    /// A native backend returned a result that was attributable to exactly this
    /// stable obligation ID.
    NativeBackend { verifier: String },
}

/// Proof evidence attached to a single obligation.
///
/// This is present only for `Proved` results. Unknown, timeout, unsupported,
/// and unattributed function-level artifacts intentionally do not produce
/// per-obligation evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ObligationProofEvidence {
    /// Backend or router that produced the proof evidence.
    pub verifier: String,
    /// Whether the evidence came from a native backend or already-attributed
    /// router result.
    pub provenance: ObligationEvidenceProvenance,
    /// Legacy proof strength preserved from the backend result.
    pub strength: ProofStrength,
    /// Normalized evidence model derived from `strength`.
    pub evidence: ProofEvidence,
    /// Raw solver/native certificate bytes, when available.
    pub proof_certificate: Option<Vec<u8>>,
    /// Warnings emitted while producing this proof.
    pub solver_warnings: Option<Vec<String>>,
}

impl ObligationProofEvidence {
    /// Build obligation evidence from a proved result.
    #[must_use]
    pub fn from_result(
        verifier: impl Into<String>,
        provenance: ObligationEvidenceProvenance,
        result: &VerificationResult,
    ) -> Option<Self> {
        let VerificationResult::Proved { strength, proof_certificate, solver_warnings, .. } =
            result
        else {
            return None;
        };

        Some(Self {
            verifier: verifier.into(),
            provenance,
            strength: strength.clone(),
            evidence: strength.clone().into(),
            proof_certificate: proof_certificate.clone(),
            solver_warnings: solver_warnings.clone(),
        })
    }
}

/// Per-obligation verifier result.
#[derive(Debug, Clone)]
pub struct VerifierObligationResult {
    /// Obligation metadata and stable ID.
    pub obligation: ObligationDescriptor,
    /// Result for this obligation only.
    pub result: VerificationResult,
    /// Proof evidence for this obligation only, when the result is proved.
    pub evidence: Option<ObligationProofEvidence>,
}

impl VerifierObligationResult {
    /// Create a new per-obligation result.
    #[must_use]
    pub fn new(obligation: ObligationDescriptor, result: VerificationResult) -> Self {
        let evidence = ObligationProofEvidence::from_result(
            result.solver_name(),
            ObligationEvidenceProvenance::RouterAttributed,
            &result,
        );
        Self { obligation, result, evidence }
    }

    /// Create a per-obligation result attributed to one native backend.
    #[must_use]
    pub fn new_native(
        obligation: ObligationDescriptor,
        verifier: impl Into<String>,
        result: VerificationResult,
    ) -> Self {
        let verifier = verifier.into();
        let evidence = ObligationProofEvidence::from_result(
            verifier.clone(),
            ObligationEvidenceProvenance::NativeBackend { verifier },
            &result,
        );
        Self { obligation, result, evidence }
    }

    /// Whether the obligation was proved.
    #[must_use]
    pub fn is_proved(&self) -> bool {
        self.result.is_proved()
    }

    /// Whether the obligation failed.
    #[must_use]
    pub fn is_failed(&self) -> bool {
        self.result.is_failed()
    }
}

/// Backend artifact that could not be attributed to one stable obligation ID.
#[derive(Debug, Clone)]
pub struct UnattributedVerifierArtifact {
    /// Native verifier name.
    pub verifier: String,
    /// Function-level result from the native verifier.
    pub result: VerificationResult,
    /// Why this artifact was not attached to individual obligations.
    pub reason: String,
}

/// Function-level batch of per-obligation verifier results.
#[derive(Debug, Clone)]
pub struct VerifierFunctionResult {
    /// Fully qualified function path.
    pub def_path: String,
    /// Short function name.
    pub function_name: String,
    /// Per-obligation results. Mixed proved/failed/unknown statuses are kept
    /// independently here.
    pub obligations: Vec<VerifierObligationResult>,
    /// Function summary derived from `obligations` plus unattributed artifacts.
    pub summary: VerifierResultSummary,
    /// Backend outputs that lacked a stable obligation ID.
    pub unattributed: Vec<UnattributedVerifierArtifact>,
}

impl VerifierFunctionResult {
    /// Build from already attributed per-obligation results.
    #[must_use]
    pub fn from_obligation_results(
        def_path: String,
        obligations: Vec<VerifierObligationResult>,
    ) -> Self {
        let function_name = short_name(&def_path);
        let summary = VerifierResultSummary::from_results(&obligations, &[]);
        Self { def_path, function_name, obligations, summary, unattributed: Vec::new() }
    }

    /// Build from v1 `(VC, result)` pairs.
    #[must_use]
    pub fn from_v1_results(results: Vec<(VerificationCondition, VerificationResult)>) -> Vec<Self> {
        let descriptors = descriptors_for_vcs(results.iter().map(|(vc, _)| vc), None);
        let mut by_function: BTreeMap<String, Vec<VerifierObligationResult>> = BTreeMap::new();

        for ((_, result), descriptor) in results.into_iter().zip(descriptors) {
            by_function
                .entry(descriptor.def_path.clone())
                .or_default()
                .push(VerifierObligationResult::new(descriptor, result));
        }

        by_function
            .into_iter()
            .map(|(def_path, obligations)| Self::from_obligation_results(def_path, obligations))
            .collect()
    }

    /// Build from a single native function-level result.
    ///
    /// If exactly one obligation is present, the result can be attributed
    /// precisely. If multiple obligations are present, the result is kept as an
    /// unattributed artifact and every obligation receives an independent
    /// Unknown result explaining that the backend did not provide IDs.
    #[must_use]
    pub fn from_function_level_result(
        def_path: String,
        verifier: impl Into<String>,
        obligations: Vec<ObligationDescriptor>,
        result: VerificationResult,
    ) -> Self {
        let verifier = verifier.into();
        if obligations.len() == 1 {
            let attributed = vec![VerifierObligationResult::new_native(
                obligations.into_iter().next().expect("obligations.len() checked above"),
                verifier,
                result,
            )];
            return Self::from_obligation_results(def_path, attributed);
        }

        let reason = format!(
            "{verifier} returned one function-level result for {} obligations without stable per-obligation IDs",
            obligations.len()
        );
        let unknowns = obligations
            .into_iter()
            .map(|obligation| {
                VerifierObligationResult::new(
                    obligation,
                    VerificationResult::Unknown {
                        solver: verifier.clone().into(),
                        time_ms: result.time_ms(),
                        reason: reason.clone(),
                    },
                )
            })
            .collect::<Vec<_>>();
        let unattributed =
            vec![UnattributedVerifierArtifact { verifier, result, reason: reason.clone() }];
        let function_name = short_name(&def_path);
        let summary = VerifierResultSummary::from_results(&unknowns, &unattributed);
        Self { def_path, function_name, obligations: unknowns, summary, unattributed }
    }

    /// Adapt a native trust_mc result.
    #[must_use]
    pub fn from_trust_mc_result(
        def_path: String,
        obligations: Vec<ObligationDescriptor>,
        result: &trust_bmc::TrustMcResult,
    ) -> Self {
        Self::from_function_level_result(
            def_path,
            "trust-mc-lib",
            obligations,
            result.to_verification_result(),
        )
    }

    /// Adapt a native trust_wp result.
    #[must_use]
    pub fn from_trust_wp_result(
        def_path: String,
        obligations: Vec<ObligationDescriptor>,
        result: &trust_wp::TrustWpResult,
    ) -> Self {
        Self::from_function_level_result(
            def_path,
            "trust-wp-lib",
            obligations,
            result.to_verification_result(),
        )
    }
}

/// Summary counts for a function result.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct VerifierResultSummary {
    /// Number of attributed obligations.
    pub total: usize,
    /// Number of attributed proved obligations.
    pub proved: usize,
    /// Number of attributed failed obligations.
    pub failed: usize,
    /// Number of attributed unknown obligations.
    pub unknown: usize,
    /// Number of attributed timeout obligations.
    pub timeout: usize,
    /// Number of backend failures that could not be attributed to a stable ID.
    pub unattributed_failed: usize,
    /// Number of backend unknown/timeout results that could not be attributed.
    pub unattributed_unknown: usize,
    /// Number of backend proofs that could not be attributed to a stable ID.
    ///
    /// These are not counted as proved obligations; they remain unresolved
    /// until the backend supplies per-obligation IDs.
    pub unattributed_proved: usize,
}

impl VerifierResultSummary {
    /// Compute summary counts from per-obligation results.
    #[must_use]
    pub fn from_results(
        results: &[VerifierObligationResult],
        unattributed: &[UnattributedVerifierArtifact],
    ) -> Self {
        let mut summary = Self { total: results.len(), ..Self::default() };

        for result in results {
            match result.result {
                VerificationResult::Proved { .. } => summary.proved += 1,
                VerificationResult::Failed { .. } => summary.failed += 1,
                VerificationResult::Unknown { .. } => summary.unknown += 1,
                VerificationResult::Timeout { .. } => summary.timeout += 1,
                _ => summary.unknown += 1,
            }
        }

        for artifact in unattributed {
            match artifact.result {
                VerificationResult::Proved { .. } => summary.unattributed_proved += 1,
                VerificationResult::Failed { .. } => summary.unattributed_failed += 1,
                VerificationResult::Unknown { .. } | VerificationResult::Timeout { .. } => {
                    summary.unattributed_unknown += 1;
                }
                _ => {}
            }
        }

        summary
    }

    /// Returns true if any obligation or native artifact is unresolved.
    #[must_use]
    pub fn has_unresolved(self) -> bool {
        self.failed > 0
            || self.unknown > 0
            || self.timeout > 0
            || self.unattributed_failed > 0
            || self.unattributed_unknown > 0
            || self.unattributed_proved > 0
    }

    /// Returns true if all attributed obligations were proved and no
    /// unattributed problem remains.
    #[must_use]
    pub fn is_fully_verified(self) -> bool {
        self.total > 0 && self.proved == self.total && !self.has_unresolved()
    }
}

/// Build stable descriptors for a VC batch.
#[must_use]
pub fn descriptors_for_vcs<'a>(
    vcs: impl IntoIterator<Item = &'a VerificationCondition>,
    strategy: Option<MirStrategy>,
) -> Vec<ObligationDescriptor> {
    let mut seen: BTreeMap<String, u32> = BTreeMap::new();
    vcs.into_iter()
        .enumerate()
        .map(|(ordinal, vc)| {
            let base = StableObligationId::for_vc(vc, 0).fingerprint;
            let occurrence = seen.entry(base).and_modify(|n| *n += 1).or_insert(0);
            let descriptor = ObligationDescriptor::from_vc(vc, *occurrence, ordinal as u32);
            match &strategy {
                Some(strategy) => descriptor.with_strategy(strategy.clone()),
                None => descriptor,
            }
        })
        .collect()
}

/// Create a single placeholder descriptor when no VC exists yet.
#[must_use]
pub fn function_placeholder_obligation(
    def_path: String,
    span: SourceSpan,
    kind: VcKind,
    strategy: Option<MirStrategy>,
) -> ObligationDescriptor {
    ObligationDescriptor {
        id: StableObligationId::for_function_placeholder(&def_path, strategy.as_ref(), &kind),
        function_name: short_name(&def_path),
        def_path,
        span,
        kind,
        strategy,
        ordinal: 0,
    }
}

fn short_name(def_path: &str) -> String {
    def_path.rsplit("::").next().unwrap_or(def_path).to_string()
}

fn hex_128(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(32);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, ProofStrength, Sort};

    use super::*;

    fn vc(function: &str, kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: function.into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
        }
    }

    fn proved(strength: ProofStrength) -> VerificationResult {
        VerificationResult::Proved {
            solver: "test".into(),
            time_ms: 7,
            strength,
            proof_certificate: Some(vec![1, 2, 3]),
            solver_warnings: Some(vec!["warn".to_string()]),
            native_proof_envelope: None,
        }
    }

    #[test]
    fn stable_ids_ignore_source_span_but_keep_duplicate_occurrences() {
        let mut first = vc("m::f", VcKind::DivisionByZero, Formula::Var("x".into(), Sort::Int));
        let mut second = first.clone();
        first.location.line_start = 10;
        second.location.line_start = 99;

        let descriptors = descriptors_for_vcs([&first, &second], None);

        assert_eq!(descriptors[0].id.fingerprint, descriptors[1].id.fingerprint);
        assert_eq!(descriptors[0].id.occurrence, 0);
        assert_eq!(descriptors[1].id.occurrence, 1);
    }

    #[test]
    fn v1_adapter_preserves_mixed_results_per_obligation() {
        let vcs = vec![
            (
                vc("m::f", VcKind::DivisionByZero, Formula::Bool(false)),
                proved(ProofStrength::smt_unsat()),
            ),
            (
                vc("m::f", VcKind::Postcondition, Formula::Bool(true)),
                VerificationResult::Failed {
                    solver: "test".into(),
                    time_ms: 3,
                    counterexample: None,
                },
            ),
            (
                vc("m::f", VcKind::Assertion { message: "a".into() }, Formula::Bool(true)),
                VerificationResult::Unknown {
                    solver: "test".into(),
                    time_ms: 4,
                    reason: "quantifiers".into(),
                },
            ),
        ];

        let functions = VerifierFunctionResult::from_v1_results(vcs);

        assert_eq!(functions.len(), 1);
        let summary = functions[0].summary;
        assert_eq!(summary.total, 3);
        assert_eq!(summary.proved, 1);
        assert_eq!(summary.failed, 1);
        assert_eq!(summary.unknown, 1);
        assert!(summary.has_unresolved());
    }

    #[test]
    fn function_level_result_is_not_smeared_across_multiple_obligations() {
        let vcs = vec![
            vc("m::f", VcKind::DivisionByZero, Formula::Bool(false)),
            vc("m::f", VcKind::Postcondition, Formula::Bool(true)),
        ];
        let descriptors = descriptors_for_vcs(&vcs, Some(MirStrategy::BoundedModelCheck));

        let function_result = VerifierFunctionResult::from_function_level_result(
            "m::f".to_string(),
            "native-test",
            descriptors,
            proved(ProofStrength::pdr()),
        );

        assert_eq!(function_result.summary.total, 2);
        assert_eq!(function_result.summary.proved, 0);
        assert_eq!(function_result.summary.unknown, 2);
        assert_eq!(function_result.summary.unattributed_proved, 1);
        assert_eq!(function_result.unattributed.len(), 1);
        assert!(function_result.summary.has_unresolved());
        assert!(matches!(
            function_result.obligations[0].result,
            VerificationResult::Unknown { .. }
        ));
        assert!(function_result.obligations.iter().all(|obligation| obligation.evidence.is_none()));
    }

    #[test]
    fn single_obligation_keeps_native_strength_and_artifacts() {
        let vcs = vec![vc("m::f", VcKind::DivisionByZero, Formula::Bool(false))];
        let descriptors = descriptors_for_vcs(&vcs, Some(MirStrategy::BoundedModelCheck));

        let function_result = VerifierFunctionResult::from_function_level_result(
            "m::f".to_string(),
            "native-test",
            descriptors,
            proved(ProofStrength::pdr()),
        );

        assert_eq!(function_result.summary.proved, 1);
        assert!(function_result.unattributed.is_empty());
        let evidence = function_result.obligations[0].evidence.as_ref().expect("native evidence");
        assert_eq!(evidence.verifier, "native-test");
        assert_eq!(evidence.strength, ProofStrength::pdr());
        assert_eq!(evidence.evidence, trust_types::ProofEvidence::from(ProofStrength::pdr()));
        assert_eq!(
            evidence.provenance,
            ObligationEvidenceProvenance::NativeBackend { verifier: "native-test".to_string() }
        );
        assert_eq!(evidence.proof_certificate.as_deref(), Some(&[1, 2, 3][..]));
        assert_eq!(evidence.solver_warnings.as_ref().map(Vec::len), Some(1));
        match &function_result.obligations[0].result {
            VerificationResult::Proved { strength, proof_certificate, solver_warnings, .. } => {
                assert_eq!(*strength, ProofStrength::pdr());
                assert_eq!(proof_certificate.as_deref(), Some(&[1, 2, 3][..]));
                assert_eq!(solver_warnings.as_ref().map(Vec::len), Some(1));
            }
            other => panic!("expected proved result, got {other:?}"),
        }
    }

    #[test]
    fn unattributed_failure_is_visible_in_summary() {
        let vcs = vec![
            vc("m::f", VcKind::DivisionByZero, Formula::Bool(false)),
            vc("m::f", VcKind::Postcondition, Formula::Bool(true)),
        ];
        let descriptors = descriptors_for_vcs(&vcs, Some(MirStrategy::ContractVerification));

        let function_result = VerifierFunctionResult::from_function_level_result(
            "m::f".to_string(),
            "native-test",
            descriptors,
            VerificationResult::Failed {
                solver: "native-test".into(),
                time_ms: 5,
                counterexample: None,
            },
        );

        assert_eq!(function_result.summary.failed, 0);
        assert_eq!(function_result.summary.unattributed_failed, 1);
        assert!(function_result.summary.has_unresolved());
    }

    #[test]
    fn unknown_unsupported_obligation_never_gets_proof_evidence() {
        let vcs = vec![vc(
            "m::f",
            VcKind::UnsupportedMir {
                kind: "asm".to_string(),
                detail: "inline assembly is not modelled".to_string(),
            },
            Formula::Bool(true),
        )];
        let descriptors = descriptors_for_vcs(&vcs, Some(MirStrategy::BoundedModelCheck));

        let function_result = VerifierFunctionResult::from_function_level_result(
            "m::f".to_string(),
            "native-test",
            descriptors,
            VerificationResult::Unknown {
                solver: "native-test".into(),
                time_ms: 2,
                reason: "unsupported MIR: inline assembly is not modelled".to_string(),
            },
        );

        assert_eq!(function_result.summary.total, 1);
        assert_eq!(function_result.summary.proved, 0);
        assert_eq!(function_result.summary.unknown, 1);
        assert!(!function_result.summary.is_fully_verified());
        assert!(function_result.obligations[0].evidence.is_none());
        assert!(matches!(
            function_result.obligations[0].result,
            VerificationResult::Unknown { .. }
        ));
    }
}
