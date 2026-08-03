// trust-clean/integration.rs: Bridge between clean CertificationPipeline and trust-proof-cert
//
// Connects the clean certification pipeline (CertificationPipeline, TrustProofCertificate)
// with the proof certificate store (ProofCertificate, CertificateChain, CertificateStore)
// from trust-proof-cert. This enables end-to-end proof-record transport:
//
//   ay proves -> clean checks -> replayable Clean payload + public record
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_proof_cert::{
    CertificateChain, CertificateStore, ChainStep, ChainStepType, FunctionHash, ProofCertificate,
    SolverInfo, VcSnapshot,
};
use trust_types::stable_sha256_hex;
use trust_types::{VerificationCondition, VerificationResult};

use crate::certification::{CertificationPipeline, CertificationResult};
use crate::error::CertificateError;
use crate::reconstruction::SolverProof;

/// Preserve the live verdict until Clean evidence has an authoritative carrier.
///
/// A [`CertificationResult::Certified`] contains a VC-bound
/// [`crate::TrustProofCertificate`], but [`VerificationResult::Proved`] exposes
/// only an untyped `proof_certificate` byte vector that already belongs to the
/// solver.  The old implementation discarded the Clean certificate, retained
/// those unrelated solver bytes, and changed only the assurance label.  Such a
/// result cannot be replayed at downstream `Certified` consumers and therefore
/// must not be minted.
///
/// This compatibility seam is deliberately an identity for every certification
/// outcome. The separate [`PipelineOutput`] record path transports the actual
/// Clean payload for independent replay; [`CertificateStore`] retains only
/// compatibility metadata and never inherits that authority. A future live upgrade
/// requires a typed envelope containing the exact VC digest, Clean goal/context,
/// proof term, and replay result.
#[must_use]
pub fn apply_certification(
    result: VerificationResult,
    _cert: &CertificationResult,
) -> VerificationResult {
    result
}

/// Compatibility wrapper for the former live-upgrade API.
///
/// It returns the verdict unchanged for the same evidence-transport reason as
/// [`apply_certification`].  Callers that need a durable Clean certificate must
/// use the certificate-producing pipeline rather than an assurance-only result.
#[must_use]
pub fn certify_and_upgrade(
    _vc: &VerificationCondition,
    result: VerificationResult,
    _solver_proof: &SolverProof,
) -> VerificationResult {
    result
}

/// How the Clean payload in a [`PipelineOutput::Record`] was produced.
///
/// This is provenance metadata, not a public proof capability. A consumer must
/// call [`crate::verify_certificate`] against its current VC before granting
/// authority, even for `KernelChecked` records.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum RecordVerification {
    /// This process replayed the exact payload through the Clean kernel.
    KernelChecked,
    /// The payload was packaged without a Clean-kernel replay.
    Unchecked,
}

/// Result of the end-to-end record pipeline.
///
/// A public [`ProofCertificate`] is retained for compatibility/indexing, while
/// `clean_payload` preserves the exact VC-bound term needed for independent
/// replay. The record never upgrades the public certificate's status by label
/// or by a throwaway signing key.
#[derive(Debug, Clone)]
#[non_exhaustive]
#[allow(clippy::large_enum_variant)]
pub enum PipelineOutput {
    /// A structural proof record plus its replayable Clean payload.
    Record {
        /// Public compatibility record. Its status/signature are not authority.
        certificate: ProofCertificate,
        /// Structural pipeline history.
        chain: CertificateChain,
        /// Exact Clean payload bound to the VC and proof term.
        clean_payload: crate::TrustProofCertificate,
        /// Whether this process replayed `clean_payload` before returning it.
        verification: RecordVerification,
    },
    /// Certification was rejected or skipped; no record was produced.
    NoRecord {
        /// Why no record was produced.
        reason: String,
    },
}

impl PipelineOutput {
    /// Returns `true` if the pipeline produced a public record.
    #[must_use]
    pub fn has_record(&self) -> bool {
        matches!(self, PipelineOutput::Record { .. })
    }

    /// Returns the record's replay provenance, if present.
    #[must_use]
    pub fn verification(&self) -> Option<RecordVerification> {
        match self {
            PipelineOutput::Record { verification, .. } => Some(*verification),
            PipelineOutput::NoRecord { .. } => None,
        }
    }
}

/// Bridge that runs the Clean certification pipeline and produces a replayable
/// Clean payload beside non-authoritative proof-record metadata.
///
/// This is the main integration point between the two crates. Callers
/// provide a VC, a VerificationResult, and a proof term. The bridge:
///
/// 1. Runs CertificationPipeline.certify() or certify_unchecked()
/// 2. Converts the CertificationResult to a ProofCertificate
/// 3. Builds a CertificateChain recording each pipeline step
/// 4. Optionally inserts into a CertificateStore
pub struct CertificationBridge {
    pipeline: CertificationPipeline,
}

impl CertificationBridge {
    /// Create a new bridge with default pipeline settings.
    #[must_use]
    pub fn new() -> Self {
        CertificationBridge { pipeline: CertificationPipeline::new() }
    }

    /// Create a bridge with a custom CertificationPipeline.
    #[must_use]
    pub fn with_pipeline(pipeline: CertificationPipeline) -> Self {
        CertificationBridge { pipeline }
    }

    /// Run the full Clean-kernel pipeline and produce a replayable record.
    ///
    /// Calls `CertificationPipeline::certify()` (clean kernel validation),
    /// then converts the result to trust-proof-cert types.
    pub fn certify(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
        timestamp: &str,
    ) -> Result<PipelineOutput, CertificateError> {
        let cert_result = self.pipeline.certify(vc, result, proof_term.clone());
        self.convert_result(vc, result, &cert_result, &proof_term, timestamp)
    }

    /// Run the unchecked pipeline and produce a record explicitly marked
    /// [`RecordVerification::Unchecked`].
    ///
    /// Calls `CertificationPipeline::certify_unchecked()` (no clean kernel
    /// validation), then converts the result to trust-proof-cert types.
    pub fn certify_unchecked(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
        timestamp: &str,
    ) -> Result<PipelineOutput, CertificateError> {
        let cert_result = self.pipeline.certify_unchecked(vc, result, proof_term.clone());
        self.convert_result(vc, result, &cert_result, &proof_term, timestamp)
    }

    /// Package an unchecked record and insert only its public compatibility
    /// metadata into a [`CertificateStore`].
    ///
    /// Convenience method that combines `certify_unchecked()` with store insertion.
    /// Returns the PipelineOutput so the caller can inspect what happened.
    pub fn certify_and_store(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
        timestamp: &str,
        store: &mut CertificateStore,
    ) -> Result<PipelineOutput, CertificateError> {
        let output = self.certify_unchecked(vc, result, proof_term, timestamp)?;
        if let PipelineOutput::Record { ref certificate, ref chain, .. } = output {
            store.insert(certificate.clone(), chain.clone());
        }
        Ok(output)
    }

    /// Run the checked pipeline and insert only its public compatibility record
    /// into the store. The returned output retains the replayable Clean payload.
    pub fn certify_checked_and_store(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
        timestamp: &str,
        store: &mut CertificateStore,
    ) -> Result<PipelineOutput, CertificateError> {
        let output = self.certify(vc, result, proof_term, timestamp)?;
        if let PipelineOutput::Record { ref certificate, ref chain, .. } = output {
            store.insert(certificate.clone(), chain.clone());
        }
        Ok(output)
    }

    /// Trust: Convert a CertificationResult (trust-clean) to a PipelineOutput
    /// containing trust-proof-cert types.
    fn convert_result(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        cert_result: &CertificationResult,
        proof_term: &[u8],
        timestamp: &str,
    ) -> Result<PipelineOutput, CertificateError> {
        match cert_result {
            CertificationResult::Certified { certificate, time_ms } => {
                // Extract solver info from the VerificationResult
                let solver_info = extract_solver_info(result, *time_ms).ok_or_else(|| {
                    CertificateError::SerializationFailed {
                        reason: "a certificate record cannot be built from a non-Proved result"
                            .to_string(),
                    }
                })?;

                // Build VcSnapshot from the VC
                let vc_snapshot = VcSnapshot::from_vc(vc).map_err(|e| {
                    CertificateError::SerializationFailed { reason: format!("VcSnapshot: {e}") }
                })?;

                // Compute function body hash from VC formula bytes
                let function_hash = compute_function_hash(vc);

                // Build a compatibility record. The exact Clean payload below,
                // not this public status field or a self-generated signature,
                // is what a consumer independently replays.
                let proof_cert = ProofCertificate::new_trusted(
                    vc.function.to_string(),
                    function_hash,
                    vc_snapshot,
                    solver_info,
                    proof_term.to_vec(),
                    timestamp.to_string(),
                );

                // Build CertificateChain
                let clean_fingerprint_str = format!("{}", certificate.vc_fingerprint);
                let chain = build_chain(
                    vc,
                    proof_term,
                    &clean_fingerprint_str,
                    timestamp,
                    RecordVerification::KernelChecked,
                    *time_ms,
                );

                Ok(PipelineOutput::Record {
                    certificate: proof_cert,
                    chain,
                    clean_payload: certificate.clone(),
                    verification: RecordVerification::KernelChecked,
                })
            }
            CertificationResult::Trusted { certificate, time_ms } => {
                // Trusted certificates are NOT kernel-verified.
                // Produce a Trusted-level ProofCertificate (no upgrade to Certified).
                let solver_info = extract_solver_info(result, *time_ms).ok_or_else(|| {
                    CertificateError::SerializationFailed {
                        reason: "an unchecked record cannot be built from a non-Proved result"
                            .to_string(),
                    }
                })?;
                let vc_snapshot = VcSnapshot::from_vc(vc).map_err(|e| {
                    CertificateError::SerializationFailed { reason: format!("VcSnapshot: {e}") }
                })?;
                let function_hash = compute_function_hash(vc);
                let proof_cert = ProofCertificate::new_trusted(
                    vc.function.to_string(),
                    function_hash,
                    vc_snapshot,
                    solver_info,
                    proof_term.to_vec(),
                    timestamp.to_string(),
                );
                // No upgrade_to_certified — this is explicitly Trusted.
                let clean_fingerprint_str = format!("{}", certificate.vc_fingerprint);
                let chain = build_chain(
                    vc,
                    proof_term,
                    &clean_fingerprint_str,
                    timestamp,
                    RecordVerification::Unchecked,
                    *time_ms,
                );
                Ok(PipelineOutput::Record {
                    certificate: proof_cert,
                    chain,
                    clean_payload: certificate.clone(),
                    verification: RecordVerification::Unchecked,
                })
            }
            CertificationResult::Rejected { reason, .. } => {
                Ok(PipelineOutput::NoRecord { reason: format!("clean rejected: {reason}") })
            }
            CertificationResult::Skipped { reason } => {
                Ok(PipelineOutput::NoRecord { reason: format!("skipped: {reason}") })
            }
        }
    }
}

impl Default for CertificationBridge {
    fn default() -> Self {
        Self::new()
    }
}

/// Trust: Extract solver info from a VerificationResult for the proof certificate.
fn extract_solver_info(result: &VerificationResult, clean_time_ms: u64) -> Option<SolverInfo> {
    match result {
        VerificationResult::Proved { solver, time_ms, strength, .. } => Some(SolverInfo {
            name: solver.to_string(),
            version: "unknown".to_string(),
            time_ms: time_ms.saturating_add(clean_time_ms),
            strength: strength.clone(),
            evidence: None,
        }),
        // Never replace a non-proof with a synthetic SMT-UNSAT strength.
        _ => None,
    }
}

/// Compute a compatibility source hash for a VC record.
///
/// This bridge has no MIR body and therefore cannot honestly manufacture a
/// body hash. It domain-separates and binds the function plus canonical VC;
/// downstream proof consumers still treat the public record as metadata.
fn compute_function_hash(vc: &VerificationCondition) -> FunctionHash {
    let canonical = crate::canonical::canonical_vc_bytes(vc);
    let mut material = Vec::with_capacity(vc.function.len() + canonical.len() + 64);
    material.extend_from_slice(b"trust-clean/vc-record-source/v2\0");
    material.extend_from_slice(&(vc.function.len() as u64).to_be_bytes());
    material.extend_from_slice(vc.function.as_bytes());
    material.extend_from_slice(&(canonical.len() as u64).to_be_bytes());
    material.extend_from_slice(&canonical);
    FunctionHash::from_bytes(&material)
}

/// Trust: Build a CertificateChain for the pipeline steps.
fn build_chain(
    vc: &VerificationCondition,
    proof_term: &[u8],
    clean_fingerprint: &str,
    timestamp: &str,
    verification: RecordVerification,
    clean_time_ms: u64,
) -> CertificateChain {
    let mut chain = CertificateChain::new();

    // Step 1: VC generation (MIR -> VC)
    let vc_hash = stable_sha256_hex(&crate::canonical::canonical_vc_bytes(vc));
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: stable_sha256_hex(vc.function.as_bytes()),
        output_hash: vc_hash.clone(),
        time_ms: 0, // VC generation time not tracked here
        timestamp: timestamp.to_string(),
    });

    // Step 2: Solver proof
    let proof_hash = stable_sha256_hex(proof_term);
    chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "ay".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: vc_hash,
        output_hash: proof_hash.clone(),
        time_ms: 0, // Solver time tracked in SolverInfo
        timestamp: timestamp.to_string(),
    });

    // Step 3: clean certification (if verified)
    if verification == RecordVerification::KernelChecked {
        chain.push(ChainStep {
            step_type: ChainStepType::CleanCertification,
            tool: "clean".to_string(),
            tool_version: "5.0.0".to_string(),
            input_hash: proof_hash,
            output_hash: clean_fingerprint.to_string(),
            time_ms: clean_time_ms,
            timestamp: timestamp.to_string(),
        });
    }

    chain
}

#[cfg(test)]
mod tests {
    use trust_proof_cert::{CertificateStore, CertificationStatus};
    use trust_types::*;

    use super::*;

    fn sample_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_div".into(),
            location: SourceSpan::default(),
            formula: Formula::Not(Box::new(Formula::Eq(
                Box::new(Formula::Var("divisor".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ))),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), time_ms: 3, counterexample: None }
    }

    fn smtbacked_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat_strict_checked(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn a_certificate() -> crate::TrustProofCertificate {
        crate::certificate::generate_certificate_unchecked(
            &sample_vc(),
            &proved_result(),
            vec![0xCA, 0xFE],
            "ay-test 0.1.0",
        )
        .expect("certificate")
    }

    // -----------------------------------------------------------------------
    // apply_certification: hard-blocked until evidence transport is replayable
    // -----------------------------------------------------------------------

    #[test]
    fn apply_certification_keeps_smtbacked_even_on_kernel_success() {
        // A genuine, separately stored Clean certificate is not enough to alter
        // this untyped live result: the result itself does not transport it.
        let cert = CertificationResult::Certified { certificate: a_certificate(), time_ms: 1 };
        let kept = apply_certification(smtbacked_result(), &cert);
        assert_eq!(
            kept.assurance(),
            Some(AssuranceLevel::SmtBacked),
            "an untransported Clean certificate must not mint live Certified assurance"
        );
    }

    #[test]
    fn apply_certification_never_upgrades_without_kernel_verification() {
        // Trusted (certificate produced but NOT kernel-verified), Rejected, and
        // Skipped must all LEAVE the assurance untouched -- no forged Certified.
        let cases = [
            CertificationResult::Trusted { certificate: a_certificate(), time_ms: 1 },
            CertificationResult::Rejected { reason: "kernel rejected".into(), time_ms: 1 },
            CertificationResult::Skipped { reason: "logic not certifiable".into() },
        ];
        for cert in &cases {
            let kept = apply_certification(smtbacked_result(), cert);
            assert_eq!(
                kept.assurance(),
                Some(AssuranceLevel::SmtBacked),
                "non-kernel-verified outcome {cert:?} must NOT upgrade to Certified"
            );
        }
    }

    #[test]
    fn apply_certification_does_not_touch_non_proved() {
        let cert = CertificationResult::Certified { certificate: a_certificate(), time_ms: 1 };
        assert!(matches!(
            apply_certification(failed_result(), &cert),
            VerificationResult::Failed { .. }
        ));
    }

    // -----------------------------------------------------------------------
    // CertificationBridge construction
    // -----------------------------------------------------------------------

    #[test]
    fn test_bridge_new_creates_instance() {
        let bridge = CertificationBridge::new();
        // Verify it can produce output (functional test, not field access)
        let vc = sample_vc();
        let result = proved_result();
        let output = bridge
            .certify_unchecked(&vc, &result, vec![1], "2026-03-28T00:00:00Z")
            .expect("bridge should work");
        assert!(output.has_record());
    }

    #[test]
    fn test_bridge_default_trait() {
        let bridge = CertificationBridge::default();
        let vc = sample_vc();
        let result = proved_result();
        let output = bridge
            .certify_unchecked(&vc, &result, vec![1], "2026-03-28T00:00:00Z")
            .expect("default bridge should work");
        assert!(output.has_record());
    }

    #[test]
    fn test_bridge_with_pipeline() {
        let pipeline = CertificationPipeline::with_prover_version("custom 1.0");
        let bridge = CertificationBridge::with_pipeline(pipeline);
        let vc = sample_vc();
        let result = proved_result();
        // Verify the custom pipeline produces certificates with the custom version info
        let output = bridge
            .certify_unchecked(&vc, &result, vec![1], "2026-03-28T00:00:00Z")
            .expect("custom bridge should work");
        assert!(output.has_record());
    }

    // -----------------------------------------------------------------------
    // Unchecked certification (Trusted path)
    // -----------------------------------------------------------------------

    #[test]
    fn test_certify_unchecked_produces_explicit_unchecked_record() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let output = bridge
            .certify_unchecked(&vc, &result, vec![0xCA, 0xFE], "2026-03-28T00:00:00Z")
            .expect("unchecked certification should succeed");

        assert!(output.has_record());
        assert_eq!(output.verification(), Some(RecordVerification::Unchecked));
        if let PipelineOutput::Record { certificate, chain, clean_payload, .. } = &output {
            assert_eq!(certificate.function, "test_div");
            assert_eq!(certificate.status, CertificationStatus::Trusted);
            assert_eq!(certificate.proof_trace, vec![0xCA, 0xFE]);
            assert_eq!(clean_payload.proof_term, vec![0xCA, 0xFE]);
            assert_eq!(certificate.solver.name, "ay");
            assert_eq!(certificate.solver.strength, ProofStrength::smt_unsat());
            assert!(certificate.timestamp.contains("2026-03-28"));

            // Chain should have 2 steps (VcGeneration + SolverProof, no CleanCertification)
            assert_eq!(chain.len(), 2);
            assert!(!chain.is_clean_certified());
            chain.verify_integrity().expect("chain should have valid integrity");
        }
    }

    #[test]
    fn test_certify_unchecked_skips_failed_result() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = failed_result();

        let output = bridge
            .certify_unchecked(&vc, &result, vec![1], "2026-03-28T00:00:00Z")
            .expect("should return NoRecord, not error");

        assert!(!output.has_record());
        if let PipelineOutput::NoRecord { reason } = &output {
            assert!(reason.contains("skipped"), "reason: {reason}");
        }
    }

    #[test]
    fn test_certify_unchecked_skips_empty_proof() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let output = bridge
            .certify_unchecked(&vc, &result, vec![], "2026-03-28T00:00:00Z")
            .expect("should return NoRecord, not error");

        assert!(!output.has_record());
    }

    // -----------------------------------------------------------------------
    // Full clean certification path (rejects invalid proofs)
    // -----------------------------------------------------------------------

    #[test]
    fn test_certify_rejects_invalid_proof_bytes() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let output = bridge
            .certify(&vc, &result, vec![0xFF, 0x00], "2026-03-28T00:00:00Z")
            .expect("should return NoRecord, not error");

        assert!(!output.has_record());
        if let PipelineOutput::NoRecord { reason } = &output {
            assert!(reason.contains("rejected"), "reason: {reason}");
        }
    }

    #[test]
    fn test_certify_rejects_sort_cert_for_div_vc() {
        use clean_kernel::cert::ProofCert;
        use clean_kernel::level::Level as LeanLevel;

        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let clean_cert = ProofCert::Sort { level: LeanLevel::zero() };
        let proof_bytes = bincode::serialize(&clean_cert).expect("serialize");

        let output = bridge
            .certify(&vc, &result, proof_bytes, "2026-03-28T00:00:00Z")
            .expect("should return NoRecord, not error");

        assert!(!output.has_record());
        if let PipelineOutput::NoRecord { reason } = &output {
            assert!(reason.contains("rejected") || reason.contains("kernel"), "reason: {reason}");
        }
    }

    // -----------------------------------------------------------------------
    // Store integration
    // -----------------------------------------------------------------------

    #[test]
    fn test_certify_and_store_inserts_into_store() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();
        let mut store = CertificateStore::new("test-crate");

        assert!(store.is_empty());

        let output = bridge
            .certify_and_store(&vc, &result, vec![0xBE, 0xEF], "2026-03-28T00:00:00Z", &mut store)
            .expect("should succeed");

        assert!(output.has_record());
        assert_eq!(store.len(), 1);

        // Verify the stored certificate is findable by function name
        let found = store.find_by_function("test_div");
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].function, "test_div");
    }

    #[test]
    fn test_certify_and_store_does_not_insert_on_skip() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = failed_result();
        let mut store = CertificateStore::new("test-crate");

        let output = bridge
            .certify_and_store(&vc, &result, vec![1], "2026-03-28T00:00:00Z", &mut store)
            .expect("should succeed");

        assert!(!output.has_record());
        assert!(store.is_empty());
    }

    #[test]
    fn test_certify_and_store_multiple_functions() {
        let bridge = CertificationBridge::new();
        let mut store = CertificateStore::new("test-crate");

        let vc1 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "func_a".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        };
        let vc2 = VerificationCondition {
            kind: VcKind::Assertion { message: "invariant".to_string() },
            function: "func_b".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let result = proved_result();

        bridge
            .certify_and_store(&vc1, &result, vec![1], "2026-03-28T00:00:00Z", &mut store)
            .expect("should succeed");
        bridge
            .certify_and_store(&vc2, &result, vec![2], "2026-03-28T00:01:00Z", &mut store)
            .expect("should succeed");

        assert_eq!(store.len(), 2);
        assert_eq!(store.find_by_function("func_a").len(), 1);
        assert_eq!(store.find_by_function("func_b").len(), 1);
    }

    // -----------------------------------------------------------------------
    // Certificate chain integrity
    // -----------------------------------------------------------------------

    #[test]
    fn test_chain_integrity_on_unchecked_path() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let output = bridge
            .certify_unchecked(&vc, &result, vec![0xAB], "2026-03-28T00:00:00Z")
            .expect("should succeed");

        if let PipelineOutput::Record { chain, .. } = &output {
            chain.verify_integrity().expect("unchecked chain should have valid integrity");
            assert_eq!(chain.len(), 2);
            assert_eq!(chain.steps[0].step_type, ChainStepType::VcGeneration);
            assert_eq!(chain.steps[1].step_type, ChainStepType::SolverProof);
        } else {
            panic!("expected a proof record");
        }
    }

    // -----------------------------------------------------------------------
    // Helper functions
    // -----------------------------------------------------------------------

    #[test]
    fn test_extract_solver_info_proved() {
        let result = proved_result();
        let info = extract_solver_info(&result, 10).expect("proved result has solver metadata");
        assert_eq!(info.name, "ay");
        assert_eq!(info.time_ms, 15); // 5 (solver) + 10 (clean)
        assert_eq!(info.strength, ProofStrength::smt_unsat());
    }

    #[test]
    fn test_extract_solver_info_non_proved() {
        let result = failed_result();
        assert!(extract_solver_info(&result, 7).is_none());
    }

    #[test]
    fn test_compute_function_hash_deterministic() {
        let vc = sample_vc();
        let h1 = compute_function_hash(&vc);
        let h2 = compute_function_hash(&vc);
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_compute_function_hash_different_formulas() {
        let vc1 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        };
        let vc2 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert_ne!(compute_function_hash(&vc1), compute_function_hash(&vc2));
    }

    #[test]
    fn test_pipeline_output_reports_record_presence_without_certification_claim() {
        let cert = PipelineOutput::NoRecord { reason: "test".to_string() };
        assert!(!cert.has_record());
        assert_eq!(cert.verification(), None);
    }

    // -----------------------------------------------------------------------
    // Certificate content validation
    // -----------------------------------------------------------------------

    #[test]
    fn test_certificate_vc_snapshot_matches_vc() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let output = bridge
            .certify_unchecked(&vc, &result, vec![0x01], "2026-03-28T12:00:00Z")
            .expect("should succeed");

        if let PipelineOutput::Record { certificate, .. } = &output {
            // The VC snapshot should contain the kind and formula
            assert!(certificate.vc_snapshot.kind.contains("DivisionByZero"));
            assert!(!certificate.vc_snapshot.formula_json.is_empty());
        } else {
            panic!("expected proof record");
        }
    }

    #[test]
    fn test_certificate_id_is_deterministic() {
        let bridge = CertificationBridge::new();
        let vc = sample_vc();
        let result = proved_result();

        let out1 = bridge
            .certify_unchecked(&vc, &result, vec![0x01], "2026-03-28T12:00:00Z")
            .expect("should succeed");
        let out2 = bridge
            .certify_unchecked(&vc, &result, vec![0x01], "2026-03-28T12:00:00Z")
            .expect("should succeed");

        if let (
            PipelineOutput::Record { certificate: c1, .. },
            PipelineOutput::Record { certificate: c2, .. },
        ) = (&out1, &out2)
        {
            assert_eq!(c1.id, c2.id, "same inputs should produce same certificate ID");
        } else {
            panic!("expected both to be Certified");
        }
    }
}
