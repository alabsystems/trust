// trust-clean/certification/pipeline.rs: CertificationPipeline struct
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{VerificationCondition, VerificationResult};

use super::result::CertificationResult;
use super::result_status_name;
use crate::certificate::{generate_certificate, generate_certificate_unchecked};
use crate::error::CertificateError;
use crate::logic_classification::{
    CertificationScope, classify_formula, degradation_strategy, scope_from_logic,
};
use crate::reconstruction::{SolverProof, reconstruct};
use crate::{TrustProofCertificate, clean_bridge};

/// Trust: The certification pipeline.
///
/// Takes verification results that are Proved/Trusted and attempts to
/// upgrade them to Certified by running the proof through clean's kernel.
///
/// The pipeline uses the clean-kernel library directly (not subprocess).
/// It translates the VC formula to a clean theorem expression, then
/// type-checks the proof term against it.
///
/// Supports proof term generation from structured solver proofs for QF_LIA
/// and QF_UF theories. For other theories, callers must provide
/// pre-built clean proof term bytes.
pub struct CertificationPipeline {
    /// Trust: Default prover version string for certificates.
    pub(crate) default_prover_version: String,
}

impl CertificationPipeline {
    /// Create a new certification pipeline.
    #[must_use]
    pub fn new() -> Self {
        CertificationPipeline { default_prover_version: "clean-kernel 0.1.0".to_string() }
    }

    /// Create a pipeline with a custom prover version string.
    #[must_use]
    pub fn with_prover_version(prover_version: &str) -> Self {
        CertificationPipeline { default_prover_version: prover_version.to_string() }
    }

    /// Trust: Attempt to certify a proved verification result.
    ///
    /// Only operates on `Proved` results. Other results return `Skipped`.
    ///
    /// The proof term bytes must be provided separately — the `VerificationResult`
    /// does not carry them (proof terms are heavy and solver-specific).
    ///
    /// # Arguments
    ///
    /// * `vc` - The verification condition that was proved
    /// * `result` - The solver's verification result (must be `Proved`)
    /// * `proof_term` - Serialized clean proof term bytes from the solver
    pub fn certify(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
    ) -> CertificationResult {
        // Trust: Only attempt certification for proved results
        let VerificationResult::Proved { solver, strength, .. } = result else {
            return CertificationResult::Skipped {
                reason: format!(
                    "only Proved results can be certified, got {}",
                    result_status_name(result)
                ),
            };
        };

        if proof_term.is_empty() {
            return CertificationResult::Skipped {
                reason: "empty proof term — solver did not produce a clean certificate".to_string(),
            };
        }

        let prover_version = self.make_prover_version(solver.as_str(), strength);

        // Trust: Run the full certification pipeline with clean kernel validation
        let start = std::time::Instant::now();
        match generate_certificate(vc, result, proof_term, &prover_version) {
            Ok(certificate) => {
                let elapsed_ms = start.elapsed().as_millis() as u64;
                CertificationResult::Certified { certificate, time_ms: elapsed_ms }
            }
            Err(e) => {
                let elapsed_ms = start.elapsed().as_millis() as u64;
                CertificationResult::Rejected { reason: format!("{e}"), time_ms: elapsed_ms }
            }
        }
    }

    /// Trust: Generate an unchecked certificate (Trusted, not Certified).
    ///
    /// Builds the certificate structure and stores the proof term bytes,
    /// but does NOT validate them against the clean kernel. Use this when
    /// the proof term comes from a solver that doesn't produce clean-compatible
    /// certificates (e.g., raw ay SMT proofs before clean translation).
    ///
    /// Certificates generated this way remain `Trusted` (not `Certified`).
    pub fn certify_unchecked(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        proof_term: Vec<u8>,
    ) -> CertificationResult {
        let VerificationResult::Proved { solver, strength, .. } = result else {
            return CertificationResult::Skipped {
                reason: format!(
                    "only Proved results can be certified, got {}",
                    result_status_name(result)
                ),
            };
        };

        if proof_term.is_empty() {
            return CertificationResult::Skipped { reason: "empty proof term".to_string() };
        }

        let prover_version = self.make_prover_version(solver.as_str(), strength);

        let start = std::time::Instant::now();
        match generate_certificate_unchecked(vc, result, proof_term, &prover_version) {
            Ok(certificate) => {
                let elapsed_ms = start.elapsed().as_millis() as u64;
                // Trust: Unchecked certificates are NOT Certified — they are Trusted.
                // The certificate was NOT clean-kernel-verified (F2 fix: #758).
                CertificationResult::Trusted { certificate, time_ms: elapsed_ms }
            }
            Err(e) => CertificationResult::Rejected {
                reason: format!("{e}"),
                time_ms: start.elapsed().as_millis() as u64,
            },
        }
    }

    /// Trust: Certify from a structured solver proof.
    ///
    /// Takes a `SolverProof` (structured sequence of inference steps) instead
    /// of raw proof bytes. The pipeline:
    ///
    /// 1. Classifies the VC formula into an SMT logic fragment
    /// 2. Checks if the logic is certifiable (QF_LIA or QF_UF)
    /// 3. Reconstructs a clean proof term from the solver proof steps
    /// 4. Serializes the proof term to bytes
    /// 5. Generates an unchecked certificate with the serialized proof
    ///
    /// This method bridges structured solver output to the certificate pipeline
    /// without requiring the solver to produce clean-native proof terms.
    ///
    /// # Arguments
    ///
    /// * `vc` - The verification condition that was proved
    /// * `result` - The solver's verification result (must be `Proved`)
    /// * `solver_proof` - Structured proof output from the solver
    pub fn certify_from_solver_proof(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        solver_proof: &SolverProof,
    ) -> CertificationResult {
        let VerificationResult::Proved { solver, strength, .. } = result else {
            return CertificationResult::Skipped {
                reason: format!(
                    "only Proved results can be certified, got {}",
                    result_status_name(result)
                ),
            };
        };

        if solver_proof.steps.is_empty() {
            return CertificationResult::Skipped {
                reason: "solver proof has no steps".to_string(),
            };
        }

        // Genuine-kernel fast path: if the VC's violation refutes purely
        // propositionally, the clean CIC kernel verifies it over axiom-free
        // terms. Soundness reduces to the clean kernel, NOT to the ay solver or
        // ay's SMT proof checker (both of which have had soundness bugs). Any
        // kernel rejection / non-propositional shape falls through to the
        // existing reconstruction (-> Trusted), never a forged Certified.
        //
        // Every constructor mints a kernel proof OF THE CANONICAL STATEMENT
        // `Trust.VC.holds <kind> <formula>` (the replay identity established by
        // the toolchain-authority audit), so the `generate_certificate` re-entry
        // below replays against the exact theorem the constructor proved. We try
        // the direct-contradiction refutation (`X ∧ ¬X`, the most elegant
        // instance) first, then the GENERAL propositional certifier — a
        // constructive double-negation case split over the formula's canonical
        // skeleton — which subsumes multi-clause resolution and arbitrary
        // And/Or/Not/Implies refutations, then the EUF certifier — equality-
        // graph transitivity/symmetry/congruence (e.g. `a=b ∧ b=c ∧ ¬(a=c)`)
        // which the propositional path cannot see. All are sound-but-incomplete
        // and fail-closed: theory-dependent refutations decline.
        let kernel_proof = clean_bridge::kernel_certify_direct_contradiction(&vc.kind, &vc.formula)
            .or_else(|| clean_bridge::kernel_certify_propositional(&vc.kind, &vc.formula))
            .or_else(|| clean_bridge::kernel_certify_euf(&vc.kind, &vc.formula));
        if let Some(proof_bytes) = kernel_proof {
            let prover_version = self.make_prover_version(solver.as_str(), strength);
            // Re-enter the canonical verifier even though the constructor that
            // produced `proof_bytes` already checked its term. This binds the
            // serialized bytes, current VC fingerprint, and canonical theorem
            // at the exact point where `Certified` is minted; a future producer
            // regression cannot turn an unchecked payload into that status.
            if let Ok(certificate) = generate_certificate(vc, result, proof_bytes, &prover_version)
            {
                return CertificationResult::Certified { certificate, time_ms: 0 };
            }
        }

        // Trust: Classify the formula and check certifiability
        let logic = classify_formula(&vc.formula);
        let strategy = degradation_strategy(&logic);

        if strategy.is_none() {
            return CertificationResult::Skipped {
                reason: format!(
                    "logic {} is not certifiable: no certification strategy available",
                    logic.name()
                ),
            };
        }

        // Trust: Reconstruct clean proof term from solver proof steps
        let proof_term = match reconstruct(solver_proof, vc) {
            Ok(term) => term,
            Err(e) => {
                return CertificationResult::Rejected {
                    reason: format!("proof reconstruction failed: {e}"),
                    time_ms: 0,
                };
            }
        };

        // Serialize the reconstructed proof term as the certificate payload.
        // Use the clean bridge serialization for kernel-compatible bytes.
        let proof_bytes = match clean_bridge::serialize_proof_cert_from_lean_term(&proof_term) {
            Ok(bytes) => bytes,
            Err(e) => {
                return CertificationResult::Rejected {
                    reason: format!("proof certificate serialization failed: {e}"),
                    time_ms: 0,
                };
            }
        };

        let prover_version = self.make_prover_version(solver.as_str(), strength);

        // Use kernel-checked path (generate_certificate) instead of
        // generate_certificate_unchecked. This means the clean kernel validates
        // the proof term, upgrading the result from Trusted to genuinely Certified.
        // Falls back to unchecked if the kernel rejects the proof term (e.g.,
        // theory lemma steps that the kernel cannot yet verify).
        let start = std::time::Instant::now();
        match generate_certificate(vc, result, proof_bytes.clone(), &prover_version) {
            Ok(certificate) => {
                let elapsed_ms = start.elapsed().as_millis() as u64;
                CertificationResult::Certified { certificate, time_ms: elapsed_ms }
            }
            Err(e) if should_fallback_to_unchecked(&e) => {
                // Fallback: kernel rejected the proof term (likely theory lemma or
                // unsupported construct). Use unchecked path to still produce a
                // Trusted certificate rather than failing entirely (F1 fix: #758).
                match generate_certificate_unchecked(vc, result, proof_bytes, &prover_version) {
                    Ok(certificate) => {
                        let elapsed_ms = start.elapsed().as_millis() as u64;
                        CertificationResult::Trusted { certificate, time_ms: elapsed_ms }
                    }
                    Err(e) => CertificationResult::Rejected {
                        reason: format!("{e}"),
                        time_ms: start.elapsed().as_millis() as u64,
                    },
                }
            }
            Err(e) => CertificationResult::Rejected {
                reason: format!("{e}"),
                time_ms: start.elapsed().as_millis() as u64,
            },
        }
    }

    /// Certify from a solver proof with graceful degradation.
    ///
    /// Like `certify_from_solver_proof`, but returns both the `CertificationResult`
    /// and the `CertificationScope` describing why certification succeeded, partially
    /// succeeded, or was not possible.
    ///
    /// For supported theories (QF_LIA, QF_UF, QF_LIA+UF), produces full
    /// Alethe-to-clean certificates. For unsupported theories, produces an
    /// "uncertified" marker with reasons instead of failing the build.
    ///
    /// # Returns
    ///
    /// `(CertificationResult, CertificationScope)` — the scope tells callers
    /// exactly what level of certification was achieved and why.
    pub fn certify_with_scope(
        &self,
        vc: &VerificationCondition,
        result: &VerificationResult,
        solver_proof: &SolverProof,
    ) -> (CertificationResult, CertificationScope) {
        let VerificationResult::Proved { .. } = result else {
            return (
                CertificationResult::Skipped {
                    reason: format!(
                        "only Proved results can be certified, got {}",
                        result_status_name(result)
                    ),
                },
                CertificationScope::Uncertified { reason: "result is not Proved".to_string() },
            );
        };

        if solver_proof.steps.is_empty() {
            return (
                CertificationResult::Skipped { reason: "solver proof has no steps".to_string() },
                CertificationScope::Uncertified { reason: "solver proof has no steps".to_string() },
            );
        }

        // Classify the formula and determine scope
        let logic = classify_formula(&vc.formula);
        let scope = scope_from_logic(&logic);

        // Graceful degradation — for uncertifiable logics, return
        // the scope information instead of failing the build
        match &scope {
            CertificationScope::FullyCertified => {
                // Fully certifiable: proceed with reconstruction
                let cert_result = self.certify_from_solver_proof(vc, result, solver_proof);
                (cert_result, scope)
            }
            CertificationScope::PartiallyCertified { logic, reason } => {
                // Partially certifiable: attempt reconstruction but tag as partial
                let cert_result = self.certify_from_solver_proof(vc, result, solver_proof);
                // Even if reconstruction succeeds, the scope records what
                // parts could not be certified
                (
                    cert_result,
                    CertificationScope::PartiallyCertified {
                        logic: logic.clone(),
                        reason: reason.clone(),
                    },
                )
            }
            CertificationScope::Uncertified { reason } => {
                // Not certifiable: skip gracefully instead of failing
                (
                    CertificationResult::Skipped {
                        reason: format!(
                            "graceful degradation: logic {} is not certifiable — {}",
                            logic.name(),
                            reason
                        ),
                    },
                    CertificationScope::Uncertified { reason: reason.clone() },
                )
            }
        }
    }

    /// Trust: Verify an existing certificate against a VC.
    ///
    /// Re-checks a previously generated certificate: validates fingerprint
    /// freshness, then runs clean kernel type-checking. Returns `Ok(())` if
    /// the certificate is still valid and clean confirms it.
    pub fn verify_existing(
        &self,
        vc: &VerificationCondition,
        certificate: &TrustProofCertificate,
    ) -> Result<(), CertificateError> {
        crate::certificate::verify_certificate(vc, certificate)
    }

    /// Trust: Translate a VC's formula to a clean theorem expression.
    ///
    /// Useful for debugging: inspect what clean sees before certification.
    pub fn translate_to_clean(vc: &VerificationCondition) -> clean_kernel::Expr {
        clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula)
    }

    /// Trust: Build a prover version string from solver info and pipeline config.
    fn make_prover_version(&self, solver: &str, strength: &trust_types::ProofStrength) -> String {
        format!(
            "{solver} via {backend} (strength: {strength:?})",
            backend = self.default_prover_version,
        )
    }
}

pub(super) fn should_fallback_to_unchecked(error: &CertificateError) -> bool {
    matches!(error, CertificateError::KernelRejected { .. })
}

impl Default for CertificationPipeline {
    fn default() -> Self {
        Self::new()
    }
}
