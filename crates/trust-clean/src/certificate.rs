// trust-clean/certificate.rs: Proof certificate types and operations
//
// A TrustProofCertificate is the bridge between a solver's proof and
// clean's kernel verification. The certificate contains:
//
// 1. A fingerprint of the canonical VC (for staleness detection)
// 2. The canonical VC bytes (so clean knows what theorem to check)
// 3. The proof term bytes (opaque to Trust, meaningful to clean)
// 4. Metadata (prover name, version)
//
// The verification chain is:
//   solver produces proof_term -> TrustProofCertificate bundles it
//   -> clean kernel type-checks proof_term against canonical_vc
//   -> if accepted, result upgrades from Trusted to Certified
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::{VerificationCondition, VerificationResult};

use crate::canonical::{canonical_vc_bytes, with_canonical_vc_bytes};
use crate::clean_bridge;
use crate::error::CertificateError;
use crate::fingerprint::{Fingerprint, compute_vc_fingerprint, fingerprint_bytes};

/// A proof certificate that can be independently verified by clean.
///
/// This is the external (serde-friendly) representation used by the
/// trust-types pipeline. It will later be converted to the compiler-internal
/// `TrustProofCertificate` (which uses `Symbol` and `&'tcx [u8]`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrustProofCertificate {
    /// Which prover generated this certificate (e.g., "trust-wp", "clean").
    pub prover: String,

    /// Serialized clean proof term. Opaque to the compiler — only clean's
    /// kernel can interpret this. The proof term witnesses that the
    /// canonical VC holds.
    pub proof_term: Vec<u8>,

    /// 128-bit fingerprint of the canonical VC. Computed structurally
    /// over the VC's logical content (formula + kind), NOT over source
    /// locations. Used to detect stale certificates after code changes.
    pub vc_fingerprint: Fingerprint,

    /// The canonical VC bytes that this certificate proves. Stored so
    /// clean can reconstruct the theorem statement without access to
    /// the original VC object.
    pub canonical_vc: Vec<u8>,

    /// Prover version string for reproducibility (e.g., "trust-wp 0.1.0").
    pub prover_version: String,
}

impl TrustProofCertificate {
    /// Check whether this certificate is still valid for the given VC.
    ///
    /// Returns `true` if the VC's fingerprint matches the certificate's.
    /// A `false` result means the code changed since the certificate was
    /// generated and the certificate is stale.
    #[must_use]
    pub fn is_valid_for(&self, vc: &VerificationCondition) -> bool {
        let current = compute_vc_fingerprint(vc);
        self.vc_fingerprint == current
    }
}

/// TINV-8 (2026-10-05): the kernel-authority gate every public certificate entry applies
/// FIRST, so no free function can mint (or re-check) a certificate for a VC the
/// `CertificationPipeline` wrappers would skip — a record-less `TypeInvariant` row, or a
/// kind refused outright (`ContractInvariant`, `TypeRefinementViolation`, ...).
fn refuse_unauthorized(vc: &VerificationCondition) -> Result<(), CertificateError> {
    match vc.kernel_authority_refusal() {
        Some(why) => Err(CertificateError::AuthorityRefused { reason: why.to_string() }),
        None => Ok(()),
    }
}

/// Generate a proof certificate for a verified VC.
///
/// This is called after a constructive prover (trust-wp, clean) produces
/// a proof term. The certificate bundles the proof term with the VC's
/// canonical form and fingerprint.
///
/// # Arguments
///
/// * `vc` - The verification condition that was proved
/// * `result` - The solver's verification result (must be Proved)
/// * `proof_term` - The serialized clean proof term from the prover
/// * `prover_version` - Version string of the prover
///
/// # Errors
///
/// - `AuthorityRefused` if `vc.kernel_authority_refusal()` refuses the VC
/// - `InvalidProofTerm` if the proof term is empty or cannot be deserialized
///   as a clean `ProofCert`
/// - `KernelRejected` if the clean kernel rejects the proof term against
///   the translated VC theorem
pub fn generate_certificate(
    vc: &VerificationCondition,
    _result: &VerificationResult,
    proof_term: Vec<u8>,
    prover_version: &str,
) -> Result<TrustProofCertificate, CertificateError> {
    refuse_unauthorized(vc)?;
    if proof_term.is_empty() {
        return Err(CertificateError::InvalidProofTerm { reason: "empty proof term".to_string() });
    }

    // Phase 1: Validate the proof term with clean kernel BEFORE allocating canonical VC bytes:
    //   1. Deserialize proof_term into clean ProofCert
    //   2. Translate the VC into a clean theorem statement
    //   3. Type-check the proof_term against the theorem
    //   4. Only return Ok if clean kernel accepts
    let clean_cert = clean_bridge::deserialize_proof_cert(&proof_term)?;
    let theorem_expr = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);
    clean_bridge::verify_proof_cert(&clean_cert, &theorem_expr)?;

    // Phase 2: Build the certificate structure (serialize canonical VC once)
    let canonical = canonical_vc_bytes(vc);
    let fingerprint = fingerprint_bytes(&canonical);

    Ok(TrustProofCertificate {
        prover: prover_version.split_whitespace().next().unwrap_or("unknown").to_string(),
        proof_term,
        vc_fingerprint: fingerprint,
        canonical_vc: canonical,
        prover_version: prover_version.to_string(),
    })
}

/// Generate a certificate without clean kernel validation.
///
/// This is the Phase 1 path: builds the certificate structure and stores
/// the proof term bytes, but does NOT validate them against the clean kernel.
/// Use this when the proof term comes from a solver that doesn't produce
/// clean-compatible certificates (e.g., ay SMT proofs that haven't been
/// translated to clean format yet).
///
/// Certificates generated this way are `Trusted` (not `Certified`) — they
/// contain the proof bytes but haven't been machine-checked by clean.
///
/// # Errors
///
/// - `AuthorityRefused` if `vc.kernel_authority_refusal()` refuses the VC
/// - `InvalidProofTerm` if the proof term is empty
pub fn generate_certificate_unchecked(
    vc: &VerificationCondition,
    _result: &VerificationResult,
    proof_term: Vec<u8>,
    prover_version: &str,
) -> Result<TrustProofCertificate, CertificateError> {
    refuse_unauthorized(vc)?;
    if proof_term.is_empty() {
        return Err(CertificateError::InvalidProofTerm { reason: "empty proof term".to_string() });
    }

    let canonical = canonical_vc_bytes(vc);
    let fingerprint = fingerprint_bytes(&canonical);

    Ok(TrustProofCertificate {
        prover: prover_version.split_whitespace().next().unwrap_or("unknown").to_string(),
        proof_term,
        vc_fingerprint: fingerprint,
        canonical_vc: canonical,
        prover_version: prover_version.to_string(),
    })
}

/// Verify a proof certificate against a verification condition.
///
/// This is the trust boundary: if this function returns `Ok(())`, the
/// proof is machine-checked and the result can be upgraded from Trusted
/// to Certified. Only Certified results permit codegen check elision.
///
/// # Verification steps
///
/// 1. Recompute the VC fingerprint and compare to certificate
/// 2. Deserialize the clean proof term
/// 3. Type-check the proof term against the canonical VC
///
/// # Errors
///
/// - `AuthorityRefused` if `vc.kernel_authority_refusal()` refuses the VC
/// - `StaleCertificate` if the VC changed since the certificate was generated
/// - `InvalidProofTerm` if the proof bytes cannot be deserialized as a clean `ProofCert`
/// - `KernelRejected` if clean kernel rejects the proof term
pub fn verify_certificate(
    vc: &VerificationCondition,
    certificate: &TrustProofCertificate,
) -> Result<(), CertificateError> {
    refuse_unauthorized(vc)?;
    // Steps 1 & 2: Compute canonical VC bytes into reusable scratch buffer, derive fingerprint,
    // and check staleness with zero per-call canonical-byte heap allocations.
    let (current_fingerprint, matches_canonical) = with_canonical_vc_bytes(vc, |current_canonical| {
        let fp = fingerprint_bytes(current_canonical);
        (
            fp,
            certificate.vc_fingerprint == fp
                && certificate.canonical_vc.as_slice() == current_canonical,
        )
    });
    if !matches_canonical {
        return Err(CertificateError::StaleCertificate {
            expected: certificate.vc_fingerprint,
            actual: current_fingerprint,
        });
    }

    // Step 3: Type-check the proof term with clean kernel
    let clean_cert = clean_bridge::deserialize_proof_cert(&certificate.proof_term)?;
    let theorem_expr = clean_bridge::translate_vc_to_clean_theorem(&vc.kind, &vc.formula);
    clean_bridge::verify_proof_cert(&clean_cert, &theorem_expr)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn sample_vc() -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "get_midpoint".into(),
            location: SourceSpan::default(),
            formula: Formula::Not(Box::new(Formula::And(vec![
                Formula::Le(
                    Box::new(Formula::Int(0)),
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("a".into(), Sort::Int)),
                        Box::new(Formula::Var("b".into(), Sort::Int)),
                    )),
                ),
                Formula::Le(
                    Box::new(Formula::Add(
                        Box::new(Formula::Var("a".into(), Sort::Int)),
                        Box::new(Formula::Var("b".into(), Sort::Int)),
                    )),
                    Box::new(Formula::Int((1i128 << 64) - 1)),
                ),
            ]))),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn sample_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    #[test]
    fn generate_certificate_unchecked_builds_structure() {
        let vc = sample_vc();
        let result = sample_result();
        let proof_term = vec![0xDE, 0xAD, 0xBE, 0xEF];
        let cert =
            generate_certificate_unchecked(&vc, &result, proof_term.clone(), "trust-wp 0.1.0")
                .expect("should build certificate");

        assert_eq!(cert.proof_term, proof_term);
        assert_eq!(cert.prover_version, "trust-wp 0.1.0");
        assert_eq!(cert.prover, "trust-wp");
        assert_eq!(cert.vc_fingerprint, compute_vc_fingerprint(&vc));
        assert_eq!(cert.canonical_vc, canonical_vc_bytes(&vc));
    }

    #[test]
    fn generate_certificate_rejects_empty_proof() {
        let vc = sample_vc();
        let result = sample_result();
        let err = generate_certificate(&vc, &result, vec![], "trust-wp 0.1.0")
            .expect_err("empty proof should fail");
        assert!(
            matches!(err, CertificateError::InvalidProofTerm { .. }),
            "should be InvalidProofTerm, got {err:?}"
        );
    }

    #[test]
    fn generate_certificate_rejects_invalid_proof_bytes() {
        // generate_certificate now validates via clean, so arbitrary bytes fail
        let vc = sample_vc();
        let result = sample_result();
        let err = generate_certificate(&vc, &result, vec![0xDE, 0xAD], "test 0.1")
            .expect_err("invalid bytes should fail clean deserialization");
        assert!(
            matches!(err, CertificateError::InvalidProofTerm { .. }),
            "should be InvalidProofTerm, got {err:?}"
        );
    }

    #[test]
    fn generate_certificate_with_valid_clean_cert_reaches_kernel() {
        // Provide a valid bincode-serialized ProofCert — the clean kernel will
        // attempt to verify it against the theorem. It will fail because the
        // proof doesn't actually match the theorem, but it proves the pipeline
        // is wired end-to-end (deserialization + kernel invocation).
        use clean_kernel::cert::ProofCert;
        use clean_kernel::level::Level as LeanLevel;

        let clean_cert = ProofCert::Sort { level: LeanLevel::zero() };
        let proof_bytes =
            bincode::serialize(&clean_cert).expect("should serialize clean ProofCert");

        let vc = sample_vc();
        let result = sample_result();

        // This will fail at the kernel verification step (structure mismatch)
        // since a Sort cert doesn't prove our VC theorem — but it exercises
        // the full generate_certificate pipeline through clean.
        let err = generate_certificate(&vc, &result, proof_bytes, "clean 0.1.0")
            .expect_err("Sort cert doesn't prove an overflow VC");
        assert!(
            matches!(err, CertificateError::KernelRejected { .. }),
            "should be KernelRejected (structure mismatch), got {err:?}"
        );
    }

    #[test]
    fn is_valid_for_detects_staleness() {
        let vc1 = sample_vc();
        let result = sample_result();
        let cert = generate_certificate_unchecked(&vc1, &result, vec![1], "test 0.1")
            .expect("should build");

        // Same VC: valid
        assert!(cert.is_valid_for(&vc1));

        // Different formula: stale
        let vc2 = VerificationCondition {
            kind: VcKind::ArithmeticOverflow {
                op: BinOp::Add,
                operand_tys: (Ty::usize(), Ty::usize()),
            },
            function: "get_midpoint".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(!cert.is_valid_for(&vc2), "changed formula must invalidate certificate");
    }

    #[test]
    fn verify_detects_stale_fingerprint() {
        let vc1 = sample_vc();
        let result = sample_result();
        let cert = generate_certificate_unchecked(&vc1, &result, vec![1], "test 0.1")
            .expect("should build");

        // Verify against a different VC
        let vc2 = VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        };
        let err = verify_certificate(&vc2, &cert).expect_err("should detect staleness");
        assert!(
            matches!(err, CertificateError::StaleCertificate { .. }),
            "should be StaleCertificate, got {err:?}"
        );
    }

    #[test]
    fn verify_rejects_non_clean_proof_bytes() {
        let vc = sample_vc();
        let result = sample_result();
        // Build with unchecked (arbitrary bytes), then verify — should fail deserialization
        let cert = generate_certificate_unchecked(&vc, &result, vec![1, 2, 3], "test 0.1")
            .expect("should build");

        let err = verify_certificate(&vc, &cert)
            .expect_err("non-clean bytes should fail deserialization");
        assert!(
            matches!(err, CertificateError::InvalidProofTerm { .. }),
            "should be InvalidProofTerm, got {err:?}"
        );
    }

    #[test]
    fn verify_reaches_kernel_with_valid_clean_bytes() {
        use clean_kernel::cert::ProofCert;
        use clean_kernel::level::Level as LeanLevel;

        let vc = sample_vc();
        let result = sample_result();

        // Build a valid clean ProofCert and serialize it
        let clean_cert = ProofCert::Sort { level: LeanLevel::zero() };
        let proof_bytes = bincode::serialize(&clean_cert).expect("serialize");

        // Use unchecked to build the TrustProofCertificate with valid clean bytes
        let cert = generate_certificate_unchecked(&vc, &result, proof_bytes, "clean 0.1.0")
            .expect("should build");

        // Verify: fingerprint matches, deserialization succeeds, kernel rejects
        // because a Sort cert doesn't prove the overflow VC theorem
        let err =
            verify_certificate(&vc, &cert).expect_err("Sort cert should be rejected by kernel");
        assert!(
            matches!(err, CertificateError::KernelRejected { .. }),
            "should be KernelRejected, got {err:?}"
        );
    }

    #[test]
    fn certificate_serialization_roundtrip() {
        let vc = sample_vc();
        let result = sample_result();
        let cert = generate_certificate_unchecked(&vc, &result, vec![0xCA, 0xFE], "trust-wp 0.1.0")
            .expect("should build");

        let json = serde_json::to_string(&cert).expect("serialize");
        let recovered: TrustProofCertificate = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(cert.vc_fingerprint, recovered.vc_fingerprint);
        assert_eq!(cert.proof_term, recovered.proof_term);
        assert_eq!(cert.canonical_vc, recovered.canonical_vc);
        assert_eq!(cert.prover_version, recovered.prover_version);
    }
}
