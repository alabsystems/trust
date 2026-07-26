//! Standalone certificate-record integrity inspection.
//!
//! These APIs check hashes, format, chain shape, signature consistency, and
//! proof-step syntax. They do not replay solver semantics and never establish
//! proof authority.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use sha2::{Digest, Sha256};

use crate::{
    CERT_FORMAT_VERSION, CertError, CertificateId, CertificationStatus, ChainValidator,
    ProofCertificate, TrustLevel, check_certificate_signature_integrity,
};

/// Internal-consistency result for a single public certificate record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateIntegrityResult {
    /// Whether all record-integrity checks succeeded.
    ///
    /// This is not a semantic proof verdict.
    pub integrity_valid: bool,
    /// Individual record-integrity checks.
    pub checks: Vec<IntegrityCheckResult>,
}

/// A single record-integrity check and its outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegrityCheckResult {
    /// Name of the check.
    pub name: String,
    /// Whether the integrity check succeeded.
    pub integrity_ok: bool,
    /// Description or error detail.
    pub detail: String,
}

impl CertificateIntegrityResult {
    fn new() -> Self {
        Self { integrity_valid: true, checks: Vec::new() }
    }

    fn add_check(&mut self, name: &str, integrity_ok: bool, detail: String) {
        if !integrity_ok {
            self.integrity_valid = false;
        }
        self.checks.push(IntegrityCheckResult { name: name.to_string(), integrity_ok, detail });
    }
}

/// Check a public certificate record against canonical VC bytes.
///
/// `true` means only that the public record is internally consistent with the
/// supplied bytes. No proof rules or solver result are replayed.
pub fn check_certificate_integrity(
    cert: &ProofCertificate,
    vc_bytes: &[u8],
) -> Result<bool, CertError> {
    Ok(inspect_certificate_integrity(cert, vc_bytes)?.integrity_valid)
}

/// Inspect a public certificate record with detailed integrity diagnostics.
pub fn inspect_certificate_integrity(
    cert: &ProofCertificate,
    vc_bytes: &[u8],
) -> Result<CertificateIntegrityResult, CertError> {
    let mut result = inspect_embedded_record_integrity(cert);

    // Bind the caller-supplied canonical VC bytes as an additional check.
    let mut hasher = Sha256::new();
    hasher.update(vc_bytes);
    let computed: [u8; 32] = hasher.finalize().into();
    let hash_matches = cert.vc_hash == computed;
    result.add_check(
        "vc_hash_matches_input",
        hash_matches,
        if hash_matches {
            "vc_hash matches sha256(vc_bytes)".to_string()
        } else {
            format!(
                "vc_hash mismatch: certificate has {:02x?}, computed {:02x?}",
                &cert.vc_hash[..4],
                &computed[..4]
            )
        },
    );

    Ok(result)
}

fn inspect_embedded_record_integrity(cert: &ProofCertificate) -> CertificateIntegrityResult {
    let mut result = CertificateIntegrityResult::new();

    let format_ok = cert.version == CERT_FORMAT_VERSION;
    result.add_check(
        "format_version",
        format_ok,
        if format_ok {
            format!("recognized certificate-record format {}", cert.version)
        } else {
            format!(
                "unrecognized certificate-record format {}; expected {CERT_FORMAT_VERSION}",
                cert.version
            )
        },
    );

    let expected_id = CertificateId::generate(&cert.function, &cert.timestamp);
    let id_ok = cert.id == expected_id;
    result.add_check(
        "record_id_binding",
        id_ok,
        if id_ok {
            "record ID matches function and timestamp".to_string()
        } else {
            "record ID does not match function and timestamp".to_string()
        },
    );

    let snapshot_matches = cert.verify_vc_hash();
    result.add_check(
        "vc_hash_matches_snapshot",
        snapshot_matches,
        if snapshot_matches {
            "vc_hash matches embedded VC snapshot".to_string()
        } else {
            "vc_hash does not match embedded VC snapshot".to_string()
        },
    );

    let chain_report = ChainValidator::validate(&cert.chain);
    result.add_check(
        "chain_structure",
        chain_report.valid,
        if chain_report.valid {
            "certificate chain structure is internally consistent".to_string()
        } else {
            format!("certificate chain structure invalid: {:?}", chain_report.findings)
        },
    );

    let steps_ok = cert.check_proof_step_shape();
    result.add_check(
        "proof_step_shape",
        steps_ok.is_ok(),
        match &steps_ok {
            Ok(()) => format!(
                "{} proof-step records are structurally well-formed",
                cert.proof_steps.len()
            ),
            Err(error) => format!("proof-step record malformed: {error}"),
        },
    );

    let function_hash_present = !cert.function_hash.0.is_empty();
    result.add_check(
        "function_hash_present",
        function_hash_present,
        if function_hash_present {
            "function hash is present".to_string()
        } else {
            "function hash is empty".to_string()
        },
    );

    let signature_consistent = match (&cert.status, &cert.signature) {
        (CertificationStatus::Certified, Some(signature)) => {
            matches!(signature.trust_level, TrustLevel::Certifier | TrustLevel::Root)
                && check_certificate_signature_integrity(cert).is_ok()
        }
        (CertificationStatus::Certified, None) => false,
        (CertificationStatus::Trusted, Some(_)) => {
            check_certificate_signature_integrity(cert).is_ok()
        }
        (CertificationStatus::Trusted, None) => true,
    };
    result.add_check(
        "signature_record_consistency",
        signature_consistent,
        if signature_consistent {
            "signature metadata is internally consistent with the record claim".to_string()
        } else {
            "signature metadata is missing, invalid, or inconsistent with the record claim"
                .to_string()
        },
    );

    result
}

// ---------------------------------------------------------------------------
// CertificateIntegrityInspector: accumulated record diagnostics
// ---------------------------------------------------------------------------

/// Accumulated integrity report for one or more public certificate records.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateIntegrityReport {
    /// Number of certificates examined.
    pub total_examined: usize,
    /// Number whose record-integrity checks all succeeded.
    pub integrity_valid_records: usize,
    /// Number that failed one or more record-integrity checks.
    pub integrity_invalid_records: usize,
    /// Per-certificate results, indexed by certificate ID.
    pub results: Vec<(String, CertificateIntegrityResult)>,
    /// Summary of failures: (cert_id, check_name, detail).
    pub failure_details: Vec<(String, String, String)>,
}

impl CertificateIntegrityReport {
    /// Returns true when at least one record was examined and all had valid
    /// internal structure. This is not proof soundness.
    pub fn all_records_integrity_valid(&self) -> bool {
        self.total_examined > 0 && self.integrity_invalid_records == 0
    }

    /// Internally valid record percentage (0.0 - 100.0).
    pub fn integrity_valid_percent(&self) -> f64 {
        if self.total_examined == 0 {
            return 0.0;
        }
        (self.integrity_valid_records as f64 / self.total_examined as f64) * 100.0
    }
}

/// A stateful public-record integrity inspector.
///
/// Use this when verifying a batch of certificates and you want a
/// consolidated report at the end.
pub struct CertificateIntegrityInspector {
    results: Vec<(String, CertificateIntegrityResult)>,
}

impl CertificateIntegrityInspector {
    /// Create a new empty inspector.
    pub fn new() -> Self {
        Self { results: Vec::new() }
    }

    /// Inspect a record against canonical VC bytes and accumulate diagnostics.
    pub fn inspect_against_vc(
        &mut self,
        cert: &ProofCertificate,
        vc_bytes: &[u8],
    ) -> Result<CertificateIntegrityResult, CertError> {
        let result = inspect_certificate_integrity(cert, vc_bytes)?;
        self.results.push((cert.id.0.clone(), result.clone()));
        Ok(result)
    }

    /// Inspect a record using only its embedded metadata.
    ///
    /// Without caller-supplied canonical VC bytes, even the input binding is
    /// self-referential. The result remains an integrity diagnostic only.
    pub fn inspect_embedded_record(
        &mut self,
        cert: &ProofCertificate,
    ) -> CertificateIntegrityResult {
        let result = inspect_embedded_record_integrity(cert);
        self.results.push((cert.id.0.clone(), result.clone()));
        result
    }

    /// Generate a consolidated integrity report.
    pub fn report(&self) -> CertificateIntegrityReport {
        let total_examined = self.results.len();
        let integrity_valid_records =
            self.results.iter().filter(|(_, result)| result.integrity_valid).count();
        let integrity_invalid_records = total_examined - integrity_valid_records;

        let mut failure_details = Vec::new();
        for (cert_id, result) in &self.results {
            for check in &result.checks {
                if !check.integrity_ok {
                    failure_details.push((
                        cert_id.clone(),
                        check.name.clone(),
                        check.detail.clone(),
                    ));
                }
            }
        }

        CertificateIntegrityReport {
            total_examined,
            integrity_valid_records,
            integrity_invalid_records,
            results: self.results.clone(),
            failure_details,
        }
    }

    /// Reset the verifier, clearing all accumulated results.
    pub fn reset(&mut self) {
        self.results.clear();
    }
}

impl Default for CertificateIntegrityInspector {
    fn default() -> Self {
        Self::new()
    }
}

/// Inspect a collection of certificate records.
///
/// No dependency edges are supplied here, so this function makes no chain
/// completeness or composition claim. It applies embedded-record integrity
/// checks independently to each item.
pub fn inspect_certificate_records(certs: &[&ProofCertificate]) -> CertificateIntegrityReport {
    let mut inspector = CertificateIntegrityInspector::new();

    for cert in certs {
        inspector.inspect_embedded_record(cert);
    }

    inspector.report()
}

#[cfg(test)]
mod tests {
    use trust_types::ProofStrength;

    use super::*;
    use crate::{
        CertificateChain, ChainStep, ChainStepType, FunctionHash, ProofStep, SolverInfo, VcSnapshot,
    };

    fn make_vc_bytes(kind: &str, formula: &str) -> Vec<u8> {
        // Must match VcSnapshot::vc_hash canonical form: kind + ":" + formula_json
        let mut bytes = Vec::new();
        bytes.extend_from_slice(kind.as_bytes());
        bytes.extend_from_slice(b":");
        bytes.extend_from_slice(formula.as_bytes());
        bytes
    }

    fn make_cert_with_steps() -> (ProofCertificate, Vec<u8>) {
        let vc_snapshot = VcSnapshot {
            kind: "Assertion".to_string(),
            formula_json: "true".to_string(),
            location: None,
        };
        let vc_bytes = make_vc_bytes("Assertion", "true");
        let solver = SolverInfo {
            name: "ay".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 10,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        };
        let steps = vec![
            ProofStep {
                index: 0,
                rule: "assume".to_string(),
                description: "assume precondition".to_string(),
                premises: vec![],
            },
            ProofStep {
                index: 1,
                rule: "resolution".to_string(),
                description: "resolve with axiom".to_string(),
                premises: vec![0],
            },
        ];
        let chain = {
            let mut c = CertificateChain::new();
            c.push(ChainStep {
                step_type: ChainStepType::VcGeneration,
                tool: "trust_vcgen".to_string(),
                tool_version: "0.1.0".to_string(),
                input_hash: "mir".to_string(),
                output_hash: "vc".to_string(),
                time_ms: 1,
                timestamp: "2026-03-28T00:00:00Z".to_string(),
            });
            c.push(ChainStep {
                step_type: ChainStepType::SolverProof,
                tool: "ay".to_string(),
                tool_version: "1.0.0".to_string(),
                input_hash: "vc".to_string(),
                output_hash: "proof".to_string(),
                time_ms: 10,
                timestamp: "2026-03-28T00:00:01Z".to_string(),
            });
            c
        };

        let cert = ProofCertificate::new_trusted(
            "crate::test_fn".to_string(),
            FunctionHash::from_bytes(b"test-body"),
            vc_snapshot,
            solver,
            vec![],
            "2026-03-28T00:00:00Z".to_string(),
        )
        .with_proof_steps(steps)
        .with_chain(chain);

        (cert, vc_bytes)
    }

    #[test]
    fn test_check_certificate_integrity_valid_record() {
        let (cert, vc_bytes) = make_cert_with_steps();
        let ok =
            check_certificate_integrity(&cert, &vc_bytes).expect("inspection should not error");
        assert!(ok, "internally consistent record should pass integrity checks");
    }

    #[test]
    fn test_inspect_certificate_integrity_valid_record() {
        let (cert, vc_bytes) = make_cert_with_steps();
        let result =
            inspect_certificate_integrity(&cert, &vc_bytes).expect("inspection should not error");
        assert!(result.integrity_valid);
        assert_eq!(result.checks.len(), 8);
        assert!(result.checks.iter().all(|check| check.integrity_ok));
    }

    #[test]
    fn test_integrity_check_wrong_vc_bytes() {
        let (cert, _vc_bytes) = make_cert_with_steps();
        let wrong_bytes = b"wrong vc bytes";
        let ok =
            check_certificate_integrity(&cert, wrong_bytes).expect("inspection should not error");
        assert!(!ok, "wrong vc_bytes should fail integrity binding");
    }

    #[test]
    fn test_integrity_check_bad_proof_step_shape() {
        let (mut cert, vc_bytes) = make_cert_with_steps();
        // Corrupt proof steps: step 1 references step 1 (self-reference)
        cert.proof_steps[1].premises = vec![1];
        let ok =
            check_certificate_integrity(&cert, &vc_bytes).expect("inspection should not error");
        assert!(!ok, "bad proof-step shape should fail integrity inspection");
    }

    #[test]
    fn test_integrity_check_broken_chain() {
        let (mut cert, vc_bytes) = make_cert_with_steps();
        // Break the chain: mismatched hashes
        cert.chain.steps[1].input_hash = "wrong".to_string();
        let ok =
            check_certificate_integrity(&cert, &vc_bytes).expect("inspection should not error");
        assert!(!ok, "broken chain should fail structural inspection");
    }

    #[test]
    fn test_integrity_check_with_witness_record() {
        let (cert, vc_bytes) = make_cert_with_steps();
        let cert = cert.with_witness(vec![0xDE, 0xAD, 0xBE, 0xEF]);
        let ok =
            check_certificate_integrity(&cert, &vc_bytes).expect("inspection should not error");
        assert!(ok, "record with an internally bound witness should pass integrity checks");
    }

    #[test]
    fn forged_certified_claim_without_signature_is_integrity_invalid() {
        let (mut cert, vc_bytes) = make_cert_with_steps();
        cert.status = CertificationStatus::Certified;

        let result = inspect_certificate_integrity(&cert, &vc_bytes).unwrap();
        assert!(!result.integrity_valid);
        let signature_check = result
            .checks
            .iter()
            .find(|check| check.name == "signature_record_consistency")
            .unwrap();
        assert!(!signature_check.integrity_ok);
    }

    #[test]
    fn wrong_format_and_forged_record_id_are_rejected() {
        let (mut cert, vc_bytes) = make_cert_with_steps();
        cert.version = CERT_FORMAT_VERSION + 1;
        cert.id = CertificateId("attacker-selected".to_string());

        let result = inspect_certificate_integrity(&cert, &vc_bytes).unwrap();
        assert!(!result.integrity_valid);
        assert!(
            result.checks.iter().any(|check| check.name == "format_version" && !check.integrity_ok)
        );
        assert!(
            result
                .checks
                .iter()
                .any(|check| check.name == "record_id_binding" && !check.integrity_ok)
        );
    }

    #[test]
    fn incomplete_but_hash_linked_chain_is_rejected() {
        let (mut cert, vc_bytes) = make_cert_with_steps();
        cert.chain.steps.remove(0); // leaves only SolverProof: links are vacuously consistent

        let result = inspect_certificate_integrity(&cert, &vc_bytes).unwrap();
        assert!(!result.integrity_valid);
        assert!(
            result
                .checks
                .iter()
                .any(|check| check.name == "chain_structure" && !check.integrity_ok)
        );
    }

    // -----------------------------------------------------------------------
    // CertificateIntegrityInspector tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_integrity_inspector_new_empty() {
        let inspector = CertificateIntegrityInspector::new();
        let report = inspector.report();
        assert_eq!(report.total_examined, 0);
        assert_eq!(report.integrity_valid_records, 0);
        assert_eq!(report.integrity_invalid_records, 0);
        assert!(!report.all_records_integrity_valid());
        assert!((report.integrity_valid_percent() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_integrity_inspector_valid_record() {
        let mut inspector = CertificateIntegrityInspector::new();
        let (cert, vc_bytes) = make_cert_with_steps();

        let result = inspector.inspect_against_vc(&cert, &vc_bytes).unwrap();
        assert!(result.integrity_valid);

        let report = inspector.report();
        assert_eq!(report.total_examined, 1);
        assert_eq!(report.integrity_valid_records, 1);
        assert_eq!(report.integrity_invalid_records, 0);
        assert!(report.all_records_integrity_valid());
        assert!((report.integrity_valid_percent() - 100.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_integrity_inspector_invalid_record() {
        let mut inspector = CertificateIntegrityInspector::new();
        let (cert, _vc_bytes) = make_cert_with_steps();

        let result = inspector.inspect_against_vc(&cert, b"wrong bytes").unwrap();
        assert!(!result.integrity_valid);

        let report = inspector.report();
        assert_eq!(report.total_examined, 1);
        assert_eq!(report.integrity_valid_records, 0);
        assert_eq!(report.integrity_invalid_records, 1);
        assert!(!report.all_records_integrity_valid());
        assert!(!report.failure_details.is_empty());
    }

    #[test]
    fn test_integrity_inspector_mixed_records() {
        let mut inspector = CertificateIntegrityInspector::new();
        let (cert1, vc_bytes1) = make_cert_with_steps();
        let (cert2, _vc_bytes2) = make_cert_with_steps();

        inspector.inspect_against_vc(&cert1, &vc_bytes1).unwrap();
        inspector.inspect_against_vc(&cert2, b"wrong").unwrap();

        let report = inspector.report();
        assert_eq!(report.total_examined, 2);
        assert_eq!(report.integrity_valid_records, 1);
        assert_eq!(report.integrity_invalid_records, 1);
        assert!((report.integrity_valid_percent() - 50.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_integrity_inspector_reset() {
        let mut inspector = CertificateIntegrityInspector::new();
        let (cert, vc_bytes) = make_cert_with_steps();

        inspector.inspect_against_vc(&cert, &vc_bytes).unwrap();
        assert_eq!(inspector.report().total_examined, 1);

        inspector.reset();
        assert_eq!(inspector.report().total_examined, 0);
    }

    #[test]
    fn test_integrity_inspector_embedded_record() {
        let mut inspector = CertificateIntegrityInspector::new();
        let (cert, _vc_bytes) = make_cert_with_steps();

        let result = inspector.inspect_embedded_record(&cert);
        assert!(result.integrity_valid);
        assert_eq!(result.checks.len(), 7);
        assert!(result.checks.iter().all(|check| check.integrity_ok));
    }

    #[test]
    fn test_integrity_inspector_embedded_bad_vc_hash() {
        let mut inspector = CertificateIntegrityInspector::new();
        let (mut cert, _) = make_cert_with_steps();
        cert.vc_hash[0] ^= 0xFF; // corrupt

        let result = inspector.inspect_embedded_record(&cert);
        assert!(!result.integrity_valid);
        let failed_check = result.checks.iter().find(|check| !check.integrity_ok).unwrap();
        assert_eq!(failed_check.name, "vc_hash_matches_snapshot");
    }

    #[test]
    fn test_integrity_inspector_embedded_broken_chain() {
        let mut inspector = CertificateIntegrityInspector::new();
        let (mut cert, _) = make_cert_with_steps();
        cert.chain.steps[1].input_hash = "broken".to_string();

        let result = inspector.inspect_embedded_record(&cert);
        assert!(!result.integrity_valid);
        let failed = result.checks.iter().find(|check| check.name == "chain_structure").unwrap();
        assert!(!failed.integrity_ok);
    }

    #[test]
    fn test_integrity_inspector_default() {
        let inspector = CertificateIntegrityInspector::default();
        assert_eq!(inspector.report().total_examined, 0);
    }

    // -----------------------------------------------------------------------
    // inspect_certificate_records tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_inspect_certificate_records_single() {
        let (cert, _) = make_cert_with_steps();
        let report = inspect_certificate_records(&[&cert]);
        assert_eq!(report.total_examined, 1);
        assert!(report.all_records_integrity_valid());
    }

    #[test]
    fn test_inspect_certificate_records_multiple() {
        let (cert1, _) = make_cert_with_steps();
        let (cert2, _) = make_cert_with_steps();
        let report = inspect_certificate_records(&[&cert1, &cert2]);
        assert_eq!(report.total_examined, 2);
        assert_eq!(report.integrity_valid_records, 2);
        assert!(report.all_records_integrity_valid());
    }

    #[test]
    fn test_inspect_certificate_records_with_invalid_record() {
        let (cert1, _) = make_cert_with_steps();
        let (mut cert2, _) = make_cert_with_steps();
        cert2.vc_hash[0] ^= 0xFF; // corrupt second cert

        let report = inspect_certificate_records(&[&cert1, &cert2]);
        assert_eq!(report.total_examined, 2);
        assert_eq!(report.integrity_valid_records, 1);
        assert_eq!(report.integrity_invalid_records, 1);
        assert!(!report.all_records_integrity_valid());
    }

    #[test]
    fn test_inspect_certificate_records_empty_fails_closed() {
        let report = inspect_certificate_records(&[]);
        assert_eq!(report.total_examined, 0);
        assert!(!report.all_records_integrity_valid());
    }

    #[test]
    fn test_verification_report_failure_details() {
        let (mut cert, _) = make_cert_with_steps();
        cert.vc_hash[0] ^= 0xFF;
        cert.chain.steps[1].input_hash = "broken".to_string();

        let report = inspect_certificate_records(&[&cert]);
        assert!(!report.all_records_integrity_valid());
        // Should have at least 2 failure details (vc_hash + chain)
        assert!(
            report.failure_details.len() >= 2,
            "expected at least 2 failures, got: {:?}",
            report.failure_details
        );
    }
}
