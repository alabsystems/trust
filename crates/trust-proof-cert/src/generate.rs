// trust-proof-cert/generate.rs: Certificate-record generation from reported outcomes
//
// Packages VerifiableFunction + VerificationResult records with an internal
// SHA-256 digest. Public result records are not replay authority.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use trust_types::{VerifiableFunction, VerificationCondition, VerificationResult};

use crate::{
    CertError, CertificateChain, ChainStep, ChainStepType, FunctionHash, ProofCertificate,
    SolverInfo, VcSnapshot,
};

/// A single reported VC-result entry within a generated certificate record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VcResultRecord {
    /// Snapshot of the verification condition.
    pub vc_snapshot: VcSnapshot,
    /// Solver that produced the result.
    pub solver: String,
    /// Caller-reported proof-strength description (e.g., "smt_unsat").
    pub reported_strength: String,
    /// Time spent solving in milliseconds.
    pub time_ms: u64,
    /// Whether the public input record reported a `Proved` outcome.
    ///
    /// This is inventory metadata, not a locally replayed verdict.
    pub reported_proved: bool,
    /// Non-authoritative evidence metadata from the input result. Certified
    /// assurance is capped because this packaging path performs no replay.
    #[serde(skip_serializing_if = "Option::is_none")]
    #[serde(default)]
    pub evidence: Option<trust_types::ProofEvidence>,
}

/// Assumptions under which the certificate was generated.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[derive(Default)]
pub struct Assumptions {
    /// Preconditions assumed from the function spec.
    pub preconditions: Vec<String>,
    /// Callee postconditions assumed (cross-function composition).
    pub callee_postconditions: Vec<String>,
    /// Any additional solver-level assumptions.
    pub solver_assumptions: Vec<String>,
}

/// Environment information captured at certificate generation time.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[derive(Default)]
pub struct Environment {
    /// Trust compiler version.
    pub trust_version: String,
    /// Rust toolchain version.
    pub toolchain: String,
    /// Target triple (e.g., "x86_64-unknown-linux-gnu").
    pub target: String,
}

/// A generated public certificate record with provenance metadata.
///
/// This wraps a `ProofCertificate` with additional metadata about the
/// verification process: individual VC results, assumptions, environment,
/// and a SHA-256 record digest covering all fields. The digest detects internal
/// corruption but is neither a signature nor proof validation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratedCertificateRecord {
    /// The core proof certificate.
    pub certificate: ProofCertificate,
    /// Function signature (def_path from VerifiableFunction).
    pub function_signature: String,
    /// SHA-256 hash of the function signature.
    pub signature_hash: String,
    /// Individual reported VC-result records.
    pub vc_entries: Vec<VcResultRecord>,
    /// Assumptions under which verification was performed.
    pub assumptions: Assumptions,
    /// Environment at generation time.
    pub environment: Environment,
    /// SHA-256 digest of all record fields (internal consistency only).
    pub record_digest: String,
}

impl GeneratedCertificateRecord {
    /// Serialize to JSON.
    pub fn to_json(&self) -> Result<String, CertError> {
        self.validate_public_record()?;
        serde_json::to_string_pretty(self)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })
    }

    /// Deserialize from JSON.
    pub fn from_json(json: &str) -> Result<Self, CertError> {
        let record: Self = serde_json::from_str(json)
            .map_err(|e| CertError::SerializationFailed { reason: e.to_string() })?;
        record.validate_public_record()?;
        Ok(record)
    }

    fn validate_public_record(&self) -> Result<(), CertError> {
        // R-U Phase C (grade migration): gate on the multi-axis grade record
        // instead of matching the legacy enum. Verdict-identical: on the
        // from_legacy image, `is_certified()` holds exactly for
        // `AssuranceLevel::Certified` (pinned by
        // named_constructor_projects_to_its_legacy_level in trust-types).
        let evidence_is_non_authoritative =
            self.certificate.solver.evidence.as_ref().is_none_or(|evidence| {
                !evidence.grade().is_certified()
            }) && self.vc_entries.iter().all(|entry| {
                entry.evidence.as_ref().is_none_or(|evidence| !evidence.grade().is_certified())
            });
        let primary_entry_present = self.vc_entries.iter().any(|entry| {
            entry.reported_proved && entry.vc_snapshot == self.certificate.vc_snapshot
        });
        let structure_valid = self.function_signature == self.certificate.function
            && self.signature_hash == compute_signature_hash(&self.function_signature)
            && self.certificate.version == crate::CERT_FORMAT_VERSION
            && self.certificate.id
                == crate::CertificateId::generate(
                    &self.certificate.function,
                    &self.certificate.timestamp,
                )
            && self.certificate.verify_vc_hash()
            && self.certificate.check_proof_step_shape().is_ok()
            && crate::ChainValidator::validate(&self.certificate.chain).valid
            && matches!(self.certificate.status, crate::CertificationStatus::Trusted)
            && !self.certificate.solver.strength.grade().is_certified()
            && evidence_is_non_authoritative
            && primary_entry_present;
        if !structure_valid || !check_generated_record_integrity(self)? {
            return Err(CertError::InvalidCertificate {
                reason: "generated certificate record failed schema, binding, assurance-cap, chain, or digest checks"
                    .to_string(),
            });
        }
        Ok(())
    }
}

/// Package reported solver outcomes into a public certificate record.
///
/// Takes the function under verification and the paired (VC, result) outcomes
/// from the solver(s). The inputs are public constructible values, so this
/// function records their claims and never grants proof authority.
///
/// # Errors
///
/// Returns `CertError` if VC snapshot creation fails, serialization fails,
/// or no VC result reports `Proved`.
pub fn generate_certificate_record(
    func: &VerifiableFunction,
    results: &[(VerificationCondition, VerificationResult)],
) -> Result<GeneratedCertificateRecord, CertError> {
    generate_certificate_record_with_env(
        func,
        results,
        Assumptions::default(),
        Environment::default(),
    )
}

/// Package a certificate record with explicit assumptions and environment.
pub fn generate_certificate_record_with_env(
    func: &VerifiableFunction,
    results: &[(VerificationCondition, VerificationResult)],
    assumptions: Assumptions,
    environment: Environment,
) -> Result<GeneratedCertificateRecord, CertError> {
    if results.is_empty() {
        return Err(CertError::InvalidCertificate {
            reason: "no verification results provided".to_string(),
        });
    }

    let timestamp = current_timestamp();
    let function_hash = FunctionHash::from_bytes(func.content_hash().as_bytes());
    let signature_hash = compute_signature_hash(&func.def_path);

    // Build VC proof entries
    let mut vc_entries = Vec::with_capacity(results.len());
    for (vc, result) in results {
        let vc_snapshot = VcSnapshot::from_vc(vc)?;
        let (solver, reported_strength, time_ms, reported_proved) = extract_result_info(result);
        let evidence =
            result.evidence().map(crate::evidence::cap_unvalidated_certificate_assurance);
        vc_entries.push(VcResultRecord {
            vc_snapshot,
            solver,
            reported_strength,
            time_ms,
            reported_proved,
            evidence,
        });
    }

    // Find the first proved result to use as the primary certificate.
    let primary_idx = results.iter().position(|(_, r)| r.is_proved()).ok_or_else(|| {
        CertError::InvalidCertificate {
            reason: "no input record reports Proved; cannot choose a primary record".to_string(),
        }
    })?;

    let (primary_vc, primary_result) = &results[primary_idx];
    let primary_snapshot = VcSnapshot::from_vc(primary_vc)?;
    let (solver_name, _, solver_time, _) = extract_result_info(primary_result);

    // Public result metadata cannot mint Certified assurance on a packaging path.
    let primary_evidence =
        primary_result.evidence().map(crate::evidence::cap_unvalidated_certificate_assurance);

    let solver_info = match primary_result {
        VerificationResult::Proved { solver, time_ms, strength, .. } => SolverInfo {
            name: solver.to_string(),
            version: String::new(),
            time_ms: *time_ms,
            strength: cap_unchecked_record_strength(strength.clone()),
            evidence: primary_evidence,
        },
        _ => {
            return Err(CertError::InvalidCertificate {
                reason: "primary result is not Proved after index lookup".to_string(),
            });
        }
    };

    // P1-15: Compute actual hashes for the chain instead of placeholders.
    let mir_hash = &function_hash.0;
    let vc_hash_hex =
        format!("{:x}", sha2::Sha256::digest(primary_snapshot.formula_json.as_bytes()));
    let chain = build_chain(&solver_name, solver_time, mir_hash, &vc_hash_hex);

    let certificate = ProofCertificate::new_trusted(
        func.def_path.clone(),
        function_hash,
        primary_snapshot,
        solver_info,
        Vec::new(),
        timestamp,
    )
    .with_chain(chain);

    // Populate assumptions from function spec
    let assumptions = populate_assumptions(func, assumptions);

    let mut generated = GeneratedCertificateRecord {
        certificate,
        function_signature: func.def_path.clone(),
        signature_hash,
        vc_entries,
        assumptions,
        environment,
        record_digest: String::new(), // computed below
    };

    // Compute the internal record digest over all fields.
    generated.record_digest = compute_record_digest(&generated)?;

    Ok(generated)
}

/// Check a generated record's internal digest.
///
/// Success detects accidental mutation only. An attacker can construct a record
/// and recompute its digest, so this is not authenticity or proof authority.
pub fn check_generated_record_integrity(
    cert: &GeneratedCertificateRecord,
) -> Result<bool, CertError> {
    let recomputed = compute_record_digest(cert)?;
    Ok(cert.record_digest == recomputed)
}

/// Compute a SHA-256 digest over every generated-record field except the digest.
fn compute_record_digest(cert: &GeneratedCertificateRecord) -> Result<String, CertError> {
    #[derive(Serialize)]
    struct DigestPayload<'a> {
        domain: &'static str,
        certificate: &'a ProofCertificate,
        function_signature: &'a str,
        signature_hash: &'a str,
        vc_entries: &'a [VcResultRecord],
        assumptions: &'a Assumptions,
        environment: &'a Environment,
    }

    let payload = serde_json::to_vec(&DigestPayload {
        domain: "trust-proof-cert.generated-record-digest.v2",
        certificate: &cert.certificate,
        function_signature: &cert.function_signature,
        signature_hash: &cert.signature_hash,
        vc_entries: &cert.vc_entries,
        assumptions: &cert.assumptions,
        environment: &cert.environment,
    })
    .map_err(|error| CertError::SerializationFailed { reason: error.to_string() })?;

    let mut hasher = Sha256::new();
    hasher.update(payload);
    Ok(format!("{:x}", hasher.finalize()))
}

/// Compute SHA-256 hash of a function signature string.
fn compute_signature_hash(signature: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(signature.as_bytes());
    format!("{:x}", hasher.finalize())
}

/// Extract solver name, strength description, time, and proved status from a result.
fn extract_result_info(result: &VerificationResult) -> (String, String, u64, bool) {
    match result {
        VerificationResult::Proved { solver, time_ms, strength, .. } => {
            (solver.to_string(), format!("{:?}", strength), *time_ms, true)
        }
        VerificationResult::Failed { solver, time_ms, .. } => {
            (solver.to_string(), "failed".to_string(), *time_ms, false)
        }
        VerificationResult::Unknown { solver, time_ms, reason } => {
            (solver.to_string(), format!("unknown: {reason}"), *time_ms, false)
        }
        VerificationResult::Timeout { solver, timeout_ms } => {
            (solver.to_string(), "timeout".to_string(), *timeout_ms, false)
        }
        _ => ("unknown".to_string(), "unhandled variant".to_string(), 0, false),
    }
}

fn cap_unchecked_record_strength(
    mut strength: trust_types::ProofStrength,
) -> trust_types::ProofStrength {
    // R-U Phase C: the downgrade is expressed through the grade record's
    // named constructors and projected back to the carried legacy level
    // (projection pinned by named_constructor_projects_to_its_legacy_level).
    if strength.grade().is_certified() {
        strength.assurance = trust_types::grade::GradeRecord::smt_backed().to_legacy();
    }
    strength
}

/// Build a basic certificate chain for a solver result.
///
/// (P1-15): Uses actual SHA-256 hashes for all chain steps.
fn build_chain(solver_name: &str, time_ms: u64, mir_hash: &str, vc_hash: &str) -> CertificateChain {
    // (P1-15): Compute a proper SHA-256 proof output hash.
    let mut proof_hasher = Sha256::new();
    proof_hasher.update(solver_name.as_bytes());
    proof_hasher.update(b":");
    proof_hasher.update(vc_hash.as_bytes());
    proof_hasher.update(b":");
    proof_hasher.update(time_ms.to_le_bytes());
    let proof_hash = format!("{:x}", proof_hasher.finalize());

    let mut chain = CertificateChain::new();
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: mir_hash.to_string(),
        output_hash: vc_hash.to_string(),
        time_ms: 0,
        timestamp: current_timestamp(),
    });
    chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: solver_name.to_string(),
        tool_version: String::new(),
        input_hash: vc_hash.to_string(),
        output_hash: proof_hash,
        time_ms,
        timestamp: current_timestamp(),
    });
    chain
}

/// Populate assumptions from the function's spec.
fn populate_assumptions(func: &VerifiableFunction, mut assumptions: Assumptions) -> Assumptions {
    // Add preconditions from function spec
    for pre in &func.preconditions {
        assumptions.preconditions.push(format!("{pre:?}"));
    }
    // Add postconditions from contracts
    for contract in &func.contracts {
        assumptions.callee_postconditions.push(format!("{contract:?}"));
    }
    assumptions
}

/// Get the current UTC timestamp in ISO 8601 format.
///
/// Falls back to a fixed timestamp if system time is unavailable.
fn current_timestamp() -> String {
    // Use a simple epoch-based timestamp since we don't have chrono.
    // In production this would use a proper time library.
    let dur =
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
    format!("{}Z", dur.as_secs())
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BlockId, Formula, FunctionSpec, HardenedVcCategory, LocalDecl, ProofStrength,
        SourceSpan, Terminator, Ty, VcKind, VerifiableBody, VerifiableFunction,
        VerificationCondition, VerificationResult,
    };

    use super::*;

    /// R-U Phase C wave-1 verdict-preservation pin (table-driven): the
    /// grade-record forms of the migrated gates are extensionally identical
    /// to the legacy `matches!` forms for EVERY assurance level and both
    /// reasoning shapes, and the minted downgrade projects to exactly the
    /// legacy level the old code assigned.
    #[test]
    fn grade_migration_preserves_legacy_gate_verdicts() {
        use trust_types::{AssuranceLevel, ReasoningKind};
        let levels = [
            AssuranceLevel::Sound,
            AssuranceLevel::BoundedSound { depth: 7 },
            AssuranceLevel::Heuristic,
            AssuranceLevel::Unchecked,
            AssuranceLevel::Trusted,
            AssuranceLevel::SmtBacked,
            AssuranceLevel::Certified,
        ];
        let reasonings =
            [ReasoningKind::Smt, ReasoningKind::BoundedModelCheck { depth: 3 }];
        for reasoning in &reasonings {
            for level in &levels {
                let strength =
                    ProofStrength { reasoning: reasoning.clone(), assurance: level.clone() };
                assert_eq!(
                    strength.grade().is_certified(),
                    matches!(strength.assurance, AssuranceLevel::Certified),
                    "gate equivalence must hold for {level:?} / {reasoning:?}",
                );
                let capped = cap_unchecked_record_strength(strength.clone());
                let mut legacy = strength.clone();
                if matches!(legacy.assurance, AssuranceLevel::Certified) {
                    legacy.assurance = AssuranceLevel::SmtBacked;
                }
                assert_eq!(
                    capped.assurance, legacy.assurance,
                    "cap equivalence must hold for {level:?} / {reasoning:?}",
                );
            }
        }
        assert_eq!(
            trust_types::grade::GradeRecord::smt_backed().to_legacy(),
            AssuranceLevel::SmtBacked,
            "the minted downgrade must project to the exact legacy level",
        );
    }

    fn sample_function() -> VerifiableFunction {
        VerifiableFunction {
            name: "add".to_string(),
            def_path: "crate::math::add".to_string(),
            span: SourceSpan {
                file: "src/math.rs".to_string(),
                line_start: 10,
                col_start: 0,
                line_end: 15,
                col_end: 1,
            },
            body: VerifiableBody {
                locals: vec![LocalDecl {
                    index: 0,
                    name: Some("_0".to_string()),
                    ty: Ty::Int { width: 32, signed: true },
                }],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::Int { width: 32, signed: true },
            },
            contracts: Vec::new(),
            preconditions: vec![Formula::Bool(true)],
            postconditions: vec![Formula::Bool(true)],
            spec: FunctionSpec::default(),
        }
    }

    fn sample_vc(kind_msg: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: kind_msg.to_string() },
            function: "crate::math::add".into(),
            location: SourceSpan {
                file: "src/math.rs".to_string(),
                line_start: 12,
                col_start: 4,
                line_end: 12,
                col_end: 20,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn proved_result() -> VerificationResult {
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn failed_result() -> VerificationResult {
        VerificationResult::Failed { solver: "ay".into(), time_ms: 15, counterexample: None }
    }

    fn assert_no_reported_proved_error(result: Result<GeneratedCertificateRecord, CertError>) {
        let err = result.expect_err("record generation should fail without a reported Proved VC");

        match err {
            CertError::InvalidCertificate { reason } => {
                assert!(
                    reason.contains("reports Proved"),
                    "error should mention missing reported Proved VC, got: {reason}"
                );
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    // -----------------------------------------------------------------------
    // generate_certificate_record tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_certificate_record_single_reported_proved() {
        let func = sample_function();
        let vc = sample_vc("result must be positive");
        let results = vec![(vc, proved_result())];

        let cert = generate_certificate_record(&func, &results)
            .expect("certificate-record generation should succeed");

        assert_eq!(cert.function_signature, "crate::math::add");
        assert!(!cert.signature_hash.is_empty());
        assert_eq!(cert.vc_entries.len(), 1);
        assert!(cert.vc_entries[0].reported_proved);
        assert_eq!(cert.vc_entries[0].solver, "ay");
        assert_eq!(cert.vc_entries[0].time_ms, 42);
        assert!(!cert.record_digest.is_empty());
        assert_eq!(cert.record_digest.len(), 64); // SHA-256 hex
    }

    #[test]
    fn test_generate_certificate_multiple_vcs() {
        let func = sample_function();
        let results = vec![
            (sample_vc("assertion 1"), proved_result()),
            (sample_vc("assertion 2"), failed_result()),
            (sample_vc("assertion 3"), proved_result()),
        ];

        let cert = generate_certificate_record(&func, &results).expect("should succeed");

        assert_eq!(cert.vc_entries.len(), 3);
        assert!(cert.vc_entries[0].reported_proved);
        assert!(!cert.vc_entries[1].reported_proved);
        assert!(cert.vc_entries[2].reported_proved);

        // Primary certificate should be from the first proved VC
        assert_eq!(cert.certificate.solver.name, "ay");
    }

    #[test]
    fn test_generate_certificate_no_proved_fails() {
        let func = sample_function();
        let results = vec![
            (sample_vc("assertion 1"), failed_result()),
            (
                sample_vc("assertion 2"),
                VerificationResult::Unknown {
                    solver: "trust-wp".into(),
                    time_ms: 100,
                    reason: "incomplete".to_string(),
                },
            ),
        ];

        assert_no_reported_proved_error(generate_certificate_record(&func, &results));
    }

    #[test]
    fn test_generate_certificate_empty_results_fails() {
        let func = sample_function();
        let results: Vec<(VerificationCondition, VerificationResult)> = vec![];

        let err =
            generate_certificate_record(&func, &results).expect_err("should fail with no results");

        match err {
            CertError::InvalidCertificate { reason } => {
                assert!(reason.contains("no verification results"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_generate_certificate_with_timeout() {
        let func = sample_function();
        let results = vec![(
            sample_vc("assertion"),
            VerificationResult::Timeout { solver: "clean".into(), timeout_ms: 5000 },
        )];

        assert_no_reported_proved_error(generate_certificate_record(&func, &results));
    }

    // -----------------------------------------------------------------------
    // check_generated_record_integrity tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_certificate_integrity_valid() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let cert = generate_certificate_record(&func, &results).unwrap();
        assert!(check_generated_record_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_returns_result() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];
        let cert = generate_certificate_record(&func, &results).unwrap();

        assert!(check_generated_record_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_tampered_signature() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let mut cert = generate_certificate_record(&func, &results).unwrap();
        cert.function_signature = "tampered::path".to_string();

        assert!(!check_generated_record_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_tampered_vc_entry() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let mut cert = generate_certificate_record(&func, &results).unwrap();
        cert.vc_entries[0].reported_proved = false;

        assert!(!check_generated_record_integrity(&cert).unwrap());
    }

    #[test]
    fn generated_record_digest_covers_entire_inner_certificate() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];
        let cert = generate_certificate_record(&func, &results).unwrap();

        let mut trace_tampered = cert.clone();
        trace_tampered.certificate.proof_trace.push(0xAA);
        assert!(!check_generated_record_integrity(&trace_tampered).unwrap());

        let mut chain_tampered = cert.clone();
        chain_tampered.certificate.chain.steps[0].tool = "attacker".to_string();
        assert!(!check_generated_record_integrity(&chain_tampered).unwrap());

        let mut version_tampered = cert;
        version_tampered.certificate.version += 1;
        assert!(!check_generated_record_integrity(&version_tampered).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_tampered_hash() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let mut cert = generate_certificate_record(&func, &results).unwrap();
        cert.record_digest = "0".repeat(64);

        assert!(!check_generated_record_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_tampered_environment() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let mut cert = generate_certificate_record(&func, &results).unwrap();
        cert.environment.trust_version = "evil-version".to_string();

        assert!(!check_generated_record_integrity(&cert).unwrap());
    }

    #[test]
    fn test_verify_certificate_integrity_tampered_assumptions() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let mut cert = generate_certificate_record(&func, &results).unwrap();
        cert.assumptions.solver_assumptions.push("injected_assumption".to_string());

        assert!(!check_generated_record_integrity(&cert).unwrap());
    }

    // -----------------------------------------------------------------------
    // JSON roundtrip tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generated_certificate_json_roundtrip() {
        let func = sample_function();
        let results =
            vec![(sample_vc("vc1"), proved_result()), (sample_vc("vc2"), failed_result())];

        let cert = generate_certificate_record(&func, &results).unwrap();
        let json = cert.to_json().expect("serialization should succeed");
        let restored =
            GeneratedCertificateRecord::from_json(&json).expect("deserialization should succeed");

        assert_eq!(restored.record_digest, cert.record_digest);
        assert_eq!(restored.function_signature, cert.function_signature);
        assert_eq!(restored.vc_entries.len(), cert.vc_entries.len());
        assert!(check_generated_record_integrity(&restored).unwrap());
    }

    #[test]
    fn test_json_roundtrip_preserves_all_fields() {
        let func = sample_function();
        let results = vec![(sample_vc("vc1"), proved_result())];

        let env = Environment {
            trust_version: "0.1.0".to_string(),
            toolchain: "nightly-2026-03-30".to_string(),
            target: "x86_64-unknown-linux-gnu".to_string(),
        };
        let assumptions = Assumptions {
            preconditions: vec!["x > 0".to_string()],
            callee_postconditions: vec!["result >= x".to_string()],
            solver_assumptions: vec![],
        };

        let cert = generate_certificate_record_with_env(&func, &results, assumptions, env).unwrap();
        let json = cert.to_json().unwrap();
        let restored = GeneratedCertificateRecord::from_json(&json).unwrap();

        assert_eq!(restored.environment.trust_version, "0.1.0");
        assert_eq!(restored.environment.toolchain, "nightly-2026-03-30");
        // "x > 0" was explicitly provided; "Bool(true)" comes from func.preconditions
        assert!(restored.assumptions.preconditions.contains(&"x > 0".to_string()));
        assert_eq!(restored.assumptions.callee_postconditions, vec!["result >= x"]);
        assert!(check_generated_record_integrity(&restored).unwrap());
    }

    // -----------------------------------------------------------------------
    // generate_certificate_record_with_env tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_with_custom_env() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];
        let env = Environment {
            trust_version: "1.0.0".to_string(),
            toolchain: "stable-2026".to_string(),
            target: "aarch64-apple-darwin".to_string(),
        };

        let cert =
            generate_certificate_record_with_env(&func, &results, Assumptions::default(), env)
                .unwrap();

        assert_eq!(cert.environment.trust_version, "1.0.0");
        assert_eq!(cert.environment.target, "aarch64-apple-darwin");
        assert!(check_generated_record_integrity(&cert).unwrap());
    }

    #[test]
    fn test_generate_with_assumptions() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];
        let assumptions = Assumptions {
            preconditions: vec!["x > 0".to_string()],
            callee_postconditions: vec![],
            solver_assumptions: vec!["no-overflow".to_string()],
        };

        let cert = generate_certificate_record_with_env(
            &func,
            &results,
            assumptions,
            Environment::default(),
        )
        .unwrap();

        // Should have the explicit assumption plus those extracted from the function
        assert!(cert.assumptions.preconditions.contains(&"x > 0".to_string()));
        assert!(cert.assumptions.solver_assumptions.contains(&"no-overflow".to_string()));
        assert!(check_generated_record_integrity(&cert).unwrap());
    }

    // -----------------------------------------------------------------------
    // Helper function tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_compute_signature_hash_deterministic() {
        let h1 = compute_signature_hash("crate::math::add");
        let h2 = compute_signature_hash("crate::math::add");
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 64);
    }

    #[test]
    fn test_compute_signature_hash_different_inputs() {
        let h1 = compute_signature_hash("crate::math::add");
        let h2 = compute_signature_hash("crate::math::sub");
        assert_ne!(h1, h2);
    }

    #[test]
    fn test_certificate_hash_deterministic() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let cert1 = generate_certificate_record(&func, &results).unwrap();
        let cert2 = generate_certificate_record(&func, &results).unwrap();

        // Hashes may differ due to timestamp, but both should verify
        assert!(check_generated_record_integrity(&cert1).unwrap());
        assert!(check_generated_record_integrity(&cert2).unwrap());
    }

    #[test]
    fn test_function_preconditions_in_assumptions() {
        let mut func = sample_function();
        func.preconditions = vec![Formula::Bool(true), Formula::Bool(false)];

        let results = vec![(sample_vc("test"), proved_result())];
        let cert = generate_certificate_record(&func, &results).unwrap();

        // Should have 2 preconditions from the function
        assert_eq!(cert.assumptions.preconditions.len(), 2);
    }

    // -----------------------------------------------------------------------
    // Bug #385: Failed/Unknown/Timeout must NOT get smt_unsat() strength
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_certificate_failed_result_not_smt_unsat() {
        let func = sample_function();
        let results = vec![(sample_vc("test"), failed_result())];

        assert_no_reported_proved_error(generate_certificate_record(&func, &results));
    }

    #[test]
    fn test_generate_certificate_unknown_result_not_smt_unsat() {
        let func = sample_function();
        let results = vec![(
            sample_vc("test"),
            VerificationResult::Unknown {
                solver: "ay".into(),
                time_ms: 50,
                reason: "incomplete".to_string(),
            },
        )];

        assert_no_reported_proved_error(generate_certificate_record(&func, &results));
    }

    #[test]
    fn test_generate_certificate_timeout_result_not_smt_unsat() {
        let func = sample_function();
        let results = vec![(
            sample_vc("test"),
            VerificationResult::Timeout { solver: "clean".into(), timeout_ms: 5000 },
        )];

        assert_no_reported_proved_error(generate_certificate_record(&func, &results));
    }

    #[test]
    fn test_generate_certificate_proved_result_is_smt_unsat() {
        // Proved results should still get smt_unsat() strength -- verify we didn't break this.
        let func = sample_function();
        let results = vec![(sample_vc("test"), proved_result())];

        let cert = generate_certificate_record(&func, &results).unwrap();

        assert!(
            cert.certificate.solver.strength.is_sound(),
            "Proved result should have Sound assurance, got: {:?}",
            cert.certificate.solver.strength
        );
        assert_eq!(cert.certificate.solver.strength, ProofStrength::smt_unsat());
    }

    // -----------------------------------------------------------------------
    // ProofEvidence pipeline integration tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_evidence_flows_through_certificate_generation() {
        // Verify that ProofEvidence is produced from VerificationResult and
        // stored in both the SolverInfo and VcResultRecord.
        let func = sample_function();
        let results = vec![(sample_vc("evidence-test"), proved_result())];

        let cert = generate_certificate_record(&func, &results)
            .expect("certificate-record generation should succeed");

        // SolverInfo should have evidence derived from smt_unsat() strength
        let solver_evidence = cert
            .certificate
            .solver
            .evidence
            .as_ref()
            .expect("proved result must produce ProofEvidence in SolverInfo");
        assert_eq!(solver_evidence.reasoning, trust_types::ReasoningKind::Smt);
        assert_eq!(solver_evidence.assurance, trust_types::AssuranceLevel::SmtBacked);

        // VcResultRecord should also have evidence
        let vc_evidence =
            cert.vc_entries[0].evidence.as_ref().expect("proved VC entry must have ProofEvidence");
        assert_eq!(vc_evidence.reasoning, trust_types::ReasoningKind::Smt);
        assert_eq!(vc_evidence.assurance, trust_types::AssuranceLevel::SmtBacked);
    }

    #[test]
    fn test_proof_evidence_absent_for_failed_results() {
        let func = sample_function();
        let results = vec![(sample_vc("fail-test"), failed_result())];

        assert_no_reported_proved_error(generate_certificate_record(&func, &results));
    }

    #[test]
    fn test_proof_evidence_survives_json_roundtrip() {
        // End-to-end: generate with evidence, serialize to JSON, deserialize,
        // verify evidence is preserved.
        let func = sample_function();
        let results = vec![(sample_vc("roundtrip"), proved_result())];

        let cert = generate_certificate_record(&func, &results).unwrap();
        let json = cert.to_json().expect("JSON serialization");
        let restored = GeneratedCertificateRecord::from_json(&json).expect("JSON deserialization");

        let original_evidence = cert.certificate.solver.evidence.as_ref().unwrap();
        let restored_evidence = restored
            .certificate
            .solver
            .evidence
            .as_ref()
            .expect("evidence must survive JSON roundtrip");
        assert_eq!(original_evidence.reasoning, restored_evidence.reasoning);
        assert_eq!(original_evidence.assurance, restored_evidence.assurance);

        // VC entry evidence too
        let orig_vc_ev = cert.vc_entries[0].evidence.as_ref().unwrap();
        let rest_vc_ev = restored.vc_entries[0]
            .evidence
            .as_ref()
            .expect("VC evidence must survive JSON roundtrip");
        assert_eq!(orig_vc_ev.reasoning, rest_vc_ev.reasoning);
        assert_eq!(orig_vc_ev.assurance, rest_vc_ev.assurance);
    }

    #[test]
    fn public_certified_result_is_capped_on_packaging_path() {
        let func = sample_function();
        let result = VerificationResult::Proved {
            solver: "caller-controlled".into(),
            time_ms: 1,
            strength: ProofStrength::smt_unsat_certified(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        };

        let record = generate_certificate_record(&func, &[(sample_vc("claim"), result)]).unwrap();
        assert_eq!(
            record.certificate.solver.strength.assurance,
            trust_types::AssuranceLevel::SmtBacked
        );
        assert_eq!(
            record.certificate.solver.evidence.as_ref().unwrap().assurance,
            trust_types::AssuranceLevel::SmtBacked
        );
        assert_eq!(
            record.vc_entries[0].evidence.as_ref().unwrap().assurance,
            trust_types::AssuranceLevel::SmtBacked
        );
        assert!(record.vc_entries[0].reported_proved);
    }

    #[test]
    fn forged_certified_generated_record_is_rejected_even_with_recomputed_digest() {
        let func = sample_function();
        let mut record =
            generate_certificate_record(&func, &[(sample_vc("claim"), proved_result())]).unwrap();
        record.certificate.solver.strength = ProofStrength::smt_unsat_certified();
        record.certificate.solver.evidence = Some(ProofStrength::smt_unsat_certified().into());
        record.record_digest = compute_record_digest(&record).unwrap();

        assert!(record.to_json().is_err());
        let forged_json = serde_json::to_string(&record).unwrap();
        assert!(GeneratedCertificateRecord::from_json(&forged_json).is_err());
    }

    #[test]
    fn hardened_certificate_evidence_keeps_hardened_vc_snapshot() {
        let func = sample_function();
        let vc = VerificationCondition {
            kind: VcKind::HardenedBoundary {
                category: HardenedVcCategory::RawPathApi,
                callee: "std::fs::remove_file".to_string(),
                detail: "path removal re-resolves a mutable direntry".to_string(),
            },
            function: "crate::paths::remove".into(),
            location: SourceSpan {
                file: "src/paths.rs".to_string(),
                line_start: 7,
                col_start: 8,
                line_end: 7,
                col_end: 31,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        };

        let cert = generate_certificate_record(&func, &[(vc, proved_result())])
            .expect("hardened certificate record should generate");
        let snapshot = &cert.certificate.vc_snapshot.kind;
        assert!(snapshot.contains("HardenedBoundary"));
        assert!(snapshot.contains("RawPathApi"));
        assert!(cert.certificate.solver.evidence.is_some());
        assert!(cert.vc_entries[0].evidence.is_some());

        let json = cert.to_json().expect("serialize hardened certificate");
        assert!(json.contains("HardenedBoundary"));
        assert!(json.contains("RawPathApi"));
        assert!(json.contains("\"evidence\""));
    }
}
