// dead_code audit: crate-level suppression removed
//! trust-proof-cert: Machine-checkable proof certificates for Trust
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub mod binary_decomp;
pub(crate) mod cert;
pub mod checked_binary_certificate;
// Ed25519 cryptographic signing for proof certificates.
pub(crate) mod signing;
// Derive ProofEvidence from solver proof certificates.
pub(crate) mod cert_chain_dag;
pub mod chain;
pub(crate) mod chain_verifier;
pub mod composition;
pub(crate) mod dep_graph;
pub(crate) mod error;
pub(crate) mod evidence;
pub(crate) mod formula_norm;
// ProofBundle format with assumptions, environment capture, and assurance tiers.
pub mod ay_certificate;
pub(crate) mod generate;
pub mod proof_bundle;
pub(crate) mod proof_replay;
pub(crate) mod registry;
pub mod serialization;
pub(crate) mod store;
pub(crate) mod timestamp;
pub(crate) mod verifier;

pub use ay_certificate::{
    AYCertificateStoreExt, AYProofCertificate, AYProofStep, AYRule,
    check_proof_step_structure as check_ay_proof_step_structure, extract_unsat_core,
    parse_ay_proof,
};
pub use binary_decomp::{
    BinaryArtifactTrustLevel, BinaryReleaseGateDecision, BinaryReleaseGateRejection,
    BinaryReplayStatusSummary, BinarySolverResultSummary, BinaryVerificationCertificateSummary,
    UnsupportedLedgerSummary, digest_lifted_binary, evaluate_binary_proof_grade_release_gate,
    hash_unsupported_ledger,
};
pub use cert::*;
pub use cert_chain_dag::{
    ARCHIVE_FORMAT_VERSION, CertificateArchive, CertificateDependencyDag, CertificateStoreLookups,
    DAG_FORMAT_VERSION, DagVerificationResult, verify_cert_chain,
};
pub use chain::*;
pub use chain_verifier::{
    ChainGap, ChainVerificationResult, PROOF_CHAIN_VERSION, ProofChain, is_chain_complete,
    verify_proof_chain,
};
pub use checked_binary_certificate::{
    AuditOnlyRawSolverProofBytes, BinaryCertificateCheckRequest, BinaryCertificateCheckResult,
    BinaryCertificateChecker, CheckError, CheckedBinaryCertificateArtifact,
    CheckedBinaryCertificateArtifactIdentity, CheckedBinaryCertificateArtifactRef,
    CheckedBinaryCertificateAuditExport, CheckedBinaryCertificateAuditExportBundle,
    CheckedBinaryCertificateAuditExportBundleAcceptedRow,
    CheckedBinaryCertificateAuditExportBundleCoverage,
    CheckedBinaryCertificateAuditExportBundleEntry,
    CheckedBinaryCertificateAuditExportBundleReadback,
    CheckedBinaryCertificateAuditExportBundleRejectedRow,
    CheckedBinaryCertificateAuditExportBundleRejectionCode,
    CheckedBinaryCertificateAuditExportBundleValidation,
    CheckedBinaryCertificateAuditExportBundleValidationRow,
    CheckedBinaryCertificateCheckerEvidenceKind, CheckedBinaryCertificateCheckerInvocationKind,
    CheckedBinaryCertificateCheckerSelection, CheckedBinaryCertificateExternalCheckerRunner,
    CheckedBinaryCertificateExternalCheckerTimeoutPolicy,
    CheckedBinaryCertificateExternalProcessProofArtifactArgument,
    CheckedBinaryCertificateExternalProcessTranscript, CheckedBinaryCertificateManifest,
    CheckedBinaryCertificateManifestAcceptance, CheckedBinaryCertificateManifestAcceptanceRecord,
    CheckedBinaryCertificateManifestAcceptanceRequest, CheckedBinaryCertificateManifestEntry,
    CheckedBinaryCertificateManifestIdentityEntry,
    CheckedBinaryCertificateProductionCheckerEvidence, CheckedBinaryCertificateProductionEvidence,
    CheckedBinaryCertificateProductionManifest,
    CheckedBinaryCertificateProductionManifestAcceptedRowInput,
    CheckedBinaryCertificateProductionManifestDecision,
    CheckedBinaryCertificateProductionManifestEntry,
    CheckedBinaryCertificateProductionManifestInput,
    CheckedBinaryCertificateProductionManifestRejection,
    CheckedBinaryCertificateProductionManifestRowAcceptance,
    CheckedBinaryCertificateProductionSourceBackpropagationGateRow,
    CheckedBinaryCertificateReplayTranscriptBinding,
    CheckedBinaryCertificateSolverProofExportBinding,
    CheckedBinaryCertificateSourceBackpropagationGate, CheckerId, ProofFormat, SolverProofExport,
    SolverProofExportArtifactRef, SolverProofExportMetadata, StructuralBinaryCertificateChecker,
    accept_checked_certificate_manifest_entry, apply_checked_certificate_to_dispatch,
    check_binary_certificate, checked_certificate_artifact_path,
    checked_certificate_audit_export_bundle_path, checked_certificate_audit_export_path,
    checked_certificate_manifest_path, checked_certificate_status_has_production_checker_evidence,
    checked_certificate_status_production_checker_evidence, digest_binary_origin,
    digest_model_assumptions, evaluate_checked_binary_certificate_production_manifest,
    import_checked_certificate_artifact_for_dispatch, import_checked_certificate_for_dispatch,
    import_checked_certificate_for_dispatch_by_canonical_digests,
    import_checked_certificate_manifest_entry_for_dispatch,
    import_content_addressed_checked_certificate_for_dispatch, load_checked_certificate_artifact,
    load_checked_certificate_artifact_ref, load_checked_certificate_audit_export,
    load_checked_certificate_audit_export_bundle,
    load_checked_certificate_audit_export_bundle_complete_vc_coverage,
    load_checked_certificate_audit_export_bundle_rows, load_checked_certificate_manifest,
    load_content_addressed_checked_certificate_artifact, persist_checked_certificate_artifact,
    persist_checked_certificate_audit_export, persist_checked_certificate_audit_export_bundle,
    persist_checked_certificate_manifest, persist_solver_proof_export_artifacts,
    produce_checked_certificate_artifact, production_checked_certificate_checker_status,
};
pub use composition::{
    CertificateComponent,
    ChangeKind,
    ComposabilityResult,
    ComposedCertificate,
    ComposedProof,
    CompositionError,
    CompositionManifest,
    CompositionMethod,
    CompositionNodeStatus,
    CompositionVerification,
    FunctionSpec,
    FunctionStrength,
    IncrementalComposition,
    ManifestEntry,
    ManifestError,
    ProofComposition,
    Property,
    check_composability,
    // Portfolio certificate composition types.
    compose_certificates,
    compose_proofs,
    generate_manifest,
    make_component,
    modular_composition,
    modular_composition_with_deps,
    strengthening_check,
    transitive_closure,
    verify_composition,
    weakening,
};
pub use dep_graph::{DepGraph, DepGraphAnalysis, DepNode, StronglyConnectedComponent};
pub use error::*;
pub use evidence::evidence_from_unchecked_record;
pub use formula_norm::{
    PropertyKind, SemanticProperty, formula_subsumes, normalize, normalized_equal,
};
pub use generate::{
    Assumptions, Environment, GeneratedCertificateRecord, VcResultRecord,
    check_generated_record_integrity, generate_certificate_record,
    generate_certificate_record_with_env,
};
pub use proof_replay::{
    ProofStep as ReplayProofStep, ReplayAuditEntry, ReplayAuditLog, ReplayConfig, ReplayEngine,
    ReplayError, ReplayErrorKind, ReplayResult, StepKind, StepVerdict,
};
pub use registry::{
    CertificateRegistry, GcPolicy, RegistryId, RegistrySnapshot, RegistryStats, Revocation,
    RevocationReason,
};
pub use signing::{
    CertSigningKey, CertVerifyingKey, CertificateSignature, Keystore, SignatureProvenance,
    TrustAnchorPolicy, TrustLevel, check_certificate_signature_integrity,
    inspect_signature_provenance, sign_certificate,
};
pub use store::*;
pub use verifier::{
    CertificateIntegrityInspector, CertificateIntegrityReport, CertificateIntegrityResult,
    IntegrityCheckResult, check_certificate_integrity, inspect_certificate_integrity,
    inspect_certificate_records,
};
// ProofBundle format re-exports.
pub use proof_bundle::{
    AssumptionSet, CodegenCertificate, CodegenOption, DependencyRef, EnvironmentFingerprint,
    FunctionCertificate, PROOF_BUNDLE_VERSION, PanicStrategy, ProofBundle, ProofBundleBuilder,
    ProvenArtifact, RecordInventory, ReportedAssurance, SelfCertLevel, SelfCertificate,
    SolverVersion, TransvalCertificate, TrustAssumption, TrustAssumptionLevel,
};
#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

    use crate::{
        CertError, CertificateChain, CertificateId, CertificateStore, CertificationStatus,
        ChainFindingKind, ChainStep, ChainStepType, ChainSummary, ChainValidator, FunctionHash,
        ProofCertificate, SolverInfo, VcSnapshot,
    };

    fn sample_solver_info() -> SolverInfo {
        SolverInfo {
            name: "ay".to_string(),
            version: "1.0.0".to_string(),
            time_ms: 42,
            strength: ProofStrength::smt_unsat(),
            evidence: None,
        }
    }

    fn sample_vc(function: &str) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::Assertion { message: "must hold".to_string() },
            function: function.into(),
            location: SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 4,
                line_end: 10,
                col_end: 18,
            },
            formula: Formula::Bool(true),
            contract_metadata: None,
            obligation: None,
        }
    }

    fn sample_vc_snapshot(function: &str) -> VcSnapshot {
        VcSnapshot::from_vc(&sample_vc(function)).expect("snapshot should serialize")
    }

    fn sample_certificate(function: &str, timestamp: &str) -> ProofCertificate {
        ProofCertificate::new_trusted(
            function.to_string(),
            FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
            sample_vc_snapshot(function),
            sample_solver_info(),
            vec![1, 2, 3, 4],
            timestamp.to_string(),
        )
    }

    fn sample_chain(include_clean: bool) -> CertificateChain {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust_vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "mir-hash".to_string(),
            output_hash: "vc-hash".to_string(),
            time_ms: 5,
            timestamp: "2026-03-27T00:00:00Z".to_string(),
        });
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "ay".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "vc-hash".to_string(),
            output_hash: "proof-hash".to_string(),
            time_ms: 42,
            timestamp: "2026-03-27T00:00:01Z".to_string(),
        });
        if include_clean {
            chain.push(ChainStep {
                step_type: ChainStepType::CleanCertification,
                tool: "clean".to_string(),
                tool_version: "5.0.0".to_string(),
                input_hash: "proof-hash".to_string(),
                output_hash: "cert-hash".to_string(),
                time_ms: 17,
                timestamp: "2026-03-27T00:00:02Z".to_string(),
            });
        }
        chain
    }

    // -----------------------------------------------------------------------
    // Certificate basics
    // -----------------------------------------------------------------------

    #[test]
    fn test_certificate_json_roundtrip() {
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let json = cert.to_json().expect("certificate should serialize");
        let restored = ProofCertificate::from_json(&json).expect("certificate should deserialize");

        assert_eq!(restored, cert);
    }

    #[test]
    fn test_certificate_staleness() {
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let same_hash = FunctionHash::from_bytes(b"crate::foo-body");
        let different_hash = FunctionHash::from_bytes(b"crate::foo-body-v2");

        assert!(cert.is_fresh_for(&same_hash));
        assert!(!cert.is_fresh_for(&different_hash));
    }

    // -----------------------------------------------------------------------
    // Chain integrity (basic, existing tests)
    // -----------------------------------------------------------------------

    #[test]
    fn test_chain_integrity_valid() {
        let chain = sample_chain(true);

        assert!(chain.verify_integrity().is_ok());
    }

    #[test]
    fn test_chain_integrity_broken() {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust_vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "mir-hash".to_string(),
            output_hash: "vc-hash".to_string(),
            time_ms: 5,
            timestamp: "2026-03-27T00:00:00Z".to_string(),
        });
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "ay".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "different-hash".to_string(),
            output_hash: "proof-hash".to_string(),
            time_ms: 42,
            timestamp: "2026-03-27T00:00:01Z".to_string(),
        });

        let err =
            chain.verify_integrity().expect_err("mismatched hashes should fail chain integrity");

        match err {
            CertError::ChainIntegrityFailure { step, reason } => {
                assert_eq!(step, 0);
                assert!(reason.contains("output hash"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_chain_clean_certified() {
        let chain = sample_chain(true);

        assert!(chain.is_clean_certified());
    }

    #[test]
    fn test_chain_not_certified() {
        let chain = sample_chain(false);

        assert!(!chain.is_clean_certified());
    }

    // -----------------------------------------------------------------------
    // ChainValidator
    // -----------------------------------------------------------------------

    #[test]
    fn test_chain_validator_valid_chain() {
        let chain = sample_chain(true);
        let result = ChainValidator::validate(&chain);
        assert!(result.valid, "well-formed chain should pass: {:?}", result.findings);
        assert!(result.findings.is_empty());
    }

    #[test]
    fn test_chain_validator_empty_chain() {
        let chain = CertificateChain::new();
        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        assert_eq!(result.findings.len(), 1);
        assert_eq!(result.findings[0].kind, ChainFindingKind::EmptyChain);
    }

    #[test]
    fn test_chain_validator_hash_mismatch() {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust_vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "mir".to_string(),
            output_hash: "vc-hash-A".to_string(),
            time_ms: 1,
            timestamp: "2026-03-27T00:00:00Z".to_string(),
        });
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "ay".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "vc-hash-B".to_string(),
            output_hash: "proof".to_string(),
            time_ms: 10,
            timestamp: "2026-03-27T00:00:01Z".to_string(),
        });

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        assert!(result.findings.iter().any(|f| f.kind == ChainFindingKind::HashMismatch));
    }

    #[test]
    fn test_chain_validator_out_of_order() {
        let mut chain = CertificateChain::new();
        // SolverProof before VcGeneration — wrong order
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "ay".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "a".to_string(),
            output_hash: "b".to_string(),
            time_ms: 10,
            timestamp: "2026-03-27T00:00:00Z".to_string(),
        });
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust_vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "b".to_string(),
            output_hash: "c".to_string(),
            time_ms: 1,
            timestamp: "2026-03-27T00:00:01Z".to_string(),
        });

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        assert!(result.findings.iter().any(|f| f.kind == ChainFindingKind::OutOfOrder));
    }

    #[test]
    fn test_chain_validator_missing_vc_generation() {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::SolverProof,
            tool: "ay".to_string(),
            tool_version: "1.0.0".to_string(),
            input_hash: "vc".to_string(),
            output_hash: "proof".to_string(),
            time_ms: 10,
            timestamp: "2026-03-27T00:00:00Z".to_string(),
        });

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        assert!(result.findings.iter().any(|f| f.kind == ChainFindingKind::MissingStep));
    }

    #[test]
    fn test_chain_validator_duplicate_step() {
        let mut chain = CertificateChain::new();
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust_vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "a".to_string(),
            output_hash: "b".to_string(),
            time_ms: 1,
            timestamp: "2026-03-27T00:00:00Z".to_string(),
        });
        chain.push(ChainStep {
            step_type: ChainStepType::VcGeneration,
            tool: "trust_vcgen".to_string(),
            tool_version: "0.1.0".to_string(),
            input_hash: "b".to_string(),
            output_hash: "c".to_string(),
            time_ms: 1,
            timestamp: "2026-03-27T00:00:01Z".to_string(),
        });

        let result = ChainValidator::validate(&chain);
        assert!(!result.valid);
        assert!(result.findings.iter().any(|f| f.kind == ChainFindingKind::DuplicateStep));
    }

    #[test]
    fn test_chain_validate_chain_returns_error_on_invalid() {
        let chain = CertificateChain::new();
        let err =
            ChainValidator::validate_chain(&chain).expect_err("empty chain should return error");
        match err {
            CertError::ChainValidationFailed { reason } => {
                assert!(reason.contains("no steps"));
            }
            other => panic!("unexpected error: {other:?}"),
        }
    }

    #[test]
    fn test_chain_validate_chain_returns_ok_on_valid() {
        let chain = sample_chain(true);
        let result = ChainValidator::validate_chain(&chain).expect("valid chain should return Ok");
        assert!(result.valid);
    }

    // -----------------------------------------------------------------------
    // ChainSummary
    // -----------------------------------------------------------------------

    #[test]
    fn test_chain_summary_basic() {
        let chain1 = sample_chain(true);
        let chain2 = sample_chain(false);
        let chains: Vec<&CertificateChain> = vec![&chain1, &chain2];

        let summary = ChainSummary::from_chains(&chains);
        assert_eq!(summary.total_vcs, 2);
        assert_eq!(summary.proved, 2); // both have SolverProof
        assert_eq!(summary.certified, 1); // only chain1 has CleanCertification
        assert_eq!(summary.valid_chains, 2);
        assert_eq!(summary.invalid_chains, 0);
        assert!((summary.coverage_percent() - 100.0).abs() < f64::EPSILON);
        assert!((summary.certification_percent() - 50.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_chain_summary_empty() {
        let chains: Vec<&CertificateChain> = vec![];
        let summary = ChainSummary::from_chains(&chains);
        assert_eq!(summary.total_vcs, 0);
        assert_eq!(summary.proved, 0);
        assert!((summary.coverage_percent() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_chain_summary_with_invalid() {
        let valid = sample_chain(true);
        let invalid = CertificateChain::new(); // empty = invalid
        let chains: Vec<&CertificateChain> = vec![&valid, &invalid];

        let summary = ChainSummary::from_chains(&chains);
        assert_eq!(summary.total_vcs, 2);
        assert_eq!(summary.valid_chains, 1);
        assert_eq!(summary.invalid_chains, 1);
    }

    #[test]
    fn test_chain_total_time() {
        let chain = sample_chain(true);
        assert_eq!(chain.total_time_ms(), 5 + 42 + 17);
    }

    // -----------------------------------------------------------------------
    // Store basics
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_insert_and_find() {
        let mut store = CertificateStore::new("sample-crate");
        let cert1 = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let cert2 = sample_certificate("crate::foo", "2026-03-27T12:05:00Z");
        let chain1 = sample_chain(true);
        let chain2 = sample_chain(false);

        store.insert(cert1.clone(), chain1.clone());
        store.insert(cert2.clone(), chain2.clone());

        assert_eq!(store.len(), 2);
        assert_eq!(store.get(&cert1.id), Some(&cert1));
        assert_eq!(store.get_chain(&cert1.id), Some(&chain1));

        let found = store.find_by_function("crate::foo");
        assert_eq!(found.len(), 2);
        assert!(found.iter().any(|cert| cert.id == cert1.id));
        assert!(found.iter().any(|cert| cert.id == cert2.id));
    }

    #[test]
    fn test_store_remove() {
        let mut store = CertificateStore::new("sample-crate");
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        store.insert(cert.clone(), sample_chain(true));

        assert_eq!(store.len(), 1);
        let removed = store.remove(&cert.id);
        assert!(removed.is_some());
        assert_eq!(store.len(), 0);
        assert!(store.get(&cert.id).is_none());
        assert!(store.get_chain(&cert.id).is_none());
    }

    #[test]
    fn test_store_find_by_vc_kind() {
        let mut store = CertificateStore::new("sample-crate");
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        store.insert(cert.clone(), sample_chain(true));

        let found = store.find_by_vc_kind("Assertion");
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].id, cert.id);

        let found = store.find_by_vc_kind("Overflow");
        assert!(found.is_empty());
    }

    #[test]
    fn test_store_find_by_strength() {
        let mut store = CertificateStore::new("sample-crate");
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        store.insert(cert.clone(), sample_chain(true));

        let found = store.find_by_strength(&ProofStrength::smt_unsat());
        assert_eq!(found.len(), 1);

        let found = store.find_by_strength(&ProofStrength::bounded(10));
        assert!(found.is_empty());
    }

    #[test]
    fn test_store_function_names() {
        let mut store = CertificateStore::new("sample-crate");
        store.insert(sample_certificate("crate::bar", "2026-03-27T12:00:00Z"), sample_chain(false));
        store.insert(sample_certificate("crate::foo", "2026-03-27T12:01:00Z"), sample_chain(true));
        store.insert(sample_certificate("crate::bar", "2026-03-27T12:02:00Z"), sample_chain(false));

        let names = store.function_names();
        assert_eq!(names, vec!["crate::bar", "crate::foo"]);
    }

    #[test]
    fn test_store_verify_all_valid() {
        let mut store = CertificateStore::new("sample-crate");
        let cert1 = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let cert2 = sample_certificate("crate::bar", "2026-03-27T12:01:00Z");

        store.insert(cert1.clone(), sample_chain(true));
        store.insert(cert2.clone(), sample_chain(false));

        let mut current_hashes = BTreeMap::new();
        current_hashes.insert(cert1.function.clone(), cert1.function_hash.clone());
        current_hashes.insert(cert2.function.clone(), cert2.function_hash.clone());

        let result = store.verify_all(&current_hashes).expect("store verification should succeed");

        assert_eq!(result.total, 2);
        assert_eq!(result.valid, 2);
        assert!(result.stale.is_empty());
        assert!(result.chain_errors.is_empty());
        assert!(result.all_valid());
    }

    #[test]
    fn test_store_verify_stale() {
        let mut store = CertificateStore::new("sample-crate");
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        store.insert(cert.clone(), sample_chain(true));

        let mut current_hashes = BTreeMap::new();
        current_hashes
            .insert(cert.function.clone(), FunctionHash::from_bytes(b"crate::foo-body-updated"));

        let result = store.verify_all(&current_hashes).expect("store verification should succeed");

        assert_eq!(result.total, 1);
        assert_eq!(result.valid, 0);
        assert_eq!(result.stale, vec![cert.id.0.clone()]);
        assert!(!result.all_valid());
    }

    #[test]
    fn test_store_json_roundtrip() {
        let mut store = CertificateStore::new("sample-crate");
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let chain = sample_chain(true);
        store.insert(cert, chain);

        let json = store.to_json().expect("store should serialize");
        let restored = CertificateStore::from_json(&json).expect("store should deserialize");

        assert_eq!(restored, store);
    }

    // -----------------------------------------------------------------------
    // Store pruning
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_prune_stale_by_timestamp() {
        let mut store = CertificateStore::new("sample-crate");
        let old = sample_certificate("crate::old", "2020-01-01T00:00:00Z");
        let recent = sample_certificate("crate::recent", "2026-03-27T12:00:00Z");

        store.insert(old.clone(), sample_chain(false));
        store.insert(recent.clone(), sample_chain(true));
        assert_eq!(store.len(), 2);

        // Prune anything older than 2025-01-01 (epoch ~1735689600)
        let cutoff = 1_735_689_600;
        let pruned = store.prune_stale(cutoff);

        assert_eq!(pruned.len(), 1);
        assert!(pruned.contains(&old.id.0));
        assert_eq!(store.len(), 1);
        assert!(store.get(&recent.id).is_some());
    }

    #[test]
    fn test_store_prune_by_hash() {
        let mut store = CertificateStore::new("sample-crate");
        let cert1 = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        let cert2 = sample_certificate("crate::bar", "2026-03-27T12:01:00Z");

        store.insert(cert1.clone(), sample_chain(true));
        store.insert(cert2.clone(), sample_chain(false));

        // foo's hash changed, bar's stayed the same
        let mut current_hashes = BTreeMap::new();
        current_hashes.insert("crate::foo".to_string(), FunctionHash::from_bytes(b"new-body"));
        current_hashes.insert("crate::bar".to_string(), cert2.function_hash.clone());

        let pruned = store.prune_by_hash(&current_hashes);
        assert_eq!(pruned.len(), 1);
        assert!(pruned.contains(&cert1.id.0));
        assert_eq!(store.len(), 1);
        assert!(store.get(&cert2.id).is_some());
    }

    // -----------------------------------------------------------------------
    // Store filesystem persistence
    // -----------------------------------------------------------------------

    #[test]
    fn test_store_save_and_load_dir() {
        let dir = std::env::temp_dir().join(format!("trust-cert-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);

        let mut store = CertificateStore::new("test-crate");
        let cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");
        store.insert(cert.clone(), sample_chain(true));

        let path = store.save_to_dir(&dir).expect("save should succeed");
        assert!(path.exists());

        let loaded = CertificateStore::load_from_dir(&dir).expect("load should succeed").unwrap();
        assert_eq!(loaded, store);
        assert_eq!(loaded.get(&cert.id), Some(&cert));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_store_load_from_dir_missing() {
        let dir = std::env::temp_dir().join("trust-cert-test-nonexistent-dir-12345");
        let _ = std::fs::remove_dir_all(&dir);

        let loaded = CertificateStore::load_from_dir(&dir).expect("should not error");
        assert!(loaded.is_none());
    }

    #[test]
    fn test_store_load_or_create() {
        let dir = std::env::temp_dir().join(format!("trust-cert-test-loc-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);

        // First call: creates new empty store
        let store = CertificateStore::load_or_create(&dir, "my-crate").expect("should succeed");
        assert_eq!(store.crate_name, "my-crate");
        assert!(store.is_empty());

        // Save some data
        let mut store = store;
        store.insert(sample_certificate("crate::foo", "2026-03-27T12:00:00Z"), sample_chain(true));
        store.save_to_dir(&dir).expect("save should succeed");

        // Second call: loads existing
        let loaded = CertificateStore::load_or_create(&dir, "my-crate").expect("should succeed");
        assert_eq!(loaded.len(), 1);

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn test_store_save_and_load_file() {
        let path =
            std::env::temp_dir().join(format!("trust-cert-file-test-{}.json", std::process::id()));
        let _ = std::fs::remove_file(&path);

        let mut store = CertificateStore::new("file-test");
        store.insert(sample_certificate("crate::bar", "2026-03-27T12:00:00Z"), sample_chain(false));

        store.save_to_file(&path).expect("save should succeed");
        let loaded = CertificateStore::load_from_file(&path).expect("load should succeed");
        assert_eq!(loaded, store);

        let _ = std::fs::remove_file(&path);
    }

    // -----------------------------------------------------------------------
    // VC snapshot & certificate ID
    // -----------------------------------------------------------------------

    #[test]
    fn test_vc_snapshot_from_vc() {
        let vc = sample_vc("crate::foo");
        let snapshot = VcSnapshot::from_vc(&vc).expect("vc snapshot should be created");

        assert_eq!(snapshot.kind, format!("{:?}", vc.kind));
        assert_eq!(
            snapshot.formula_json,
            serde_json::to_string(&vc.formula).expect("formula should serialize")
        );
        assert_eq!(
            snapshot.location,
            Some(crate::SourceLocation {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 4,
                line_end: 10,
                col_end: 18,
            })
        );
    }

    #[test]
    fn test_certificate_id_deterministic() {
        let first = CertificateId::generate("crate::foo", "2026-03-27T12:00:00Z");
        let second = CertificateId::generate("crate::foo", "2026-03-27T12:00:00Z");

        assert_eq!(first, second);
    }

    #[test]
    fn test_function_hash_from_bytes() {
        let first = FunctionHash::from_bytes(b"fn foo() -> bool { true }");
        let second = FunctionHash::from_bytes(b"fn foo() -> bool { true }");
        let third = FunctionHash::from_bytes(b"fn foo() -> bool { false }");

        assert_eq!(first, second);
        assert_ne!(first, third);
        assert_eq!(first.0.len(), 64);
    }

    #[test]
    fn test_upgrade_to_certified() {
        let certifier_key = crate::CertSigningKey::generate(crate::TrustLevel::Certifier);
        let mut cert = sample_certificate("crate::foo", "2026-03-27T12:00:00Z");

        assert_eq!(cert.status, CertificationStatus::Trusted);
        cert.upgrade_to_certified(&certifier_key).expect("upgrade should succeed");
        assert_eq!(cert.status, CertificationStatus::Certified);
        assert!(cert.signature.is_some(), "upgrade should attach signature");
    }

    #[test]
    fn test_chain_json_roundtrip() {
        let chain = sample_chain(true);
        let json = chain.to_json().expect("chain should serialize");
        let restored = CertificateChain::from_json(&json).expect("chain should deserialize");

        assert_eq!(restored, chain);
    }

    // -----------------------------------------------------------------------
    // Proptest: ProofCertificate JSON roundtrip
    // -----------------------------------------------------------------------

    mod proptest_cert {
        use super::*;
        use proptest::prelude::*;

        use trust_types::{AssuranceLevel, ProofEvidence, ProofStrength, ReasoningKind, SmtTheory};

        fn arb_smt_theory() -> impl Strategy<Value = SmtTheory> {
            prop_oneof![
                Just(SmtTheory::LinearArithmetic),
                Just(SmtTheory::Bitvectors),
                Just(SmtTheory::UninterpretedFunctions),
                Just(SmtTheory::Arrays),
                Just(SmtTheory::Datatypes),
                Just(SmtTheory::NonlinearArithmetic),
                Just(SmtTheory::Strings),
            ]
        }

        fn arb_reasoning_kind() -> impl Strategy<Value = ReasoningKind> {
            prop_oneof![
                Just(ReasoningKind::Smt),
                any::<u64>().prop_map(|d| ReasoningKind::BoundedModelCheck { depth: d }),
                any::<u64>().prop_map(ReasoningKind::ExhaustiveFinite),
                Just(ReasoningKind::Inductive),
                Just(ReasoningKind::Deductive),
                Just(ReasoningKind::Constructive),
                Just(ReasoningKind::Pdr),
                Just(ReasoningKind::ChcSpacer),
                Just(ReasoningKind::AbstractInterpretation),
                Just(ReasoningKind::CdclResolution),
                arb_smt_theory().prop_map(|theory| ReasoningKind::TheoryLemma { theory }),
                Just(ReasoningKind::BitBlasting),
            ]
        }

        // Second set of ReasoningKind variants (prop_oneof! limit is ~12 arms).
        fn arb_reasoning_kind_extra() -> impl Strategy<Value = ReasoningKind> {
            prop_oneof![
                Just(ReasoningKind::SymbolicExecution),
                Just(ReasoningKind::OwnershipAnalysis),
                Just(ReasoningKind::ExplicitStateModel),
                Just(ReasoningKind::NeuralBounding),
                Just(ReasoningKind::Interpolation),
            ]
        }

        fn arb_reasoning_kind_all() -> impl Strategy<Value = ReasoningKind> {
            prop_oneof![arb_reasoning_kind(), arb_reasoning_kind_extra(),]
        }

        fn arb_assurance_level() -> impl Strategy<Value = AssuranceLevel> {
            prop_oneof![
                Just(AssuranceLevel::Sound),
                any::<u64>().prop_map(|d| AssuranceLevel::BoundedSound { depth: d }),
                Just(AssuranceLevel::Heuristic),
                Just(AssuranceLevel::Unchecked),
                Just(AssuranceLevel::Trusted),
                Just(AssuranceLevel::SmtBacked),
                Just(AssuranceLevel::Certified),
            ]
        }

        fn arb_proof_strength() -> impl Strategy<Value = ProofStrength> {
            (arb_reasoning_kind_all(), arb_assurance_level())
                .prop_map(|(reasoning, assurance)| ProofStrength { reasoning, assurance })
        }

        fn arb_proof_evidence() -> impl Strategy<Value = Option<ProofEvidence>> {
            proptest::option::of(
                (arb_reasoning_kind_all(), arb_assurance_level())
                    .prop_map(|(reasoning, assurance)| ProofEvidence::new(reasoning, assurance)),
            )
        }

        fn arb_solver_info() -> impl Strategy<Value = SolverInfo> {
            (
                "[a-z]{2,8}",
                "[0-9]+\\.[0-9]+\\.[0-9]+",
                any::<u64>(),
                arb_proof_strength(),
                arb_proof_evidence(),
            )
                .prop_map(|(name, version, time_ms, strength, evidence)| SolverInfo {
                    name,
                    version,
                    time_ms,
                    strength,
                    evidence,
                })
        }

        fn arb_source_location() -> impl Strategy<Value = Option<crate::SourceLocation>> {
            proptest::option::of(
                ("[a-z_/]{1,30}\\.rs", 1..10000u32, 0..200u32, 1..10000u32, 0..200u32).prop_map(
                    |(file, ls, cs, le, ce)| crate::SourceLocation {
                        file,
                        line_start: ls,
                        col_start: cs,
                        line_end: le,
                        col_end: ce,
                    },
                ),
            )
        }

        fn arb_vc_snapshot() -> impl Strategy<Value = VcSnapshot> {
            (
                "[A-Za-z]{3,15}",
                prop_oneof![
                    Just("true".to_string()),
                    Just("false".to_string()),
                    Just("null".to_string()),
                    Just("42".to_string()),
                    Just(r#""hello""#.to_string()),
                    Just(r#"{"a":1}"#.to_string()),
                ],
                arb_source_location(),
            )
                .prop_map(|(kind, formula_json, location)| VcSnapshot {
                    kind,
                    formula_json,
                    location,
                })
        }

        fn arb_proof_step() -> impl Strategy<Value = crate::cert::ProofStep> {
            (0..100u32, "[a-z_]{3,15}", "[a-z ]{5,30}").prop_map(|(index, rule, description)| {
                crate::cert::ProofStep { index, rule, description, premises: Vec::new() }
            })
        }

        fn arb_chain_step_type() -> impl Strategy<Value = ChainStepType> {
            prop_oneof![
                Just(ChainStepType::VcGeneration),
                Just(ChainStepType::SolverProof),
                Just(ChainStepType::CleanCertification),
            ]
        }

        fn arb_chain_step() -> impl Strategy<Value = ChainStep> {
            (
                arb_chain_step_type(),
                "[a-z0-9_-]{2,15}",
                "[0-9]+\\.[0-9]+\\.[0-9]+",
                "[a-f0-9]{8,16}",
                "[a-f0-9]{8,16}",
                any::<u64>(),
                "2026-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z",
            )
                .prop_map(
                    |(
                        step_type,
                        tool,
                        tool_version,
                        input_hash,
                        output_hash,
                        time_ms,
                        timestamp,
                    )| {
                        ChainStep {
                            step_type,
                            tool,
                            tool_version,
                            input_hash,
                            output_hash,
                            time_ms,
                            timestamp,
                        }
                    },
                )
        }

        fn arb_certificate_chain() -> impl Strategy<Value = CertificateChain> {
            proptest::collection::vec(arb_chain_step(), 0..5).prop_map(|steps| {
                let mut chain = CertificateChain::new();
                for s in steps {
                    chain.push(s);
                }
                chain
            })
        }

        fn arb_certification_status() -> impl Strategy<Value = CertificationStatus> {
            prop_oneof![Just(CertificationStatus::Trusted), Just(CertificationStatus::Certified),]
        }

        fn arb_proof_certificate() -> impl Strategy<Value = ProofCertificate> {
            let identity = (
                "[a-z_:]{5,30}",
                "[a-f0-9]{16,64}",
                "[a-f0-9]{64}",
                any::<[u8; 32]>(),
                arb_vc_snapshot(),
                arb_solver_info(),
            );
            let payload = (
                proptest::collection::vec(arb_proof_step(), 0..5),
                proptest::option::of(proptest::collection::vec(any::<u8>(), 0..64)),
                arb_certificate_chain(),
                proptest::collection::vec(any::<u8>(), 0..128),
                "2026-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z",
                arb_certification_status(),
                1..10u32,
            );
            (identity, payload).prop_map(
                |(
                    (function, id_str, hash_str, vc_hash, vc_snapshot, solver),
                    (proof_steps, witness, chain, proof_trace, timestamp, status, version),
                )| {
                    ProofCertificate {
                        id: CertificateId(id_str),
                        function,
                        function_hash: FunctionHash(hash_str),
                        vc_hash,
                        vc_snapshot,
                        solver,
                        proof_steps,
                        witness,
                        chain,
                        proof_trace,
                        timestamp,
                        status,
                        version,
                        signature: None,
                    }
                },
            )
        }

        proptest! {
            #[test]
            fn proof_certificate_json_roundtrip(cert in arb_proof_certificate()) {
                let json = cert.to_json().expect("certificate should serialize to JSON");
                let restored = ProofCertificate::from_json(&json)
                    .expect("certificate should deserialize from JSON");
                prop_assert_eq!(restored, cert);
            }
        }
    }
}
