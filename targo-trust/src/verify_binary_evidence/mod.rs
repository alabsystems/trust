// Binary verification evidence accounting for targo-trust proof-grade gates.
//
// This module is deliberately conservative: raw solver proof bytes are recorded
// as audit artifacts, but only checked certificates and completed counterexample
// replay count toward proof-grade coverage.
//
// The implementation is split across submodules for navigability:
//
// * `diagnostics`   — diagnostic prefix constants (EXACT_REPLAY_*).
// * `types`         — public-facing data types: evidence aggregate, import /
//                     production reports, and the records they contain.
// * `digests`       — digest, identity, and canonical-SHA-256 helpers.
// * `normalized_proof_export` — build/validate/persist/load of the normalized
//                     solver proof export artifact.
// * `loaded_metadata` — checked-certificate metadata aggregation.
// * `loaders`       — checked-certificate manifest and artifact loaders.
// * `evidence`      — `VerifyBinaryEvidence` driver: counters, import, produce.
// * `production`    — checked-certificate production helpers and structs.
// * `dispatch`      — dispatch-level binding/witness/replay helpers.

mod diagnostics;
mod digests;
mod dispatch;
mod evidence;
mod loaded_metadata;
mod loaders;
mod normalized_proof_export;
mod production;
mod types;

// `pub(crate)` items in each child are re-exported as part of the public
// `verify_binary_evidence::*` surface used by the rest of targo-trust.
// External imports re-exported for the in-module test suite below. The
// original single-file implementation imported these at the top; preserving
// them here keeps `use super::*;` in `mod tests` working without touching the
// test code.
#[cfg(test)]
use std::collections::BTreeMap;
#[cfg(test)]
use std::path::{Path, PathBuf};

pub(crate) use diagnostics::*;
pub(crate) use digests::*;
pub(crate) use dispatch::*;
// Bring `pub(super)` helpers into mod.rs's namespace so sibling submodules
// (and the tests below) can refer to them through `super::*`.
use loaded_metadata::*;
pub(crate) use loaders::*;
pub(crate) use normalized_proof_export::*;
use production::*;
#[cfg(test)]
use trust_proof_cert::{
    BinaryCertificateCheckRequest, CheckedBinaryCertificateArtifact,
    CheckedBinaryCertificateManifest, CheckedBinaryCertificateManifestEntry,
    CheckedBinaryCertificateSourceBackpropagationGate, SolverProofExport,
    StructuralBinaryCertificateChecker, checked_certificate_audit_export_bundle_path,
};
#[cfg(test)]
use trust_types::{
    BinaryArtifactDigestIdentity, ProofCertificateStatus, ReplayStatus, SolverDispatchRecord,
    SolverDispatchStatus, SolverQuerySemantics, VerificationResult,
};
pub(crate) use types::*;

#[cfg(test)]
mod tests {
    use trust_types::{
        BinaryArtifactDigest, BinaryOrigin, BinarySelectedImageIdentity, Counterexample,
        CounterexampleTrace, CounterexampleValue, Formula, ProofStrength, SerializableVc,
        SourceSpan, Symbol, TraceStep, VcKind,
    };

    use super::*;

    fn temp_test_dir(label: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "targo-trust-verify-binary-evidence-{label}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system time should be after unix epoch")
                .as_nanos()
        ))
    }

    fn set_test_dispatch_binary_path(dispatch: &mut SolverDispatchRecord, binary_path: &Path) {
        dispatch.origin.as_mut().expect("fixture dispatch has origin").binary_path =
            Some(binary_path.display().to_string());
    }

    fn derive_test_dispatch_binary_identity(dispatch: &mut SolverDispatchRecord) {
        let mut cache = BTreeMap::new();
        bind_dispatch_binary_artifact_digest_identity(dispatch, &mut cache);
        assert!(
            dispatch_binary_artifact_digest_identity_acceptance_blockers(dispatch).is_empty(),
            "{:?}",
            dispatch_binary_artifact_digest_identity_acceptance_blockers(dispatch)
        );
    }

    fn checked_artifact_for_dispatch(
        dispatch: &SolverDispatchRecord,
        canonical_vc_bytes: &[u8],
    ) -> CheckedBinaryCertificateArtifact {
        let export = SolverProofExport::new(
            dispatch,
            canonical_vc_bytes,
            "lrat",
            b"verify-binary evidence checked proof payload".to_vec(),
            Some("4.13.0".to_string()),
            1_777_070_400_000,
        );
        let checker = StructuralBinaryCertificateChecker::new(
            "verify-binary-evidence-checker",
            "0.1.0",
            vec!["lrat".to_string()],
            1_777_070_401_000,
        );
        let check = trust_proof_cert::check_binary_certificate(
            &checker,
            BinaryCertificateCheckRequest::from_export(dispatch, canonical_vc_bytes, &export),
        );
        assert!(check.accepted, "{:?}", check.error);
        check.certificate.expect("accepted check should carry artifact")
    }

    fn exact_replay_counterexample(address: u64) -> Counterexample {
        Counterexample::with_trace(
            vec![("_local0".to_string(), CounterexampleValue::Int(1))],
            CounterexampleTrace::new(vec![TraceStep {
                step: 0,
                assignments: BTreeMap::new(),
                program_point: Some(format!("bb0@0x{address:x}")),
            }]),
        )
    }

    fn exact_replay_sat_dispatch_for_binary(
        id: &str,
        binary_path: &Path,
        binary_bytes: &[u8],
    ) -> SolverDispatchRecord {
        assert!(!binary_bytes.is_empty(), "exact replay fixture needs image bytes");
        let binary_sha256 = trust_types::digest::stable_sha256_hex(binary_bytes);
        let vc = SerializableVc {
            kind: VcKind::DivisionByZero,
            function: Symbol::intern("binary::main"),
            location: SourceSpan::binary_address(0x401010),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        SolverDispatchRecord {
            id: id.to_string(),
            function: Some("main".to_string()),
            origin: Some(BinaryOrigin {
                binary_path: Some(binary_path.display().to_string()),
                function_entry: Some(0x401000),
                instruction_address: 0x401010,
                instruction_size: Some(1),
                encoding: Some(u32::from(binary_bytes[0])),
                instruction_bytes: vec![binary_bytes[0]],
                source: Some(SourceSpan::binary_address(0x401010)),
            }),
            vc_kind: Some(VcKind::DivisionByZero),
            vc: Some(vc),
            solver: "ay-smtlib".to_string(),
            backend: Some("ay-incremental".to_string()),
            status: SolverDispatchStatus::Sat,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            result: Some(VerificationResult::Failed {
                solver: Symbol::intern("ay-smtlib"),
                time_ms: 17,
                counterexample: Some(exact_replay_counterexample(0x401010)),
            }),
            binary_artifact_digest_identity: Some(BinaryArtifactDigestIdentity {
                root_artifact_digest: Some(BinaryArtifactDigest::sha256(binary_sha256.clone())),
                selected_image: Some(BinarySelectedImageIdentity {
                    file_offset: 0,
                    file_size: u64::try_from(binary_bytes.len())
                        .expect("fixture binary len fits u64"),
                    sha256: binary_sha256,
                }),
            }),
            replay: ReplayStatus::Replayed,
            certificate: ProofCertificateStatus::NotRequested,
            diagnostics: vec![EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC.to_string()],
            ..Default::default()
        }
    }

    fn exact_replay_evidence_from_dispatch(dispatch: SolverDispatchRecord) -> VerifyBinaryEvidence {
        let mut evidence = VerifyBinaryEvidence::default();
        evidence.add_required_vcs(1);
        evidence.extend_solver_dispatch([dispatch]);
        evidence
    }

    fn actual_binary_dispatch_and_artifact(
        label: &str,
    ) -> (PathBuf, Vec<u8>, SolverDispatchRecord, CheckedBinaryCertificateArtifact) {
        let root = temp_test_dir(label);
        std::fs::create_dir_all(&root).expect("temp root should be writable");
        let binary_path = root.join("selected-image.bin");
        let binary_bytes = b"\x7fELF verify-binary selected image bytes".to_vec();
        std::fs::write(&binary_path, &binary_bytes).expect("test binary should be writable");

        let mut producer = test_checked_certificate_dispatch(
            &format!("{label}:producer:vc0"),
            ProofCertificateStatus::Unavailable {
                reason: Some("fixture starts unchecked".to_string()),
            },
        );
        set_test_dispatch_binary_path(&mut producer, &binary_path);
        producer.binary_artifact_digest_identity = None;
        derive_test_dispatch_binary_identity(&mut producer);
        let canonical_vc_bytes =
            canonical_vc_bytes(producer.vc.as_ref().expect("fixture dispatch has VC"))
                .expect("fixture VC should serialize");
        let artifact = checked_artifact_for_dispatch(&producer, &canonical_vc_bytes);

        let mut current = producer.clone();
        current.id = format!("{label}:current:vc0");
        current.certificate = ProofCertificateStatus::Unavailable {
            reason: Some("checked artifact not imported yet".to_string()),
        };
        current.binary_artifact_digest_identity = None;

        (root, binary_bytes, current, artifact)
    }

    #[test]
    fn exact_replay_transcript_digest_binds_real_selected_image_and_import_row() {
        let root = temp_test_dir("exact-replay-real-selected-image-transcript");
        std::fs::create_dir_all(&root).expect("temp root should be writable");
        let binary_path = root.join("selected-image.bin");
        let binary_bytes = b"\x90\x90\xc3 selected image bytes for exact replay".to_vec();
        std::fs::write(&binary_path, &binary_bytes).expect("selected image should be writable");
        let binary_sha256 = trust_types::digest::stable_sha256_hex(&binary_bytes);

        let dispatch = exact_replay_sat_dispatch_for_binary(
            "exact-replay-real-image:vc0",
            &binary_path,
            &binary_bytes,
        );
        let evidence = exact_replay_evidence_from_dispatch(dispatch);

        assert_eq!(evidence.replayed_vcs(), 1);
        assert_eq!(evidence.exact_replay_slice_attested_vcs(), 1);
        assert_eq!(evidence.replay_semantics_satisfied_vcs(), 1);
        let dispatch = &evidence.solver_dispatch[0];
        let transcript_digest = dispatch_exact_replay_transcript_artifact_digest(dispatch)
            .expect("real selected-image replay should produce transcript digest");
        assert!(is_canonical_sha256_hex(&transcript_digest));
        assert!(dispatch.diagnostics.iter().any(|diagnostic| diagnostic
            == &format!(
                "{EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX}{transcript_digest}"
            )));
        let identity = dispatch.binary_artifact_digest_identity.as_ref().expect("binary identity");
        assert_eq!(
            identity.root_artifact_digest.as_ref().map(|digest| digest.value.as_str()),
            Some(binary_sha256.as_str())
        );
        let selected = identity.selected_image.as_ref().expect("selected image identity");
        assert_eq!(selected.file_offset, 0);
        assert_eq!(
            selected.file_size,
            u64::try_from(binary_bytes.len()).expect("fixture binary len fits u64")
        );
        assert_eq!(selected.sha256, binary_sha256);

        let mut certificate_dispatch = dispatch.clone();
        certificate_dispatch.status = SolverDispatchStatus::Unsat;
        certificate_dispatch.result = Some(VerificationResult::Proved {
            solver: Symbol::intern("ay-smtlib"),
            time_ms: 11,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        });
        certificate_dispatch.certificate = ProofCertificateStatus::Unavailable {
            reason: Some("checked artifact not imported yet".to_string()),
        };
        let canonical_vc_bytes =
            canonical_vc_bytes(certificate_dispatch.vc.as_ref().expect("fixture dispatch has VC"))
                .expect("fixture VC should serialize");
        let export = SolverProofExport::new(
            &certificate_dispatch,
            &canonical_vc_bytes,
            "lrat",
            b"normalized exact replay proof payload".to_vec(),
            Some("4.13.0".to_string()),
            1_777_070_407_000,
        );
        let checker = StructuralBinaryCertificateChecker::new(
            "exact-replay-transcript-checker",
            "0.1.0",
            vec!["lrat".to_string()],
            1_777_070_407_000,
        );
        let mut request = BinaryCertificateCheckRequest::from_export(
            &certificate_dispatch,
            &canonical_vc_bytes,
            &export,
        );
        request.replay_transcript_digest = Some(transcript_digest.as_str());
        let check = trust_proof_cert::check_binary_certificate(&checker, request);
        assert!(check.accepted, "{:?}", check.error);
        let artifact = check.certificate.expect("accepted check should carry artifact");
        assert_eq!(artifact.replay_transcript_digest.as_deref(), Some(transcript_digest.as_str()));

        let mut import_evidence =
            VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![certificate_dispatch]);
        let report = import_evidence.import_checked_certificate_artifacts(&[artifact]);

        assert_eq!(report.imported, 1, "{report:#?}");
        let row = &report.artifacts[0];
        assert_eq!(row.status, "imported");
        assert_eq!(row.replay_transcript_digest.as_deref(), Some(transcript_digest.as_str()));
        assert_eq!(row.replay_digest_identity.status, "accepted");
        assert_eq!(
            row.replay_digest_identity.replay_transcript_digest.as_deref(),
            Some(transcript_digest.as_str())
        );

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn exact_replay_transcript_digest_rejects_missing_loaded_image_bytes() {
        let root = temp_test_dir("exact-replay-missing-loaded-image");
        std::fs::create_dir_all(&root).expect("temp root should be writable");
        let missing_binary = root.join("missing-selected-image.bin");
        let binary_bytes = b"\x90 real bytes used only for declared digest".to_vec();
        let dispatch = exact_replay_sat_dispatch_for_binary(
            "exact-replay-missing-image:vc0",
            &missing_binary,
            &binary_bytes,
        );
        let evidence = exact_replay_evidence_from_dispatch(dispatch);

        assert_eq!(evidence.replayed_vcs(), 1);
        assert_eq!(evidence.exact_replay_slice_attested_vcs(), 0);
        assert!(
            dispatch_exact_replay_transcript_artifact_digest(&evidence.solver_dispatch[0])
                .is_none()
        );
        let blockers = evidence.exact_replay_slice_attestation_blockers().join("\n");
        assert!(blockers.contains("missing or unreadable loaded-image bytes"), "{blockers}");

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn exact_replay_transcript_digest_rejects_mismatched_and_out_of_image_bindings() {
        let root = temp_test_dir("exact-replay-image-binding-negatives");
        std::fs::create_dir_all(&root).expect("temp root should be writable");
        let binary_path = root.join("selected-image.bin");
        let binary_bytes = b"\x90\x90\xc3 selected image bytes".to_vec();
        std::fs::write(&binary_path, &binary_bytes).expect("selected image should be writable");

        let mut mismatched = exact_replay_sat_dispatch_for_binary(
            "exact-replay-mismatched-image:vc0",
            &binary_path,
            &binary_bytes,
        );
        mismatched
            .binary_artifact_digest_identity
            .as_mut()
            .and_then(|identity| identity.selected_image.as_mut())
            .expect("selected image identity")
            .sha256 = trust_types::digest::stable_sha256_hex(b"stale selected image bytes");
        let mismatched_evidence = exact_replay_evidence_from_dispatch(mismatched);

        assert_eq!(mismatched_evidence.exact_replay_slice_attested_vcs(), 0);
        assert!(
            dispatch_exact_replay_transcript_artifact_digest(
                &mismatched_evidence.solver_dispatch[0],
            )
            .is_none()
        );
        let blockers = mismatched_evidence.exact_replay_slice_attestation_blockers().join("\n");
        assert!(blockers.contains("selected image digest does not match"), "{blockers}");

        let mut out_of_image = exact_replay_sat_dispatch_for_binary(
            "exact-replay-out-of-image:vc0",
            &binary_path,
            &binary_bytes,
        );
        let selected = out_of_image
            .binary_artifact_digest_identity
            .as_mut()
            .and_then(|identity| identity.selected_image.as_mut())
            .expect("selected image identity");
        selected.file_offset = 2;
        selected.file_size = u64::try_from(binary_bytes.len()).expect("fixture len fits u64");
        selected.sha256 = trust_types::digest::stable_sha256_hex(&binary_bytes);
        let out_of_image_evidence = exact_replay_evidence_from_dispatch(out_of_image);

        assert_eq!(out_of_image_evidence.exact_replay_slice_attested_vcs(), 0);
        assert!(
            dispatch_exact_replay_transcript_artifact_digest(
                &out_of_image_evidence.solver_dispatch[0],
            )
            .is_none()
        );
        let blockers = out_of_image_evidence.exact_replay_slice_attestation_blockers().join("\n");
        assert!(blockers.contains("selected image range exceeds loaded binary size"), "{blockers}");

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn exact_replay_transcript_digest_rejects_unsupported_effect_and_architecture_mismatch() {
        let root = temp_test_dir("exact-replay-effect-arch-negatives");
        std::fs::create_dir_all(&root).expect("temp root should be writable");
        let binary_path = root.join("selected-image.bin");
        let binary_bytes = b"\x90\x90\xc3 selected image bytes".to_vec();
        std::fs::write(&binary_path, &binary_bytes).expect("selected image should be writable");

        let mut unsupported_effect = exact_replay_sat_dispatch_for_binary(
            "exact-replay-unsupported-effect:vc0",
            &binary_path,
            &binary_bytes,
        );
        unsupported_effect
            .diagnostics
            .push("unsupported machine memory/effect witness class".to_string());
        let unsupported_effect_evidence = exact_replay_evidence_from_dispatch(unsupported_effect);

        assert_eq!(unsupported_effect_evidence.exact_replay_slice_attested_vcs(), 0);
        assert!(
            dispatch_exact_replay_transcript_artifact_digest(
                &unsupported_effect_evidence.solver_dispatch[0],
            )
            .is_none()
        );
        let blockers =
            unsupported_effect_evidence.exact_replay_slice_attestation_blockers().join("\n");
        assert!(blockers.contains("memory/effect attestation"), "{blockers}");

        let mut arch_mismatch = exact_replay_sat_dispatch_for_binary(
            "exact-replay-architecture-mismatch:vc0",
            &binary_path,
            &binary_bytes,
        );
        arch_mismatch.diagnostics.push(
            "exact replay architecture mismatch: selected image x86_64, replay backend aarch64"
                .to_string(),
        );
        let arch_mismatch_evidence = exact_replay_evidence_from_dispatch(arch_mismatch);

        assert_eq!(arch_mismatch_evidence.exact_replay_slice_attested_vcs(), 0);
        assert!(
            dispatch_exact_replay_transcript_artifact_digest(
                &arch_mismatch_evidence.solver_dispatch[0],
            )
            .is_none()
        );
        let blockers = arch_mismatch_evidence.exact_replay_slice_attestation_blockers().join("\n");
        assert!(blockers.contains("architecture"), "{blockers}");

        let _ = std::fs::remove_dir_all(root);
    }

    fn test_checked_certificate_dispatch(
        id: &str,
        certificate: ProofCertificateStatus,
    ) -> SolverDispatchRecord {
        let binary_sha256 = trust_types::digest::stable_sha256_hex(b"checked-certificate-test-binary");
        SolverDispatchRecord {
            id: id.to_string(),
            function: Some("main".to_string()),
            origin: Some(BinaryOrigin {
                binary_path: Some("fixtures/tiny.bin".to_string()),
                function_entry: Some(0x401000),
                instruction_address: 0x401010,
                instruction_size: Some(1),
                encoding: Some(0x90),
                instruction_bytes: vec![0x90],
                source: Some(SourceSpan::binary_address(0x401010)),
            }),
            vc_kind: Some(VcKind::DivisionByZero),
            vc: Some(SerializableVc {
                kind: VcKind::DivisionByZero,
                function: Symbol::intern("binary::main"),
                location: SourceSpan::binary_address(0x401010),
                formula: Formula::Bool(false),
                contract_metadata: None,
                obligation: None,
            }),
            solver: "ay-incremental".to_string(),
            backend: Some("ay-incremental".to_string()),
            status: SolverDispatchStatus::Unsat,
            query_semantics: SolverQuerySemantics::SatIsCounterexample,
            result: Some(VerificationResult::Proved {
                solver: Symbol::intern("ay-incremental"),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            }),
            binary_artifact_digest_identity: Some(BinaryArtifactDigestIdentity {
                root_artifact_digest: Some(BinaryArtifactDigest::sha256(binary_sha256.clone())),
                selected_image: Some(BinarySelectedImageIdentity {
                    file_offset: 0,
                    file_size: 1,
                    sha256: binary_sha256,
                }),
            }),
            replay: ReplayStatus::NotAttempted,
            certificate,
            ..Default::default()
        }
    }

    #[test]
    fn import_binds_selected_image_identity_from_actual_binary_path() {
        let (root, binary_bytes, current, artifact) =
            actual_binary_dispatch_and_artifact("import-selected-image-identity");
        let binary_sha256 = trust_types::digest::stable_sha256_hex(&binary_bytes);
        let mut evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current]);

        let report = evidence.import_checked_certificate_artifacts(&[artifact]);

        assert_eq!(report.imported, 1, "{report:#?}");
        assert_eq!(report.rejected_artifacts, 0);
        let row = &report.artifacts[0];
        assert_eq!(row.status, "imported");
        let identity = &row.binary_artifact_digest_identity;
        assert_eq!(
            identity.root_artifact_digest.as_ref().map(|digest| digest.value.as_str()),
            Some(binary_sha256.as_str())
        );
        let selected = identity.selected_image.as_ref().expect("selected image identity");
        assert_eq!(selected.file_offset, 0);
        assert_eq!(
            selected.file_size,
            u64::try_from(binary_bytes.len()).expect("fixture binary len fits u64")
        );
        assert_eq!(selected.sha256, binary_sha256);
        assert_eq!(evidence.checked_certificates(), 1);

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn production_report_preserves_missing_binary_identity_and_rejects_it() {
        let certificate_sha256 = trust_types::digest::stable_sha256_hex(b"checked certificate fixture");
        let valid_dispatch = test_checked_certificate_dispatch(
            "missing-binary-identity:vc0",
            ProofCertificateStatus::Checked {
                checker: "fixture-checker".to_string(),
                format: "lrat".to_string(),
                sha256: Some(certificate_sha256),
            },
        );
        let valid_record = certificate_check_record(&valid_dispatch, None, None, None, true, &[]);
        assert!(valid_record.binary_artifact_digest_identity.is_some());
        let valid_serialized =
            serde_json::to_value(&valid_record).expect("valid record serialization");
        assert!(valid_serialized["binary_artifact_digest_identity"].is_object());

        let mut dispatch = valid_dispatch;
        dispatch.binary_artifact_digest_identity = None;
        let evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);

        let report = evidence
            .checked_certificate_production_blocker_report(Path::new("target/checked-certs"));
        let record = &report.certificate_check_records[0];
        assert_eq!(record.status, "rejected");
        assert_eq!(record.error_kind.as_deref(), Some("binary-artifact-digest-identity-invalid"));
        assert!(record.binary_artifact_digest_identity.is_none());
        assert!(record.replay_digest_identity.binary_artifact_digest_identity.is_none());
        assert!(
            record
                .replay_digest_identity
                .blockers
                .iter()
                .any(|blocker| blocker.contains("identity is missing"))
        );

        let serialized = serde_json::to_value(record).expect("record serialization");
        assert!(
            serialized.get("binary_artifact_digest_identity").is_none(),
            "missing identity must remain absent, not serialize as an empty identity object"
        );
        assert!(
            serialized["replay_digest_identity"].get("binary_artifact_digest_identity").is_none(),
            "nested replay identity must preserve absence"
        );
    }

    #[test]
    fn import_rejects_stale_selected_image_binding() {
        let (root, binary_bytes, mut current, artifact) =
            actual_binary_dispatch_and_artifact("import-stale-selected-image");
        let binary_sha256 = trust_types::digest::stable_sha256_hex(&binary_bytes);
        current.binary_artifact_digest_identity = Some(BinaryArtifactDigestIdentity {
            root_artifact_digest: Some(BinaryArtifactDigest::sha256(binary_sha256)),
            selected_image: Some(BinarySelectedImageIdentity {
                file_offset: 0,
                file_size: u64::try_from(binary_bytes.len()).expect("fixture binary len fits u64"),
                sha256: trust_types::digest::stable_sha256_hex(b"stale selected image digest"),
            }),
        });
        let mut evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current]);

        let report = evidence.import_checked_certificate_artifacts(&[artifact]);

        assert_eq!(report.imported, 0);
        assert_eq!(report.rejected_artifacts, 1);
        assert_eq!(evidence.checked_certificates(), 0);
        let diagnostic = report.diagnostics.join("\n");
        assert!(
            diagnostic.contains("selected image digest does not match loaded binary range"),
            "{diagnostic}"
        );
        assert!(!evidence.solver_dispatch[0].certificate.is_checked());

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn import_rejects_binary_artifact_digest_mismatch() {
        let (root, binary_bytes, mut current, artifact) =
            actual_binary_dispatch_and_artifact("import-binary-digest-mismatch");
        let binary_sha256 = trust_types::digest::stable_sha256_hex(&binary_bytes);
        current.binary_artifact_digest_identity = Some(BinaryArtifactDigestIdentity {
            root_artifact_digest: Some(BinaryArtifactDigest::sha256(trust_types::digest::stable_sha256_hex(
                b"stale root binary digest",
            ))),
            selected_image: Some(BinarySelectedImageIdentity {
                file_offset: 0,
                file_size: u64::try_from(binary_bytes.len()).expect("fixture binary len fits u64"),
                sha256: binary_sha256,
            }),
        });
        let mut evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![current]);

        let report = evidence.import_checked_certificate_artifacts(&[artifact]);

        assert_eq!(report.imported, 0);
        assert_eq!(report.rejected_artifacts, 1);
        assert_eq!(evidence.checked_certificates(), 0);
        let diagnostic = report.diagnostics.join("\n");
        assert!(
            diagnostic.contains("root artifact digest does not match loaded binary"),
            "{diagnostic}"
        );
        assert!(!evidence.solver_dispatch[0].certificate.is_checked());

        let _ = std::fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn production_export_row_binds_selected_image_identity_from_actual_binary_path() {
        use std::os::unix::fs::PermissionsExt;

        let root = temp_test_dir("production-selected-image-identity");
        let proof_dir = root.join("proofs");
        std::fs::create_dir_all(&proof_dir).expect("proof dir should be writable");
        let binary_path = root.join("selected-image.bin");
        let binary_bytes = b"\x7fELF verify-binary production selected image".to_vec();
        std::fs::write(&binary_path, &binary_bytes).expect("test binary should be writable");
        let proof_bytes = b"normalized verify-binary evidence production proof";

        let mut dispatch = test_checked_certificate_dispatch(
            "production-selected-image-identity:vc0",
            ProofCertificateStatus::Unavailable {
                reason: Some("fixture starts unchecked".to_string()),
            },
        );
        set_test_dispatch_binary_path(&mut dispatch, &binary_path);
        dispatch.binary_artifact_digest_identity = None;
        derive_test_dispatch_binary_identity(&mut dispatch);
        let canonical_vc_bytes =
            canonical_vc_bytes(dispatch.vc.as_ref().expect("fixture dispatch has canonical VC"))
                .expect("fixture VC should serialize");
        let source_backpropagation_gate =
            CheckedBinaryCertificateSourceBackpropagationGate::default();
        let proof_artifact = build_normalized_solver_proof_export_artifact(
            NormalizedSolverProofExportArtifactInput {
                dispatch: &dispatch,
                canonical_vc_bytes: &canonical_vc_bytes,
                format: "lrat",
                proof_bytes: proof_bytes.to_vec(),
                solver_version: None,
                exported_at_unix_ms: 1_777_070_404_000,
                replay_transcript_digest: None,
                source_backpropagation_gate: &source_backpropagation_gate,
            },
        )
        .expect("normalized proof export should build");
        let proof_path =
            persist_normalized_solver_proof_export_artifact(&proof_dir, &proof_artifact)
                .expect("normalized proof export should persist");
        dispatch.certificate = ProofCertificateStatus::Present {
            format: "lrat".to_string(),
            sha256: Some(proof_artifact.proof_sha256.clone()),
            artifact_path: Some(proof_path.display().to_string()),
        };
        let mut evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);

        let checker_path = root.join("checker.sh");
        std::fs::write(&checker_path, "#!/bin/sh\nprintf 'checked'\n")
            .expect("checker should be writable");
        let mut permissions =
            std::fs::metadata(&checker_path).expect("checker metadata").permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&checker_path, permissions).expect("checker should be executable");

        let report = evidence.produce_checked_certificate_artifacts(
            &root.join("checked-certs"),
            Some(checker_path.as_path()),
            1_777_070_404_000,
        );

        assert_eq!(report.status, "exported", "{report:#?}");
        let binary_sha256 = trust_types::digest::stable_sha256_hex(&binary_bytes);
        let export_row = &report.export_row_records[0];
        assert_eq!(
            export_row
                .binary_artifact_digest_identity
                .root_artifact_digest
                .as_ref()
                .map(|digest| digest.value.as_str()),
            Some(binary_sha256.as_str())
        );
        assert_eq!(export_row.selected_image_identity.file_offset, 0);
        assert_eq!(
            export_row.selected_image_identity.file_size,
            u64::try_from(binary_bytes.len()).expect("fixture binary len fits u64")
        );
        assert_eq!(export_row.selected_image_identity.sha256, binary_sha256);
        assert_eq!(
            report.certificate_check_records[0].binary_artifact_digest_identity,
            Some(export_row.binary_artifact_digest_identity.clone())
        );

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn normalized_proof_loader_rejects_oversized_input_before_deserialization() {
        let root = temp_test_dir("normalized-proof-oversized");
        std::fs::create_dir_all(&root).expect("create proof fixture");
        let path = root.join("proof.json");
        let file = std::fs::File::create(&path).expect("create oversized proof");
        file.set_len(crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES as u64 + 1)
            .expect("size oversized proof");
        let dispatch = test_checked_certificate_dispatch(
            "normalized-proof-oversized:vc0",
            ProofCertificateStatus::Unavailable { reason: None },
        );
        let gate = CheckedBinaryCertificateSourceBackpropagationGate::default();

        let error = load_normalized_solver_proof_export_artifact(
            &path,
            &dispatch,
            b"{}",
            "lrat",
            &trust_types::digest::stable_sha256_hex(b"proof"),
            None,
            &gate,
        )
        .expect_err("oversized normalized proof must fail closed");
        assert_eq!(error.code, "normalized-proof-export-unreadable");
        assert!(error.detail.contains("safety limit"), "{error:?}");

        let _ = std::fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn normalized_proof_loader_rejects_leaf_symlink() {
        use std::os::unix::fs::symlink;

        let root = temp_test_dir("normalized-proof-symlink");
        std::fs::create_dir_all(&root).expect("create proof fixture");
        let target = root.join("target.json");
        let path = root.join("proof.json");
        std::fs::write(&target, b"{}").expect("write proof target");
        symlink(&target, &path).expect("link proof artifact");
        let dispatch = test_checked_certificate_dispatch(
            "normalized-proof-symlink:vc0",
            ProofCertificateStatus::Unavailable { reason: None },
        );
        let gate = CheckedBinaryCertificateSourceBackpropagationGate::default();

        let error = load_normalized_solver_proof_export_artifact(
            &path,
            &dispatch,
            b"{}",
            "lrat",
            &trust_types::digest::stable_sha256_hex(b"proof"),
            None,
            &gate,
        )
        .expect_err("symlinked normalized proof must fail closed");
        assert_eq!(error.code, "normalized-proof-export-unreadable");
        assert!(error.detail.contains("not a regular file"), "{error:?}");

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn noncanonical_checked_certificate_digest_does_not_satisfy_coverage() {
        let canonical_certificate_sha256 = trust_types::digest::stable_sha256_hex(b"checked certificate");
        let noncanonical_certificate_sha256 = canonical_certificate_sha256.to_uppercase();
        let noncanonical_dispatch = test_checked_certificate_dispatch(
            "checked-noncanonical:vc0",
            ProofCertificateStatus::Checked {
                checker: "ay-lrat-binary-check".to_string(),
                format: "lrat".to_string(),
                sha256: Some(noncanonical_certificate_sha256),
            },
        );
        let evidence =
            VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![noncanonical_dispatch]);

        assert_eq!(evidence.proved_vcs(), 1);
        assert_eq!(evidence.checked_certificates(), 0);
        assert_eq!(evidence.certificate_only_replay_semantics_vcs(), 0);
        assert_eq!(evidence.replay_semantics_satisfied_vcs(), 0);

        let canonical_dispatch = test_checked_certificate_dispatch(
            "checked-canonical:vc0",
            ProofCertificateStatus::Checked {
                checker: "ay-lrat-binary-check".to_string(),
                format: "lrat".to_string(),
                sha256: Some(canonical_certificate_sha256),
            },
        );
        let evidence =
            VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![canonical_dispatch]);

        assert_eq!(evidence.checked_certificates(), 1);
        assert_eq!(evidence.certificate_only_replay_semantics_vcs(), 1);
        assert_eq!(evidence.replay_semantics_satisfied_vcs(), 1);
    }

    #[test]
    fn production_report_rejects_noncanonical_normalized_proof_export_digest() {
        let proof_sha256 = trust_types::digest::stable_sha256_hex(b"normalized proof export").to_uppercase();
        let dispatch = test_checked_certificate_dispatch(
            "proof-export-noncanonical:vc0",
            ProofCertificateStatus::Present {
                format: "lrat".to_string(),
                sha256: Some(proof_sha256.clone()),
                artifact_path: Some("target/proofs/vc0.lrat".to_string()),
            },
        );
        let evidence = VerifyBinaryEvidence::from_solver_dispatch_records(1, vec![dispatch]);

        let report = evidence
            .checked_certificate_production_blocker_report(Path::new("target/checked-certs"));

        assert!(report.is_blocked());
        assert_eq!(report.proof_export_candidates, 0);
        assert_eq!(report.proof_export_records[0].status, "blocked_noncanonical_digest");
        assert_eq!(
            report.proof_export_records[0].proof_sha256.as_deref(),
            Some(proof_sha256.as_str())
        );
        assert_eq!(report.certificate_check_records[0].status, "rejected");
        assert_eq!(
            report.certificate_check_records[0].error_kind.as_deref(),
            Some("normalized-proof-export-digest-noncanonical")
        );
        assert!(report.blocker_records.iter().any(|record| {
            record.code == "normalized-proof-export-digest-noncanonical"
                && record.dispatch_id.as_deref() == Some("proof-export-noncanonical:vc0")
        }));
    }

    #[test]
    fn manifest_loader_rejects_missing_source_backpropagation_gate_row() {
        let dispatch = test_checked_certificate_dispatch(
            "missing-source-backprop-row:vc0",
            ProofCertificateStatus::Unavailable {
                reason: Some("fixture starts unchecked".to_string()),
            },
        );
        let canonical_vc_bytes =
            canonical_vc_bytes(dispatch.vc.as_ref().expect("fixture dispatch has canonical VC"))
                .expect("fixture VC should serialize");
        let export = SolverProofExport::new(
            &dispatch,
            &canonical_vc_bytes,
            "lrat",
            b"normalized proof payload with missing source gate row".to_vec(),
            None,
            1_777_070_406_000,
        );
        let checker = StructuralBinaryCertificateChecker::new(
            "missing-source-backprop-row-checker",
            "0.1.0",
            vec!["lrat".to_string()],
            1_777_070_406_000,
        );
        let check = trust_proof_cert::check_binary_certificate(
            &checker,
            BinaryCertificateCheckRequest::from_export(&dispatch, &canonical_vc_bytes, &export),
        );
        assert!(check.accepted, "{:?}", check.error);
        let artifact = check.certificate.expect("accepted check should carry artifact");

        let root = std::env::temp_dir().join(format!(
            "targo-trust-missing-source-backprop-row-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system time should be after unix epoch")
                .as_nanos()
        ));
        std::fs::create_dir_all(&root).expect("temp root should be created");
        let artifact_path =
            trust_proof_cert::persist_checked_certificate_artifact(&root, &artifact)
                .expect("checked artifact should persist");
        let relative_path = artifact_path
            .strip_prefix(&root)
            .expect("artifact should be below manifest root")
            .to_path_buf();
        let mut manifest = CheckedBinaryCertificateManifest::new();
        manifest.add_certificate(CheckedBinaryCertificateManifestEntry::from_artifact(
            &artifact,
            relative_path,
        ));
        let manifest_json = manifest.to_json().expect("manifest JSON should serialize");
        let manifest_path = trust_proof_cert::checked_certificate_manifest_path(&root);
        std::fs::write(&manifest_path, manifest_json.as_bytes()).expect("manifest should persist");

        let bundle = trust_proof_cert::CheckedBinaryCertificateAuditExportBundle::new(
            trust_types::digest::stable_sha256_hex(manifest_json.as_bytes()),
            Vec::new(),
        )
        .expect("empty bundle structure should serialize for negative fixture");
        std::fs::write(
            checked_certificate_audit_export_bundle_path(&root),
            bundle.to_json().expect("bundle JSON should serialize").as_bytes(),
        )
        .expect("bundle should persist");

        let error = load_checked_certificate_artifact_rows(
            std::iter::empty::<&Path>(),
            [manifest_path.as_path()],
        )
        .expect_err("missing source_backpropagation_gate audit row must fail closed")
        .to_string();
        assert!(error.contains("missing source_backpropagation_gate row"), "{error}");
        assert!(error.contains(&artifact.certificate_sha256), "{error}");
        assert!(error.contains("missing-source-backprop-row:vc0"), "{error}");

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn manifest_loader_rejects_oversized_manifest_before_deserialization() {
        let root = temp_test_dir("manifest-oversized");
        std::fs::create_dir_all(&root).expect("create manifest fixture");
        let manifest = root.join("manifest.json");
        let file = std::fs::File::create(&manifest).expect("create oversized manifest");
        file.set_len(crate::input_limits::MAX_SAVED_PROOF_REPORT_BYTES as u64 + 1)
            .expect("size oversized manifest");

        let error =
            load_checked_certificate_artifact_rows(std::iter::empty::<&Path>(), [&manifest])
                .expect_err("oversized checked-certificate manifest must fail closed");
        assert!(error.to_string().contains("safety limit"), "{error}");

        let _ = std::fs::remove_dir_all(root);
    }

    #[cfg(unix)]
    #[test]
    fn manifest_loader_rejects_leaf_symlink() {
        use std::os::unix::fs::symlink;

        let root = temp_test_dir("manifest-symlink");
        std::fs::create_dir_all(&root).expect("create manifest fixture");
        let target = root.join("target.json");
        let manifest = root.join("manifest.json");
        std::fs::write(&target, b"{}").expect("write manifest target");
        symlink(&target, &manifest).expect("link manifest");

        let error =
            load_checked_certificate_artifact_rows(std::iter::empty::<&Path>(), [&manifest])
                .expect_err("symlinked checked-certificate manifest must fail closed");
        assert!(error.to_string().contains("not a regular file"), "{error}");

        let _ = std::fs::remove_dir_all(root);
    }
}
