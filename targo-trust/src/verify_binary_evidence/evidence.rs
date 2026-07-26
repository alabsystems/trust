// VerifyBinaryEvidence — aggregated counters and the checked-certificate
// import / production driver.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use trust_proof_cert::{
    CertError, CheckedBinaryCertificateArtifact, CheckedBinaryCertificateAuditExport,
    CheckedBinaryCertificateManifest, CheckedBinaryCertificateProductionManifestAcceptedRowInput,
    CheckedBinaryCertificateSourceBackpropagationGate,
    checked_certificate_audit_export_bundle_path,
    evaluate_checked_binary_certificate_production_manifest,
    import_checked_certificate_for_dispatch_by_canonical_digests,
    persist_checked_certificate_audit_export_bundle, persist_checked_certificate_manifest,
};
use trust_types::{ReplayStatus, SolverDispatchRecord, VerificationResult};

use crate::external_checker::prepare_external_checker;

use super::{
    CheckedCertificateArtifactImportRecord, CheckedCertificateImportReport,
    CheckedCertificateLoadedMetadata, CheckedCertificateProductionCandidate,
    CheckedCertificateProductionInventory, CheckedCertificateProductionReport,
    ProofExportRecordInput, VerifyBinaryEvidence, bind_dispatch_binary_artifact_digest_identity,
    certificate_check_record, checked_certificate_replay_digest_identity_record,
    derive_exact_replay_witness_binding,
    dispatch_binary_artifact_digest_identity_acceptance_blockers, dispatch_canonical_binding,
    dispatch_exact_replay_slice_attestation_blockers,
    dispatch_exact_replay_transcript_artifact_digest_raw,
    dispatch_has_checked_certificate_identity, dispatch_has_exact_replay_slice_attestation,
    dispatch_proves_required_vc, dispatch_satisfies_replay_semantics, has_solver_proof_bytes,
    is_canonical_sha256_hex, load_checked_certificate_artifact_rows,
    load_normalized_solver_proof_export_artifact, loaded_checked_certificate_metadata,
    loaded_import_loader_status, normalized_proof_export_present,
    produce_one_checked_certificate_artifact, production_blocker_record,
    production_checker_evidence_status_label, production_export_row_record, proof_export_record,
    push_dispatch_blocker, raw_solver_proof_byte_evidence,
    validate_checked_certificate_required_vc_production_inventory,
};

impl PartialEq for VerifyBinaryEvidence {
    fn eq(&self, other: &Self) -> bool {
        self.required_vcs == other.required_vcs
            && self.solver_dispatch.len() == other.solver_dispatch.len()
            && self.proved_vcs() == other.proved_vcs()
            && self.checked_certificates() == other.checked_certificates()
            && self.replayed_vcs() == other.replayed_vcs()
            && self.exact_replay_slice_attested_vcs() == other.exact_replay_slice_attested_vcs()
            && self.replay_semantics_satisfied_vcs() == other.replay_semantics_satisfied_vcs()
            && self.raw_solver_proof_bytes() == other.raw_solver_proof_bytes()
    }
}

impl Eq for VerifyBinaryEvidence {}

impl VerifyBinaryEvidence {
    #[cfg(test)]
    pub(crate) fn from_solver_dispatch_records(
        required_vcs: usize,
        solver_dispatch: Vec<SolverDispatchRecord>,
    ) -> Self {
        let mut artifact_identity_cache = BTreeMap::new();
        let solver_dispatch = solver_dispatch
            .into_iter()
            .map(|mut record| {
                bind_dispatch_binary_artifact_digest_identity(
                    &mut record,
                    &mut artifact_identity_cache,
                );
                record
            })
            .collect();
        Self { required_vcs, solver_dispatch }
    }

    pub(crate) fn add_required_vcs(&mut self, count: usize) {
        self.required_vcs = self.required_vcs.saturating_add(count);
    }

    pub(crate) fn extend_solver_dispatch(
        &mut self,
        records: impl IntoIterator<Item = SolverDispatchRecord>,
    ) {
        let mut artifact_identity_cache = BTreeMap::new();
        for mut record in records {
            bind_dispatch_binary_artifact_digest_identity(
                &mut record,
                &mut artifact_identity_cache,
            );
            derive_exact_replay_witness_binding(&mut record, &mut artifact_identity_cache);
            self.solver_dispatch.push(record);
        }
    }

    pub(crate) fn proved_vcs(&self) -> usize {
        self.solver_dispatch.iter().filter(|record| dispatch_proves_required_vc(record)).count()
    }

    pub(crate) fn checked_certificates(&self) -> usize {
        self.solver_dispatch
            .iter()
            .filter(|record| {
                dispatch_proves_required_vc(record)
                    && dispatch_has_checked_certificate_identity(record)
            })
            .count()
    }

    pub(crate) fn replayed_vcs(&self) -> usize {
        self.solver_dispatch.iter().filter(|record| record.replay == ReplayStatus::Replayed).count()
    }

    pub(crate) fn exact_replay_slice_attested_vcs(&self) -> usize {
        self.solver_dispatch
            .iter()
            .filter(|record| {
                record.replay == ReplayStatus::Replayed
                    && dispatch_has_exact_replay_slice_attestation(record)
            })
            .count()
    }

    pub(crate) fn exact_replay_slice_attestation_blockers(&self) -> Vec<String> {
        self.solver_dispatch
            .iter()
            .flat_map(dispatch_exact_replay_slice_attestation_blockers)
            .collect()
    }

    pub(crate) fn certificate_only_replay_semantics_vcs(&self) -> usize {
        self.solver_dispatch
            .iter()
            .filter(|record| {
                dispatch_proves_required_vc(record)
                    && record.replay == ReplayStatus::NotAttempted
                    && dispatch_has_checked_certificate_identity(record)
            })
            .count()
    }

    pub(crate) fn replay_semantics_satisfied_vcs(&self) -> usize {
        self.solver_dispatch
            .iter()
            .filter(|record| dispatch_satisfies_replay_semantics(record))
            .count()
    }

    pub(crate) fn raw_solver_proof_bytes(&self) -> usize {
        self.solver_dispatch
            .iter()
            .filter(|record| {
                matches!(
                    record.result,
                    Some(VerificationResult::Proved { proof_certificate: Some(_), .. })
                )
            })
            .count()
    }

    #[cfg(test)]
    pub(crate) fn load_and_import_checked_certificate_artifacts<I, P>(
        &mut self,
        paths: I,
    ) -> Result<CheckedCertificateImportReport, CertError>
    where
        I: IntoIterator<Item = P>,
        P: AsRef<Path>,
    {
        let paths = paths.into_iter().map(|path| path.as_ref().to_path_buf()).collect::<Vec<_>>();
        let loaded = load_checked_certificate_artifact_rows(&paths, std::iter::empty::<PathBuf>())?;
        let artifacts = loaded.iter().map(|row| row.artifact.clone()).collect::<Vec<_>>();
        let artifact_paths = loaded.iter().map(|row| row.path.clone()).collect::<Vec<_>>();
        let metadata = loaded.iter().map(loaded_checked_certificate_metadata).collect::<Vec<_>>();
        let mut report = self.import_checked_certificate_artifacts_with_paths_and_metadata(
            &artifacts,
            Some(&artifact_paths),
            &metadata,
        );
        report.requested_artifacts = paths.len();
        report.loader_status = loaded_import_loader_status(report.loaded_artifacts);
        Ok(report)
    }

    pub(crate) fn load_and_import_checked_certificate_artifacts_and_manifests<AI, AP, MI, MP>(
        &mut self,
        artifact_paths: AI,
        manifest_paths: MI,
    ) -> Result<CheckedCertificateImportReport, CertError>
    where
        AI: IntoIterator<Item = AP>,
        AP: AsRef<Path>,
        MI: IntoIterator<Item = MP>,
        MP: AsRef<Path>,
    {
        let artifact_paths =
            artifact_paths.into_iter().map(|path| path.as_ref().to_path_buf()).collect::<Vec<_>>();
        let manifest_paths =
            manifest_paths.into_iter().map(|path| path.as_ref().to_path_buf()).collect::<Vec<_>>();
        let requested_artifacts = artifact_paths.len();
        let requested_manifests = manifest_paths.len();
        let loaded = load_checked_certificate_artifact_rows(&artifact_paths, &manifest_paths)?;
        let artifacts = loaded.iter().map(|row| row.artifact.clone()).collect::<Vec<_>>();
        let loaded_artifact_paths = loaded.iter().map(|row| row.path.clone()).collect::<Vec<_>>();
        let metadata = loaded.iter().map(loaded_checked_certificate_metadata).collect::<Vec<_>>();
        let mut report = self.import_checked_certificate_artifacts_with_paths_and_metadata(
            &artifacts,
            Some(&loaded_artifact_paths),
            &metadata,
        );
        report.requested_artifacts = requested_artifacts;
        report.requested_manifests = requested_manifests;
        report.loader_status = loaded_import_loader_status(report.loaded_artifacts);
        Ok(report)
    }

    #[cfg(test)]
    pub(crate) fn import_checked_certificate_artifacts(
        &mut self,
        artifacts: &[CheckedBinaryCertificateArtifact],
    ) -> CheckedCertificateImportReport {
        let mut report = self.import_checked_certificate_artifacts_with_paths(artifacts, None);
        report.loader_status = loaded_import_loader_status(report.loaded_artifacts);
        report.requested_artifacts = artifacts.len();
        report
    }

    #[cfg(test)]
    pub(crate) fn checked_certificate_production_blocker_report(
        &self,
        export_dir: &Path,
    ) -> CheckedCertificateProductionReport {
        self.clone().produce_checked_certificate_artifacts(export_dir, None, 0)
    }

    pub(crate) fn produce_checked_certificate_artifacts(
        &mut self,
        export_dir: &Path,
        checker_path: Option<&Path>,
        checked_at_unix_ms: u64,
    ) -> CheckedCertificateProductionReport {
        self.bind_binary_artifact_digest_identities();

        let mut proof_export_records = Vec::new();
        let mut certificate_check_records = Vec::new();
        let mut blocker_records = Vec::new();
        let mut candidates = Vec::new();
        let mut successes = Vec::new();
        let mut artifact_paths = Vec::new();
        let mut manifest_entries = Vec::new();
        let mut export_row_records = Vec::new();
        let mut diagnostics = Vec::new();
        let checker_selection = checker_path
            .map(|path| path.display().to_string())
            .unwrap_or_else(|| "absent".to_string());
        let source_backpropagation_gate =
            CheckedBinaryCertificateSourceBackpropagationGate::default();

        if checker_path.is_none() {
            blocker_records.push(production_blocker_record(
                "checker-selection-missing",
                "checked-certificate-production",
                None,
                "no production checked-certificate checker was selected; pass --checked-cert-checker <path>",
                ["production_checker"],
            ));
        }

        for (dispatch_index, dispatch) in self
            .solver_dispatch
            .iter()
            .enumerate()
            .filter(|(_, dispatch)| dispatch_proves_required_vc(dispatch))
        {
            let binding = dispatch_canonical_binding(dispatch);
            let raw_proof = raw_solver_proof_byte_evidence(dispatch);
            let proof_export_present = normalized_proof_export_present(dispatch);
            let proof_export = proof_export_present
                .as_ref()
                .filter(|export| is_canonical_sha256_hex(&export.proof_sha256))
                .cloned();
            let checked = dispatch_has_checked_certificate_identity(dispatch);
            let replay_transcript_digest_raw =
                dispatch_exact_replay_transcript_artifact_digest_raw(dispatch);
            let replay_transcript_digest = replay_transcript_digest_raw
                .as_deref()
                .filter(|digest| is_canonical_sha256_hex(digest))
                .map(str::to_string);
            let digest_identity_blockers =
                dispatch_binary_artifact_digest_identity_acceptance_blockers(dispatch);
            let mut dispatch_blocker_codes = Vec::new();
            let mut loaded_proof_export_artifact = None;

            if binding.is_none() {
                push_dispatch_blocker(
                    &mut blocker_records,
                    &mut dispatch_blocker_codes,
                    dispatch,
                    "canonical-binding-missing",
                    "checked-certificate-production",
                    "solver dispatch is missing canonical VC or binary-origin binding required for checked-certificate production",
                    ["canonical_vc", "binary_origin"],
                );
            }
            if let Some(raw) = &raw_proof {
                let detail = format!(
                    "raw solver proof bytes are audit-only evidence and cannot be checked without a normalized solver proof export: sha256={} byte_len={}",
                    raw.sha256, raw.byte_len
                );
                push_dispatch_blocker(
                    &mut blocker_records,
                    &mut dispatch_blocker_codes,
                    dispatch,
                    "raw-solver-proof-bytes-audit-only",
                    "checked-certificate-production",
                    detail,
                    ["normalized_solver_proof_export", "production_checker"],
                );
            }
            if let Some(proof_export) = proof_export_present
                .as_ref()
                .filter(|export| !is_canonical_sha256_hex(&export.proof_sha256))
            {
                push_dispatch_blocker(
                    &mut blocker_records,
                    &mut dispatch_blocker_codes,
                    dispatch,
                    "normalized-proof-export-digest-noncanonical",
                    "checked-certificate-production",
                    format!(
                        "normalized solver proof export digest for dispatch {} is not canonical lowercase SHA-256 hex: {}",
                        dispatch.id, proof_export.proof_sha256
                    ),
                    ["canonical_sha256_proof_export_digest"],
                );
            }
            if binding.is_some() && !digest_identity_blockers.is_empty() {
                push_dispatch_blocker(
                    &mut blocker_records,
                    &mut dispatch_blocker_codes,
                    dispatch,
                    "binary-artifact-digest-identity-invalid",
                    "checked-certificate-production",
                    format!(
                        "solver dispatch binary artifact digest identity is not accepted: {}",
                        digest_identity_blockers.join("; ")
                    ),
                    ["binary_artifact_digest_identity", "selected_image_digest_identity"],
                );
            }
            if dispatch.replay == ReplayStatus::Replayed && replay_transcript_digest.is_none() {
                match replay_transcript_digest_raw {
                    Some(digest) => push_dispatch_blocker(
                        &mut blocker_records,
                        &mut dispatch_blocker_codes,
                        dispatch,
                        "replay-transcript-digest-noncanonical",
                        "checked-certificate-production",
                        format!(
                            "solver dispatch replay transcript digest is not canonical lowercase SHA-256 hex: {digest}"
                        ),
                        ["canonical_sha256_replay_transcript_digest"],
                    ),
                    None => push_dispatch_blocker(
                        &mut blocker_records,
                        &mut dispatch_blocker_codes,
                        dispatch,
                        "replay-transcript-digest-missing",
                        "checked-certificate-production",
                        "replayed solver dispatch is missing a canonical replay transcript digest required for checked-certificate production",
                        ["machine_replay_transcript", "canonical_sha256_replay_transcript_digest"],
                    ),
                }
            }
            if !checked && proof_export.is_none() {
                push_dispatch_blocker(
                    &mut blocker_records,
                    &mut dispatch_blocker_codes,
                    dispatch,
                    "normalized-proof-export-missing",
                    "checked-certificate-production",
                    "solver dispatch has no normalized solver proof export bound to the canonical VC digest",
                    ["normalized_solver_proof_export"],
                );
            }
            if let Some(proof_export) = &proof_export {
                if proof_export.artifact_path.as_ref().is_none_or(|path| path.trim().is_empty()) {
                    push_dispatch_blocker(
                        &mut blocker_records,
                        &mut dispatch_blocker_codes,
                        dispatch,
                        "normalized-proof-export-path-missing",
                        "checked-certificate-production",
                        "solver dispatch has a normalized proof export digest but no readable artifact path",
                        ["normalized_solver_proof_export"],
                    );
                } else if let Some(binding) = binding.as_ref() {
                    if dispatch.replay != ReplayStatus::Replayed
                        || replay_transcript_digest.is_some()
                    {
                        let proof_path = PathBuf::from(
                            proof_export
                                .artifact_path
                                .as_ref()
                                .expect("checked non-empty proof artifact path"),
                        );
                        match load_normalized_solver_proof_export_artifact(
                            &proof_path,
                            dispatch,
                            &binding.canonical_vc_bytes,
                            proof_export.format.as_str(),
                            proof_export.proof_sha256.as_str(),
                            replay_transcript_digest.as_deref(),
                            &source_backpropagation_gate,
                        ) {
                            Ok(loaded) => loaded_proof_export_artifact = Some(loaded),
                            Err(error) => {
                                push_dispatch_blocker(
                                    &mut blocker_records,
                                    &mut dispatch_blocker_codes,
                                    dispatch,
                                    error.code,
                                    "checked-certificate-production",
                                    error.detail,
                                    [
                                        "normalized_solver_proof_export",
                                        "content_addressed_proof_export",
                                        "proof_export_binding",
                                    ],
                                );
                            }
                        }
                    }
                }
            }
            if !checked {
                push_dispatch_blocker(
                    &mut blocker_records,
                    &mut dispatch_blocker_codes,
                    dispatch,
                    "checked-certificate-missing",
                    "checked-certificate-production",
                    "solver dispatch has no independently checked certificate artifact",
                    ["checker_success", "checked_certificate_artifact"],
                );
            }

            if let (Some(binding), Some(proof_export), Some(loaded_proof_export_artifact)) =
                (binding.as_ref(), proof_export.as_ref(), loaded_proof_export_artifact.as_ref())
            {
                if !checked
                    && digest_identity_blockers.is_empty()
                    && raw_proof.is_none()
                    && (dispatch.replay != ReplayStatus::Replayed
                        || replay_transcript_digest.is_some())
                    && proof_export
                        .artifact_path
                        .as_ref()
                        .is_some_and(|path| !path.trim().is_empty())
                {
                    candidates.push(CheckedCertificateProductionCandidate {
                        dispatch_index,
                        dispatch: dispatch.clone(),
                        binding: binding.clone(),
                        proof_export: proof_export.clone(),
                        proof_export_artifact: loaded_proof_export_artifact.clone(),
                        replay_transcript_digest,
                    });
                }
            }

            proof_export_records.push(proof_export_record(ProofExportRecordInput {
                dispatch,
                binding: binding.as_ref(),
                proof_export_present: proof_export_present.as_ref(),
                proof_export: proof_export.as_ref(),
                proof_export_artifact: loaded_proof_export_artifact.as_ref(),
                raw_proof: raw_proof.as_ref(),
                checked,
                blocker_codes: &dispatch_blocker_codes,
            }));
            certificate_check_records.push(certificate_check_record(
                dispatch,
                proof_export_present.as_ref(),
                proof_export.as_ref(),
                raw_proof.as_ref(),
                checked,
                &dispatch_blocker_codes,
            ));
        }

        if let Some(checker_path) = checker_path {
            match prepare_external_checker(checker_path, checked_at_unix_ms) {
                Ok(prepared_checker) => {
                    let runner = &prepared_checker.runner;
                    let checker_id = checker_path
                        .file_name()
                        .and_then(|name| name.to_str())
                        .filter(|name| !name.trim().is_empty())
                        .unwrap_or("checked-cert-checker")
                        .to_string();
                    let checker_version =
                        format!("external-sha256:{}", prepared_checker.checker_sha256);
                    for candidate in candidates {
                        match produce_one_checked_certificate_artifact(
                            export_dir,
                            &checker_id,
                            &checker_version,
                            checked_at_unix_ms,
                            runner,
                            &candidate,
                            &mut self.solver_dispatch[candidate.dispatch_index],
                        ) {
                            Ok(success) => {
                                blocker_records.retain(|record| {
                                    !(record.dispatch_id.as_deref()
                                        == Some(success.dispatch_id.as_str())
                                        && matches!(
                                            record.code.as_str(),
                                            "checked-certificate-missing"
                                                | "checker-selection-missing"
                                        ))
                                });
                                artifact_paths.push(success.artifact_path.clone());
                                if let Some(record) = proof_export_records
                                    .iter_mut()
                                    .find(|record| record.dispatch_id == success.dispatch_id)
                                {
                                    record.status = "exported".to_string();
                                    record.proof_export_metadata_path =
                                        Some(success.proof_export_metadata_path.clone());
                                    record.proof_export_payload_path =
                                        Some(success.proof_export_payload_path.clone());
                                    record.checked_certificate_artifact_path =
                                        Some(success.artifact_path.clone());
                                    record.proof_export_artifact_sha256 =
                                        Some(success.proof_export_artifact_sha256.clone());
                                    record.proof_export_content_addressed = Some(true);
                                    record.blocker_codes.retain(|code| {
                                        code != "checked-certificate-missing"
                                            && code != "checker-selection-missing"
                                    });
                                }
                                if let Some(record) = certificate_check_records
                                    .iter_mut()
                                    .find(|record| record.dispatch_id == success.dispatch_id)
                                {
                                    record.status = "checked".to_string();
                                    record.certificate_status = "checked".to_string();
                                    record.checker = Some(success.checker.clone());
                                    record.format = Some(success.format.clone());
                                    record.certificate_sha256 =
                                        Some(success.certificate_sha256.clone());
                                    record.manifest_identity_sha256 =
                                        Some(success.manifest_identity_sha256.clone());
                                    record.source_backpropagation_gate_sha256 =
                                        success.source_backpropagation_gate_sha256.clone();
                                    record.replay_transcript_digest =
                                        success.replay_transcript_digest.clone();
                                    record.binary_artifact_digest_identity =
                                        Some(success.binary_artifact_digest_identity.clone());
                                    record.replay_digest_identity =
                                        checked_certificate_replay_digest_identity_record(
                                            success.replay,
                                            success.replay_transcript_digest.clone(),
                                            Some(success.binary_artifact_digest_identity.clone()),
                                        );
                                    record.production_checker_evidence_sha256 =
                                        Some(success.production_checker_evidence_sha256.clone());
                                    record.external_checker_binary_sha256 =
                                        Some(success.external_checker_binary_sha256.clone());
                                    record.external_checker_invocation_sha256 =
                                        Some(success.external_checker_invocation_sha256.clone());
                                    record.external_checker_stdout_sha256 =
                                        success.external_checker_stdout_sha256.clone();
                                    record.external_checker_stderr_sha256 =
                                        success.external_checker_stderr_sha256.clone();
                                    record.diagnostic = Some(format!(
                                        "production checker evidence sha256={} checker={} checker_version={}",
                                        success.production_checker_evidence_sha256,
                                        success.checker,
                                        success.checker_version
                                    ));
                                    record.error_kind = None;
                                    record.blocker_codes.retain(|code| {
                                        code != "checked-certificate-missing"
                                            && code != "checker-selection-missing"
                                    });
                                }
                                successes.push(success);
                            }
                            Err(blocker) => {
                                if let Some(record) = certificate_check_records
                                    .iter_mut()
                                    .find(|record| record.dispatch_id == candidate.dispatch.id)
                                {
                                    record.status = "rejected".to_string();
                                    record.error_kind = Some(blocker.code.clone());
                                    record.diagnostic = Some(blocker.detail.clone());
                                    record.blocker_codes.push(blocker.code.clone());
                                }
                                blocker_records.push(blocker);
                            }
                        }
                    }
                }
                Err(error) => blocker_records.push(production_blocker_record(
                    "checker-unreadable",
                    "checked-certificate-production",
                    None,
                    format!(
                        "checked certificate production checker `{}` is not readable: {error}",
                        checker_path.display()
                    ),
                    ["production_checker"],
                )),
            }
        }

        for success in &successes {
            diagnostics.push(format!(
                "checked certificate production exported artifact for dispatch {} to {}",
                success.dispatch_id, success.artifact_path
            ));
            diagnostics.push(format!(
            "checked certificate production exported normalized proof metadata for dispatch {} to {} and payload to {}",
            success.dispatch_id,
            success.proof_export_metadata_path,
            success.proof_export_payload_path
        ));
        }

        let candidate_dispatches = self
            .solver_dispatch
            .iter()
            .filter(|dispatch| dispatch_proves_required_vc(dispatch))
            .count();
        let canonical_binding_candidates = self
            .solver_dispatch
            .iter()
            .filter(|dispatch| dispatch_proves_required_vc(dispatch))
            .filter(|dispatch| dispatch_canonical_binding(dispatch).is_some())
            .count();
        let raw_solver_proof_byte_dispatches = self
            .solver_dispatch
            .iter()
            .filter(|dispatch| dispatch_proves_required_vc(dispatch))
            .filter(|dispatch| has_solver_proof_bytes(dispatch))
            .count();
        let proof_export_candidates = proof_export_records
            .iter()
            .filter(|record| matches!(record.status.as_str(), "available" | "exported"))
            .count();
        let already_checked_certificates = self.checked_certificates();
        let exported_artifacts = artifact_paths.len();
        let rejected_dispatches = candidate_dispatches.saturating_sub(already_checked_certificates);
        let mut blockers = if checker_path.is_none() {
            vec![
                "no production checked-certificate checker was selected; pass --checked-cert-checker <path>".to_string(),
                "structural proof metadata and raw solver proof bytes cannot be promoted to checked certificates without a selected production checker".to_string(),
            ]
        } else {
            blocker_records.iter().map(|record| record.detail.clone()).collect::<Vec<_>>()
        };
        blockers.sort();
        blockers.dedup();
        if raw_solver_proof_byte_dispatches > 0 {
            blockers.push(format!(
                "raw solver proof bytes were observed for {raw_solver_proof_byte_dispatches} dispatch(es), but no production checker/exportable proof artifact exists; raw bytes are not checked certificates"
            ));
        }
        if proof_export_candidates == 0 {
            blockers.push(
                "solver dispatch evidence contains no normalized proof exports for checked-certificate production".to_string(),
            );
        }
        if exported_artifacts > 0 {
            let mut manifest = CheckedBinaryCertificateManifest::new();
            let mut audit_exports = Vec::new();
            for success in &successes {
                manifest.add_certificate(success.manifest_entry.clone());
                match CheckedBinaryCertificateAuditExport::from_manifest_entry_and_record(
                    success.manifest_entry.clone(),
                    success.acceptance_record.clone(),
                ) {
                    Ok(audit_export) => {
                        match production_export_row_record(success, &audit_export) {
                            Ok(row) => export_row_records.push(row),
                            Err(blocker) => {
                                blockers.push(blocker.detail.clone());
                                blocker_records.push(blocker);
                            }
                        }
                        audit_exports.push(audit_export);
                    }
                    Err(error) => {
                        blockers.push(format!(
                            "checked certificate production audit export could not include dispatch `{}`: {error}",
                            success.dispatch_id
                        ));
                        blocker_records.push(production_blocker_record(
                            "checked-certificate-audit-export-build-failed",
                            "checked-certificate-production",
                            None,
                            format!(
                                "checked certificate production audit export could not include dispatch `{}`: {error}",
                                success.dispatch_id
                            ),
                            ["checked_certificate_manifest", "checked_certificate_audit_export"],
                        ));
                    }
                }
            }
            export_row_records.sort_by(|left, right| {
                left.certificate_sha256
                    .cmp(&right.certificate_sha256)
                    .then_with(|| left.vc_sha256.cmp(&right.vc_sha256))
                    .then_with(|| left.dispatch_id.cmp(&right.dispatch_id))
            });
            if !manifest.certificates.is_empty() {
                manifest_entries = manifest.certificates.clone();
                let persisted = if audit_exports.len() == manifest.certificates.len() {
                    persist_checked_certificate_audit_export_bundle(
                        export_dir,
                        &manifest,
                        &audit_exports,
                    )
                    .map(|_| trust_proof_cert::checked_certificate_manifest_path(export_dir))
                } else {
                    persist_checked_certificate_manifest(export_dir, &manifest)
                };
                match persisted {
                    Ok(path) => {
                        diagnostics.push(format!(
                            "checked certificate production manifest written to {}",
                            path.display()
                        ));
                        if audit_exports.len() == manifest.certificates.len() {
                            diagnostics.push(format!(
                                "checked certificate production audit export bundle written to {}",
                                checked_certificate_audit_export_bundle_path(export_dir).display()
                            ));
                        }
                    }
                    Err(error) => {
                        blockers.push(format!(
                            "checked certificate production manifest/audit export bundle could not be written: {error}"
                        ));
                        blocker_records.push(production_blocker_record(
                            "checked-certificate-manifest-write-failed",
                            "checked-certificate-production",
                            None,
                            format!(
                                "checked certificate production manifest/audit export bundle could not be written: {error}"
                            ),
                            ["checked_certificate_manifest", "checked_certificate_audit_export"],
                        ));
                    }
                }
            } else if blockers.is_empty() {
                let error = "manifest contains no exported checked certificate rows";
                blockers.push(format!(
                    "checked certificate production manifest could not be built: {error}"
                ));
                blocker_records.push(production_blocker_record(
                    "checked-certificate-manifest-build-failed",
                    "checked-certificate-production",
                    None,
                    format!("checked certificate production manifest could not be built: {error}"),
                    ["checked_certificate_manifest"],
                ));
            }
        }

        let mut manifest_path = None;
        if !manifest_entries.is_empty() {
            manifest_path = Some(
                trust_proof_cert::checked_certificate_manifest_path(export_dir)
                    .display()
                    .to_string(),
            );
        }
        if checker_path.is_some() {
            let production_manifest_inputs = successes
                .iter()
                .map(|success| CheckedBinaryCertificateProductionManifestAcceptedRowInput {
                    manifest_entry: &success.manifest_entry,
                    acceptance_record: &success.acceptance_record,
                })
                .collect::<Vec<_>>();
            let production_manifest =
                trust_proof_cert::CheckedBinaryCertificateProductionManifest::from_manifest_acceptance_records(
                    self.required_vcs,
                    &production_manifest_inputs,
                );
            match production_manifest {
                Ok(production_manifest) => {
                    let production_manifest_decision =
                        evaluate_checked_binary_certificate_production_manifest(
                            &production_manifest,
                        );
                    if !production_manifest_decision.accepted {
                        for rejection in production_manifest_decision.rejections {
                            let detail = format!(
                                "checked certificate production manifest failed coverage validation: {rejection:?}"
                            );
                            blockers.push(detail.clone());
                            blocker_records.push(production_blocker_record(
                                "checked-certificate-production-coverage-incomplete",
                                "checked-certificate-production",
                                None,
                                detail,
                                ["checked_certificate_artifact", "production_checker_evidence"],
                            ));
                        }
                    }
                }
                Err(error) => {
                    let detail = format!(
                        "checked certificate production manifest failed coverage validation: {error}"
                    );
                    blockers.push(detail.clone());
                    blocker_records.push(production_blocker_record(
                        "checked-certificate-production-coverage-incomplete",
                        "checked-certificate-production",
                        None,
                        detail,
                        ["checked_certificate_artifact", "production_checker_evidence"],
                    ));
                }
            }

            validate_checked_certificate_required_vc_production_inventory(
                CheckedCertificateProductionInventory {
                    required_vcs: self.required_vcs,
                    candidate_dispatches,
                    proof_export_candidates,
                    exported_artifacts,
                    proof_export_records: proof_export_records.as_slice(),
                    export_row_records: export_row_records.as_slice(),
                },
                &mut blockers,
                &mut blocker_records,
            );
        }

        blockers.sort();
        blockers.dedup();
        let status = if blockers.is_empty() && exported_artifacts == proof_export_candidates {
            "exported"
        } else {
            "blocked"
        };

        CheckedCertificateProductionReport {
            requested: true,
            status: status.to_string(),
            export_dir: export_dir.display().to_string(),
            checker_selection,
            candidate_dispatches,
            canonical_binding_candidates,
            proof_export_candidates,
            raw_solver_proof_byte_dispatches,
            already_checked_certificates,
            exported_artifacts,
            rejected_dispatches,
            artifact_paths,
            manifest_path,
            source_backpropagation_gate,
            proof_export_records,
            certificate_check_records,
            export_row_records,
            blocker_records,
            blockers,
            diagnostics,
        }
    }

    #[cfg(test)]
    fn import_checked_certificate_artifacts_with_paths(
        &mut self,
        artifacts: &[CheckedBinaryCertificateArtifact],
        artifact_paths: Option<&[String]>,
    ) -> CheckedCertificateImportReport {
        self.import_checked_certificate_artifacts_with_paths_and_source_gates(
            artifacts,
            artifact_paths,
            None,
        )
    }

    #[cfg(test)]
    fn import_checked_certificate_artifacts_with_paths_and_source_gates(
        &mut self,
        artifacts: &[CheckedBinaryCertificateArtifact],
        artifact_paths: Option<&[String]>,
        source_backpropagation_gates: Option<&[CheckedBinaryCertificateSourceBackpropagationGate]>,
    ) -> CheckedCertificateImportReport {
        let artifact_metadata = artifacts
            .iter()
            .enumerate()
            .map(|(index, artifact)| {
                CheckedCertificateLoadedMetadata::from_artifact_and_gate(
                    artifact,
                    source_backpropagation_gates.and_then(|gates| gates.get(index)).cloned(),
                    None,
                    None,
                    None,
                    None,
                )
            })
            .collect::<Vec<_>>();
        self.import_checked_certificate_artifacts_with_paths_and_metadata(
            artifacts,
            artifact_paths,
            &artifact_metadata,
        )
    }

    fn import_checked_certificate_artifacts_with_paths_and_metadata(
        &mut self,
        artifacts: &[CheckedBinaryCertificateArtifact],
        artifact_paths: Option<&[String]>,
        artifact_metadata: &[CheckedCertificateLoadedMetadata],
    ) -> CheckedCertificateImportReport {
        self.bind_binary_artifact_digest_identities();

        let mut report = CheckedCertificateImportReport {
            loader_status: loaded_import_loader_status(artifacts.len()),
            requested_artifacts: artifact_paths.map(|paths| paths.len()).unwrap_or(artifacts.len()),
            loaded_artifacts: artifacts.len(),
            artifacts: artifacts
                .iter()
                .enumerate()
                .map(|(index, artifact)| {
                    let metadata = artifact_metadata.get(index).cloned().unwrap_or_else(|| {
                        CheckedCertificateLoadedMetadata::from_artifact_and_gate(
                            artifact, None, None, None, None, None,
                        )
                    });
                    CheckedCertificateArtifactImportRecord {
                        artifact_path: artifact_paths.and_then(|paths| paths.get(index)).cloned(),
                        certificate_sha256: artifact.certificate_sha256.clone(),
                        checker: artifact.checker.clone(),
                        checker_version: artifact.checker_version.clone(),
                        format: artifact.format.clone(),
                        checked_at_unix_ms: artifact.checked_at_unix_ms,
                        vc_sha256: artifact.vc_sha256.clone(),
                        origin_sha256: artifact.origin_sha256.clone(),
                        proof_export_sha256: artifact.proof_export_sha256.clone(),
                        binary_artifact_digest_identity: artifact
                            .binary_artifact_digest_identity
                            .clone(),
                        source_backpropagation_gate: metadata.source_backpropagation_gate,
                        manifest_identity_sha256: metadata.manifest_identity_sha256,
                        source_backpropagation_gate_sha256: metadata
                            .source_backpropagation_gate_sha256,
                        replay_transcript_digest: metadata.replay_transcript_digest,
                        replay_digest_identity: metadata.replay_digest_identity,
                        production_checker_evidence_status:
                            production_checker_evidence_status_label(
                                metadata.production_checker_evidence_sha256.as_deref(),
                            )
                            .to_string(),
                        production_checker_evidence_sha256: metadata
                            .production_checker_evidence_sha256,
                        status: "unmatched".to_string(),
                        dispatch_id: None,
                        diagnostic: None,
                    }
                })
                .collect(),
            ..Default::default()
        };
        let mut accounted_artifacts = vec![false; artifacts.len()];

        for dispatch in &mut self.solver_dispatch {
            let Some(binding) = dispatch_canonical_binding(dispatch) else {
                report.dispatches_missing_canonical_binding += 1;
                continue;
            };

            for (index, artifact) in artifacts.iter().enumerate() {
                if accounted_artifacts[index]
                    || artifact.vc_sha256 != binding.vc_sha256
                    || artifact.origin_sha256 != binding.origin_sha256
                {
                    continue;
                }

                accounted_artifacts[index] = true;
                let digest_identity_blockers =
                    dispatch_binary_artifact_digest_identity_acceptance_blockers(dispatch);
                if !digest_identity_blockers.is_empty() {
                    let diagnostic = format!(
                        "checked certificate {} rejected for dispatch {}: binary artifact digest identity is not accepted: {}",
                        artifact.certificate_sha256,
                        dispatch.id,
                        digest_identity_blockers.join("; ")
                    );
                    report.rejected_artifacts += 1;
                    report.artifacts[index].status = "rejected".to_string();
                    report.artifacts[index].dispatch_id = Some(dispatch.id.clone());
                    report.artifacts[index].diagnostic = Some(diagnostic.clone());
                    report.diagnostics.push(diagnostic);
                    break;
                }
                match import_checked_certificate_for_dispatch_by_canonical_digests(
                    dispatch,
                    &binding.canonical_vc_bytes,
                    artifact,
                ) {
                    Ok(()) => {
                        report.imported += 1;
                        report.artifacts[index].status = "imported".to_string();
                        report.artifacts[index].dispatch_id = Some(dispatch.id.clone());
                        break;
                    }
                    Err(error) => {
                        let diagnostic = format!(
                            "checked certificate {} rejected for dispatch {}: {error}",
                            artifact.certificate_sha256, dispatch.id
                        );
                        report.rejected_artifacts += 1;
                        report.artifacts[index].status = "rejected".to_string();
                        report.artifacts[index].dispatch_id = Some(dispatch.id.clone());
                        report.artifacts[index].diagnostic = Some(diagnostic.clone());
                        report.diagnostics.push(diagnostic);
                    }
                }
            }
        }

        report.unmatched_artifacts =
            accounted_artifacts.iter().filter(|accounted| !**accounted).count();
        report
    }

    fn bind_binary_artifact_digest_identities(&mut self) {
        let mut artifact_identity_cache = BTreeMap::new();
        for record in &mut self.solver_dispatch {
            bind_dispatch_binary_artifact_digest_identity(record, &mut artifact_identity_cache);
        }
    }
}
