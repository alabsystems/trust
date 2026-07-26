// Checked-certificate artifact and manifest loaders, including audit-export
// bundle validation.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use trust_proof_cert::{
    CertError, CheckedBinaryCertificateArtifact, CheckedBinaryCertificateAuditExportBundle,
    CheckedBinaryCertificateAuditExportBundleValidation,
    CheckedBinaryCertificateAuditExportBundleValidationRow, CheckedBinaryCertificateManifest,
    CheckedBinaryCertificateProductionManifest,
    CheckedBinaryCertificateProductionManifestAcceptedRowInput,
    CheckedBinaryCertificateSourceBackpropagationGate,
    checked_certificate_audit_export_bundle_path,
    evaluate_checked_binary_certificate_production_manifest,
    load_checked_certificate_audit_export_bundle_rows,
};

use super::{LoadedCheckedCertificateArtifact, is_canonical_sha256_hex, stable_json_sha256};
use crate::input_limits::{MAX_SAVED_PROOF_REPORT_BYTES, read_bounded_utf8_file};

fn read_checked_json(path: &Path) -> Result<String, CertError> {
    read_bounded_utf8_file(path, MAX_SAVED_PROOF_REPORT_BYTES).map_err(Into::into)
}

pub(crate) fn load_checked_certificate_artifact_rows<AI, AP, MI, MP>(
    artifact_paths: AI,
    manifest_paths: MI,
) -> Result<Vec<LoadedCheckedCertificateArtifact>, CertError>
where
    AI: IntoIterator<Item = AP>,
    AP: AsRef<Path>,
    MI: IntoIterator<Item = MP>,
    MP: AsRef<Path>,
{
    let mut paths: Vec<PathBuf> =
        artifact_paths.into_iter().map(|path| path.as_ref().to_path_buf()).collect();
    let mut metadata_by_certificate = BTreeMap::<String, LoadedManifestAuditMetadata>::new();
    let mut seen_manifest_identities = BTreeMap::<String, String>::new();

    for manifest_path in manifest_paths {
        let manifest_path = manifest_path.as_ref();
        let manifest_json = read_checked_json(manifest_path)?;
        let manifest = CheckedBinaryCertificateManifest::from_json(&manifest_json)?;
        let manifest_parent = manifest_path
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."));
        let manifest_root = manifest_parent
            .parent()
            .filter(|candidate| {
                trust_proof_cert::checked_certificate_manifest_path(*candidate) == manifest_path
            })
            .unwrap_or(manifest_parent);
        // Preflight every authority-bearing artifact through the bounded,
        // regular-file, snapshot-stable reader before the proof-cert library
        // performs its binding validation.
        for entry in &manifest.certificates {
            let _ = read_checked_json(&manifest_root.join(&entry.certificate_path))?;
        }
        manifest.validate_files(manifest_root)?;
        let audit_bundle_path = checked_certificate_audit_export_bundle_path(manifest_root);
        let audit_bundle_present = match std::fs::symlink_metadata(&audit_bundle_path) {
            Ok(_) => true,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
            Err(error) => return Err(error.into()),
        };
        if audit_bundle_present {
            let bundle_json = read_checked_json(&audit_bundle_path)?;
            let bundle = CheckedBinaryCertificateAuditExportBundle::from_json(&bundle_json)?;
            let _ = read_checked_json(&manifest_root.join(&bundle.manifest_path))?;
            for entry in &bundle.audit_exports {
                let _ = read_checked_json(&manifest_root.join(&entry.audit_export_path))?;
            }
            let validation = load_checked_certificate_audit_export_bundle_rows(manifest_root)?;
            if let Some(rejected) = validation.rejected_rows().next() {
                return Err(CertError::InvalidCertificate {
                    reason: format!(
                        "checked certificate audit export bundle row rejected for certificate {}: {:?}: {}",
                        rejected.certificate_sha256, rejected.code, rejected.reason
                    ),
                });
            }
            validate_checked_certificate_audit_export_bundle_source_backpropagation_gate_rows(
                manifest_path,
                &validation,
                &mut seen_manifest_identities,
            )?;
            for row in validation.rows {
                if let CheckedBinaryCertificateAuditExportBundleValidationRow::Accepted(accepted) =
                    row
                {
                    let production_checker_evidence_sha256 = accepted
                        .acceptance_record
                        .production_checker_evidence
                        .as_ref()
                        .and_then(|evidence| evidence.sha256().ok());
                    let certificate_sha256 = accepted.bundle_entry.certificate_sha256.clone();
                    let metadata = LoadedManifestAuditMetadata {
                        source_backpropagation_gate: accepted
                            .bundle_entry
                            .source_backpropagation_gate
                            .clone(),
                        manifest_identity_sha256: (!accepted
                            .bundle_entry
                            .manifest_identity_sha256
                            .trim()
                            .is_empty())
                        .then_some(accepted.bundle_entry.manifest_identity_sha256.clone()),
                        source_backpropagation_gate_sha256: stable_json_sha256(
                            &accepted.bundle_entry.source_backpropagation_gate,
                        ),
                        replay_transcript_digest: accepted
                            .acceptance_record
                            .replay_transcript
                            .replay_transcript_digest
                            .clone(),
                        production_checker_evidence_sha256,
                    };
                    if metadata_by_certificate
                        .insert(certificate_sha256.clone(), metadata)
                        .is_some()
                    {
                        return Err(CertError::InvalidCertificate {
                            reason: format!(
                                "checked certificate audit export bundle readback has duplicate production row metadata for certificate {certificate_sha256}"
                            ),
                        });
                    }
                }
            }
        }
        paths.extend(
            manifest.certificates.iter().map(|entry| manifest_root.join(&entry.certificate_path)),
        );
    }

    paths
        .into_iter()
        .map(|path| {
            let artifact_json = read_checked_json(&path)?;
            let artifact = CheckedBinaryCertificateArtifact::from_json(&artifact_json)?;
            let metadata = metadata_by_certificate.get(&artifact.certificate_sha256);
            let source_backpropagation_gate = metadata
                .map(|metadata| metadata.source_backpropagation_gate.clone())
                .unwrap_or_default();
            Ok(LoadedCheckedCertificateArtifact {
                path: path.display().to_string(),
                artifact,
                source_backpropagation_gate,
                manifest_identity_sha256: metadata
                    .and_then(|metadata| metadata.manifest_identity_sha256.clone()),
                source_backpropagation_gate_sha256: metadata
                    .and_then(|metadata| metadata.source_backpropagation_gate_sha256.clone()),
                replay_transcript_digest: metadata
                    .and_then(|metadata| metadata.replay_transcript_digest.clone()),
                production_checker_evidence_sha256: metadata
                    .and_then(|metadata| metadata.production_checker_evidence_sha256.clone()),
            })
        })
        .collect()
}

fn validate_checked_certificate_audit_export_bundle_source_backpropagation_gate_rows(
    manifest_path: &Path,
    validation: &CheckedBinaryCertificateAuditExportBundleValidation,
    seen_manifest_identities: &mut BTreeMap<String, String>,
) -> Result<(), CertError> {
    let accepted_certificates = validation
        .accepted_rows()
        .map(|row| row.bundle_entry.certificate_sha256.as_str())
        .collect::<BTreeSet<_>>();

    for entry in &validation.manifest.certificates {
        if !accepted_certificates.contains(entry.certificate_sha256.as_str()) {
            return Err(CertError::InvalidCertificate {
                reason: format!(
                    "checked certificate audit export bundle for manifest `{}` is missing source_backpropagation_gate row for certificate {} dispatch {}",
                    manifest_path.display(),
                    entry.certificate_sha256,
                    entry.dispatch_id
                ),
            });
        }
    }

    for accepted in validation.accepted_rows() {
        let manifest_identity = accepted.bundle_entry.manifest_identity_sha256.trim();
        if !is_canonical_sha256_hex(manifest_identity) {
            return Err(CertError::InvalidCertificate {
                reason: format!(
                    "checked certificate audit export bundle for manifest `{}` has noncanonical manifest identity for certificate {} dispatch {}: {}",
                    manifest_path.display(),
                    accepted.bundle_entry.certificate_sha256,
                    accepted.bundle_entry.dispatch_id,
                    if manifest_identity.is_empty() { "empty" } else { manifest_identity }
                ),
            });
        }
        if let Some(first_certificate) = seen_manifest_identities
            .insert(manifest_identity.to_string(), accepted.bundle_entry.certificate_sha256.clone())
        {
            return Err(CertError::InvalidCertificate {
                reason: format!(
                    "checked certificate audit export bundle for manifest `{}` has duplicate manifest identity {} for certificates {} and {}",
                    manifest_path.display(),
                    manifest_identity,
                    first_certificate,
                    accepted.bundle_entry.certificate_sha256
                ),
            });
        }
    }

    let accepted_rows = validation.accepted_rows().collect::<Vec<_>>();
    let production_manifest_inputs = accepted_rows
        .iter()
        .map(|accepted| CheckedBinaryCertificateProductionManifestAcceptedRowInput {
            manifest_entry: &accepted.manifest_entry,
            acceptance_record: &accepted.acceptance_record,
        })
        .collect::<Vec<_>>();
    let production_manifest =
        CheckedBinaryCertificateProductionManifest::from_manifest_acceptance_records(
            validation.manifest.certificates.len(),
            &production_manifest_inputs,
        )
        .map_err(|error| CertError::InvalidCertificate {
            reason: format!(
                "checked certificate audit export bundle for manifest `{}` could not reconstruct production readback row identity: {error}",
                manifest_path.display()
            ),
        })?;
    let decision = evaluate_checked_binary_certificate_production_manifest(&production_manifest);
    if !decision.accepted {
        return Err(CertError::InvalidCertificate {
            reason: format!(
                "checked certificate audit export bundle for manifest `{}` failed production readback row identity validation: {:?}",
                manifest_path.display(),
                decision.rejections
            ),
        });
    }

    Ok(())
}

#[derive(Debug, Clone)]
struct LoadedManifestAuditMetadata {
    source_backpropagation_gate: CheckedBinaryCertificateSourceBackpropagationGate,
    manifest_identity_sha256: Option<String>,
    source_backpropagation_gate_sha256: Option<String>,
    replay_transcript_digest: Option<String>,
    production_checker_evidence_sha256: Option<String>,
}
