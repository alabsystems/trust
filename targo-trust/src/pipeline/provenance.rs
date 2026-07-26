// Runtime source-backpropagation provenance imports for the rewrite loop.
//
// Parses --binary-source-provenance-artifact and --checked-cert-artifact files,
// validates checked-binary identity and source-backpropagation-gate alignment, and
// hands a fully-vetted RuntimeBinarySourceProvenance to the rewrite loop. The rewrite
// loop refuses to upgrade binary-derived spans into source rewrites unless the
// provenance handoff is exact and the proof evidence is publishable.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::Path;

use serde::Deserialize;
use trust_types::{
    BinaryArtifactDigestIdentity, BinaryOrigin, BinarySourceProvenanceSummary,
    BinaryVerificationSummary, ReconstructionSummary, SourceSpan,
};

use crate::cli::SubcommandArgs;
use crate::input_limits::{MAX_SAVED_PROOF_REPORT_BYTES, read_bounded_utf8_file};

const CHECKED_SOURCE_GATE_ARTIFACT_KIND: &str = "checked_source_backpropagation_gate";
const CHECKED_SOURCE_GATE_ARTIFACT_SCHEMA: &str =
    "targo-trust.checked-source-backpropagation-gate.v1";

#[derive(Debug, PartialEq, Eq)]
struct ImportedRuntimeSourceGate {
    source_backpropagation_gate_sha256: String,
    gate: trust_backprop::BinarySourceBackpropagationGateDetails,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RuntimeCheckedSourceGateArtifact {
    kind: String,
    schema_version: String,
    source_backpropagation_gate_sha256: String,
    source_backpropagation_gate: trust_backprop::BinarySourceBackpropagationGateDetails,
}

pub(super) fn runtime_binary_source_provenance_for_rewrite_loop(
    sub_args: &SubcommandArgs,
) -> Result<Option<crate::rewrite_loop::RuntimeBinarySourceProvenance>, String> {
    if sub_args.binary_source_provenance_artifacts.is_empty() {
        if !sub_args.checked_certificate_artifacts.is_empty() {
            return Err(format!(
                "rewrite loop cannot use --checked-cert-artifact source-backpropagation gate artifact(s) without --binary-source-provenance-artifact: {}",
                sub_args.checked_certificate_artifacts.join(", ")
            ));
        }
        return Ok(None);
    }
    if sub_args.binary_source_provenance_artifacts.len() > 1 {
        return Err(format!(
            "rewrite loop accepts exactly one --binary-source-provenance-artifact, got {}",
            sub_args.binary_source_provenance_artifacts.len()
        ));
    }

    let checked_source_gate =
        runtime_checked_certificate_source_backpropagation_gate_for_rewrite_loop(
            &sub_args.checked_certificate_artifacts,
        )?;
    let path = Path::new(&sub_args.binary_source_provenance_artifacts[0]);
    import_runtime_binary_source_provenance(path, checked_source_gate.as_ref()).map(Some)
}

#[derive(Debug, Deserialize)]
struct RuntimeBinarySourceProvenanceArtifact {
    #[serde(default)]
    source_provenance: BinarySourceProvenanceSummary,
    #[serde(default)]
    checked_binary_identity: crate::rewrite_loop::RuntimeBinarySourceIdentity,
    #[serde(default)]
    source_provenance_artifact_digest: Option<String>,
    #[serde(default, alias = "source_gate_sha256")]
    source_backpropagation_gate_sha256: Option<String>,
    #[serde(default)]
    verification: BinaryVerificationSummary,
    #[serde(default)]
    reconstruction: Option<ReconstructionSummary>,
    #[serde(default, alias = "checked_certificate_source_backpropagation_gate")]
    source_backpropagation_gate: Option<trust_backprop::BinarySourceBackpropagationGateDetails>,
    #[serde(
        default,
        alias = "exact_source_type_ownership_artifact",
        alias = "source_type_ownership",
        alias = "source_type_fact_ownership"
    )]
    exact_source_type_ownership:
        Option<crate::rewrite_loop::RuntimeExactSourceTypeOwnershipArtifact>,
    #[serde(default, alias = "exact_mappings")]
    source_mappings: Vec<crate::rewrite_loop::RuntimeBinarySourceMapping>,
    #[serde(default, alias = "checked_provenance_records", alias = "binary_provenance_records")]
    provenance_records: Vec<RuntimeBinarySourceProvenanceRecord>,
    #[serde(default)]
    canonical_binary_provenance: Option<RuntimeCanonicalBinaryProvenanceRecords>,
}

#[derive(Debug, Deserialize)]
struct RuntimeCanonicalBinaryProvenanceRecords {
    #[serde(default)]
    records: Vec<RuntimeBinarySourceProvenanceRecord>,
}

#[derive(Debug, Deserialize)]
struct RuntimeBinarySourceProvenanceRecord {
    origin: BinaryOrigin,
    #[serde(default, alias = "binary_artifact_digest_identity", alias = "digest_identity")]
    artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
    #[serde(default)]
    source_status: Option<String>,
    #[serde(default)]
    provenance_status: Option<String>,
    #[serde(default, alias = "record_digest", alias = "provenance_sha256")]
    provenance_record_digest: Option<String>,
    #[serde(default, alias = "proof_evidence", alias = "proof_evidence_identifiers")]
    proof_evidence: crate::rewrite_loop::RuntimeBinarySourceProofEvidence,
}

impl RuntimeBinarySourceProvenanceRecord {
    fn into_mapping(self) -> crate::rewrite_loop::RuntimeBinarySourceMapping {
        let source = self
            .origin
            .source
            .clone()
            .unwrap_or_else(|| SourceSpan::binary_address(self.origin.instruction_address));
        crate::rewrite_loop::RuntimeBinarySourceMapping {
            binary_address: self.origin.instruction_address,
            binary_path: self.origin.binary_path,
            function_entry: self.origin.function_entry,
            instruction_size: self.origin.instruction_size,
            instruction_bytes: self.origin.instruction_bytes,
            binary_artifact_digest_identity: self.artifact_digest_identity,
            source_status: self.source_status,
            provenance_status: self.provenance_status,
            provenance_record_digest: self.provenance_record_digest,
            proof_evidence: self.proof_evidence,
            source,
        }
    }
}

fn import_runtime_binary_source_provenance(
    path: &Path,
    imported_source_gate: Option<&ImportedRuntimeSourceGate>,
) -> Result<crate::rewrite_loop::RuntimeBinarySourceProvenance, String> {
    let json = read_bounded_utf8_file(path, MAX_SAVED_PROOF_REPORT_BYTES).map_err(|error| {
        format!("failed to read --binary-source-provenance-artifact {}: {error}", path.display())
    })?;
    let value: serde_json::Value = serde_json::from_str(&json).map_err(|error| {
        format!("failed to parse --binary-source-provenance-artifact {}: {error}", path.display())
    })?;
    let profile_blockers = runtime_checked_binary_source_provenance_artifact_profile_blockers(
        &value,
    )
    .map_err(|error| {
        format!(
            "failed to parse checked binary-source provenance artifact profile {}: {error}",
            path.display()
        )
    })?;
    if !profile_blockers.is_empty() {
        return Err(format!(
            "--binary-source-provenance-artifact {} is not an accepted checked binary-source provenance artifact: {}",
            path.display(),
            profile_blockers.join("; ")
        ));
    }
    let artifact: RuntimeBinarySourceProvenanceArtifact =
        serde_json::from_value(value).map_err(|error| {
            format!(
                "failed to parse --binary-source-provenance-artifact {}: {error}",
                path.display()
            )
        })?;

    let source_mappings = if let Some(records) = artifact.canonical_binary_provenance {
        // Canonical rows are the only authoritative mapping representation.
        // Legacy aliases may coexist in compatibility exports, but combining
        // them would let an ignored duplicate create conflicting authority.
        records.records.into_iter().map(RuntimeBinarySourceProvenanceRecord::into_mapping).collect()
    } else {
        let mut mappings = artifact.source_mappings;
        mappings.extend(
            artifact
                .provenance_records
                .into_iter()
                .map(RuntimeBinarySourceProvenanceRecord::into_mapping),
        );
        mappings
    };

    let mut summary = artifact.source_provenance;
    if source_mappings.is_empty() {
        summary.source_backpropagation_allowed = false;
        summary.diagnostics.push(
            "binary source provenance artifact has no exact address mappings; source backpropagation rejected"
                .to_string(),
        );
    }
    let identity_blockers = runtime_binary_source_identity_blockers(
        &artifact.checked_binary_identity,
        &artifact.verification,
    );
    if !identity_blockers.is_empty() {
        summary.source_backpropagation_allowed = false;
        summary.diagnostics.push(format!(
            "checked source-provenance binary identity is missing or mismatched: {}",
            identity_blockers.join("; ")
        ));
    }

    let provenance =
        crate::rewrite_loop::RuntimeBinarySourceProvenance::new_with_checked_binary_identity(
            summary,
            artifact.checked_binary_identity,
            source_mappings,
        );
    if !provenance.summary().effective_source_backpropagation_allowed() {
        return Err(format!(
            "--binary-source-provenance-artifact {} does not carry accepted exact source provenance for source rewriting: {}",
            path.display(),
            runtime_binary_source_provenance_diagnostic(provenance.summary())
        ));
    }

    let source_gate = runtime_source_gate_for_provenance_artifact(
        path,
        artifact.source_backpropagation_gate.as_ref(),
        imported_source_gate.map(|imported| &imported.gate),
    )?;
    match artifact.source_backpropagation_gate_sha256.as_deref() {
        Some(digest) if is_canonical_sha256_hex(digest) => {}
        Some(_) => {
            return Err(format!(
                "--binary-source-provenance-artifact {} source_backpropagation_gate_sha256 is not canonical SHA-256",
                path.display()
            ));
        }
        None => {
            return Err(format!(
                "--binary-source-provenance-artifact {} is missing source_backpropagation_gate_sha256 required to bind checked source provenance to the source-backpropagation gate",
                path.display()
            ));
        }
    }
    if let Some(imported) = imported_source_gate {
        if artifact.source_backpropagation_gate_sha256.as_deref()
            != Some(imported.source_backpropagation_gate_sha256.as_str())
        {
            return Err(format!(
                "--checked-cert-artifact source_backpropagation_gate_sha256 {} does not match --binary-source-provenance-artifact {} gate identity {}",
                imported.source_backpropagation_gate_sha256,
                path.display(),
                artifact.source_backpropagation_gate_sha256.as_deref().unwrap_or("<missing>")
            ));
        }
    }
    let provenance = provenance
        .with_imported_binary_backpropagation_evidence_and_source_gate_identity(
            &artifact.verification,
            artifact.reconstruction.as_ref(),
            source_gate,
            artifact.source_backpropagation_gate_sha256.as_deref(),
        );
    if !provenance.binary_backpropagation_authority_allows_source_rewrites() {
        let rejection_detail = provenance.source_rewrite_authority_diagnostics().join("; ");
        return Err(format!(
            "--binary-source-provenance-artifact {} has accepted exact source provenance, but runtime source rewrites require complete proof-grade binary backpropagation evidence: {}; verification={}",
            path.display(),
            rejection_detail,
            runtime_binary_verification_diagnostic(&artifact.verification)
        ));
    }

    let provenance = provenance.with_exact_source_type_ownership_artifact(
        artifact.exact_source_type_ownership,
        artifact.source_provenance_artifact_digest.as_deref(),
        &artifact.verification,
    );
    if !provenance.effective_source_backpropagation_allowed() {
        let rejection_detail = provenance.source_rewrite_authority_diagnostics().join("; ");
        return Err(format!(
            "--binary-source-provenance-artifact {} has proof-grade source backpropagation evidence, but runtime source rewrites require accepted exact source/type-fact ownership: {}",
            path.display(),
            rejection_detail,
        ));
    }

    Ok(provenance)
}

fn runtime_binary_source_identity_blockers(
    identity: &crate::rewrite_loop::RuntimeBinarySourceIdentity,
    verification: &BinaryVerificationSummary,
) -> Vec<String> {
    let mut blockers = identity.blockers();
    if blockers.is_empty() {
        let binary_sha256 =
            identity.binary_sha256.as_deref().expect("checked identity has binary_sha256");
        let selected_image_sha256 = identity
            .selected_image_sha256
            .as_deref()
            .expect("checked identity has selected_image_sha256");
        let dispatch_matches = verification.solver_dispatch.iter().any(|dispatch| {
            dispatch.binary_artifact_digest_identity.as_ref().is_some_and(|digest_identity| {
                digest_identity
                    .root_artifact_digest
                    .as_ref()
                    .is_some_and(|root| root.value == binary_sha256)
                    && digest_identity
                        .selected_image
                        .as_ref()
                        .is_some_and(|selected| selected.sha256 == selected_image_sha256)
            })
        });
        if !dispatch_matches {
            blockers.push(
                "checked binary identity does not match any solver dispatch digest identity"
                    .to_string(),
            );
        }
    }
    blockers
}

fn runtime_checked_binary_source_provenance_artifact_profile_blockers(
    value: &serde_json::Value,
) -> Result<Vec<String>, serde_json::Error> {
    serde_json::from_value::<trust_report::BinarySourceProvenanceArtifactReport>(value.clone())
        .map(|artifact| artifact.canonical_artifact_profile_blockers())
}

fn runtime_checked_certificate_source_backpropagation_gate_for_rewrite_loop(
    paths: &[String],
) -> Result<Option<ImportedRuntimeSourceGate>, String> {
    let mut imported_gate = None;
    for path in paths {
        let path = Path::new(path);
        let gate = import_runtime_checked_certificate_source_backpropagation_gate(path)?;
        if let Some(existing) = &imported_gate {
            if existing != &gate {
                return Err(format!(
                    "rewrite loop rejected conflicting checked certificate source_backpropagation_gate artifact {}",
                    path.display()
                ));
            }
        } else {
            imported_gate = Some(gate);
        }
    }
    Ok(imported_gate)
}

fn import_runtime_checked_certificate_source_backpropagation_gate(
    path: &Path,
) -> Result<ImportedRuntimeSourceGate, String> {
    let json = read_bounded_utf8_file(path, MAX_SAVED_PROOF_REPORT_BYTES).map_err(|error| {
        format!("failed to read --checked-cert-artifact {}: {error}", path.display())
    })?;
    let artifact: RuntimeCheckedSourceGateArtifact =
        serde_json::from_str(&json).map_err(|error| {
            format!("failed to parse --checked-cert-artifact {}: {error}", path.display())
        })?;
    if artifact.kind != CHECKED_SOURCE_GATE_ARTIFACT_KIND {
        return Err(format!(
            "--checked-cert-artifact {} kind {:?} is not {:?}",
            path.display(),
            artifact.kind,
            CHECKED_SOURCE_GATE_ARTIFACT_KIND
        ));
    }
    if artifact.schema_version != CHECKED_SOURCE_GATE_ARTIFACT_SCHEMA {
        return Err(format!(
            "--checked-cert-artifact {} schema_version {:?} is not {:?}",
            path.display(),
            artifact.schema_version,
            CHECKED_SOURCE_GATE_ARTIFACT_SCHEMA
        ));
    }
    if !is_canonical_sha256_hex(&artifact.source_backpropagation_gate_sha256) {
        return Err(format!(
            "--checked-cert-artifact {} source_backpropagation_gate_sha256 is not canonical SHA-256",
            path.display()
        ));
    }
    Ok(ImportedRuntimeSourceGate {
        source_backpropagation_gate_sha256: artifact.source_backpropagation_gate_sha256,
        gate: artifact.source_backpropagation_gate,
    })
}

fn runtime_source_gate_for_provenance_artifact<'a>(
    path: &Path,
    embedded_source_gate: Option<&'a trust_backprop::BinarySourceBackpropagationGateDetails>,
    imported_source_gate: Option<&'a trust_backprop::BinarySourceBackpropagationGateDetails>,
) -> Result<Option<&'a trust_backprop::BinarySourceBackpropagationGateDetails>, String> {
    match (embedded_source_gate, imported_source_gate) {
        (Some(embedded), Some(imported)) if embedded != imported => Err(format!(
            "--binary-source-provenance-artifact {} carries a source_backpropagation_gate that conflicts with imported --checked-cert-artifact gate evidence",
            path.display()
        )),
        (Some(embedded), _) => Ok(Some(embedded)),
        (None, Some(_)) => Err(format!(
            "--checked-cert-artifact cannot supply a source_backpropagation_gate missing from --binary-source-provenance-artifact {}; imported evidence may corroborate but never create source-rewrite authority",
            path.display()
        )),
        (None, None) => Ok(None),
    }
}

fn runtime_binary_source_provenance_diagnostic(summary: &BinarySourceProvenanceSummary) -> String {
    summary
        .typed_diagnostics()
        .into_iter()
        .next()
        .map(|diagnostic| diagnostic.message)
        .unwrap_or_else(|| {
            "binary source provenance is present but not effective for source backpropagation"
                .to_string()
        })
}

fn runtime_binary_verification_diagnostic(verification: &BinaryVerificationSummary) -> String {
    format!(
        "status={:?} trust_level={:?} total_vcs={} proved={} failed={} unknown={} timeout={} unsupported={} rejected={} replay={:?} proof_certificate={:?}",
        verification.status,
        verification.trust_level,
        verification.total_vcs,
        verification.proved,
        verification.failed,
        verification.unknown,
        verification.timeout,
        verification.unsupported,
        verification.rejected,
        verification.replay,
        verification.proof_certificate
    )
}

fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

pub(super) fn print_runtime_binary_source_backpropagation_blocker(
    blockers: &[crate::rewrite_loop::BinarySourceBackpropagationBlocker],
) {
    eprintln!(
        "targo trust: error: runtime rewrite loop rejected binary-derived source backpropagation without exact provenance"
    );
    eprintln!(
        "  every binary-derived source span must match an exact imported binary-source provenance mapping"
    );
    for blocker in blockers.iter().take(5) {
        eprintln!(
            "  - {} `{}` at {}: {}",
            blocker.function, blocker.kind, blocker.source_file, blocker.reason
        );
    }
    if blockers.len() > 5 {
        eprintln!("  ... {} more blocked source-path upgrade(s)", blockers.len() - 5);
    }
    eprintln!(
        "  refusing to upgrade binary-derived addresses into source rewrites until a proof-grade exact-provenance handoff is imported"
    );
}
