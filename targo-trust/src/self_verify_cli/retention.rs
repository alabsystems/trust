//! Durable, observational evidence for the native self-verification owner.
//! Artifact storage and its policy are shared with the canonical report writer.

use serde::{Deserialize, Serialize};
use trust_types::{
    TransportEvidenceArtifact, TransportNativeTrustIrEvidence, TransportProofEvidence,
};

use super::*;

const SCHEMA: &str = "trust.self-verify.evidence-bundle.v1";
const SIDECAR: &str = "self-verify.evidence-bundle.json";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RowLocation {
    stage: String,
    row_ordinal: usize,
    cargo_target: Value,
    source: String,
    line: usize,
    function: Option<String>,
    raw_function: Option<String>,
    row_index: usize,
    obligation_id: Option<String>,
    outcome: trust_types::Outcome,
}

#[derive(Debug)]
pub(super) struct ArtifactRow {
    location: RowLocation,
    artifacts: Vec<TransportEvidenceArtifact>,
}

impl ArtifactRow {
    fn core_row(&self) -> crate::report::OmittedArtifactRow {
        crate::report::OmittedArtifactRow {
            function: self.location.function.clone().unwrap_or_default(),
            // The self-report sidecar maps this global ordinal back to the
            // exact stage/Cargo/source/function/list index; names alone do not.
            obligation_index: self.location.row_ordinal,
            obligation_id: self.location.obligation_id.clone(),
            outcome: self.location.outcome.as_str(),
        }
    }
}

fn path_artifacts(
    native: Option<&TransportNativeTrustIrEvidence>,
    proof: Option<&TransportProofEvidence>,
) -> Vec<TransportEvidenceArtifact> {
    native
        .into_iter()
        .flat_map(|native| &native.artifacts)
        .chain(proof.into_iter().flat_map(|proof| &proof.artifacts))
        .filter(|artifact| {
            artifact
                .materialization
                .as_ref()
                .and_then(|materialization| materialization.materialized_path.as_ref())
                .is_some()
        })
        .cloned()
        .collect()
}

pub(super) fn collect_typed_row(
    rows: &mut Vec<ArtifactRow>,
    stage: &str,
    row_ordinal: usize,
    target: &CargoTargetIdentity,
    source: &str,
    line: usize,
    function: Option<&str>,
    row_index: usize,
    transport: &trust_types::TransportObligationResult,
) {
    let artifacts =
        path_artifacts(transport.native_trust_ir.as_ref(), transport.proof_evidence.as_ref());
    if !artifacts.is_empty() {
        rows.push(ArtifactRow {
            location: RowLocation {
                stage: stage.to_owned(),
                row_ordinal,
                cargo_target: cargo_target_identity_json(target),
                source: source.to_owned(),
                line,
                function: function.map(|name| cargo_scoped_function(target, name)),
                raw_function: function.map(str::to_owned),
                row_index,
                obligation_id: transport.obligation_id.clone(),
                outcome: transport.outcome,
            },
            artifacts,
        });
    }
}

pub(super) struct PreparedBundle {
    status: Value,
    locations: Vec<RowLocation>,
}

pub(super) fn prepare_bundle(
    report_dir: &Path,
    source_root: &Path,
    rows: Vec<ArtifactRow>,
) -> Result<PreparedBundle, String> {
    validate_private_directory(report_dir, "report directory")?;
    let staging = tempfile::Builder::new()
        .prefix(".evidence-")
        .tempdir_in(report_dir)
        .map_err(|error| format!("could not create private evidence staging: {error}"))?;
    make_directory_private(staging.path())?;
    validate_private_directory(staging.path(), "evidence staging directory")?;
    let occurrences = rows.iter().flat_map(|row| {
        row.artifacts.iter().map(move |artifact| crate::report::ReportArtifactOccurrence {
            row_ordinal: row.location.row_ordinal,
            row: row.core_row(),
            artifact,
        })
    });
    let status =
        crate::report::persist_artifact_occurrences(occurrences, source_root, staging.path())
            .map_err(|error| format!("could not retain self-verification artifacts: {error}"))?;
    let staged_store = staging.path().join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY);
    if staged_store.exists() {
        let destination = report_dir.join(trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY);
        match fs::symlink_metadata(&destination) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            _ => return Err("refusing an existing self-verification artifact store".into()),
        }
        sync_directory(&staged_store.join("sha256"))
            .and_then(|()| sync_directory(&staged_store))
            .map_err(|error| format!("could not fsync retained artifact store: {error}"))?;
        fs::rename(&staged_store, &destination)
            .map_err(|error| format!("could not publish retained artifact store: {error}"))?;
        sync_directory(report_dir)
            .map_err(|error| format!("could not fsync retained artifact directory: {error}"))?;
    }
    Ok(PreparedBundle {
        status: serde_json::to_value(status).map_err(|error| error.to_string())?,
        locations: rows.into_iter().map(|row| row.location).collect(),
    })
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema: String,
    report_file: String,
    report_sha256: String,
    report_bytes: u64,
    bundle: Value,
    rows: Vec<RowLocation>,
}

fn encode(value: &impl Serialize) -> Result<Vec<u8>, String> {
    let bound = crate::input_limits::max_emitted_proof_report_bytes();
    let mut bytes = crate::report::serialize_json_bounded(value, bound.saturating_sub(1))
        .map_err(|error| format!("could not encode bounded self-verification evidence: {error}"))?;
    bytes.push(b'\n');
    Ok(bytes)
}

impl PreparedBundle {
    pub(super) fn summary(&self, report: &Value) -> Result<Value, String> {
        let (_, untyped_rows) = rows_from_report(report)?;
        Ok(json!({"schema": SCHEMA, "sidecar": SIDECAR, "observational_only": true,
            "complete": self.status["complete"] == true && untyped_rows == 0,
            "collection_complete": untyped_rows == 0, "untyped_transport_rows": untyped_rows,
            "bundle": self.status}))
    }

    pub(super) fn publish(self, report_path: &Path, report: &Value) -> Result<(), String> {
        let (expected, _) = rows_from_report(report)?;
        if expected.iter().map(|row| &row.location).collect::<Vec<_>>()
            != self.locations.iter().collect::<Vec<_>>()
        {
            return Err("retained artifact rows disagree with the emitted self report".into());
        }
        if report.get("evidence_retention") != Some(&self.summary(report)?) {
            return Err(
                "self report retention declaration disagrees with the retained bundle".into()
            );
        }
        let bytes = encode(report)?;
        let manifest = Manifest {
            schema: SCHEMA.into(),
            report_file: REPORT_NAME.into(),
            report_sha256: format!("{:x}", Sha256::digest(&bytes)),
            report_bytes: bytes.len() as u64,
            bundle: self.status,
            rows: self.locations,
        };
        let parent = report_path.parent().ok_or("self report has no parent")?;
        // The JSON report is the commit marker. Interrupted store/sidecar
        // publication cannot masquerade as a complete saved report.
        write_report_bytes(&parent.join(SIDECAR), &encode(&manifest)?)?;
        write_report_bytes(report_path, &bytes)
    }
}

fn required<T>(value: Option<T>, what: &str) -> Result<T, String> {
    value.ok_or_else(|| format!("saved self-verification report omitted {what}"))
}

fn rows_from_report(report: &Value) -> Result<(Vec<ArtifactRow>, usize), String> {
    let stages = required(report.get("stages").and_then(Value::as_array), "stages")?;
    let mut rows = Vec::new();
    let mut ordinal = 0;
    let mut untyped_rows = 0;
    for stage in stages {
        let label = required(stage.get("label").and_then(Value::as_str), "stage label")?;
        let retained = required(
            stage
                .get("solver_suite")
                .and_then(|suite| suite.get("verification_rows"))
                .and_then(Value::as_array),
            "verification rows",
        )?;
        for row in retained {
            match row.get("artifact_collection_status").and_then(Value::as_str) {
                Some("rejected") => {
                    if row.get("complete").and_then(Value::as_bool) != Some(false)
                        || row
                            .get("proof_binding")
                            .and_then(|binding| binding.get("accepted"))
                            .and_then(Value::as_bool)
                            != Some(false)
                    {
                        return Err("untyped transport row claimed a complete proof binding".into());
                    }
                    // Retain the original malformed row for diagnosis. Its raw
                    // paths are never interpreted as typed artifact authority.
                    untyped_rows += 1;
                    ordinal += 1;
                    continue;
                }
                Some("typed") => {}
                _ => return Err("saved row omitted typed artifact collection status".into()),
            }
            let native: Option<TransportNativeTrustIrEvidence> =
                serde_json::from_value(row.get("native_trust_ir").cloned().unwrap_or(Value::Null))
                    .map_err(|error| {
                        format!("invalid saved native artifact descriptors: {error}")
                    })?;
            let proof: Option<TransportProofEvidence> =
                serde_json::from_value(row.get("proof_evidence").cloned().unwrap_or(Value::Null))
                    .map_err(|error| format!("invalid saved proof artifact descriptors: {error}"))?;
            let artifacts = path_artifacts(native.as_ref(), proof.as_ref());
            if !artifacts.is_empty() {
                let target = cargo_target_identity_from_json(required(
                    row.get("cargo_target"),
                    "Cargo target",
                )?)?;
                let function = row.get("raw_function").and_then(Value::as_str);
                let scoped = function.map(|name| cargo_scoped_function(&target, name));
                if row.get("function") != Some(&json!(scoped)) {
                    return Err("saved row function disagrees with its exact Cargo scope".into());
                }
                rows.push(ArtifactRow {
                    location: RowLocation {
                        stage: label.into(),
                        row_ordinal: ordinal,
                        cargo_target: cargo_target_identity_json(&target),
                        source: required(row.get("source").and_then(Value::as_str), "row source")?
                            .into(),
                        line: usize::try_from(required(
                            row.get("line").and_then(Value::as_u64),
                            "row line",
                        )?)
                        .map_err(|error| error.to_string())?,
                        function: scoped,
                        raw_function: function.map(str::to_owned),
                        row_index: usize::try_from(required(
                            row.get("row_index").and_then(Value::as_u64),
                            "row index",
                        )?)
                        .map_err(|error| error.to_string())?,
                        obligation_id: row
                            .get("obligation_id")
                            .and_then(Value::as_str)
                            .map(str::to_owned),
                        outcome: serde_json::from_value(
                            required(row.get("outcome"), "row outcome")?.clone(),
                        )
                        .map_err(|error| format!("invalid saved outcome: {error}"))?,
                    },
                    artifacts,
                });
            }
            ordinal += 1;
        }
    }
    Ok((rows, untyped_rows))
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Deserialize)]
struct OmittedRow {
    function: String,
    obligation_index: usize,
    obligation_id: Option<String>,
    outcome: String,
}

impl From<crate::report::OmittedArtifactRow> for OmittedRow {
    fn from(row: crate::report::OmittedArtifactRow) -> Self {
        Self {
            function: row.function,
            obligation_index: row.obligation_index,
            obligation_id: row.obligation_id,
            outcome: row.outcome.into(),
        }
    }
}

#[derive(Deserialize)]
struct OmittedArtifact {
    digest_sha256: String,
    byte_len: u64,
    rows: Vec<OmittedRow>,
}

#[derive(Deserialize)]
struct StorageStatus {
    complete: bool,
    persisted_artifacts: usize,
    persisted_bytes: u64,
    omitted_artifacts: usize,
    omitted_bytes: u64,
    omitted_proved_or_runtime_checked_rows: usize,
    omitted: Vec<OmittedArtifact>,
}

fn validate_existing_directory_tree(path: &Path) -> Result<PathBuf, String> {
    let mut current = PathBuf::new();
    for component in path.components() {
        match component {
            Component::RootDir | Component::Prefix(_) => current.push(component.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => return Err("saved report directory contains traversal".into()),
            Component::Normal(name) => {
                current.push(name);
                let metadata = fs::symlink_metadata(&current).map_err(|error| error.to_string())?;
                if metadata.file_type().is_symlink()
                    && trusted_platform_ancestor_symlink(&current, &metadata)
                {
                    continue;
                }
                if metadata.file_type().is_symlink() || !metadata.is_dir() {
                    return Err(
                        "saved report directory has a symlink or non-directory ancestor".into()
                    );
                }
            }
        }
    }
    path.canonicalize().map_err(|error| error.to_string())
}

pub(super) fn inspect_saved_report(report_path: &Path) -> Result<Value, String> {
    let parent = required(report_path.parent(), "report parent")?;
    let root = validate_existing_directory_tree(parent)?;
    let bytes = crate::input_limits::read_bounded_file(
        report_path,
        crate::input_limits::max_emitted_proof_report_bytes(),
    )
    .map_err(|error| format!("could not read saved self report: {error}"))?;
    // Accepted transport metadata gains nesting inside the saved report.
    // Keep the existing byte bound and use the shared bounded-stack decoder.
    let report: Value =
        trust_types::json_depth::from_slice_deep(&bytes).map_err(|error| error.to_string())?;
    validate_report_payload(&report)?;
    let Some(retention) = report.get("evidence_retention") else {
        return Ok(json!({"status": "unavailable", "complete": false, "observational_only": true,
            "reason": "legacy self report has no retained evidence bundle"}));
    };
    if report_path.file_name().and_then(|name| name.to_str()) != Some(REPORT_NAME)
        || retention.get("schema").and_then(Value::as_str) != Some(SCHEMA)
        || retention.get("sidecar").and_then(Value::as_str) != Some(SIDECAR)
        || retention.get("observational_only").and_then(Value::as_bool) != Some(true)
    {
        return Err("invalid self-report evidence retention contract".into());
    }
    let manifest_bytes = crate::input_limits::read_bounded_file(
        &root.join(SIDECAR),
        crate::input_limits::max_emitted_proof_report_bytes(),
    )
    .map_err(|error| error.to_string())?;
    let manifest: Manifest =
        serde_json::from_slice(&manifest_bytes).map_err(|error| error.to_string())?;
    if manifest.schema != SCHEMA
        || manifest.report_file != REPORT_NAME
        || manifest.report_bytes != bytes.len() as u64
        || manifest.report_sha256 != format!("{:x}", Sha256::digest(&bytes))
        || retention.get("bundle") != Some(&manifest.bundle)
    {
        return Err("self-report evidence sidecar does not bind these exact report bytes".into());
    }
    let (rows, untyped_rows) = rows_from_report(&report)?;
    if rows.iter().map(|row| &row.location).collect::<Vec<_>>()
        != manifest.rows.iter().collect::<Vec<_>>()
    {
        return Err("saved artifact row locators disagree with the report".into());
    }
    let status: StorageStatus =
        serde_json::from_value(manifest.bundle).map_err(|error| error.to_string())?;
    let mut inventory = BTreeMap::<String, (u64, BTreeSet<OmittedRow>)>::new();
    for row in &rows {
        for artifact in &row.artifacts {
            let digest = required(artifact.digest.as_ref(), "artifact digest")?;
            let materialization =
                required(artifact.materialization.as_ref(), "artifact materialization")?;
            if digest.algorithm != "sha256"
                || !trust_types::digest::is_stable_sha256_hex(&digest.value)
                || materialization.materialized_path.as_deref()
                    != Some(
                        format!(
                            "{}/sha256/{}",
                            trust_types::TRANSPORT_ARTIFACT_STORE_DIRECTORY,
                            digest.value
                        )
                        .as_str(),
                    )
            {
                return Err("saved artifact has a noncanonical digest or store path".into());
            }
            let entry = inventory
                .entry(digest.value.clone())
                .or_insert_with(|| (materialization.byte_len, BTreeSet::new()));
            if entry.0 != materialization.byte_len {
                return Err("conflicting saved artifact lengths".into());
            }
            entry.1.insert(row.core_row().into());
        }
    }
    let mut omitted = BTreeSet::new();
    let mut omitted_bytes = 0_u64;
    let mut favourable_omitted_rows = BTreeSet::new();
    for artifact in &status.omitted {
        let expected = inventory
            .get(&artifact.digest_sha256)
            .ok_or("omitted artifact is absent from report")?;
        let listed = artifact.rows.iter().cloned().collect::<BTreeSet<_>>();
        if !omitted.insert(artifact.digest_sha256.clone())
            || artifact.byte_len != expected.0
            || listed.len() != artifact.rows.len()
            || listed != expected.1
        {
            return Err("omitted artifact accounting disagrees with scoped report rows".into());
        }
        omitted_bytes =
            omitted_bytes.checked_add(artifact.byte_len).ok_or("omitted artifact byte overflow")?;
        for row in &listed {
            if matches!(row.outcome.as_str(), "proved" | "runtime_checked") {
                favourable_omitted_rows.insert(row.obligation_index);
            }
        }
    }
    let mut persisted =
        BTreeMap::<String, Vec<trust_types::TransportArtifactMaterialization>>::new();
    let mut persisted_bytes = 0_u64;
    for row in &rows {
        for artifact in &row.artifacts {
            let digest = artifact.digest.as_ref().ok_or("missing saved digest")?;
            if !omitted.contains(&digest.value) {
                let materialization =
                    artifact.materialization.as_ref().ok_or("missing saved materialization")?;
                let descriptors = persisted.entry(digest.value.clone()).or_default();
                let first = descriptors.is_empty();
                if !descriptors.contains(materialization) {
                    materialization.decoded_bytes_at_root(digest, &root).map_err(|error| {
                        format!("saved proof artifact failed revalidation: {error}")
                    })?;
                    descriptors.push(materialization.clone());
                }
                if first {
                    persisted_bytes = persisted_bytes
                        .checked_add(inventory[&digest.value].0)
                        .ok_or("persisted artifact byte overflow")?;
                }
            }
        }
    }
    if status.complete != omitted.is_empty()
        || status.persisted_artifacts != persisted.len()
        || status.persisted_bytes != persisted_bytes
        || status.omitted_artifacts != omitted.len()
        || status.omitted_bytes != omitted_bytes
        || status.omitted_proved_or_runtime_checked_rows != favourable_omitted_rows.len()
    {
        return Err("saved evidence bundle counters disagree with actual retained artifacts".into());
    }
    recheck_claimed_native_topology(&report, &root, &omitted)?;
    let complete = status.complete && untyped_rows == 0;
    if retention.get("complete").and_then(Value::as_bool) != Some(complete)
        || retention.get("collection_complete").and_then(Value::as_bool) != Some(untyped_rows == 0)
        || retention.get("untyped_transport_rows").and_then(Value::as_u64)
            != Some(untyped_rows as u64)
    {
        return Err("saved typed artifact collection accounting disagrees with its rows".into());
    }
    Ok(json!({"schema": SCHEMA, "status": if complete { "retained" } else { "incomplete" },
        "complete": complete, "collection_complete": untyped_rows == 0,
        "untyped_transport_rows": untyped_rows, "persisted_artifacts": persisted.len(),
        "omitted_artifacts": omitted.len(), "observational_only": true,
        "execution_identity_bound": false, "source_provenance_bound": false}))
}

fn recheck_claimed_native_topology(
    report: &Value,
    root: &Path,
    omitted: &BTreeSet<String>,
) -> Result<(), String> {
    for stage in required(report.get("stages").and_then(Value::as_array), "stages")? {
        let rows = required(
            stage
                .get("solver_suite")
                .and_then(|suite| suite.get("verification_rows"))
                .and_then(Value::as_array),
            "verification rows",
        )?;
        for row in rows {
            if row
                .get("proof_binding")
                .and_then(|binding| binding.get("accepted"))
                .and_then(Value::as_bool)
                != Some(true)
                || row
                    .get("proof_binding")
                    .and_then(|binding| binding.get("publication_grade_native_proof"))
                    .and_then(Value::as_bool)
                    != Some(true)
            {
                continue;
            }
            let proof: TransportProofEvidence = serde_json::from_value(
                required(row.get("proof_evidence"), "native proof")?.clone(),
            )
            .map_err(|error| error.to_string())?;
            let native: TransportNativeTrustIrEvidence = serde_json::from_value(
                required(row.get("native_trust_ir"), "native envelope")?.clone(),
            )
            .map_err(|error| error.to_string())?;
            if proof.artifacts.iter().chain(&native.artifacts).any(|artifact| {
                artifact.digest.as_ref().is_some_and(|digest| omitted.contains(&digest.value))
            }) {
                // Omitted bytes remain explicitly unavailable; comparison
                // never substitutes the producer's deleted private root.
                continue;
            }
            if let Some(defect) = trust_types::transport_proof_artifact_topology_defect_at_root(
                &proof.suite,
                &proof.artifacts,
                row.get("obligation_id").and_then(Value::as_str),
                root,
            ) {
                return Err(format!("saved native proof topology failed revalidation: {defect}"));
            }
            if !trust_types::native_trust_ir_artifact_shape_is_publishable_at_root(&native, root) {
                return Err("saved native envelope failed structural revalidation".into());
            }
        }
    }
    Ok(())
}
