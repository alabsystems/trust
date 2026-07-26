// Dispatch-level helpers: canonical bindings, exact-replay witness derivation,
// transcript artifact construction, and dispatch classification predicates.

use std::collections::BTreeMap;
use std::path::Path;

use serde::Serialize;
use trust_proof_cert::digest_binary_origin;
#[cfg(test)]
use trust_router::Router;
#[cfg(test)]
use trust_types::VerificationCondition;
use trust_types::{
    BinaryArtifactDigest, BinaryArtifactDigestIdentity, BinaryOrigin, BinarySelectedImageIdentity,
    ProofCertificateStatus, ReplayStatus, SolverDispatchRecord, SolverDispatchStatus,
    SolverQuerySemantics, VerificationResult,
};

use crate::input_limits::{MAX_BINARY_ARTIFACT_BYTES, read_bounded_file};

use super::{
    DispatchCanonicalBinding, EXACT_REPLAY_BYTE_RANGE_FACT_DIAGNOSTIC_PREFIX,
    EXACT_REPLAY_CONTROL_FLOW_FACT_DIAGNOSTIC_PREFIX,
    EXACT_REPLAY_MEMORY_EFFECT_FACT_DIAGNOSTIC_PREFIX, EXACT_REPLAY_REQUIRED_WITNESS_BINDINGS,
    EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC,
    EXACT_REPLAY_SLICE_ATTESTATION_REJECTED_PREFIX,
    EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX,
    EXACT_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA, EXACT_REPLAY_WITNESS_ARTIFACT_DIGEST_DIAGNOSTIC,
    EXACT_REPLAY_WITNESS_BINDING_ACCEPTED_DIAGNOSTIC,
    EXACT_REPLAY_WITNESS_CONTROL_FLOW_CAPABILITY_DIAGNOSTIC,
    EXACT_REPLAY_WITNESS_EXECUTED_RANGE_DIAGNOSTIC,
    EXACT_REPLAY_WITNESS_INSTRUCTION_BYTES_DIAGNOSTIC,
    EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC, EXACT_REPLAY_WITNESS_SELECTED_IMAGE_DIAGNOSTIC,
    is_canonical_sha256_hex, stable_json_sha256,
};
use crate::vc_kind_key;
#[cfg(test)]
use crate::{
    BinarySolverResultReport, BinarySolverRoute, binary_solver_result_report_with_replay,
    format_solver_location,
};

pub(super) fn dispatch_canonical_binding(
    dispatch: &SolverDispatchRecord,
) -> Option<DispatchCanonicalBinding> {
    let canonical_vc_bytes = serde_json::to_vec(dispatch.vc.as_ref()?).ok()?;
    let origin_sha256 = digest_binary_origin(dispatch.origin.as_ref()?).ok()?;
    let vc_sha256 = trust_types::digest::stable_sha256_hex(&canonical_vc_bytes);
    Some(DispatchCanonicalBinding::new(canonical_vc_bytes, vc_sha256, origin_sha256))
}

pub(super) fn dispatch_proves_required_vc(record: &SolverDispatchRecord) -> bool {
    record.status == SolverDispatchStatus::Unsat
        && record.query_semantics == SolverQuerySemantics::SatIsCounterexample
}

pub(super) fn dispatch_satisfies_replay_semantics(record: &SolverDispatchRecord) -> bool {
    match (record.status, record.query_semantics) {
        (SolverDispatchStatus::Sat, SolverQuerySemantics::SatIsCounterexample) => {
            record.replay == ReplayStatus::Replayed
                && dispatch_has_exact_replay_slice_attestation(record)
        }
        (SolverDispatchStatus::Unsat, SolverQuerySemantics::SatIsCounterexample) => {
            (record.replay == ReplayStatus::Replayed
                && dispatch_has_exact_replay_slice_attestation(record))
                || (record.replay == ReplayStatus::NotAttempted
                    && dispatch_has_checked_certificate_identity(record))
        }
        _ => false,
    }
}

pub(crate) fn dispatch_has_exact_replay_slice_attestation(record: &SolverDispatchRecord) -> bool {
    if !dispatch_has_exact_replay_slice_attestation_diagnostic(record) {
        return false;
    }

    if dispatch_requires_exact_replay_witness_binding(record) {
        dispatch_exact_replay_witness_binding_blockers(record).is_empty()
    } else {
        true
    }
}

fn dispatch_has_exact_replay_slice_attestation_diagnostic(record: &SolverDispatchRecord) -> bool {
    record
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.trim() == EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC)
}

pub(crate) fn dispatch_exact_replay_slice_attestation_blockers(
    record: &SolverDispatchRecord,
) -> Vec<String> {
    if record.replay != ReplayStatus::Replayed
        || dispatch_has_exact_replay_slice_attestation(record)
    {
        return Vec::new();
    }

    let mut blockers = record
        .diagnostics
        .iter()
        .filter_map(|diagnostic| {
            diagnostic
                .trim()
                .strip_prefix(EXACT_REPLAY_SLICE_ATTESTATION_REJECTED_PREFIX)
                .map(|detail| detail.trim_start_matches(':').trim().to_string())
        })
        .filter(|detail| !detail.is_empty())
        .collect::<Vec<_>>();

    if dispatch_requires_exact_replay_witness_binding(record) {
        blockers.extend(dispatch_exact_replay_witness_binding_blockers(record));
    }

    if blockers.is_empty() {
        blockers.push("missing exact replay selected-image byte/segment attestation".to_string());
    }

    blockers.into_iter().map(|blocker| format!("dispatch {}: {blocker}", record.id)).collect()
}

fn dispatch_requires_exact_replay_witness_binding(record: &SolverDispatchRecord) -> bool {
    record.status == SolverDispatchStatus::Sat
        && record.query_semantics == SolverQuerySemantics::SatIsCounterexample
}

#[derive(Debug, Clone, Serialize)]
struct ExactReplayTranscriptArtifact {
    schema_version: &'static str,
    dispatch: ExactReplayTranscriptDispatch,
    binary_artifact_digest_identity: BinaryArtifactDigestIdentity,
    selected_image_identity: BinarySelectedImageIdentity,
    binary_origin_sha256: String,
    instruction: ExactReplayTranscriptInstruction,
    executed_range: ExactReplayTranscriptExecutedRange,
    control_flow_capability_evidence: ExactReplayTranscriptBindingEvidence,
    memory_effect_attestation: ExactReplayTranscriptBindingEvidence,
    byte_range_facts: ExactReplayTranscriptFactSet,
    control_flow_facts: ExactReplayTranscriptFactSet,
    memory_effect_facts: ExactReplayTranscriptFactSet,
    vc: ExactReplayTranscriptVc,
    solver_dispatch_artifact_sha256: String,
}

#[derive(Debug, Clone, Serialize)]
struct ExactReplayTranscriptDispatch {
    id: String,
    function: Option<String>,
    solver: String,
    backend: Option<String>,
    status: SolverDispatchStatus,
    query_semantics: SolverQuerySemantics,
    replay: ReplayStatus,
}

#[derive(Debug, Clone, Serialize)]
struct ExactReplayTranscriptInstruction {
    binary_path: Option<String>,
    function_entry: Option<u64>,
    instruction_address: u64,
    instruction_size: u8,
    encoding: Option<u32>,
    instruction_bytes: Vec<u8>,
    instruction_bytes_sha256: String,
}

#[derive(Debug, Clone, Serialize)]
struct ExactReplayTranscriptExecutedRange {
    start_address: u64,
    end_address: u64,
    instruction_count: usize,
    instruction_addresses: Vec<u64>,
}

#[derive(Debug, Clone, Serialize)]
struct ExactReplayTranscriptBindingEvidence {
    accepted: bool,
    diagnostic: &'static str,
    diagnostic_sha256: String,
}

#[derive(Debug, Clone, Serialize)]
struct ExactReplayTranscriptFactSet {
    diagnostic_prefix: &'static str,
    count: usize,
    facts: Vec<String>,
    facts_sha256: String,
}

#[derive(Debug, Clone, Serialize)]
struct ExactReplayTranscriptVc {
    kind: Option<String>,
    sha256: String,
}

pub(super) fn derive_exact_replay_witness_binding(
    record: &mut SolverDispatchRecord,
    artifact_identity_cache: &mut BTreeMap<String, Option<BinaryArtifactDigestIdentity>>,
) {
    if record.replay != ReplayStatus::Replayed
        || !dispatch_requires_exact_replay_witness_binding(record)
        || !dispatch_has_exact_replay_slice_attestation_diagnostic(record)
    {
        return;
    }

    if let Some(derived_identity) =
        derive_dispatch_binary_artifact_digest_identity(record, artifact_identity_cache)
    {
        match &mut record.binary_artifact_digest_identity {
            Some(identity) => {
                if identity.root_artifact_digest.is_none() {
                    identity.root_artifact_digest = derived_identity.root_artifact_digest.clone();
                }
                if identity.selected_image.is_none() {
                    identity.selected_image = derived_identity.selected_image.clone();
                }
            }
            None => record.binary_artifact_digest_identity = Some(derived_identity),
        }
    }

    let artifact_digest_ready = dispatch_exact_replay_artifact_digest_binding_ready(record);
    let selected_image_ready = dispatch_exact_replay_selected_image_binding_ready(record);
    let instruction_bytes_ready = dispatch_exact_replay_instruction_bytes_binding_ready(record);
    let executed_range_ready = dispatch_exact_replay_executed_range_binding_ready(record);
    let control_flow_ready = dispatch_exact_replay_control_flow_binding_ready(record);
    let memory_effect_ready = dispatch_exact_replay_memory_effect_binding_ready(record);
    let origin_query_vc_ready = dispatch_exact_replay_origin_query_vc_binding_ready(record);

    if artifact_digest_ready {
        push_diagnostic_if_absent(record, EXACT_REPLAY_WITNESS_ARTIFACT_DIGEST_DIAGNOSTIC);
    }
    if selected_image_ready {
        push_diagnostic_if_absent(record, EXACT_REPLAY_WITNESS_SELECTED_IMAGE_DIAGNOSTIC);
    }
    if instruction_bytes_ready {
        push_diagnostic_if_absent(record, EXACT_REPLAY_WITNESS_INSTRUCTION_BYTES_DIAGNOSTIC);
    }
    if executed_range_ready {
        push_diagnostic_if_absent(record, EXACT_REPLAY_WITNESS_EXECUTED_RANGE_DIAGNOSTIC);
    }
    if control_flow_ready {
        push_diagnostic_if_absent(record, EXACT_REPLAY_WITNESS_CONTROL_FLOW_CAPABILITY_DIAGNOSTIC);
    }
    if memory_effect_ready {
        push_diagnostic_if_absent(record, EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC);
    }

    if artifact_digest_ready
        && selected_image_ready
        && instruction_bytes_ready
        && executed_range_ready
        && control_flow_ready
        && memory_effect_ready
        && origin_query_vc_ready
    {
        if let Some(replay_transcript_digest) =
            derive_exact_replay_transcript_artifact_digest(record)
        {
            push_owned_diagnostic_if_absent(
                record,
                format!(
                    "{EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX}{replay_transcript_digest}"
                ),
            );
        }
        push_diagnostic_if_absent(record, EXACT_REPLAY_WITNESS_BINDING_ACCEPTED_DIAGNOSTIC);
    }
}

fn derive_dispatch_binary_artifact_digest_identity(
    record: &SolverDispatchRecord,
    artifact_identity_cache: &mut BTreeMap<String, Option<BinaryArtifactDigestIdentity>>,
) -> Option<BinaryArtifactDigestIdentity> {
    let path = record.origin.as_ref()?.binary_path.as_ref()?.trim();
    if path.is_empty() {
        return None;
    }

    if let Some(cached) = artifact_identity_cache.get(path) {
        return cached.clone();
    }

    let identity =
        read_bounded_file(Path::new(path), MAX_BINARY_ARTIFACT_BYTES).ok().and_then(|bytes| {
            let file_size = u64::try_from(bytes.len()).ok()?;
            let digest = trust_types::digest::stable_sha256_hex(&bytes);
            Some(BinaryArtifactDigestIdentity {
                root_artifact_digest: Some(BinaryArtifactDigest::sha256(digest.clone())),
                selected_image: Some(BinarySelectedImageIdentity {
                    file_offset: 0,
                    file_size,
                    sha256: digest,
                }),
            })
        });
    artifact_identity_cache.insert(path.to_string(), identity.clone());
    identity
}

pub(super) fn bind_dispatch_binary_artifact_digest_identity(
    record: &mut SolverDispatchRecord,
    artifact_identity_cache: &mut BTreeMap<String, Option<BinaryArtifactDigestIdentity>>,
) {
    let Some(derived_identity) =
        derive_dispatch_binary_artifact_digest_identity(record, artifact_identity_cache)
    else {
        return;
    };

    match &mut record.binary_artifact_digest_identity {
        Some(identity) => {
            if identity.root_artifact_digest.is_none() {
                identity.root_artifact_digest = derived_identity.root_artifact_digest;
            }
            if identity.selected_image.is_none() {
                identity.selected_image = derived_identity.selected_image;
            }
        }
        None => record.binary_artifact_digest_identity = Some(derived_identity),
    }
}

fn dispatch_exact_replay_artifact_digest_binding_ready(record: &SolverDispatchRecord) -> bool {
    if dispatch_exact_replay_loaded_image_bytes_blocker(record).is_some() {
        return false;
    }
    record
        .binary_artifact_digest_identity
        .as_ref()
        .and_then(|identity| identity.root_artifact_digest.as_ref())
        .is_some_and(BinaryArtifactDigest::is_canonical_sha256)
        && dispatch_root_artifact_digest_mismatch_blocker(record).is_none()
}

fn dispatch_exact_replay_selected_image_binding_ready(record: &SolverDispatchRecord) -> bool {
    if dispatch_exact_replay_loaded_image_bytes_blocker(record).is_some() {
        return false;
    }
    record
        .binary_artifact_digest_identity
        .as_ref()
        .and_then(|identity| identity.selected_image.as_ref())
        .is_some_and(|selected| {
            selected.file_size > 0
                && selected.is_canonical_sha256()
                && selected.end_offset().is_some()
        })
        && dispatch_selected_image_mismatch_blocker(record).is_none()
}

fn dispatch_exact_replay_instruction_bytes_binding_ready(record: &SolverDispatchRecord) -> bool {
    record.origin.as_ref().is_some_and(|origin| {
        !origin.instruction_bytes.is_empty()
            && origin
                .instruction_size
                .is_some_and(|size| usize::from(size) == origin.instruction_bytes.len())
    })
}

fn dispatch_exact_replay_executed_range_binding_ready(record: &SolverDispatchRecord) -> bool {
    let Some(addresses) = dispatch_counterexample_trace_addresses(record) else {
        return false;
    };
    if addresses.is_empty() {
        return false;
    }
    record.origin.as_ref().is_some_and(|origin| addresses.contains(&origin.instruction_address))
}

fn dispatch_exact_replay_control_flow_binding_ready(record: &SolverDispatchRecord) -> bool {
    record.replay == ReplayStatus::Replayed
        && !dispatch_has_unsupported_binding_diagnostic(record, &["control", "capability"])
}

fn dispatch_exact_replay_memory_effect_binding_ready(record: &SolverDispatchRecord) -> bool {
    record.replay == ReplayStatus::Replayed
        && !dispatch_has_unsupported_binding_diagnostic(record, &["effect", "memory"])
}

fn dispatch_exact_replay_loaded_image_bytes_blocker(
    record: &SolverDispatchRecord,
) -> Option<String> {
    let origin = record.origin.as_ref()?;
    let path = origin.binary_path.as_ref().map(|path| path.trim()).filter(|path| !path.is_empty());
    let path = match path {
        Some(path) => path,
        None => return Some("missing loaded-image path for exact replay transcript".to_string()),
    };
    match read_bounded_file(Path::new(path), MAX_BINARY_ARTIFACT_BYTES) {
        Ok(bytes) if bytes.is_empty() => {
            Some(format!("loaded-image bytes are empty for exact replay transcript: {path}"))
        }
        Ok(_) => None,
        Err(error) => Some(format!(
            "missing or unreadable loaded-image bytes for exact replay transcript: {path}: {error}"
        )),
    }
}

fn dispatch_has_unsupported_binding_diagnostic(
    record: &SolverDispatchRecord,
    required_terms: &[&str],
) -> bool {
    record.diagnostics.iter().any(|diagnostic| {
        let diagnostic = diagnostic.to_ascii_lowercase();
        diagnostic.contains("unsupported")
            && required_terms.iter().any(|term| diagnostic.contains(term))
    })
}

fn dispatch_has_replay_architecture_mismatch_diagnostic(record: &SolverDispatchRecord) -> bool {
    record.diagnostics.iter().any(|diagnostic| {
        let diagnostic = diagnostic.to_ascii_lowercase();
        diagnostic.contains("architecture")
            && (diagnostic.contains("mismatch") || diagnostic.contains("unsupported"))
    })
}

fn dispatch_exact_replay_origin_query_vc_binding_ready(record: &SolverDispatchRecord) -> bool {
    record.origin.is_some()
        && record.vc.is_some()
        && record.vc_kind.is_some()
        && record.query_semantics == SolverQuerySemantics::SatIsCounterexample
}

fn push_diagnostic_if_absent(record: &mut SolverDispatchRecord, diagnostic: &'static str) {
    if !dispatch_has_diagnostic(record, diagnostic) {
        record.diagnostics.push(diagnostic.to_string());
    }
}

fn push_owned_diagnostic_if_absent(record: &mut SolverDispatchRecord, diagnostic: String) {
    if !dispatch_has_diagnostic(record, &diagnostic) {
        record.diagnostics.push(diagnostic);
    }
}

pub(super) fn dispatch_exact_replay_transcript_artifact_digest_raw(
    record: &SolverDispatchRecord,
) -> Option<String> {
    record.diagnostics.iter().find_map(|diagnostic| {
        diagnostic
            .trim()
            .strip_prefix(EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
            .map(str::to_string)
    })
}

#[cfg(test)]
pub(crate) fn dispatch_exact_replay_transcript_artifact_digest(
    record: &SolverDispatchRecord,
) -> Option<String> {
    dispatch_exact_replay_transcript_artifact_digest_raw(record)
        .and_then(|digest| is_canonical_sha256_hex(&digest).then_some(digest))
}

fn dispatch_exact_replay_witness_binding_blockers(record: &SolverDispatchRecord) -> Vec<String> {
    let mut blockers = Vec::new();

    if !dispatch_has_exact_replay_slice_attestation_diagnostic(record) {
        blockers.push(
            "missing exact replay selected-image byte/segment attestation acceptance".to_string(),
        );
    }
    if !dispatch_has_diagnostic(record, EXACT_REPLAY_WITNESS_BINDING_ACCEPTED_DIAGNOSTIC) {
        blockers.push("missing exact replay normalized witness binding acceptance".to_string());
    }

    for (diagnostic, binding) in EXACT_REPLAY_REQUIRED_WITNESS_BINDINGS {
        if !dispatch_has_diagnostic(record, diagnostic) {
            blockers.push(format!("missing exact replay normalized witness binding: {binding}"));
        }
    }

    match &record.binary_artifact_digest_identity {
        Some(identity) => {
            blockers.extend(identity.digest_identity_blockers().into_iter().map(|blocker| {
                format!("exact replay normalized witness artifact identity rejected: {blocker}")
            }));
            blockers.extend(
                dispatch_binary_artifact_digest_identity_mismatch_blockers(record).into_iter().map(
                    |blocker| {
                        format!(
                            "exact replay normalized witness artifact identity rejected: {blocker}"
                        )
                    },
                ),
            );
        }
        None => blockers.push(
            "missing exact replay normalized witness artifact identity on dispatch".to_string(),
        ),
    }
    if let Some(blocker) = dispatch_exact_replay_loaded_image_bytes_blocker(record) {
        blockers.push(format!(
            "exact replay normalized witness loaded-image identity rejected: {blocker}"
        ));
    }
    if dispatch_has_replay_architecture_mismatch_diagnostic(record) {
        blockers.push(
            "exact replay normalized witness architecture rejected: replay architecture mismatch or unsupported architecture diagnostic is present"
                .to_string(),
        );
    }

    match &record.origin {
        Some(origin) => {
            if origin.instruction_bytes.is_empty() {
                blockers.push(
                    "missing exact replay normalized witness instruction bytes on dispatch origin"
                        .to_string(),
                );
            }
            match origin.instruction_size {
                Some(size) if usize::from(size) == origin.instruction_bytes.len() => {}
                Some(size) => blockers.push(format!(
                    "exact replay normalized witness instruction byte length mismatch: instruction_size={size} byte_len={}",
                    origin.instruction_bytes.len()
                )),
                None => blockers.push(
                    "missing exact replay normalized witness instruction size on dispatch origin"
                        .to_string(),
                ),
            }
        }
        None => blockers.push(
            "missing exact replay normalized witness instruction origin on dispatch".to_string(),
        ),
    }

    if record.vc.is_none() {
        blockers.push("missing exact replay normalized witness VC on dispatch".to_string());
    }
    if record.vc_kind.is_none() {
        blockers.push("missing exact replay normalized witness VC kind on dispatch".to_string());
    }

    match dispatch_counterexample_trace_addresses(record) {
        Some(addresses) if !addresses.is_empty() => {
            if let Some(origin) = &record.origin {
                if !addresses.contains(&origin.instruction_address) {
                    blockers.push(format!(
                        "exact replay normalized witness executed range does not include dispatch instruction 0x{:x}",
                        origin.instruction_address
                    ));
                }
            }
        }
        Some(_) => blockers
            .push("missing exact replay normalized witness executed instruction range".to_string()),
        None => blockers.push(
            "missing exact replay normalized witness counterexample trace binding".to_string(),
        ),
    }

    blockers
}

fn derive_exact_replay_transcript_artifact_digest(record: &SolverDispatchRecord) -> Option<String> {
    if record.replay != ReplayStatus::Replayed
        || !dispatch_requires_exact_replay_witness_binding(record)
        || !dispatch_has_exact_replay_slice_attestation_diagnostic(record)
        || dispatch_exact_replay_loaded_image_bytes_blocker(record).is_some()
        || dispatch_has_unsupported_binding_diagnostic(record, &["control", "capability"])
        || dispatch_has_unsupported_binding_diagnostic(record, &["effect", "memory"])
        || dispatch_has_replay_architecture_mismatch_diagnostic(record)
        || !EXACT_REPLAY_REQUIRED_WITNESS_BINDINGS
            .iter()
            .all(|(diagnostic, _)| dispatch_has_diagnostic(record, diagnostic))
    {
        return None;
    }

    let identity = record.binary_artifact_digest_identity.clone()?;
    if !identity.digest_identity_blockers().is_empty()
        || !dispatch_binary_artifact_digest_identity_mismatch_blockers(record).is_empty()
    {
        return None;
    }
    let selected_image_identity = identity.selected_image.clone()?;
    let origin = record.origin.as_ref()?;
    let instruction_size = origin.instruction_size?;
    if usize::from(instruction_size) != origin.instruction_bytes.len()
        || origin.instruction_bytes.is_empty()
    {
        return None;
    }
    let binding = dispatch_canonical_binding(record)?;
    let executed_range = dispatch_exact_replay_executed_range(record, origin)?;
    let solver_dispatch_artifact_sha256 = solver_dispatch_artifact_sha256(record)?;
    let byte_range_facts =
        exact_replay_transcript_fact_set(record, EXACT_REPLAY_BYTE_RANGE_FACT_DIAGNOSTIC_PREFIX);
    let control_flow_facts =
        exact_replay_transcript_fact_set(record, EXACT_REPLAY_CONTROL_FLOW_FACT_DIAGNOSTIC_PREFIX);
    let memory_effect_facts =
        exact_replay_transcript_fact_set(record, EXACT_REPLAY_MEMORY_EFFECT_FACT_DIAGNOSTIC_PREFIX);
    let artifact = ExactReplayTranscriptArtifact {
        schema_version: EXACT_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA,
        dispatch: ExactReplayTranscriptDispatch {
            id: record.id.clone(),
            function: record.function.clone(),
            solver: record.solver.clone(),
            backend: record.backend.clone(),
            status: record.status,
            query_semantics: record.query_semantics,
            replay: record.replay,
        },
        binary_artifact_digest_identity: identity,
        selected_image_identity,
        binary_origin_sha256: binding.origin_sha256,
        instruction: ExactReplayTranscriptInstruction {
            binary_path: origin.binary_path.clone(),
            function_entry: origin.function_entry,
            instruction_address: origin.instruction_address,
            instruction_size,
            encoding: origin.encoding,
            instruction_bytes: origin.instruction_bytes.clone(),
            instruction_bytes_sha256: trust_types::digest::stable_sha256_hex(&origin.instruction_bytes),
        },
        executed_range,
        control_flow_capability_evidence: ExactReplayTranscriptBindingEvidence {
            accepted: true,
            diagnostic: EXACT_REPLAY_WITNESS_CONTROL_FLOW_CAPABILITY_DIAGNOSTIC,
            diagnostic_sha256: trust_types::digest::stable_sha256_hex(
                EXACT_REPLAY_WITNESS_CONTROL_FLOW_CAPABILITY_DIAGNOSTIC.as_bytes(),
            ),
        },
        memory_effect_attestation: ExactReplayTranscriptBindingEvidence {
            accepted: true,
            diagnostic: EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC,
            diagnostic_sha256: trust_types::digest::stable_sha256_hex(EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC.as_bytes()),
        },
        byte_range_facts,
        control_flow_facts,
        memory_effect_facts,
        vc: ExactReplayTranscriptVc {
            kind: record.vc_kind.as_ref().map(vc_kind_key),
            sha256: binding.vc_sha256,
        },
        solver_dispatch_artifact_sha256,
    };
    stable_json_sha256(&artifact)
}

fn exact_replay_transcript_fact_set(
    record: &SolverDispatchRecord,
    diagnostic_prefix: &'static str,
) -> ExactReplayTranscriptFactSet {
    let mut facts = record
        .diagnostics
        .iter()
        .filter_map(|diagnostic| {
            diagnostic.trim().strip_prefix(diagnostic_prefix).map(|fact| fact.to_string())
        })
        .collect::<Vec<_>>();
    facts.sort();
    facts.dedup();
    let facts_sha256 = stable_json_sha256(&facts).unwrap_or_else(|| trust_types::digest::stable_sha256_hex(b"[]"));
    ExactReplayTranscriptFactSet { diagnostic_prefix, count: facts.len(), facts, facts_sha256 }
}

fn dispatch_exact_replay_executed_range(
    record: &SolverDispatchRecord,
    origin: &BinaryOrigin,
) -> Option<ExactReplayTranscriptExecutedRange> {
    let instruction_addresses = dispatch_counterexample_trace_addresses(record)?;
    if instruction_addresses.is_empty() {
        return None;
    }
    let start_address = instruction_addresses.iter().copied().min()?;
    let mut end_address = 0;
    for address in &instruction_addresses {
        let size = if *address == origin.instruction_address {
            u64::from(origin.instruction_size?)
        } else {
            1
        };
        end_address = end_address.max(address.checked_add(size)?);
    }
    Some(ExactReplayTranscriptExecutedRange {
        start_address,
        end_address,
        instruction_count: instruction_addresses.len(),
        instruction_addresses,
    })
}

fn solver_dispatch_artifact_sha256(record: &SolverDispatchRecord) -> Option<String> {
    let mut artifact = record.clone();
    artifact.diagnostics.retain(|diagnostic| {
        let diagnostic = diagnostic.trim();
        !diagnostic.starts_with(EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX)
    });
    artifact.diagnostics.sort();
    artifact.diagnostics.dedup();
    stable_json_sha256(&artifact)
}

fn dispatch_binary_artifact_digest_identity_mismatch_blockers(
    record: &SolverDispatchRecord,
) -> Vec<String> {
    let mut blockers = Vec::new();
    if let Some(blocker) = dispatch_root_artifact_digest_mismatch_blocker(record) {
        blockers.push(blocker);
    }
    if let Some(blocker) = dispatch_selected_image_mismatch_blocker(record) {
        blockers.push(blocker);
    }
    blockers
}

pub(super) fn dispatch_binary_artifact_digest_identity_acceptance_blockers(
    record: &SolverDispatchRecord,
) -> Vec<String> {
    let Some(identity) = &record.binary_artifact_digest_identity else {
        return vec!["missing binary artifact digest identity".to_string()];
    };

    let mut blockers = identity.digest_identity_blockers();
    blockers.extend(dispatch_binary_artifact_digest_identity_mismatch_blockers(record));
    blockers
}

fn dispatch_root_artifact_digest_mismatch_blocker(record: &SolverDispatchRecord) -> Option<String> {
    let identity = record.binary_artifact_digest_identity.as_ref()?;
    let expected = identity.root_artifact_digest.as_ref()?;
    if !expected.is_canonical_sha256() {
        return None;
    }
    let bytes = dispatch_binary_path_bytes(record)?;
    let observed = trust_types::digest::stable_sha256_hex(&bytes);
    (expected.value != observed).then(|| {
        format!(
            "root artifact digest does not match loaded binary: expected sha256={} observed sha256={observed}",
            expected.value
        )
    })
}

fn dispatch_selected_image_mismatch_blocker(record: &SolverDispatchRecord) -> Option<String> {
    let identity = record.binary_artifact_digest_identity.as_ref()?;
    let selected = identity.selected_image.as_ref()?;
    if selected.file_size == 0 || !selected.is_canonical_sha256() {
        return None;
    }
    let bytes = dispatch_binary_path_bytes(record)?;
    let start = usize::try_from(selected.file_offset).ok()?;
    let size = usize::try_from(selected.file_size).ok()?;
    let end = start.checked_add(size)?;
    if end > bytes.len() {
        return Some(format!(
            "selected image range exceeds loaded binary size: file_offset={} file_size={} binary_size={}",
            selected.file_offset,
            selected.file_size,
            bytes.len()
        ));
    }
    let observed = trust_types::digest::stable_sha256_hex(&bytes[start..end]);
    (selected.sha256 != observed).then(|| {
        format!(
            "selected image digest does not match loaded binary range: file_offset={} file_size={} expected sha256={} observed sha256={observed}",
            selected.file_offset, selected.file_size, selected.sha256
        )
    })
}

fn dispatch_binary_path_bytes(record: &SolverDispatchRecord) -> Option<Vec<u8>> {
    let path = record.origin.as_ref()?.binary_path.as_ref()?.trim();
    if path.is_empty() {
        return None;
    }
    read_bounded_file(Path::new(path), MAX_BINARY_ARTIFACT_BYTES).ok()
}

fn dispatch_has_diagnostic(record: &SolverDispatchRecord, expected: &str) -> bool {
    record.diagnostics.iter().any(|diagnostic| diagnostic.trim() == expected)
}

fn dispatch_counterexample_trace_addresses(record: &SolverDispatchRecord) -> Option<Vec<u64>> {
    let Some(VerificationResult::Failed { counterexample: Some(counterexample), .. }) =
        &record.result
    else {
        return None;
    };
    let trace = counterexample.trace.as_ref()?;
    Some(
        trace
            .steps
            .iter()
            .filter_map(|step| {
                step.program_point
                    .as_deref()
                    .and_then(parse_address_from_counterexample_program_point)
            })
            .collect(),
    )
}

fn parse_address_from_counterexample_program_point(program_point: &str) -> Option<u64> {
    let bytes = program_point.as_bytes();
    let mut idx = 0;
    while idx + 2 <= bytes.len() {
        if bytes[idx] == b'0' && matches!(bytes.get(idx + 1), Some(b'x' | b'X')) {
            let start = idx + 2;
            let mut end = start;
            while end < bytes.len() && bytes[end].is_ascii_hexdigit() {
                end += 1;
            }
            if end > start {
                return u64::from_str_radix(&program_point[start..end], 16).ok();
            }
        }
        idx += 1;
    }
    None
}

pub(super) fn dispatch_has_checked_certificate_identity(record: &SolverDispatchRecord) -> bool {
    if dispatch_canonical_binding(record).is_none() {
        return false;
    }
    if !dispatch_binary_artifact_digest_identity_acceptance_blockers(record).is_empty() {
        return false;
    }

    matches!(
        &record.certificate,
        ProofCertificateStatus::Checked { checker, format, sha256 }
            if !checker.trim().is_empty()
                && !format.trim().is_empty()
                && sha256.as_deref().is_some_and(is_canonical_sha256_hex)
    )
}

pub(super) fn has_solver_proof_bytes(record: &SolverDispatchRecord) -> bool {
    matches!(record.result, Some(VerificationResult::Proved { proof_certificate: Some(_), .. }))
}

#[cfg(test)]
pub(crate) fn dispatch_binary_vcs_with_evidence(
    router: &Router,
    solver_route: BinarySolverRoute,
    function: &str,
    entry_point: u64,
    vcs: &[VerificationCondition],
) -> (Vec<BinarySolverResultReport>, Vec<SolverDispatchRecord>) {
    let mut reports = Vec::with_capacity(vcs.len());
    let mut dispatch_records = Vec::with_capacity(vcs.len());

    for (index, vc) in vcs.iter().enumerate() {
        let result = router.verify_one(vc);
        let report = binary_solver_result_report_with_replay(
            function,
            vc_kind_key(&vc.kind),
            format_solver_location(&vc.location),
            &result,
            None,
        );
        let replay = replay_status_from_solver_report(&report);
        dispatch_records.push(solver_dispatch_record(
            solver_route,
            function,
            entry_point,
            index,
            vc,
            result,
            replay,
        ));
        reports.push(report);
    }

    (reports, dispatch_records)
}

#[cfg(test)]
fn solver_dispatch_record(
    solver_route: BinarySolverRoute,
    function: &str,
    entry_point: u64,
    index: usize,
    vc: &VerificationCondition,
    result: VerificationResult,
    replay: ReplayStatus,
) -> SolverDispatchRecord {
    let status = solver_dispatch_status(&result);
    let certificate = proof_certificate_status(&result);
    let elapsed_ms = Some(result.time_ms());
    SolverDispatchRecord {
        id: format!("{function}:{entry_point:#x}:{index}"),
        function: Some(function.to_string()),
        vc_kind: Some(vc.kind.clone()),
        solver: result.solver_name().to_string(),
        backend: Some(solver_route.backend_label().to_string()),
        status,
        query_semantics: SolverQuerySemantics::SatIsCounterexample,
        result: Some(result),
        elapsed_ms,
        replay,
        certificate,
        ..Default::default()
    }
}

#[cfg(test)]
fn replay_status_from_solver_report(report: &BinarySolverResultReport) -> ReplayStatus {
    match report.replay_status.as_deref() {
        Some("replayed") => ReplayStatus::Replayed,
        Some("spurious") => ReplayStatus::Spurious,
        Some("failed") => ReplayStatus::Failed,
        Some("not_attempted") | None => ReplayStatus::NotAttempted,
        Some(_) => ReplayStatus::NotAttempted,
    }
}

#[cfg(test)]
fn solver_dispatch_status(result: &VerificationResult) -> SolverDispatchStatus {
    match result {
        VerificationResult::Proved { .. } => SolverDispatchStatus::Unsat,
        VerificationResult::Failed { .. } => SolverDispatchStatus::Sat,
        VerificationResult::Unknown { .. } => SolverDispatchStatus::Unknown,
        VerificationResult::Timeout { .. } => SolverDispatchStatus::Timeout,
        _ => SolverDispatchStatus::Unknown,
    }
}

#[cfg(test)]
fn proof_certificate_status(result: &VerificationResult) -> ProofCertificateStatus {
    match result {
        VerificationResult::Proved { proof_certificate: Some(_), .. } => {
            ProofCertificateStatus::Present {
                format: "solver-native".to_string(),
                sha256: None,
                artifact_path: None,
            }
        }
        VerificationResult::Proved { .. } => ProofCertificateStatus::Unavailable {
            reason: Some("solver did not return a proof artifact".to_string()),
        },
        _ => ProofCertificateStatus::NotRequested,
    }
}
