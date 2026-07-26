// Diagnostic prefix constants for the binary verification evidence pipeline.

pub(crate) const EXACT_REPLAY_SLICE_ATTESTATION_ACCEPTED_DIAGNOSTIC: &str =
    "exact_replay_slice_attestation=accepted";
pub(crate) const EXACT_REPLAY_SLICE_ATTESTATION_REJECTED_PREFIX: &str =
    "exact_replay_slice_attestation=rejected";
pub(crate) const EXACT_REPLAY_WITNESS_BINDING_ACCEPTED_DIAGNOSTIC: &str =
    "exact_replay_witness_binding=accepted";
pub(crate) const EXACT_REPLAY_WITNESS_ARTIFACT_DIGEST_DIAGNOSTIC: &str =
    "exact_replay_witness_binding:artifact_digest=accepted";
pub(crate) const EXACT_REPLAY_WITNESS_SELECTED_IMAGE_DIAGNOSTIC: &str =
    "exact_replay_witness_binding:selected_image_digest_range=accepted";
pub(crate) const EXACT_REPLAY_WITNESS_INSTRUCTION_BYTES_DIAGNOSTIC: &str =
    "exact_replay_witness_binding:instruction_bytes=accepted";
pub(crate) const EXACT_REPLAY_WITNESS_EXECUTED_RANGE_DIAGNOSTIC: &str =
    "exact_replay_witness_binding:executed_range=accepted";
pub(crate) const EXACT_REPLAY_WITNESS_CONTROL_FLOW_CAPABILITY_DIAGNOSTIC: &str =
    "exact_replay_witness_binding:branch_call_return_capability_evidence=accepted";
pub(crate) const EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC: &str =
    "exact_replay_witness_binding:memory_effect_attestation=accepted";
pub(crate) const EXACT_REPLAY_TRANSCRIPT_ARTIFACT_DIGEST_DIAGNOSTIC_PREFIX: &str =
    "exact_replay_transcript_artifact_digest=accepted:sha256=";
pub(crate) const EXACT_REPLAY_BYTE_RANGE_FACT_DIAGNOSTIC_PREFIX: &str =
    "exact_replay_transcript_fact:byte_range:";
pub(crate) const EXACT_REPLAY_CONTROL_FLOW_FACT_DIAGNOSTIC_PREFIX: &str =
    "exact_replay_transcript_fact:control_flow:";
pub(crate) const EXACT_REPLAY_MEMORY_EFFECT_FACT_DIAGNOSTIC_PREFIX: &str =
    "exact_replay_transcript_fact:memory_effect:";
pub(super) const EXACT_REPLAY_TRANSCRIPT_ARTIFACT_SCHEMA: &str =
    "targo-trust.exact-replay-transcript-artifact.v1";
pub(crate) const NORMALIZED_SOLVER_PROOF_EXPORT_ARTIFACT_SCHEMA: &str =
    "targo-trust.normalized-solver-proof-export.v1";
pub(crate) const NORMALIZED_SOLVER_PROOF_EXPORT_ARTIFACT_SUFFIX: &str =
    "targo-trust-normalized-solver-proof-export.json";

pub(super) const EXACT_REPLAY_REQUIRED_WITNESS_BINDINGS: [(&str, &str); 6] = [
    (EXACT_REPLAY_WITNESS_ARTIFACT_DIGEST_DIAGNOSTIC, "artifact digest"),
    (EXACT_REPLAY_WITNESS_SELECTED_IMAGE_DIAGNOSTIC, "selected-image digest/range"),
    (EXACT_REPLAY_WITNESS_INSTRUCTION_BYTES_DIAGNOSTIC, "instruction bytes"),
    (EXACT_REPLAY_WITNESS_EXECUTED_RANGE_DIAGNOSTIC, "executed range"),
    (
        EXACT_REPLAY_WITNESS_CONTROL_FLOW_CAPABILITY_DIAGNOSTIC,
        "branch/call/return capability evidence",
    ),
    (EXACT_REPLAY_WITNESS_MEMORY_EFFECT_DIAGNOSTIC, "memory/effect attestation"),
];
