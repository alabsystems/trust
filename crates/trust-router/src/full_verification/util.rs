//! Small utility helpers shared across full-verification submodules.

use trust_verifier_api::{ArtifactHash, EvidenceArtifact, MetadataEntry, SupportLevel};

pub(super) fn status_label(status: trust_verifier_api::EvidenceStatus) -> &'static str {
    status.outcome().as_str()
}

pub(super) fn support_description(support: &SupportLevel) -> String {
    match support {
        SupportLevel::Unsupported { reason } => format!("unsupported: {reason}"),
        SupportLevel::Experimental { reason } => format!("experimental: {reason}"),
        SupportLevel::Supported => "supported".to_string(),
        SupportLevel::Preferred => "preferred".to_string(),
        _ => "unrecognized support level".to_string(),
    }
}

pub(super) fn worker_threads(
    context: Option<&trust_verifier_api::VerifierExecutionContext>,
) -> Option<usize> {
    context.and_then(|context| context.limits.worker_threads).map(usize::from)
}

pub(super) fn append_unique_artifacts(
    target: &mut Vec<EvidenceArtifact>,
    artifacts: Vec<EvidenceArtifact>,
) {
    for artifact in artifacts {
        if !target.contains(&artifact) {
            target.push(artifact);
        }
    }
}

pub(super) fn metadata_u32(metadata: &[MetadataEntry], key: &str) -> Result<Option<u32>, String> {
    metadata
        .iter()
        .find(|entry| entry.key == key)
        .map(|entry| {
            entry.value.parse::<u32>().map_err(|_| {
                format!(
                    "metadata `{key}` must be an unsigned 32-bit integer, got `{}`",
                    entry.value
                )
            })
        })
        .transpose()
}

pub(super) fn metadata_value<'a>(metadata: &'a [MetadataEntry], key: &str) -> Option<&'a str> {
    metadata.iter().find(|entry| entry.key == key).map(|entry| entry.value.as_str())
}

pub(super) fn artifact_hash_label(hash: &ArtifactHash) -> String {
    format!("{}:{}", hash.algorithm, hash.value)
}
