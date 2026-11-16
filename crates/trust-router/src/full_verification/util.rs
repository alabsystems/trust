//! Small utility helpers shared across full-verification submodules.

use trust_verifier_api::{ArtifactHash, EvidenceArtifact, SupportLevel};

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

pub(super) fn artifact_hash_label(hash: &ArtifactHash) -> String {
    format!("{}:{}", hash.algorithm, hash.value)
}
