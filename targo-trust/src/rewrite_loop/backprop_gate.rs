// Gate logic deciding whether a verification result's source span may drive a
// source rewrite. Binary-derived results are gated by the imported runtime
// binary source provenance artifact.

use trust_types::SourceSpan;

use super::provenance::RuntimeBinarySourceProvenance;
use super::types::BinarySourceBackpropagationBlocker;
use crate::types::{VerificationOutcome, VerificationResult};

pub(super) fn source_backed_path(path: &str) -> Option<&str> {
    (!path.is_empty() && !is_binary_only_path(path)).then_some(path)
}

pub(super) fn source_backed_location_path(result: &VerificationResult) -> Option<&str> {
    result.location.as_ref().map(|span| span.file.as_str()).and_then(source_backed_path)
}

pub(super) fn source_backed_location_path_for_backprop<'a>(
    result: &'a VerificationResult,
    source_provenance: Option<&RuntimeBinarySourceProvenance>,
) -> Option<&'a str> {
    let path = source_backed_location_path(result)?;
    source_backpropagation_allowed_for_result(result, source_provenance).then_some(path)
}

pub(crate) fn binary_source_backpropagation_blockers(
    results: &[VerificationResult],
    source_provenance: Option<&RuntimeBinarySourceProvenance>,
) -> Vec<BinarySourceBackpropagationBlocker> {
    results
        .iter()
        .filter(|result| result.outcome == VerificationOutcome::Failed)
        .filter(|result| is_binary_derived_result(result))
        .filter(|result| !source_backpropagation_allowed_for_result(result, source_provenance))
        .filter_map(|result| {
            let reason =
                binary_source_backpropagation_blocker_reason_for_result(result, source_provenance);
            source_backed_location_path(result).map(|source_file| {
                BinarySourceBackpropagationBlocker {
                    function: if result.function.is_empty() {
                        "<unknown>".to_string()
                    } else {
                        result.function.clone()
                    },
                    kind: result.kind.clone(),
                    source_file: source_file.to_string(),
                    reason: reason.clone(),
                }
            })
        })
        .collect()
}

fn binary_source_backpropagation_blocker_reason_for_result(
    result: &VerificationResult,
    source_provenance: Option<&RuntimeBinarySourceProvenance>,
) -> String {
    if !binary_source_backpropagation_allowed(source_provenance) {
        return binary_source_backpropagation_blocker_reason(source_provenance);
    }

    match binary_address_for_result(result) {
        Some(address) => format!(
            "binary-derived source span is not backed by an exact imported mapping for binary:0x{address:x}"
        ),
        None => {
            "binary-derived source span does not carry a binary address that can be checked against the imported provenance artifact"
                .to_string()
        }
    }
}

fn binary_source_backpropagation_blocker_reason(
    source_provenance: Option<&RuntimeBinarySourceProvenance>,
) -> String {
    let Some(source_provenance) = source_provenance else {
        return "no exact binary source provenance artifact has been imported by the runtime rewrite loop"
            .to_string();
    };

    if let Some(reason) = source_provenance.source_rewrite_authority_blocker_reason() {
        return reason;
    }

    source_provenance
        .summary()
        .typed_diagnostics()
        .into_iter()
        .next()
        .map(|diagnostic| diagnostic.message)
        .unwrap_or_else(|| {
            "binary source provenance is present but not effective for source backpropagation"
                .to_string()
        })
}

pub(super) fn source_backpropagation_allowed_for_result(
    result: &VerificationResult,
    source_provenance: Option<&RuntimeBinarySourceProvenance>,
) -> bool {
    !is_binary_derived_result(result)
        || exact_binary_source_mapping_matches_result(result, source_provenance)
}

fn binary_source_backpropagation_allowed(
    source_provenance: Option<&RuntimeBinarySourceProvenance>,
) -> bool {
    source_provenance
        .is_some_and(RuntimeBinarySourceProvenance::effective_source_backpropagation_allowed)
}

fn exact_binary_source_mapping_matches_result(
    result: &VerificationResult,
    source_provenance: Option<&RuntimeBinarySourceProvenance>,
) -> bool {
    let Some(location) = result.location.as_ref() else {
        return false;
    };
    if location.is_binary() {
        return false;
    }

    let Some(address) = binary_address_for_result(result) else {
        return false;
    };
    source_provenance
        .and_then(|provenance| provenance.exact_source_span_for_address(address))
        .is_some_and(|source| source == location)
}

fn binary_address_for_result(result: &VerificationResult) -> Option<u64> {
    result
        .location
        .as_ref()
        .and_then(SourceSpan::binary_address_value)
        .or_else(|| extract_binary_address(&result.raw_line))
        .or_else(|| result.reason.as_deref().and_then(extract_binary_address))
}

fn extract_binary_address(text: &str) -> Option<u64> {
    let (_, after_prefix) = text.split_once("binary:0x")?;
    let hex: String = after_prefix.chars().take_while(|ch| ch.is_ascii_hexdigit()).collect();
    (!hex.is_empty()).then(|| u64::from_str_radix(&hex, 16).ok()).flatten()
}

pub(super) fn is_binary_derived_result(result: &VerificationResult) -> bool {
    is_binary_only_path(&result.function)
        || result.location.as_ref().is_some_and(|span| is_binary_only_path(&span.file))
        || binary_address_for_result(result).is_some()
}

#[cfg(test)]
pub(super) fn has_binary_only_location(result: &VerificationResult) -> bool {
    result.location.as_ref().is_some_and(|span| is_binary_only_path(&span.file))
}

pub(super) fn is_binary_only_path(path: &str) -> bool {
    path.starts_with("binary:") || path.starts_with("binary::")
}
