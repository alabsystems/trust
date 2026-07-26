// SHA-256 digest helpers and binary artifact identity validation shared by the
// runtime binary source provenance subsystem.

use std::collections::BTreeMap;

use super::mapping::RuntimeBinarySourceMapping;

pub(super) fn checked_certificate_sha256(
    certificate: &trust_types::ProofCertificateStatus,
) -> Option<&str> {
    match certificate {
        trust_types::ProofCertificateStatus::Checked { sha256: Some(sha256), .. } => {
            Some(sha256.as_str())
        }
        _ => None,
    }
}

pub(super) fn production_checker_evidence_sha256(
    certificate: &trust_types::ProofCertificateStatus,
) -> Option<String> {
    certificate
        .production_checker_evidence()
        .map(|evidence| evidence.production_checker_evidence_sha256)
}

pub(super) fn expected_binary_artifact_identity(
    mappings: &BTreeMap<u64, RuntimeBinarySourceMapping>,
) -> Result<(String, Option<&trust_types::BinarySelectedImageIdentity>), Vec<String>> {
    let mut blockers = Vec::new();
    let mut expected_root = None;
    let mut expected_selected = None;

    for mapping in mappings.values() {
        let label = format!("binary:0x{:x}", mapping.binary_address);
        let Some(identity) = mapping.binary_artifact_digest_identity.as_ref() else {
            blockers.push(format!("{label} exact mapping is missing binary artifact identity"));
            continue;
        };
        for blocker in identity.digest_identity_blockers() {
            blockers.push(format!("{label} binary artifact identity: {blocker}"));
        }

        if let Some(root) = identity.root_artifact_digest.as_ref() {
            let prefixed = format!("{}:{}", root.algorithm, root.value);
            match &expected_root {
                Some(existing) if existing != &prefixed => blockers.push(
                    "imported exact mappings do not agree on binary artifact digest".to_string(),
                ),
                Some(_) => {}
                None => expected_root = Some(prefixed),
            }
        }

        if let Some(selected) = identity.selected_image.as_ref() {
            match expected_selected {
                Some(existing) if existing != selected => blockers.push(
                    "imported exact mappings do not agree on selected image digest/range"
                        .to_string(),
                ),
                Some(_) => {}
                None => expected_selected = Some(selected),
            }
        }
    }

    if let Some(root) = expected_root {
        if blockers.is_empty() { Ok((root, expected_selected)) } else { Err(blockers) }
    } else {
        blockers.push("imported exact mappings have no binary artifact digest".to_string());
        Err(blockers)
    }
}

pub(super) fn require_canonical_optional_sha256(
    blockers: &mut Vec<String>,
    label: &str,
    digest: Option<&str>,
) {
    match digest {
        Some(digest) if is_canonical_sha256_hex(digest) => {}
        Some(_) => blockers.push(format!("{label} is not canonical SHA-256 hex")),
        None => blockers.push(format!("missing {label}")),
    }
}

pub(super) fn require_canonical_sha256_digest(
    blockers: &mut Vec<String>,
    label: &str,
    digest: Option<&str>,
) {
    match digest {
        Some(digest) if canonical_sha256_hex_from_digest(digest).is_some() => {}
        Some(_) => blockers.push(format!("{label} is not canonical SHA-256 digest")),
        None => blockers.push(format!("missing {label}")),
    }
}

pub(super) fn require_nonempty_canonical_digest_list(
    blockers: &mut Vec<String>,
    label: &str,
    digests: &[String],
) {
    if digests.is_empty() {
        blockers.push(format!("missing {label} list"));
        return;
    }
    for digest in digests {
        require_canonical_sha256_digest(blockers, label, Some(digest));
    }
}

pub(super) fn require_digest_membership(
    blockers: &mut Vec<String>,
    label: &str,
    digests: &[String],
    expected: Option<&str>,
) {
    match expected {
        Some(expected) if digest_list_contains(digests, expected) => {}
        Some(_) => {
            blockers.push(format!("{label} is not listed in ownership checked proof identifiers"))
        }
        None => blockers.push(format!("missing {label} in exact mapping proof evidence")),
    }
}

pub(super) fn digest_list_contains(digests: &[String], expected: &str) -> bool {
    digests.iter().any(|digest| sha256_digests_equal(digest, expected))
}

pub(super) fn sha256_digests_equal(left: &str, right: &str) -> bool {
    match (canonical_sha256_hex_from_digest(left), canonical_sha256_hex_from_digest(right)) {
        (Some(left), Some(right)) => left == right,
        _ => false,
    }
}

pub(super) fn canonical_prefixed_sha256(value: &str) -> Option<String> {
    canonical_sha256_hex_from_digest(value).map(|hex| format!("sha256:{hex}"))
}

pub(super) fn canonical_sha256_hex_from_digest(value: &str) -> Option<&str> {
    let hex = value.strip_prefix("sha256:").unwrap_or(value);
    is_canonical_sha256_hex(hex).then_some(hex)
}

pub(super) fn is_canonical_sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value.bytes().all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}
