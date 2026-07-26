// Runtime exact source/type-fact ownership artifact validation.
//
// Imports the exact-ownership artifact emitted by the offline pipeline and
// checks that it agrees with the runtime binary source provenance mappings
// and the binary verification evidence before allowing source rewrites.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use trust_types::SourceSpan;

use super::digests::{
    canonical_prefixed_sha256, digest_list_contains, expected_binary_artifact_identity,
    require_canonical_sha256_digest, require_digest_membership,
    require_nonempty_canonical_digest_list, sha256_digests_equal,
};
use super::mapping::RuntimeBinarySourceMapping;

pub(super) const EXACT_SOURCE_TYPE_OWNERSHIP_SCHEMA_VERSION: &str =
    "targo-trust.exact-source-type-ownership.v1";

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct RuntimeExactSourceTypeOwnershipSummary {
    pub(crate) artifact_digest: String,
    pub(crate) source_provenance_artifact_digest: String,
    pub(crate) type_fact_digests: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct RuntimeExactSourceTypeOwnershipArtifact {
    pub(crate) schema_version: String,
    pub(crate) status: String,
    #[serde(default, alias = "digest", alias = "sha256")]
    pub(crate) artifact_digest: Option<String>,
    #[serde(default, alias = "binary_sha256")]
    pub(crate) binary_digest: Option<String>,
    #[serde(default)]
    pub(crate) selected_image: Option<trust_types::BinarySelectedImageIdentity>,
    #[serde(default)]
    pub(crate) source_provenance_artifact_digest: Option<String>,
    #[serde(default)]
    pub(crate) type_fact_digests: Vec<String>,
    #[serde(default)]
    pub(crate) checked_proof_identifiers: RuntimeExactSourceTypeOwnershipProofIdentifiers,
    #[serde(default, alias = "ownership")]
    pub(crate) ownership_rows: Vec<RuntimeExactSourceTypeOwnershipRow>,
    #[serde(default)]
    pub(crate) ambiguous_ownership_count: usize,
    #[serde(default)]
    pub(crate) blockers: Vec<String>,
}

#[derive(Debug, Clone, Default, Deserialize)]
pub(crate) struct RuntimeExactSourceTypeOwnershipProofIdentifiers {
    #[serde(default, alias = "dispatch_ids")]
    pub(crate) solver_dispatch_ids: Vec<String>,
    #[serde(default, alias = "checked_certificate_digests")]
    pub(crate) checked_certificate_sha256: Vec<String>,
    #[serde(default)]
    pub(crate) production_checker_evidence_sha256: Vec<String>,
    #[serde(default)]
    pub(crate) source_backpropagation_gate_sha256: Vec<String>,
    #[serde(default, alias = "replay_transcript_sha256")]
    pub(crate) replay_transcript_digests: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct RuntimeExactSourceTypeOwnershipRow {
    pub(crate) binary_address: u64,
    #[serde(default)]
    pub(crate) source: Option<SourceSpan>,
    #[serde(default)]
    pub(crate) source_provenance_record_digest: Option<String>,
    #[serde(default)]
    pub(crate) type_fact_digest: Option<String>,
    #[serde(default, alias = "dispatch_id")]
    pub(crate) solver_dispatch_id: Option<String>,
}

impl RuntimeExactSourceTypeOwnershipArtifact {
    pub(super) fn accepted_handoff(
        &self,
        mappings: &BTreeMap<u64, RuntimeBinarySourceMapping>,
        imported_source_provenance_artifact_digest: Option<&str>,
        verification: &trust_types::BinaryVerificationSummary,
    ) -> Result<RuntimeExactSourceTypeOwnershipSummary, Vec<String>> {
        let mut blockers = self.handoff_blockers(
            mappings,
            imported_source_provenance_artifact_digest,
            verification,
        );
        if !blockers.is_empty() {
            for blocker in &mut blockers {
                *blocker =
                    format!("exact-source-type-ownership-runtime-handoff-rejected: {blocker}");
            }
            return Err(blockers);
        }

        Ok(RuntimeExactSourceTypeOwnershipSummary {
            artifact_digest: canonical_prefixed_sha256(
                self.artifact_digest.as_deref().expect("validated ownership artifact digest"),
            )
            .expect("validated ownership artifact digest"),
            source_provenance_artifact_digest: canonical_prefixed_sha256(
                self.source_provenance_artifact_digest
                    .as_deref()
                    .expect("validated source provenance artifact digest"),
            )
            .expect("validated source provenance artifact digest"),
            type_fact_digests: self
                .type_fact_digests
                .iter()
                .map(|digest| {
                    canonical_prefixed_sha256(digest).expect("validated type-fact digest")
                })
                .collect(),
        })
    }

    fn handoff_blockers(
        &self,
        mappings: &BTreeMap<u64, RuntimeBinarySourceMapping>,
        imported_source_provenance_artifact_digest: Option<&str>,
        verification: &trust_types::BinaryVerificationSummary,
    ) -> Vec<String> {
        let mut blockers = Vec::new();

        if self.schema_version != EXACT_SOURCE_TYPE_OWNERSHIP_SCHEMA_VERSION {
            blockers.push(format!(
                "ownership artifact schema_version `{}` is not `{}`",
                self.schema_version, EXACT_SOURCE_TYPE_OWNERSHIP_SCHEMA_VERSION
            ));
        }
        if self.status != "accepted" {
            blockers.push(format!("ownership artifact status `{}` is not accepted", self.status));
        }
        if self.ambiguous_ownership_count > 0 {
            blockers.push(format!(
                "ownership artifact reports {} ambiguous source/type ownership row(s)",
                self.ambiguous_ownership_count
            ));
        }
        if !self.blockers.is_empty() {
            blockers.push(format!(
                "ownership artifact carries blocker(s): {}",
                self.blockers.join("; ")
            ));
        }

        require_canonical_sha256_digest(
            &mut blockers,
            "ownership artifact digest",
            self.artifact_digest.as_deref(),
        );
        require_canonical_sha256_digest(
            &mut blockers,
            "ownership source provenance artifact digest",
            self.source_provenance_artifact_digest.as_deref(),
        );
        require_nonempty_canonical_digest_list(
            &mut blockers,
            "ownership type fact digest",
            &self.type_fact_digests,
        );
        match (
            self.source_provenance_artifact_digest.as_deref(),
            imported_source_provenance_artifact_digest,
        ) {
            (Some(actual), Some(expected)) if sha256_digests_equal(actual, expected) => {}
            (Some(_), Some(_)) => blockers.push(
                "ownership source provenance artifact digest does not match imported source provenance artifact digest"
                    .to_string(),
            ),
            (_, None) => blockers.push(
                "missing imported source provenance artifact digest for ownership binding"
                    .to_string(),
            ),
            (None, _) => {}
        }

        match expected_binary_artifact_identity(mappings) {
            Ok((binary_digest, selected_image)) => {
                match self.binary_digest.as_deref() {
                    Some(actual) if sha256_digests_equal(actual, &binary_digest) => {}
                    Some(_) => blockers.push(
                        "ownership binary digest does not match imported binary artifact digest"
                            .to_string(),
                    ),
                    None => blockers.push("missing ownership binary digest".to_string()),
                }
                match (&self.selected_image, selected_image) {
                    (Some(actual), Some(expected)) if actual == expected => {}
                    (Some(_), Some(_)) => blockers.push(
                        "ownership selected image digest/range does not match imported selected image"
                            .to_string(),
                    ),
                    (None, Some(_)) => {
                        blockers.push("missing ownership selected image digest/range".to_string())
                    }
                    (_, None) => {}
                }
            }
            Err(identity_blockers) => blockers.extend(identity_blockers),
        }

        blockers.extend(self.checked_proof_identifiers.schema_blockers());
        blockers.extend(self.checked_proof_identifiers.mapping_blockers(mappings));
        blockers.extend(self.checked_proof_identifiers.verification_blockers(verification));
        blockers.extend(self.ownership_row_blockers(mappings));

        blockers
    }

    fn ownership_row_blockers(
        &self,
        mappings: &BTreeMap<u64, RuntimeBinarySourceMapping>,
    ) -> Vec<String> {
        let mut blockers = Vec::new();
        if self.ownership_rows.is_empty() {
            blockers.push("ownership artifact has no exact source/type ownership rows".to_string());
            return blockers;
        }
        if self.ownership_rows.len() != mappings.len() {
            blockers.push(format!(
                "ownership artifact row count {} does not match {} imported exact mapping(s)",
                self.ownership_rows.len(),
                mappings.len()
            ));
        }

        let mut by_address: BTreeMap<u64, &RuntimeExactSourceTypeOwnershipRow> = BTreeMap::new();
        for row in &self.ownership_rows {
            if by_address.insert(row.binary_address, row).is_some() {
                blockers.push(format!(
                    "ambiguous duplicate ownership row for binary:0x{:x}",
                    row.binary_address
                ));
                continue;
            }
            blockers.extend(row.schema_blockers());
        }

        for mapping in mappings.values() {
            let Some(row) = by_address.get(&mapping.binary_address) else {
                blockers.push(format!(
                    "missing exact source/type ownership row for binary:0x{:x}",
                    mapping.binary_address
                ));
                continue;
            };
            blockers.extend(row.mapping_blockers(mapping, &self.type_fact_digests));
        }

        blockers
    }
}

impl RuntimeExactSourceTypeOwnershipProofIdentifiers {
    fn schema_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();
        if self.solver_dispatch_ids.iter().all(|id| id.trim().is_empty()) {
            blockers
                .push("ownership checked proof identifiers omit solver dispatch id(s)".to_string());
        }
        require_nonempty_canonical_digest_list(
            &mut blockers,
            "ownership checked certificate digest",
            &self.checked_certificate_sha256,
        );
        require_nonempty_canonical_digest_list(
            &mut blockers,
            "ownership production checker evidence digest",
            &self.production_checker_evidence_sha256,
        );
        require_nonempty_canonical_digest_list(
            &mut blockers,
            "ownership source-backpropagation gate digest",
            &self.source_backpropagation_gate_sha256,
        );
        require_nonempty_canonical_digest_list(
            &mut blockers,
            "ownership replay transcript digest",
            &self.replay_transcript_digests,
        );
        blockers
    }

    fn mapping_blockers(
        &self,
        mappings: &BTreeMap<u64, RuntimeBinarySourceMapping>,
    ) -> Vec<String> {
        let mut blockers = Vec::new();
        for mapping in mappings.values() {
            let label = format!("binary:0x{:x}", mapping.binary_address);
            let evidence = &mapping.proof_evidence;
            if evidence
                .solver_dispatch_id
                .as_deref()
                .is_none_or(|id| !self.solver_dispatch_ids.iter().any(|known| known == id))
            {
                blockers.push(format!(
                    "{label} ownership proof identifiers do not include solver dispatch id"
                ));
            }
            require_digest_membership(
                &mut blockers,
                &format!("{label} ownership checked certificate digest"),
                &self.checked_certificate_sha256,
                evidence.certificate_sha256.as_deref(),
            );
            require_digest_membership(
                &mut blockers,
                &format!("{label} ownership production checker evidence digest"),
                &self.production_checker_evidence_sha256,
                evidence.production_checker_evidence_sha256.as_deref(),
            );
            require_digest_membership(
                &mut blockers,
                &format!("{label} ownership source-backpropagation gate digest"),
                &self.source_backpropagation_gate_sha256,
                evidence.source_backpropagation_gate_sha256.as_deref(),
            );
            require_digest_membership(
                &mut blockers,
                &format!("{label} ownership replay transcript digest"),
                &self.replay_transcript_digests,
                evidence.replay_transcript_digest.as_deref(),
            );
        }
        blockers
    }

    fn verification_blockers(
        &self,
        verification: &trust_types::BinaryVerificationSummary,
    ) -> Vec<String> {
        let mut blockers = Vec::new();
        for solver_dispatch_id in self.solver_dispatch_ids.iter().filter(|id| !id.trim().is_empty())
        {
            let Some(dispatch) = verification
                .solver_dispatch
                .iter()
                .find(|dispatch| dispatch.id == *solver_dispatch_id)
            else {
                blockers.push(format!(
                    "ownership solver dispatch id `{solver_dispatch_id}` is not present in binary verification evidence"
                ));
                continue;
            };
            if !dispatch.canonical_replay_allows_proof_grade() {
                blockers.push(format!(
                    "ownership solver dispatch id `{solver_dispatch_id}` is not proof-grade replay evidence"
                ));
            }
        }
        blockers
    }
}

impl RuntimeExactSourceTypeOwnershipRow {
    fn schema_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();
        if self.source.is_none() {
            blockers.push(format!(
                "ownership row for binary:0x{:x} is missing exact source span",
                self.binary_address
            ));
        }
        require_canonical_sha256_digest(
            &mut blockers,
            &format!(
                "ownership row for binary:0x{:x} source provenance record digest",
                self.binary_address
            ),
            self.source_provenance_record_digest.as_deref(),
        );
        require_canonical_sha256_digest(
            &mut blockers,
            &format!("ownership row for binary:0x{:x} type fact digest", self.binary_address),
            self.type_fact_digest.as_deref(),
        );
        if self.solver_dispatch_id.as_ref().is_none_or(|id| id.trim().is_empty()) {
            blockers.push(format!(
                "ownership row for binary:0x{:x} is missing solver dispatch id",
                self.binary_address
            ));
        }
        blockers
    }

    fn mapping_blockers(
        &self,
        mapping: &RuntimeBinarySourceMapping,
        type_fact_digests: &[String],
    ) -> Vec<String> {
        let mut blockers = Vec::new();
        let label = format!("binary:0x{:x}", mapping.binary_address);

        if self.source.as_ref() != Some(&mapping.source) {
            blockers.push(format!("{label} ownership source span does not match exact mapping"));
        }

        match (
            self.source_provenance_record_digest.as_deref(),
            mapping.provenance_record_digest.as_deref(),
        ) {
            (Some(row_digest), Some(mapping_digest))
                if sha256_digests_equal(row_digest, mapping_digest) => {}
            (Some(_), Some(_)) => blockers.push(format!(
                "{label} ownership source provenance record digest does not match exact mapping"
            )),
            (_, None) => blockers
                .push(format!("{label} exact mapping is missing source provenance record digest")),
            (None, _) => {}
        }

        match self.type_fact_digest.as_deref() {
            Some(digest) if digest_list_contains(type_fact_digests, digest) => {}
            Some(_) => blockers.push(format!(
                "{label} ownership type fact digest is not listed in the ownership artifact"
            )),
            None => {}
        }

        if self.solver_dispatch_id.as_deref()
            != mapping.proof_evidence.solver_dispatch_id.as_deref()
        {
            blockers.push(format!(
                "{label} ownership solver dispatch id does not match exact mapping proof evidence"
            ));
        }

        blockers
    }
}
