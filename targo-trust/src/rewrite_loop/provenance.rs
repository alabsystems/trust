// Runtime binary source provenance: checked binary identity, exact mappings,
// and the gate that decides whether binary-derived diagnostics may drive source
// rewrites.

use std::collections::BTreeMap;

use trust_types::{BinarySourceProvenanceSummary, SourceSpan};

use super::digests::{canonical_sha256_hex_from_digest, sha256_digests_equal};
use super::identity::RuntimeBinarySourceIdentity;
use super::mapping::RuntimeBinarySourceMapping;
use super::ownership::{
    RuntimeExactSourceTypeOwnershipArtifact, RuntimeExactSourceTypeOwnershipSummary,
};

#[derive(Debug, Clone)]
struct RuntimeBinarySourceRewriteAuthority {
    checked_and_proof_grade: bool,
    diagnostics: Vec<String>,
}

impl RuntimeBinarySourceRewriteAuthority {
    fn unchecked() -> Self {
        Self {
            checked_and_proof_grade: false,
            diagnostics: vec![
                "source rewrite authority is unchecked: no proof-grade binary verification, exact replay, checked certificate source-backpropagation gate, and accepted reconstruction/target-validation evidence was imported; diagnostics remain binary-address-only"
                    .to_string(),
            ],
        }
    }

    fn allows_source_rewrites(&self) -> bool {
        self.checked_and_proof_grade
    }

    fn blocker_reason(&self) -> Option<String> {
        (!self.checked_and_proof_grade).then(|| {
            self.diagnostics
                .iter()
                .find(|diagnostic| !diagnostic.trim().is_empty())
                .cloned()
                .unwrap_or_else(|| {
                    "source rewrite authority is not checked by proof-grade binary backpropagation evidence; diagnostics remain binary-address-only"
                        .to_string()
                })
        })
    }
}

#[derive(Debug, Clone)]
pub(crate) struct RuntimeBinarySourceProvenance {
    summary: BinarySourceProvenanceSummary,
    checked_binary_identity: RuntimeBinarySourceIdentity,
    exact_mappings: BTreeMap<u64, RuntimeBinarySourceMapping>,
    source_rewrite_authority: RuntimeBinarySourceRewriteAuthority,
    exact_source_type_ownership: Option<RuntimeExactSourceTypeOwnershipSummary>,
}

impl RuntimeBinarySourceProvenance {
    #[cfg(test)]
    pub(crate) fn new(
        summary: BinarySourceProvenanceSummary,
        mappings: Vec<RuntimeBinarySourceMapping>,
    ) -> Self {
        Self::new_with_checked_binary_identity(
            summary,
            RuntimeBinarySourceIdentity::default(),
            mappings,
        )
    }

    pub(crate) fn new_with_checked_binary_identity(
        summary: BinarySourceProvenanceSummary,
        checked_binary_identity: RuntimeBinarySourceIdentity,
        mappings: Vec<RuntimeBinarySourceMapping>,
    ) -> Self {
        let mut exact_mappings = BTreeMap::new();
        let mut duplicate_addresses = Vec::new();
        for mapping in mappings {
            let binary_address = mapping.binary_address;
            if exact_mappings.insert(binary_address, mapping).is_some() {
                duplicate_addresses.push(binary_address);
            }
        }

        let mut summary = summary;
        let imported_mapping_count = exact_mappings.len();
        if summary.exact_mapping_count != imported_mapping_count {
            summary.source_backpropagation_allowed = false;
            summary.diagnostics.push(format!(
                "binary source provenance artifact exact_mapping_count={} does not match {} imported exact mapping(s); source backpropagation rejected",
                summary.exact_mapping_count, imported_mapping_count
            ));
        }
        if !duplicate_addresses.is_empty() {
            summary.source_backpropagation_allowed = false;
            summary.ambiguous_mapping_count += duplicate_addresses.len();
            summary.diagnostics.push(format!(
                "binary source provenance artifact has ambiguous duplicate mapping(s) for {}",
                duplicate_addresses
                    .into_iter()
                    .map(|address| format!("0x{address:x}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }

        Self {
            summary,
            checked_binary_identity,
            exact_mappings,
            source_rewrite_authority: RuntimeBinarySourceRewriteAuthority::unchecked(),
            exact_source_type_ownership: None,
        }
    }

    pub(crate) fn summary(&self) -> &BinarySourceProvenanceSummary {
        &self.summary
    }

    #[cfg(test)]
    pub(crate) fn checked_binary_identity(&self) -> &RuntimeBinarySourceIdentity {
        &self.checked_binary_identity
    }

    #[allow(dead_code)]
    pub(crate) fn with_checked_binary_backpropagation_evidence(
        self,
        verification: &trust_types::BinaryVerificationSummary,
        reconstruction: &trust_types::ReconstructionSummary,
        source_gate: &trust_backprop::BinarySourceBackpropagationGateDetails,
    ) -> Self {
        self.with_imported_binary_backpropagation_evidence(
            verification,
            Some(reconstruction),
            Some(source_gate),
        )
    }

    pub(crate) fn with_imported_binary_backpropagation_evidence(
        mut self,
        verification: &trust_types::BinaryVerificationSummary,
        reconstruction: Option<&trust_types::ReconstructionSummary>,
        source_gate: Option<&trust_backprop::BinarySourceBackpropagationGateDetails>,
    ) -> Self {
        self = self.with_imported_binary_backpropagation_evidence_and_source_gate_identity(
            verification,
            reconstruction,
            source_gate,
            None,
        );
        self
    }

    pub(crate) fn with_imported_binary_backpropagation_evidence_and_source_gate_identity(
        mut self,
        verification: &trust_types::BinaryVerificationSummary,
        reconstruction: Option<&trust_types::ReconstructionSummary>,
        source_gate: Option<&trust_backprop::BinarySourceBackpropagationGateDetails>,
        source_backpropagation_gate_sha256: Option<&str>,
    ) -> Self {
        let evidence = trust_backprop::BinaryBackpropEvidence::new(&self.summary, verification);
        let evidence = if let Some(reconstruction) = reconstruction {
            evidence.with_reconstruction(reconstruction)
        } else {
            evidence
        };
        let evidence = if let Some(source_gate) = source_gate {
            evidence.with_certificate_source_backpropagation_gate(source_gate)
        } else {
            evidence
        };
        let diagnostics = evidence.rejection_diagnostics();
        let exact_handoff_blockers = self.exact_provenance_proof_handoff_blockers(
            verification,
            source_backpropagation_gate_sha256,
        );
        self.source_rewrite_authority =
            if diagnostics.is_empty() && exact_handoff_blockers.is_empty() {
                RuntimeBinarySourceRewriteAuthority {
                    checked_and_proof_grade: true,
                    diagnostics: Vec::new(),
                }
            } else {
                let mut authority_diagnostics: Vec<String> = diagnostics
                    .iter()
                    .map(trust_backprop::BinaryBackpropRejectionDiagnostic::message)
                    .collect();
                authority_diagnostics.extend(exact_handoff_blockers);
                RuntimeBinarySourceRewriteAuthority {
                    checked_and_proof_grade: false,
                    diagnostics: authority_diagnostics,
                }
            };
        self
    }

    pub(crate) fn with_exact_source_type_ownership_artifact(
        mut self,
        ownership: Option<RuntimeExactSourceTypeOwnershipArtifact>,
        source_provenance_artifact_digest: Option<&str>,
        verification: &trust_types::BinaryVerificationSummary,
    ) -> Self {
        let Some(ownership) = ownership else {
            self.append_source_rewrite_authority_blockers(vec![
                "exact-source-type-ownership-runtime-handoff-rejected: missing exact source/type-fact ownership artifact"
                    .to_string(),
            ]);
            return self;
        };

        match ownership.accepted_handoff(
            &self.exact_mappings,
            source_provenance_artifact_digest,
            verification,
        ) {
            Ok(summary) => self.exact_source_type_ownership = Some(summary),
            Err(blockers) => self.append_source_rewrite_authority_blockers(blockers),
        }
        self
    }

    fn append_source_rewrite_authority_blockers(&mut self, blockers: Vec<String>) {
        if blockers.is_empty() {
            return;
        }
        self.source_rewrite_authority.checked_and_proof_grade = false;
        self.source_rewrite_authority.diagnostics.extend(blockers);
    }

    pub(crate) fn binary_backpropagation_authority_allows_source_rewrites(&self) -> bool {
        self.summary.effective_source_backpropagation_allowed()
            && self.checked_binary_identity.is_checked()
            && !self.exact_mappings.is_empty()
            && self.source_rewrite_authority.allows_source_rewrites()
    }

    pub(crate) fn effective_source_backpropagation_allowed(&self) -> bool {
        self.binary_backpropagation_authority_allows_source_rewrites()
            && self.exact_source_type_ownership.is_some()
    }

    pub(crate) fn source_rewrite_authority_diagnostics(&self) -> &[String] {
        &self.source_rewrite_authority.diagnostics
    }

    pub(crate) fn exact_source_type_ownership_artifact_digest(&self) -> Option<&str> {
        self.exact_source_type_ownership
            .as_ref()
            .map(|ownership| ownership.artifact_digest.as_str())
    }

    pub(super) fn exact_source_span_for_address(&self, address: u64) -> Option<&SourceSpan> {
        self.effective_source_backpropagation_allowed()
            .then(|| self.exact_mappings.get(&address).map(|mapping| &mapping.source))
            .flatten()
    }

    pub(super) fn source_rewrite_authority_blocker_reason(&self) -> Option<String> {
        if !self.summary.effective_source_backpropagation_allowed() {
            return None;
        }
        if let Some(reason) = self.source_rewrite_authority.blocker_reason() {
            return Some(reason);
        }
        let identity_blockers = self.checked_binary_identity.blockers();
        if !identity_blockers.is_empty() {
            return Some(format!(
                "checked binary identity is missing from the imported source provenance artifact: {}",
                identity_blockers.join("; ")
            ));
        }
        if self.exact_source_type_ownership.is_none() {
            return Some(
                "exact source/type-fact ownership artifact is missing; binary-derived rewrite facts remain binary-address-only"
                    .to_string(),
            );
        }
        None
    }

    fn exact_provenance_proof_handoff_blockers(
        &self,
        verification: &trust_types::BinaryVerificationSummary,
        source_backpropagation_gate_sha256: Option<&str>,
    ) -> Vec<String> {
        let mut blockers = Vec::new();
        if source_backpropagation_gate_sha256
            .is_some_and(|digest| canonical_sha256_hex_from_digest(digest).is_none())
        {
            blockers.push(
                "exact-provenance-runtime-handoff-rejected: imported source-backpropagation gate identity digest is not canonical SHA-256"
                    .to_string(),
            );
        }
        for mapping in self.exact_mappings.values() {
            let mapping_label = format!("binary:0x{:x}", mapping.binary_address);
            let mapping_blockers = mapping.canonical_handoff_blockers();
            if !mapping_blockers.is_empty() {
                blockers.extend(mapping_blockers.into_iter().map(|blocker| {
                    format!(
                        "exact-provenance-runtime-handoff-rejected: imported mapping {mapping_label}: {blocker}"
                    )
                }));
                continue;
            }

            if source_backpropagation_gate_sha256.is_some_and(|expected_gate_sha256| {
                !mapping
                    .proof_evidence
                    .source_backpropagation_gate_sha256
                    .as_deref()
                    .is_some_and(|actual| sha256_digests_equal(actual, expected_gate_sha256))
            }) {
                blockers.push(format!(
                    "exact-provenance-runtime-handoff-rejected: imported mapping {mapping_label} source-backpropagation gate identity does not match imported source_backpropagation_gate_sha256"
                ));
                continue;
            }

            if !verification
                .solver_dispatch
                .iter()
                .any(|dispatch| mapping.matches_proof_grade_solver_dispatch(dispatch))
            {
                blockers.push(format!(
                    "exact-provenance-runtime-handoff-rejected: imported mapping {mapping_label} is not bound to a proof-grade replayed solver dispatch with matching binary path, root/selected-image digest identity, function entry, instruction address/size/bytes, source mapping, and proof evidence identifiers"
                ));
            }
        }
        blockers
    }
}
