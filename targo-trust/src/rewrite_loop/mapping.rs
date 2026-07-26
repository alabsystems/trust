// Exact binary-source mapping records and proof-evidence identifiers used by
// the runtime binary source provenance subsystem.

use serde::Deserialize;
use trust_types::{BinaryArtifactDigestIdentity, BinaryOrigin, SourceSpan};

use super::backprop_gate::is_binary_only_path;
use super::digests::{
    checked_certificate_sha256, is_canonical_sha256_hex, production_checker_evidence_sha256,
    require_canonical_optional_sha256,
};

#[derive(Debug, Clone, Deserialize)]
pub(crate) struct RuntimeBinarySourceMapping {
    #[serde(alias = "address", alias = "instruction_address")]
    pub(crate) binary_address: u64,
    #[serde(default)]
    pub(crate) binary_path: Option<String>,
    #[serde(default)]
    pub(crate) function_entry: Option<u64>,
    #[serde(default)]
    pub(crate) instruction_size: Option<u8>,
    #[serde(default)]
    pub(crate) instruction_bytes: Vec<u8>,
    #[serde(default, alias = "binary_digest_identity", alias = "digest_identity")]
    pub(crate) binary_artifact_digest_identity: Option<BinaryArtifactDigestIdentity>,
    #[serde(default)]
    pub(crate) source_status: Option<String>,
    #[serde(default)]
    pub(crate) provenance_status: Option<String>,
    #[serde(default, alias = "record_digest", alias = "provenance_sha256")]
    pub(crate) provenance_record_digest: Option<String>,
    #[serde(default, alias = "proof_evidence", alias = "proof_evidence_identifiers")]
    pub(crate) proof_evidence: RuntimeBinarySourceProofEvidence,
    pub(crate) source: SourceSpan,
}

#[derive(Debug, Clone, Default, Deserialize)]
pub(crate) struct RuntimeBinarySourceProofEvidence {
    #[serde(default, alias = "dispatch_id")]
    pub(crate) solver_dispatch_id: Option<String>,
    #[serde(default, alias = "checked_certificate_sha256")]
    pub(crate) certificate_sha256: Option<String>,
    #[serde(default)]
    pub(crate) production_checker_evidence_sha256: Option<String>,
    #[serde(default)]
    pub(crate) source_backpropagation_gate_sha256: Option<String>,
    #[serde(default)]
    pub(crate) replay_transcript_digest: Option<String>,
}

impl RuntimeBinarySourceMapping {
    pub(super) fn canonical_origin(&self) -> BinaryOrigin {
        BinaryOrigin {
            binary_path: self.binary_path.clone(),
            function_entry: self.function_entry,
            instruction_address: self.binary_address,
            instruction_size: self.instruction_size,
            encoding: None,
            instruction_bytes: self.instruction_bytes.clone(),
            source: Some(self.source.clone()),
        }
    }

    pub(super) fn canonical_handoff_blockers(&self) -> Vec<String> {
        let mut blockers = self.canonical_origin().canonical_provenance_blockers();
        if self.source.file.trim().is_empty() {
            blockers.push("missing source mapping path".to_string());
        } else if is_binary_only_path(&self.source.file) {
            blockers.push("source mapping is still binary-address-only".to_string());
        }

        match self.source_status.as_deref() {
            Some("exact") => {}
            Some(status) => blockers.push(format!(
                "source provenance status `{status}` is not accepted exact provenance"
            )),
            None => blockers.push("missing source provenance status for exact mapping".to_string()),
        }

        match self.provenance_status.as_deref() {
            Some("checked_exact") => {}
            Some(status) => blockers
                .push(format!("binary provenance row status `{status}` is not checked_exact")),
            None => blockers.push("missing checked exact binary provenance row status".to_string()),
        }

        match self.provenance_record_digest.as_deref() {
            Some(digest) if is_canonical_sha256_hex(digest) => {}
            Some(_) => blockers
                .push("binary provenance row digest is not canonical SHA-256 hex".to_string()),
            None => blockers.push("missing binary provenance row digest".to_string()),
        }

        blockers.extend(self.proof_evidence.schema_blockers());

        match &self.binary_artifact_digest_identity {
            Some(identity) => {
                for blocker in identity.digest_identity_blockers() {
                    blockers.push(format!("binary artifact digest identity: {blocker}"));
                }
            }
            None => blockers.push(
                "missing binary artifact digest identity for exact source mapping".to_string(),
            ),
        }

        blockers
    }

    pub(super) fn matches_proof_grade_solver_dispatch(
        &self,
        dispatch: &trust_types::SolverDispatchRecord,
    ) -> bool {
        let Some(origin) = &dispatch.origin else {
            return false;
        };
        let Some(dispatch_identity) = &dispatch.binary_artifact_digest_identity else {
            return false;
        };
        let Some(mapping_identity) = &self.binary_artifact_digest_identity else {
            return false;
        };

        dispatch.canonical_replay_allows_proof_grade()
            && origin.binary_path == self.binary_path
            && origin.function_entry == self.function_entry
            && origin.instruction_address == self.binary_address
            && origin.instruction_size == self.instruction_size
            && origin.instruction_bytes == self.instruction_bytes
            && origin.source.as_ref() == Some(&self.source)
            && dispatch_identity == mapping_identity
            && self.proof_evidence.matches_solver_dispatch(dispatch)
    }
}

impl RuntimeBinarySourceProofEvidence {
    fn schema_blockers(&self) -> Vec<String> {
        let mut blockers = Vec::new();
        if self.solver_dispatch_id.as_ref().is_none_or(|id| id.trim().is_empty()) {
            blockers.push("missing solver dispatch proof evidence id".to_string());
        }
        require_canonical_optional_sha256(
            &mut blockers,
            "checked certificate proof evidence id",
            self.certificate_sha256.as_deref(),
        );
        require_canonical_optional_sha256(
            &mut blockers,
            "production checker proof evidence id",
            self.production_checker_evidence_sha256.as_deref(),
        );
        require_canonical_optional_sha256(
            &mut blockers,
            "checked certificate source-backpropagation gate proof evidence id",
            self.source_backpropagation_gate_sha256.as_deref(),
        );
        require_canonical_optional_sha256(
            &mut blockers,
            "exact replay transcript proof evidence id",
            self.replay_transcript_digest.as_deref(),
        );
        blockers
    }

    fn matches_solver_dispatch(&self, dispatch: &trust_types::SolverDispatchRecord) -> bool {
        self.schema_blockers().is_empty()
            && self.solver_dispatch_id.as_deref() == Some(dispatch.id.as_str())
            && checked_certificate_sha256(&dispatch.certificate)
                == self.certificate_sha256.as_deref()
            && production_checker_evidence_sha256(&dispatch.certificate).as_deref()
                == self.production_checker_evidence_sha256.as_deref()
    }
}
