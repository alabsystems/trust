//! Bounded mathematical proof DATA from a fresh, opaque checked presentation.
//!
//! This leaf neither selects a publication nor creates caller/optimizer proof
//! authority. The parent retains the complete Original while it checks native
//! member debt, source/model coverage, the exact proposed row inventory, and
//! the original publication clock. Only that parent may atomically apply these
//! patches after its remaining fit/currentness checks. Saved capsule bytes,
//! grades and booleans cannot construct `CheckedPresentation`.

use super::*;
use clean_auto::bridge::ay_contract::serialize_term;
use sha2::{Digest, Sha256};
use std::io::{self, Write};
use trust_certify::calculus_row::CalculusRowClaim;
use trust_certify::calculus_row::hints::CheckedPresentation;
use trust_types::authority_grade::{
    CALCULUS_ROW_PREMISES, GradeDischarge, GradeEncoding, ObligationGrade,
};
use trust_types::determinism::StopCause;

const CAPSULE_SCHEMA: &str = "trust.vf5-model-proof.v1";
const CAPSULE_FORMAT: &str = "trust-vf5-model-proof-v1";

/// Narrow, nonserialized DATA patches, never a proof capability or a verdict.
/// Private fields prevent callers from substituting a partial successful loop.
pub(super) struct PreparedCalculusRows {
    rows: Vec<(usize, TransportObligationResult)>,
}

impl PreparedCalculusRows {
    pub(super) fn into_rows(self) -> Vec<(usize, TransportObligationResult)> { self.rows }
}

/// The four exact terms which the reference entry actually checked. The
/// maintained codec has its own finite 64 MiB / 2M-node / 4096-depth limits.
/// It has no mid-call stop hook, so every call is bracketed by the ORIGINAL
/// parent's currentness check. No locally renewed deadline or proof is made.
struct Terms {
    goal: Vec<u8>,
    proof: Vec<u8>,
    annotation: Vec<u8>,
    certificates: Vec<u8>,
}

impl Terms {
    fn capture(token: &CheckedPresentation, current: &mut impl FnMut() -> bool) -> Option<Self> {
        let mut total = 0usize;
        let mut encode = |term| {
            if !current() { return None; }
            let bytes = serialize_term(term).ok()?;
            if !current() { return None; }
            total = total.checked_add(bytes.len())?;
            if total > trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES {
                return None;
            }
            Some(bytes)
        };
        Some(Self {
            goal: encode(token.goal())?,
            proof: encode(token.proof())?,
            annotation: encode(token.annotation())?,
            certificates: encode(token.certificates())?,
        })
    }
}

/// This format is a VF5 MODEL judgment, not a source-VC equivalence proof,
/// CleanCic/CertifiedPayload, legacy certificate, or materialized source file.
/// The exact goal/proof include the claimed artifact bytes; its separate SHA
/// is a correlation aid, never a reference to an invented external payload.
#[derive(serde::Serialize)]
struct Capsule<'a> {
    schema: &'static str,
    judgment: &'static str,
    artifact_sha256: &'a str,
    fid: u64,
    symbol: &'a [u8],
    environment_sha256: &'a str,
    statement_sha256: &'a str,
    term_codec: &'static str,
    goal: &'a [u8],
    proof: &'a [u8],
    annotation: &'a [u8],
    certificates: &'a [u8],
    premises: [&'static str; 3],
    // Preserve the entire original evidence record as DATA. None of it is
    // promoted into the calculus proof, and no member provenance is lost.
    original_evidence: Option<&'a TransportProofEvidence>,
}

/// Bounds actual accumulated JSON bytes/allocation BEFORE growth. Poll once
/// per 4 KiB (and at entry/finish), rather than once per serde numeric byte.
struct BoundedBytes<'a, F> {
    bytes: Vec<u8>,
    limit: usize,
    since_poll: usize,
    current: &'a mut F,
}

impl<'a, F: FnMut() -> bool> BoundedBytes<'a, F> {
    fn new(limit: usize, current: &'a mut F) -> Option<Self> {
        current().then_some(Self { bytes: Vec::new(), limit, since_poll: 0, current })
    }

    fn finish(self) -> Option<Vec<u8>> {
        (self.current)().then_some(self.bytes)
    }
}

impl<F: FnMut() -> bool> Write for BoundedBytes<'_, F> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if self.since_poll >= 4096 {
            if !(self.current)() {
                return Err(io::Error::new(io::ErrorKind::Interrupted, "VF5 capsule stopped"));
            }
            self.since_poll = 0;
        }
        let needed = self.bytes.len().checked_add(bytes.len())
            .filter(|needed| *needed <= self.limit)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "VF5 capsule exceeds transport cap"))?;
        if needed > self.bytes.capacity() {
            let capacity = needed.checked_next_power_of_two().unwrap_or(self.limit).min(self.limit);
            self.bytes.try_reserve_exact(capacity - self.bytes.len()).map_err(io::Error::other)?;
        }
        self.bytes.extend_from_slice(bytes);
        self.since_poll = self.since_poll.saturating_add(bytes.len());
        Ok(bytes.len())
    }

    fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}

fn held(row: &TransportObligationResult) -> bool {
    // The SAME established negative markers as
    // `result_is_held_assert_refutation`; text never grants positive credit.
    row.reason.as_deref().is_some_and(|reason| {
        reason == TRUST_HELD_ASSERT_REFUTATION_REASON
            || reason.starts_with(trust_vcgen::GENERIC_REFUTATION_HELD_PREFIX)
    })
}

fn eligible(row: &TransportObligationResult) -> bool {
    matches!(row.outcome, Outcome::Unknown | Outcome::RuntimeChecked | Outcome::Proved)
        && matches!(StopCause::of_outcome(row.outcome, row.reason.as_deref()),
            StopCause::Solved | StopCause::SolverIncomplete | StopCause::Unclassified)
        && !held(row)
        && !row.design_mandate
        && row.gap_class.is_none()
        && row.assumes.is_empty()
        && row.counterexample.is_none()
        && row.counterexample_model.is_none()
        && row.grade.as_ref().is_none_or(|grade| {
            grade.discharge != GradeDischarge::Assumed && grade.admitted().is_ok()
        })
        && row.proof_evidence.as_ref().is_none_or(|evidence| {
            matches!(evidence.status, TransportProofStatus::Unknown | TransportProofStatus::Proved)
        })
}

fn calculus_grade(original: &TransportObligationResult) -> ObligationGrade {
    let mut grade = ObligationGrade::new(
        GradeEncoding::ProvenCalculus, GradeDischarge::KernelReferenceChecked,
        &CALCULUS_ROW_PREMISES,
    );
    // Retaining extra original premises can only constrain this disclosure;
    // an artifact theorem cannot erase a source premise already reported.
    if let Some(original) = &original.grade {
        for premise in &original.premises { grade = grade.with_premise(*premise); }
    }
    grade
}

/// `published_indices` must come from the parent's exact, authenticated
/// source/native/member inventory. This leaf checks only their DATA shape;
/// neither an index, a public grade nor the token alone pays that native debt.
pub(super) fn prepare(
    token: &CheckedPresentation,
    claim: &CalculusRowClaim,
    original: &[TransportObligationResult],
    published_indices: &[usize],
    mut still_current: impl FnMut() -> bool,
) -> Option<PreparedCalculusRows> {
    if !still_current() || published_indices.is_empty() || !token.matches_claim(claim)
        || !still_current()
    {
        return None;
    }
    // A held/refuted/timed-out NONcandidate still belongs to the whole
    // function. Do not erase it merely because some other rows have a token.
    for row in original {
        if !still_current() || held(row)
            || matches!(row.outcome, Outcome::Failed | Outcome::Timeout | Outcome::Canceled)
        {
            return None;
        }
    }
    let mut seen = FxHashSet::default();
    seen.try_reserve(published_indices.len()).ok()?;
    for index in published_indices {
        if !still_current() || !seen.insert(*index) || !eligible(original.get(*index)?) {
            return None;
        }
    }
    let terms = Terms::capture(token, &mut still_current)?;
    let artifact_sha256 = hex(&token.artifact_sha256());
    let environment_sha256 = hex(&token.environment_sha256());
    let statement_sha256 = hex(&token.statement_sha256());
    let mut rows = Vec::new();
    rows.try_reserve(published_indices.len()).ok()?;
    let mut materialized_bytes = 0u64;
    for index in published_indices {
        if !still_current() { return None; }
        let original_row = original.get(*index)?;
        let capsule = Capsule {
            schema: CAPSULE_SCHEMA, judgment: "VF5.RowProved",
            artifact_sha256: &artifact_sha256, fid: token.fid(), symbol: token.symbol(),
            environment_sha256: &environment_sha256, statement_sha256: &statement_sha256,
            term_codec: "clean-canonical-bincode2-standard",
            goal: &terms.goal, proof: &terms.proof, annotation: &terms.annotation,
            certificates: &terms.certificates,
            premises: CALCULUS_ROW_PREMISES.map(|premise| premise.as_str()),
            original_evidence: original_row.proof_evidence.as_ref(),
        };
        let mut writer = BoundedBytes::new(
            trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES, &mut still_current,
        )?;
        serde_json::to_writer(&mut writer, &capsule).ok()?;
        let bytes = writer.finish()?;
        materialized_bytes = materialized_bytes.checked_add(u64::try_from(bytes.len()).ok()?)?;
        // This is the EXISTING per-function materialization ceiling, not an
        // independently enlarged pool. Parent fit also counts ALL old+new
        // artifacts before commit and retains Original on a cap failure.
        if materialized_bytes > publication_transport::MAX_FUNCTION_TRANSPORT_MATERIALIZATION_BYTES {
            return None;
        }
        let mut digest = Sha256::new();
        for chunk in bytes.chunks(4096) {
            if !still_current() { return None; }
            digest.update(chunk);
        }
        let digest = hex(&digest.finalize());
        let proof_id = format!("vf5-model:v1:{digest}");
        let materialization = trust_types::TransportArtifactMaterialization::from_exact_bytes(
            &bytes, &proof_id, Vec::new(),
        )?;
        if !still_current() { return None; }
        let strength = ProofStrength::constructive();
        let mut row = original_row.clone();
        row.outcome = Outcome::Proved;
        row.solver = CALCULUS_ROW_SOLVER.to_string();
        row.reason = None;
        row.counterexample = None;
        row.counterexample_model = None;
        row.grade = Some(calculus_grade(original_row));
        row.proof_evidence = Some(TransportProofEvidence {
            suite: "trust-certify".into(), backend: CALCULUS_ROW_SOLVER.into(),
            request_id: None, proof_id: Some(proof_id.clone()), native_id: None,
            status: TransportProofStatus::Proved,
            strength: Some(strength.clone()), evidence: Some(trust_types::ProofEvidence::from(strength)),
            artifacts: vec![TransportEvidenceArtifact {
                kind: "vf5_model_proof".into(), format: Some(CAPSULE_FORMAT.into()),
                artifact_id: Some(proof_id),
                digest: Some(TransportArtifactDigest { algorithm: "sha256".into(), value: digest }),
                uri: None, materialization: Some(materialization), metadata: None,
            }],
            diagnostics: vec![transport_diagnostic(
                "vf5_model_judgment", TransportEvidenceDiagnosticSeverity::Info,
                "reference-checked VF5 model judgment; SemR translation, target kappa and closed-world entry remain explicit premises; no source-VC equivalence or CertifiedPayload is asserted",
            )],
        });
        rows.push((*index, row));
    }
    if !still_current() { return None; }
    Some(PreparedCalculusRows { rows })
}

#[cfg(test)]
mod tests;
