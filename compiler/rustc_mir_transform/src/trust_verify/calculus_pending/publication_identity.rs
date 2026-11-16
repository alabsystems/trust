//! Complete original publication inventory, not proof authority. Small live
//! per-row commitments let a refused DATA read fail closed on the actual owed
//! rows after the full native/source/context payloads have been released.

use super::*;
use sha2::{Digest, Sha256};
use std::io::{self, Write};

const ROW_DOMAIN: &[u8] = b"trustc.vf5.original-publication-row.v1\0";

#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(super) struct OwedInventory {
    rows: Vec<OwedRow>,
    counts: [usize; 7],
}

#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct OwedRow {
    identity: [u8; 32],
    outcome: trust_types::Outcome,
    stop: trust_types::determinism::StopCause,
    assumed_discharge: bool,
}

pub(super) struct RowIndex {
    unique: FxHashMap<[u8; 32], usize>,
    ambiguous: FxHashSet<[u8; 32]>,
}

impl RowIndex {
    pub(super) fn unique_row(&self, identity: &[u8; 32]) -> Option<usize> {
        (!self.ambiguous.contains(identity)).then(|| self.unique.get(identity).copied()).flatten()
    }
}

struct Hashing<'a>(&'a mut Sha256);

impl Write for Hashing<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.0.update(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

/// Full typed diagnostic identity, including the actual original VC snapshot
/// when present. This grants no authority: native/candidate approval still
/// comes from the actual original private carriers and complete member join.
pub(super) fn row_identity(row: &TransportObligationResult) -> io::Result<[u8; 32]> {
    let mut hash = Sha256::new();
    hash.update(ROW_DOMAIN);
    serde_json::to_writer(Hashing(&mut hash), &(
        &row.obligation_id, &row.claim_digest_sha256, &row.kind,
        &row.typed_kind, &row.location, &row.description, &row.assumes,
        &row.original_vc_snapshot,
    )).map_err(io::Error::other)?;
    Ok(hash.finalize().into())
}

impl OwedInventory {
    pub(super) fn capture(
        actual: &[TransportObligationResult],
        tally: PublishedRowTally,
        mut may_continue: impl FnMut() -> bool,
    ) -> io::Result<Self> {
        let stopped = || io::Error::new(io::ErrorKind::Interrupted,
            "original publication inventory preparation stopped");
        if !may_continue() { return Err(stopped()); }
        let mut rows = Vec::new();
        rows.try_reserve(actual.len()).map_err(io::Error::other)?;
        for row in actual {
            if !may_continue() { return Err(stopped()); }
            // Materialization and per-row evidence withholding preserve these
            // identity fields. Whole-report replacement separately discloses
            // the withheld original denominator. None is proof authority.
            // Actual candidate eligibility separately reads the full original
            // typed VC/binding/native/member carriers before paired sealing.
            rows.push(OwedRow {
                identity: row_identity(row)?, outcome: row.outcome,
                stop: trust_types::determinism::StopCause::of_outcome(
                    row.outcome, row.reason.as_deref(),
                ),
                assumed_discharge: trust_types::assumption::is_instance_hypothesis_discharge_row(
                    &row.kind, &row.solver,
                ),
            });
        }
        let counts = tally.json_counts();
        if counts.total != rows.len() {
            return Err(io::Error::new(io::ErrorKind::InvalidData,
                "original published tally does not match its complete row inventory"));
        }
        if !may_continue() { return Err(stopped()); }
        Ok(Self { rows, counts: [
            counts.proved, counts.failed, counts.unknown, counts.timed_out,
            counts.skipped, counts.runtime_checked, counts.total,
        ] })
    }

    pub(super) fn total(&self) -> usize { self.rows.len() }

    pub(super) fn row_index(&self, mut may_continue: impl FnMut() -> bool) -> io::Result<RowIndex> {
        let stopped = || io::Error::new(io::ErrorKind::Interrupted,
            "original publication identity indexing stopped");
        if !may_continue() { return Err(stopped()); }
        let mut unique = FxHashMap::default();
        let mut ambiguous = FxHashSet::default();
        unique.try_reserve(self.rows.len()).map_err(io::Error::other)?;
        ambiguous.try_reserve(self.rows.len()).map_err(io::Error::other)?;
        for (index, row) in self.rows.iter().enumerate() {
            if !may_continue() { return Err(stopped()); }
            if ambiguous.contains(&row.identity) { continue; }
            if unique.insert(row.identity, index).is_some() {
                unique.remove(&row.identity);
                ambiguous.insert(row.identity);
            }
        }
        if !may_continue() { return Err(stopped()); }
        Ok(RowIndex { unique, ambiguous })
    }

    pub(super) fn outcome(&self, index: usize) -> Option<trust_types::Outcome> {
        self.rows.get(index).map(|row| row.outcome)
    }

    pub(super) fn stop(&self, index: usize) -> Option<trust_types::determinism::StopCause> {
        self.rows.get(index).map(|row| row.stop)
    }

    /// Added policy rows are not covered by a root/native candidate merely
    /// because their counts reconcile. Retain every independent assumption,
    /// runtime check, refusal and unproved row in the original policy.
    pub(super) fn independently_proved(&self, index: usize) -> bool {
        self.rows.get(index).is_some_and(|row| {
            row.outcome == Outcome::Proved && !row.assumed_discharge
        })
    }

    /// A diagnostic/data-integrity commitment only. Equality cannot establish
    /// any row's truth or replace exact private native-debt validation.
    pub(super) fn digest(&self) -> [u8; 32] {
        let mut hash = Sha256::new();
        hash.update(b"trustc.vf5.original-publication-inventory.v1\0");
        for count in self.counts { hash.update((count as u64).to_le_bytes()); }
        for row in &self.rows {
            hash.update(row.identity);
            hash.update([u8::from(row.assumed_discharge)]);
            for text in [row.outcome.as_str(), row.stop.as_str()] {
                hash.update((text.len() as u64).to_le_bytes());
                hash.update(text.as_bytes());
            }
        }
        hash.finalize().into()
    }
}
