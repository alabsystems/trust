//! Ordering checks for the diagnostic Lean-island observer. This module does
//! not check Lean, enumerate runtime bodies, or grant compilation authority.
//!
//! Trust (LEAN-CENSUS-IMPORT-BATCH-1): every HIR check is header-first. The
//! pre-walk prefix is one module batch; the deferred `trust_import_*` suffix is
//! TG14's ONE import batch, checked after the program-admission boundary in
//! the lane that actually ran. Both lanes mint admissions (TG3), so both
//! record the boundary.

use std::collections::BTreeSet;

#[derive(Clone, Copy)]
pub(crate) enum CheckPhase {
    HeaderFirst,
    AfterProgramAdmissions,
    VerificationDisabled,
}

#[derive(Default)]
pub(crate) struct IslandCheckOrder {
    spans: Option<Vec<(u32, u32)>>,
    checked: BTreeSet<usize>,
    pre_batch_seen: bool,
    /// Trust (LEAN-CENSUS-IMPORT-BATCH-1): TG14 checks the whole deferred
    /// suffix as ONE header-first import batch, so there is at most one.
    suffix_seen: bool,
    admissions_seen: bool,
    rejected: bool,
}

impl IslandCheckOrder {
    pub(crate) fn inventory(&mut self, spans: Vec<(u32, u32)>) -> Result<(), String> {
        if self.spans.is_some() {
            return Err("duplicate HIR island inventory".into());
        }
        // Keep ambiguous spans: they are genuine HIR observations. The
        // frontend refuses their authored order before performing any check.
        self.spans = Some(spans);
        Ok(())
    }

    /// TG3 (COMPILE-TIME-FACTS-1) mints program admissions in every build,
    /// `-Ztrust-verify=off` included, so the boundary belongs to both lanes.
    pub(crate) fn admissions_boundary(&mut self) -> Result<(), String> {
        if self.spans.is_none() || self.admissions_seen || self.suffix_seen {
            return Err("missing inventory or duplicate admission boundary".into());
        }
        self.admissions_seen = true;
        Ok(())
    }

    pub(crate) fn check(
        &mut self,
        positions: &[(u32, u32)],
        phase: CheckPhase,
        verification: bool,
        rejected: bool,
    ) -> Result<Vec<usize>, String> {
        let spans = self.spans.as_ref().ok_or("check without HIR island inventory")?;
        let suffix = !matches!(phase, CheckPhase::HeaderFirst);
        let phase_allowed = match phase {
            CheckPhase::HeaderFirst => {
                !self.pre_batch_seen && !self.admissions_seen && !self.suffix_seen
            }
            CheckPhase::AfterProgramAdmissions => {
                self.admissions_seen && !self.suffix_seen && verification
            }
            CheckPhase::VerificationDisabled => {
                self.admissions_seen && !self.suffix_seen && !verification
            }
        };
        if positions.is_empty() || !phase_allowed {
            return Err("island check phase/order mismatch".into());
        }
        let mut ids = Vec::new();
        for position in positions {
            let found: Vec<_> = spans
                .iter()
                .enumerate()
                .filter_map(|(id, candidate)| (candidate == position).then_some(id))
                .collect();
            if found.len() != 1 || self.checked.contains(&found[0]) || ids.contains(&found[0]) {
                return Err("missing, ambiguous or duplicated checked island".into());
            }
            // Failed source recovery leaves a genuine inventory hole. Keep
            // later checks in order; only completion demands the exact set.
            if ids.last().or_else(|| self.checked.last()).is_some_and(|last| found[0] <= *last) {
                return Err("island checking differs from inventoried source order".into());
            }
            ids.push(found[0]);
        }
        self.checked.extend(ids.iter().copied());
        self.pre_batch_seen |= !suffix;
        self.suffix_seen |= suffix;
        self.rejected |= rejected;
        Ok(ids)
    }

    /// Trust (LEAN-CENSUS-IMPORT-BATCH-1): a completed analysis reached the
    /// admission mint in either lane, so a missing boundary is a lost phase
    /// whichever lane ran.
    pub(crate) fn completion_count(&self) -> Result<usize, String> {
        let count = self.spans.as_ref().ok_or("missing island inventory at completion")?.len();
        if self.rejected || !self.admissions_seen {
            return Err("rejected language check or missing admission phase at completion".into());
        }
        if self.checked != (0..count).collect() {
            return Err("an inventoried island has no completed language check".into());
        }
        Ok(count)
    }
}

#[cfg(test)]
mod tests;
