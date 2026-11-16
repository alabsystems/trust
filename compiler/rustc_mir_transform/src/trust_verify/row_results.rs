//! Trust (T3 L4, C07r; plan `docs/design/2026-10-11-t3-l4-commit-plan.md` C07r, design
//! `docs/design/2026-10-08-t3-memory-proportional-reconstruction.md` D-VC-1, D-VC-2, I1):
//! a body's verification results, each row carried with its id in the body's [`VcContext`].
//!
//! [`RowResults`] is `VerificationArtifacts::results`. It keeps the
//! `(VerificationCondition, VerificationResult)` rows and their ids in two private lists of
//! equal length. Every reader sees the rows as the slice they always were ([`Deref`], and
//! `for _ in &results`), so no reader changed. A writer has only the operations below, each
//! of which keeps a row and its id together: [`RowResults::intern`] builds the carrier,
//! [`RowResults::set_result`] changes one row's verdict, leaving its VC, and so its id, as
//! they are, and [`RowResults::rewrite`] runs a list writer (one that appends, replaces or
//! rewrites rows) and pairs every row with its id again before it returns. Nothing outside
//! this module can reach either list mutably except inside a rewrite, which ends aligned, so
//! a misalignment cannot be observed outside one (L4-CARRIER-1).
//!
//! The full lane builds the carrier where it rebuilds its rows from the run's evidence, and
//! every writer after that works on it (`collect_full_verification_artifacts_once`), so
//! every results row has an id from its first write on (plan C07r, change 1).
//!
//! THE ROW ORACLE (L4-ORACLE-1) covers every results row. Each row is interned through
//! [`VcContext::push_checked_row`] as it joins the carrier, which compares its
//! materialization with it in every field. With the elision audit on, [`RowResults::check_in`]
//! also reads every id back at the publication seam and compares it with the row as
//! published, which catches a misalignment between building and publishing. Both count under
//! `Oracle::Row` and charge nothing (L4-METER-1). The rows stay authoritative: every reader
//! reads them, so no verdict, row, key or transport byte depends on an id yet.
//!
//! An id is `None` only for a row the context could not hold (a full table, 2^32 entries).
//! Such a row is still carried and read as itself, and the seam's check counts it as a
//! disagreement.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::ops::Deref;

use trust_types::vc_context::{Oracle, RowId, VcContext, same_row};
use trust_types::{VerificationCondition, VerificationResult};

/// One results row: the VC and its verdict.
type ResultRow = (VerificationCondition, VerificationResult);

/// A body's results rows and their ids, aligned (module docs).
#[derive(Clone, Debug, Default)]
pub(crate) struct RowResults {
    rows: Vec<ResultRow>,
    ids: Vec<Option<RowId>>,
}

/// Whether row `id` of `context` reads back as `vc` in every field. `None` never does.
fn reads_back(context: &VcContext, id: Option<RowId>, vc: &VerificationCondition) -> bool {
    id.is_some_and(|id| {
        context.materialize(id).is_ok_and(|materialized| same_row(materialized.vc(), vc))
    })
}

impl RowResults {
    /// The carrier of `rows`, each row interned into `context` through the row oracle.
    pub(super) fn intern(context: &mut VcContext, rows: Vec<ResultRow>) -> Self {
        let ids = rows.iter().map(|(vc, _)| context.push_checked_row(vc).ok()).collect();
        Self { rows, ids }
    }

    /// Replace row `index`'s verdict and return the one it had; `None`, and nothing
    /// changes, when there is no row `index`. The row's VC, and so its id, stays.
    pub(super) fn set_result(
        &mut self,
        index: usize,
        result: VerificationResult,
    ) -> Option<VerificationResult> {
        let (_, verdict) = self.rows.get_mut(index)?;
        Some(std::mem::replace(verdict, result))
    }

    /// Run `write` over the rows as a list (and the body's context, for a writer that
    /// interns rows of its own), then pair every row with its id again: the one way a
    /// writer that appends, replaces or rewrites rows works on the carrier.
    ///
    /// A row that still reads back from its position's previous id in every field keeps
    /// that id, uncounted (it is not joining: a verdict change moves no id). Every other
    /// row, one `write` appended or changed or one an insertion moved, joins `context`
    /// through the row oracle, as [`Self::intern`] interns it, under a new id. So the
    /// carrier is aligned again when this returns, whatever `write` did. Each call reads
    /// every row back once; a verdict-only writer on [`Self::set_result`] would not.
    pub(super) fn rewrite<R>(
        &mut self,
        context: &mut VcContext,
        write: impl FnOnce(&mut Vec<ResultRow>, &mut VcContext) -> R,
    ) -> R {
        let out = write(&mut self.rows, &mut *context);
        let previous = std::mem::take(&mut self.ids);
        let mut ids = Vec::with_capacity(self.rows.len());
        for (index, (vc, _)) in self.rows.iter().enumerate() {
            let previous_id = previous.get(index).copied().flatten();
            let id = if reads_back(context, previous_id, vc) {
                previous_id
            } else {
                context.push_checked_row(vc).ok()
            };
            ids.push(id);
        }
        self.ids = ids;
        out
    }

    /// The row oracle over the carrier as it stands: each row's id is read back from
    /// `context`, the context the ids were interned into, and compared with the row in
    /// every field, one count under `Oracle::Row` per row. A row with no id counts as a
    /// disagreement. Reads only, apart from the count.
    pub(super) fn check_in(&self, context: &VcContext) {
        for ((vc, _), id) in self.rows.iter().zip(self.ids.iter().copied()) {
            context.record_parity(Oracle::Row, !reads_back(context, id, vc));
        }
    }

    /// Each row's id, in row order.
    #[cfg(test)]
    pub(super) fn ids(&self) -> &[Option<RowId>] {
        &self.ids
    }

    /// Whether every row's id reads back from `context` as the row: the alignment the
    /// carrier promises. Reads only; counts nothing.
    #[cfg(test)]
    pub(super) fn aligned_in(&self, context: &VcContext) -> bool {
        self.rows.len() == self.ids.len()
            && self.rows.iter().zip(&self.ids).all(|((vc, _), &id)| reads_back(context, id, vc))
    }

    /// Swap the ids of rows `a` and `b`: the misalignment a negative control plants.
    #[cfg(test)]
    pub(super) fn misalign_for_test(&mut self, a: usize, b: usize) {
        if a < self.ids.len() && b < self.ids.len() {
            self.ids.swap(a, b);
        }
    }
}

impl Deref for RowResults {
    type Target = [ResultRow];

    fn deref(&self) -> &[ResultRow] {
        &self.rows
    }
}

impl<'a> IntoIterator for &'a RowResults {
    type Item = &'a ResultRow;
    type IntoIter = std::slice::Iter<'a, ResultRow>;

    fn into_iter(self) -> Self::IntoIter {
        self.rows.iter()
    }
}

#[cfg(test)]
mod tests;
