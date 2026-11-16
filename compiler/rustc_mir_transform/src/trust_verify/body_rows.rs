//! Trust (T3 L4, C07; plan `docs/design/2026-10-11-t3-l4-commit-plan.md` C07, design
//! `docs/design/2026-10-08-t3-memory-proportional-reconstruction.md` D-VC-1, D-VC-6, I1):
//! a body's consumed solver rows, each carried with its id in the body's [`VcContext`].
//!
//! [`BodyRows`] keeps the eager VCs and their ids in two private lists of equal length,
//! and offers only the operations the consumed path performs on them, each of which moves
//! a row and its id together: [`BodyRows::extend`], [`BodyRows::filter`],
//! [`BodyRows::dedupe_by`] and [`BodyRows::flip`]. An operation it does not offer cannot
//! misalign them, because nothing outside this module can reach either list mutably.
//!
//! THE ROW ORACLE (L4-ORACLE-1). Every eager VC that joins is interned and checked by
//! [`VcContext::push_checked_row`]: its materialization is compared with it in every field,
//! and on a disagreement the eager row is interned instead and the disagreement counted.
//! The eager VCs stay authoritative: every consumer reads [`BodyRows::vcs`], so no verdict,
//! row, key or transport byte depends on the ids yet. The oracle polls no step budget and
//! charges nothing (L4-METER-1), and runs outside vcgen's `gen_work_scope`.
//!
//! An id is `None` only for a row the context could not hold (a full table, 2^32 entries).
//! Such a row is still carried and consumed as its eager VC.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::hash::Hash;

use rustc_data_structures::fx::FxHashSet;
use trust_types::VerificationCondition;
use trust_types::vc_context::{RowId, VcContext, same_row};

/// A body's consumed solver rows and their ids, aligned (module docs).
#[derive(Debug, Default)]
pub(super) struct BodyRows {
    vcs: Vec<VerificationCondition>,
    ids: Vec<Option<RowId>>,
}

impl BodyRows {
    /// The generation's solver rows with the ids vcgen interned them under
    /// (`trust_vcgen::ConsumedGeneration`). Lists of different lengths cannot be paired:
    /// every row is then interned again here, so the carrier is aligned whatever it was
    /// handed.
    pub(super) fn from_generation(
        rows: &mut VcContext,
        vcs: Vec<VerificationCondition>,
        ids: Vec<Option<RowId>>,
    ) -> Self {
        if vcs.len() == ids.len() {
            return Self { vcs, ids };
        }
        let mut aligned = Self::default();
        aligned.extend(rows, vcs);
        aligned
    }

    /// The eager rows, in order: what every consumer reads.
    pub(super) fn vcs(&self) -> &[VerificationCondition] {
        &self.vcs
    }

    /// Each row's id, in the order of [`Self::vcs`]. Nothing outside the tests reads an id
    /// before C07r puts the results on rows.
    #[cfg(test)]
    pub(super) fn ids(&self) -> &[Option<RowId>] {
        &self.ids
    }

    /// Append `vcs`, each interned through the row oracle as it joins.
    pub(super) fn extend(
        &mut self,
        rows: &mut VcContext,
        vcs: impl IntoIterator<Item = VerificationCondition>,
    ) {
        for vc in vcs {
            self.ids.push(rows.push_checked_row(&vc).ok());
            self.vcs.push(vc);
        }
    }

    /// Keep the rows `keep` accepts, each with its id.
    pub(super) fn filter(&mut self, mut keep: impl FnMut(&VerificationCondition) -> bool) {
        let vcs = std::mem::take(&mut self.vcs);
        let ids = std::mem::take(&mut self.ids);
        for (vc, id) in vcs.into_iter().zip(ids) {
            if keep(&vc) {
                self.vcs.push(vc);
                self.ids.push(id);
            }
        }
    }

    /// Keep the first row of each `key`, each with its id. A row with no key (`None`) is
    /// always kept: no key means no exact equality, so it is never merged.
    pub(super) fn dedupe_by<K: Eq + Hash>(
        &mut self,
        mut key: impl FnMut(&VerificationCondition) -> Option<K>,
    ) {
        let mut seen = FxHashSet::default();
        self.filter(|vc| key(vc).is_none_or(|found| seen.insert(found)));
    }

    /// Run a whole-list rewrite (the spine verdict flips) and re-pair its output. A row
    /// the rewrite left where it was, equal in every field, keeps its id; every other row
    /// it returns joins the context through the row oracle.
    pub(super) fn flip<R>(
        &mut self,
        rows: &mut VcContext,
        rewrite: impl FnOnce(Vec<VerificationCondition>) -> (Vec<VerificationCondition>, R),
    ) -> R {
        let previous = std::mem::take(&mut self.ids);
        let (vcs, out) = rewrite(std::mem::take(&mut self.vcs));
        let mut ids = Vec::with_capacity(vcs.len());
        for (index, vc) in vcs.iter().enumerate() {
            let kept = previous.get(index).copied().flatten().filter(|&id| {
                rows.materialize(id).is_ok_and(|materialized| same_row(materialized.vc(), vc))
            });
            ids.push(match kept {
                Some(id) => Some(id),
                None => rows.push_checked_row(vc).ok(),
            });
        }
        self.vcs = vcs;
        self.ids = ids;
        out
    }

    /// Whether every id reads back, from `rows`, as its eager row in every field: the
    /// alignment the carrier promises. Reads only; counts nothing.
    #[cfg(test)]
    pub(super) fn aligned_in(&self, rows: &VcContext) -> bool {
        self.vcs.len() == self.ids.len()
            && self.vcs.iter().zip(&self.ids).all(|(vc, id)| {
                id.is_some_and(|id| {
                    rows.materialize(id).is_ok_and(|materialized| same_row(materialized.vc(), vc))
                })
            })
    }

    /// Swap the ids of rows `a` and `b`: the misalignment a negative control plants.
    #[cfg(test)]
    pub(super) fn misalign_for_test(&mut self, a: usize, b: usize) {
        if a < self.ids.len() && b < self.ids.len() {
            self.ids.swap(a, b);
        }
    }
}

#[cfg(test)]
mod tests;
