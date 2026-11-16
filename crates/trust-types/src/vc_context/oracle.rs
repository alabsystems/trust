//! The row oracle (plan C07, L4-ORACLE-1): a row read back from the context is compared,
//! field by field, with the eager `VerificationCondition` it was made from, and the eager
//! row decides.
//!
//! Until C11 the eager tree is authoritative. A row whose materialization differs from
//! its eager VC in any field is replaced by `Node(intern(eager))`, and the disagreement is
//! counted under [`Oracle::Row`]; a consumer therefore only ever reads the eager row, and
//! every vector stays identical by construction. The oracle is UNMETERED (L4-METER-1): it
//! polls no step budget and charges nothing, so no reproducible stop can move because it
//! ran. Its cost is reported by the context's counters, not paid from a budget.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use super::{Oracle, ParityCount, RowId, VcContext, VcContextError};
use crate::VerificationCondition;

/// Whether `a` and `b` agree in every field (`kind`, `function`, `location`, `formula`,
/// `contract_metadata`, `obligation`). Every field type is `Eq`, so this is reflexive, and
/// a VC's canonical JSON is a function of these six fields.
#[must_use]
pub fn same_row(a: &VerificationCondition, b: &VerificationCondition) -> bool {
    a.kind == b.kind
        && a.function == b.function
        && a.location == b.location
        && a.formula == b.formula
        && a.contract_metadata == b.contract_metadata
        && a.obligation == b.obligation
}

impl VcContext {
    /// The row oracle for row `id` against `eager`: materialize `id` and compare it with
    /// `eager` in every field. On agreement `id` is returned; on a disagreement, or when
    /// `id` cannot be materialized, `eager` is pushed as a Node row and that row's id is
    /// returned instead. Either way the comparison is counted under [`Oracle::Row`].
    ///
    /// # Errors
    ///
    /// [`VcContextError::Full`] when the substitute row cannot be pushed.
    pub fn check_row(
        &mut self,
        id: RowId,
        eager: &VerificationCondition,
    ) -> Result<RowId, VcContextError> {
        let agrees = match self.materialize(id) {
            Ok(materialized) => same_row(materialized.vc(), eager),
            Err(_) => false,
        };
        self.record_parity(Oracle::Row, !agrees);
        if agrees { Ok(id) } else { self.push_node_row(eager) }
    }

    /// Intern `eager` as a Node row and run the row oracle on it ([`Self::check_row`]):
    /// the one way a producer's eager VC joins a body's context.
    ///
    /// A row the context refuses is still counted under [`Oracle::Row`], as a
    /// disagreement: it has no id, so no read-back can agree with it, and every row that
    /// tried to join reaches the count (callers keep consuming it as its eager VC and drop
    /// the error).
    ///
    /// # Errors
    ///
    /// [`VcContextError::Full`] when a table the row needs is full.
    pub fn push_checked_row(
        &mut self,
        eager: &VerificationCondition,
    ) -> Result<RowId, VcContextError> {
        match self.push_node_row(eager) {
            Ok(id) => self.check_row(id, eager),
            Err(refused) => {
                self.record_parity(Oracle::Row, true);
                Err(refused)
            }
        }
    }

    /// Oracle `oracle`'s count so far: rows compared and mismatches.
    #[must_use]
    pub fn parity(&self, oracle: Oracle) -> ParityCount {
        self.stats.parity(oracle)
    }
}

/// The parity counts of contexts that have ended, summed per oracle (plan C07p): what a
/// crate phase reports for the short-lived contexts it ran and dropped, such as each R1
/// harvest's (design D-VC-6), as one crate-level `PARITY` row per oracle.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ParityTally {
    /// One count per oracle, in the order of [`Oracle::ALL`].
    counts: [ParityCount; Oracle::ALL.len()],
}

impl ParityTally {
    /// Add `rows`'s count of every oracle.
    pub fn fold(&mut self, rows: &VcContext) {
        let all = rows.stats.parity_all();
        for (total, count) in self.counts.iter_mut().zip(all) {
            total.rows = total.rows.saturating_add(count.rows);
            total.mismatches = total.mismatches.saturating_add(count.mismatches);
        }
    }

    /// Oracle `oracle`'s summed count.
    #[must_use]
    pub fn get(&self, oracle: Oracle) -> ParityCount {
        self.counts[oracle.slot()]
    }
}
