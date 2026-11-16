//! The context's counters (design §13, plan C06 item 2). Deterministic and report-only:
//! none is in a vector or a key.
//!
//! * Retention: `dag_nodes`, `dag_edges`, `seq_cells`, `spines`, `spans`, `rows`,
//!   `retained_row_bytes`, `trees_alive` (now and at most), `materialized_nodes_max`, and
//!   `sum_cone_blocks` (vcgen fills it from C08, when it knows a row's cone in blocks: at
//!   C08, a Spine row's one block; `cone_rows` counts the rows it knows a cone for).
//! * Per-consumer work ([`ConsumerWork`]): the work each consumer of rows did, and its
//!   largest per-row ratio of work to the row's size ([`WorkRatio`]), the per-consumer
//!   linearity measure. A row's size is its node count (I4's size(q), the one size
//!   measure of BUDGET-1). C06 fills materialization, record replay and the relevance
//!   closure (per spine whose kept list it computed: the nodes its name walks visited and
//!   the names it compared, over the distinct nodes the walks reached plus its candidates
//!   and body); C10 fills the transcript (with the largest row's bytes) and ay
//!   translation; C10c certify input; C12 the trust-mc and BMC payload.
//! * Per-oracle parity ([`ParityCount`] by [`Oracle`]): rows compared and mismatches,
//!   from C07.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use super::{RecordRef, VcContext, VcRow, WrapperRef};

/// The trees materialized and not yet dropped, and the most ever alive at once.
#[derive(Debug, Default)]
pub(super) struct TreeCount {
    alive: AtomicU64,
    max: AtomicU64,
}

impl TreeCount {
    pub(super) fn acquire(&self) {
        let alive = self.alive.fetch_add(1, Ordering::AcqRel).saturating_add(1);
        self.max.fetch_max(alive, Ordering::AcqRel);
    }

    pub(super) fn release(&self) {
        let _ = self
            .alive
            .try_update(Ordering::AcqRel, Ordering::Acquire, |alive| Some(alive.saturating_sub(1)));
    }
}

/// A consumer's largest per-row ratio of work to row size, as the pair that attains it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct WorkRatio {
    /// The work the row cost.
    pub work: u64,
    /// The row's size (its node count).
    pub size: u64,
}

impl WorkRatio {
    /// Keep the larger of this ratio and `work / size`, compared exactly.
    pub fn keep_max(&mut self, work: u64, size: u64) {
        let size = size.max(1);
        if u128::from(work) * u128::from(self.size.max(1))
            > u128::from(self.work) * u128::from(size)
        {
            *self = WorkRatio { work, size };
        }
    }
}

/// The work one consumer of rows did.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ConsumerWork {
    /// Rows consumed.
    pub rows: u64,
    /// Work units over every row (nodes built or visited, or bytes).
    pub work: u64,
    /// The largest per-row work-to-size ratio.
    pub max_ratio: WorkRatio,
}

impl ConsumerWork {
    fn record(&mut self, work: u64, size: u64) {
        self.rows = self.rows.saturating_add(1);
        self.work = self.work.saturating_add(work);
        self.max_ratio.keep_max(work, size);
    }
}

/// An L4 oracle (L4-ORACLE-1).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Oracle {
    /// The row oracle: a materialized row against the eager VC (C07).
    Row,
    /// Row identity against canonical-key equality (C09).
    Identity,
    /// The dedup partition (C10).
    Dedup,
    /// Lowering from the node against the tree (I3, C10).
    Lowering,
    /// Asserted sizes (I4, C10).
    Size,
}

impl Oracle {
    /// Every oracle, in order.
    pub const ALL: [Oracle; 5] =
        [Oracle::Row, Oracle::Identity, Oracle::Dedup, Oracle::Lowering, Oracle::Size];

    /// The audit spelling (`PARITY <fn> <oracle>`).
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Oracle::Row => "row",
            Oracle::Identity => "identity",
            Oracle::Dedup => "dedup",
            Oracle::Lowering => "lowering",
            Oracle::Size => "size",
        }
    }

    pub(super) const fn slot(self) -> usize {
        match self {
            Oracle::Row => 0,
            Oracle::Identity => 1,
            Oracle::Dedup => 2,
            Oracle::Lowering => 3,
            Oracle::Size => 4,
        }
    }
}

/// One oracle's count.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ParityCount {
    /// Rows compared.
    pub rows: u64,
    /// Rows on which the two mechanisms disagreed.
    pub mismatches: u64,
}

#[derive(Debug, Default)]
struct WorkCounters {
    materialized_nodes_max: u64,
    sum_cone_blocks: u64,
    cone_rows: u64,
    materialization: ConsumerWork,
    record_replay: ConsumerWork,
    relevance: ConsumerWork,
    transcript: ConsumerWork,
    transcript_bytes_max_row: u64,
    ay_translation: ConsumerWork,
    certify_input: ConsumerWork,
    payload: ConsumerWork,
    parity: [ParityCount; 5],
}

/// The live counters of a context.
#[derive(Debug, Default)]
pub(super) struct StatsCell {
    work: Mutex<WorkCounters>,
    trees: Arc<TreeCount>,
}

impl StatsCell {
    pub(super) fn trees(&self) -> Arc<TreeCount> {
        Arc::clone(&self.trees)
    }

    fn work(&self) -> std::sync::MutexGuard<'_, WorkCounters> {
        self.work.lock().unwrap_or_else(PoisonError::into_inner)
    }

    pub(super) fn record_materialization(&self, formula_nodes: u64, record_nodes: u64, size: u64) {
        let mut work = self.work();
        work.materialized_nodes_max =
            work.materialized_nodes_max.max(formula_nodes.saturating_add(record_nodes));
        work.materialization.record(formula_nodes, size);
        if record_nodes > 0 {
            work.record_replay.record(record_nodes, size);
        }
    }

    pub(super) fn record_relevance(&self, work: u64, size: u64) {
        self.work().relevance.record(work, size);
    }

    pub(super) fn record_cone_blocks(&self, blocks: u64) {
        let mut work = self.work();
        work.sum_cone_blocks = work.sum_cone_blocks.saturating_add(blocks);
        work.cone_rows = work.cone_rows.saturating_add(1);
    }

    pub(super) fn record_parity(&self, oracle: Oracle, mismatch: bool) {
        let mut work = self.work();
        if let Some(count) = work.parity.get_mut(oracle.slot()) {
            count.rows = count.rows.saturating_add(1);
            count.mismatches = count.mismatches.saturating_add(u64::from(mismatch));
        }
    }

    pub(super) fn parity(&self, oracle: Oracle) -> ParityCount {
        self.work().parity.get(oracle.slot()).copied().unwrap_or_default()
    }

    pub(super) fn parity_all(&self) -> [ParityCount; 5] {
        self.work().parity
    }

    pub(super) fn snapshot(&self, context: &VcContext) -> ContextStats {
        let work = self.work();
        ContextStats {
            rows: context.rows.len() as u64,
            dag_nodes: context.dag.len() as u64,
            dag_edges: context.dag.edge_count() as u64,
            seq_cells: context.seqs.cells() as u64,
            spines: context.spines.len() as u64,
            spans: context.spans.len() as u64,
            retained_row_bytes: context.rows.iter().map(retained_bytes).sum(),
            trees_alive: self.trees.alive.load(Ordering::Acquire),
            trees_alive_max: self.trees.max.load(Ordering::Acquire),
            materialized_nodes_max: work.materialized_nodes_max,
            sum_cone_blocks: work.sum_cone_blocks,
            cone_rows: work.cone_rows,
            materialization: work.materialization,
            record_replay: work.record_replay,
            relevance: work.relevance,
            transcript: work.transcript,
            transcript_bytes_max_row: work.transcript_bytes_max_row,
            ay_translation: work.ay_translation,
            certify_input: work.certify_input,
            payload: work.payload,
            parity: Oracle::ALL.map(|oracle| {
                (oracle, work.parity.get(oracle.slot()).copied().unwrap_or_default())
            }),
        }
    }
}

/// What one row retains beside the shared stores: the row and its record's wrapper and
/// path lists. The DAG, sequences, spans and spines it points into are counted by their
/// own counters; a kind's own strings are not counted.
fn retained_bytes(row: &VcRow) -> u64 {
    let record = row.obligation.as_ref().map_or(0, |record: &RecordRef| {
        record.wrappers.len() * size_of::<WrapperRef>()
            + record
                .wrappers
                .iter()
                .map(|wrapper| match wrapper {
                    WrapperRef::PathGuardOr { paths } => {
                        paths.len() * size_of::<super::PathGuardRef>()
                    }
                    WrapperRef::ConjoinFactsLast { .. } | WrapperRef::SpineKept => 0,
                })
                .sum::<usize>()
    });
    (size_of::<VcRow>() + record) as u64
}

/// The counters of one context, as of one moment (module docs).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextStats {
    /// Rows pushed.
    pub rows: u64,
    /// Distinct DAG nodes.
    pub dag_nodes: u64,
    /// DAG child edges.
    pub dag_edges: u64,
    /// Sequence cells.
    pub seq_cells: u64,
    /// Distinct spines.
    pub spines: u64,
    /// Distinct spans.
    pub spans: u64,
    /// Bytes the rows retain beside the shared stores.
    pub retained_row_bytes: u64,
    /// Materialized trees alive now.
    pub trees_alive: u64,
    /// The most materialized trees alive at once.
    pub trees_alive_max: u64,
    /// The most tree nodes one materialization built.
    pub materialized_nodes_max: u64,
    /// The rows' cones in blocks, summed over the rows whose cone vcgen knows (from C08).
    pub sum_cone_blocks: u64,
    /// The rows whose cone `sum_cone_blocks` counts (from C08): totals are judged against
    /// it only when it is every row.
    pub cone_rows: u64,
    /// Materialization: formula tree nodes built.
    pub materialization: ConsumerWork,
    /// Record replay: record tree nodes built.
    pub record_replay: ConsumerWork,
    /// The relevance closure: per spine, the nodes its name walks visited and the names it
    /// compared (module docs).
    pub relevance: ConsumerWork,
    /// Transcript bytes (C10).
    pub transcript: ConsumerWork,
    /// The largest row's transcript bytes (C10).
    pub transcript_bytes_max_row: u64,
    /// ay translation (C10).
    pub ay_translation: ConsumerWork,
    /// Certify input (C10c).
    pub certify_input: ConsumerWork,
    /// trust-mc and BMC payload (C12).
    pub payload: ConsumerWork,
    /// Each oracle's count (from C07).
    pub parity: [(Oracle, ParityCount); 5],
}

impl ContextStats {
    /// The counters as `(name, value)` pairs, for reports.
    #[must_use]
    pub fn counters(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("ctx_rows", self.rows),
            ("ctx_dag_nodes", self.dag_nodes),
            ("ctx_dag_edges", self.dag_edges),
            ("ctx_seq_cells", self.seq_cells),
            ("ctx_spines", self.spines),
            ("ctx_spans", self.spans),
            ("ctx_retained_row_bytes", self.retained_row_bytes),
            ("ctx_trees_alive", self.trees_alive),
            ("ctx_trees_alive_max", self.trees_alive_max),
            ("ctx_materialized_nodes_max", self.materialized_nodes_max),
            ("ctx_sum_cone_blocks", self.sum_cone_blocks),
            ("ctx_cone_rows", self.cone_rows),
            ("ctx_materialization_work", self.materialization.work),
            ("ctx_record_replay_work", self.record_replay.work),
            ("ctx_relevance_work", self.relevance.work),
        ]
    }
}
