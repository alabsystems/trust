//! The per-function VC context (work item T3, landing L4, commit C06): the types a body's
//! verification conditions are held in once L4 moves them out of owned trees.
//!
//! Design of record: `docs/design/2026-10-08-t3-memory-proportional-reconstruction.md`
//! §3 (D-VC-1, 2, 3, 5, 6 and "Data structures (C06)"), §2 (I1, I4, I5), §13 (the
//! counters). Plan: `docs/design/2026-10-11-t3-l4-commit-plan.md` C06 and L4-SPINE-ID-1,
//! L4-MAT-1, L4-CTX-1.
//!
//! From C07 each body's consumed generation is interned into one context and its row ids
//! are carried beside the eager VCs. The eager VCs stay authoritative until C11: the row
//! oracle ([`VcContext::check_row`]) compares every row read back with its eager VC and
//! substitutes the eager row on a disagreement, so no verdict, row, key or transport byte
//! depends on anything here yet.
//!
//! # What a context holds
//!
//! * `dag`: one hash-consed [`FormulaDag`] for every formula the body's rows mention.
//! * `seqs`: persistent, prefix-shared, hash-consed sequences of DAG nodes ([`SeqId`]):
//!   a block's candidate facts, a wrapper's facts or guards.
//! * `spans`: every [`SourceSpan`] interned by its full value ([`SpanId`]).
//! * `spines`: the block-def recipes ([`Spine`]), hash-consed by (candidates, body,
//!   rule). A spine's root (the conjunction of its kept facts and its body) is NEVER
//!   interned into `dag` (D-VC-3): it is computed when a row is materialized, identified
//!   or counted.
//! * `memo`: type-erased per-owner slots ([`ContextMemos`]) that drop with the context.
//! * `vars`: the per-function relevance names ([`RelevanceVars`]), data vcgen supplies,
//!   and the relevance walk's cache of name sets and kept lists (D-VC-6).
//! * `merkle`: the [`MerkleCache`] of `dag` (`crate::formula_merkle`).
//! * `stats`: the counters of design §13 ([`ContextStats`]).
//! * the rows themselves ([`VcRow`]), immutable: a rewrite pushes a new row.
//!
//! # Identity (D-VC-5, L4-SPINE-ID-1)
//!
//! Two rows of one context have the same formula exactly when their [`FormulaKey`]s are
//! equal: a node for a Node row, the transient kept-plus-body list for a Spine row, and a
//! spine's list equal to an `And` node's children ([`VcContext::formula_eq`]). A Merkle
//! digest only selects candidates; it never decides. From C09 a VC that is no row has the
//! identity it would have as one ([`VcContext::identity_of`]): the compiler's identity
//! oracle compares row identities beside the canonical keys its exact sites compare.
//!
//! # Ownership (L4-CTX-1, L4-MAT-1)
//!
//! A context is `Send` and `Sync` and is not `Clone`:
//!
//! ```compile_fail,E0277
//! fn needs_clone<T: Clone>() {}
//! needs_clone::<trust_types::vc_context::VcContext>();
//! ```
//!
//! A row is read as a tree only through a [`MaterializedVc`], which owns one
//! `VerificationCondition`, lends it by [`MaterializedVc::vc`], and has neither `Clone`
//! nor `Deref`, so nothing can keep a tree it borrowed for one use; `trees_alive` counts
//! the ones alive.
//!
//! Every walk here is iterative, and nothing here panics: an id of another context, or a
//! push past a table's 2^32 entries, is refused with [`VcContextError`].
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

mod identity;
mod materialize;
mod memo;
mod oracle;
mod record;
mod row;
mod spine;
mod stats;

use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

/// A node of the context's DAG ([`VcContext::intern`]): named here so a supplier can key
/// its own per-node memos (trust-vcgen's row sink, C08).
pub use trust_ir_contract::formula_dag::NodeId;
use trust_ir_contract::formula_dag::{DagError, FormulaDag};

pub use self::identity::{
    ExactIdentity, FormulaKey, PathGuardKey, RecordKey, RowIdentity, WrapperKey,
};
pub use self::materialize::MaterializedVc;
pub use self::memo::{ContextMemos, MemoSlot};
pub use self::oracle::{ParityTally, same_row};
pub use self::record::{PathGuardRef, RecordRef, WrapperRef};
use self::row::SpanTable;
pub use self::row::{RowFormula, SpineRow, VcRow};
use self::spine::{RelevanceCache, SeqStore, SpineStore};
pub use self::spine::{RelevanceRule, RelevanceVars, Spine};
use self::stats::StatsCell;
pub use self::stats::{ConsumerWork, ContextStats, Oracle, ParityCount, WorkRatio};
use crate::formula_merkle::{FormulaDigest, MerkleCache, MerkleError};
use crate::{Formula, SourceSpan, VerificationCondition};

/// The brand of the next context: process-wide and never reused, so an id of one context
/// never names an entry of another.
static NEXT_CONTEXT_BRAND: AtomicU64 = AtomicU64::new(0);

macro_rules! context_id {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name {
            brand: u64,
            index: u32,
        }

        impl $name {
            /// The dense index of the entry in its context.
            #[must_use]
            pub fn index(self) -> usize {
                self.index as usize
            }
        }
    };
}

context_id! {
    /// One row of one [`VcContext`].
    RowId
}
context_id! {
    /// One interned [`SourceSpan`] of one [`VcContext`].
    SpanId
}
context_id! {
    /// One [`Spine`] of one [`VcContext`].
    SpineId
}

/// One hash-consed node sequence of one [`VcContext`]; the empty sequence has no cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SeqId {
    brand: u64,
    cell: Option<u32>,
}

/// Why a context operation was refused. Nothing here panics: a foreign or unknown id is a
/// refusal, and so is a digest the Merkle cache refuses.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum VcContextError {
    /// The row id is not a row of this context.
    UnknownRow(RowId),
    /// The node id is not a node of this context's DAG.
    UnknownNode(NodeId),
    /// The sequence id is not a sequence of this context.
    UnknownSeq(SeqId),
    /// The spine id is not a spine of this context.
    UnknownSpine(SpineId),
    /// The span id is not a span of this context.
    UnknownSpan(SpanId),
    /// A record of a Node row names the spine's kept facts, which only a Spine row has.
    KeptOutsideSpine(RowId),
    /// A record identified with no row ([`VcContext::identity_of`]) names a spine's kept
    /// facts, which only a Spine row has.
    KeptOutsideRow,
    /// The Merkle cache refused a digest.
    Merkle(MerkleError),
    /// The DAG refused an operation.
    Dag(DagError),
    /// A table of this context holds 2^32 entries, as many as its ids can name.
    Full(&'static str),
}

/// The index the next entry of a table of `len` entries gets, or the refusal of a full
/// table (`table` names it): an id is 32 bits, and two entries never share one.
fn next_index(len: usize, table: &'static str) -> Result<u32, VcContextError> {
    u32::try_from(len).map_err(|_| VcContextError::Full(table))
}

impl fmt::Display for VcContextError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VcContextError::UnknownRow(row) => write!(f, "{row:?} is not a row of this context"),
            VcContextError::UnknownNode(node) => {
                write!(f, "{node} is not a node of this context's DAG")
            }
            VcContextError::UnknownSeq(seq) => {
                write!(f, "{seq:?} is not a sequence of this context")
            }
            VcContextError::UnknownSpine(spine) => {
                write!(f, "{spine:?} is not a spine of this context")
            }
            VcContextError::UnknownSpan(span) => {
                write!(f, "{span:?} is not a span of this context")
            }
            VcContextError::KeptOutsideSpine(row) => {
                write!(f, "{row:?} is a Node row whose record names a spine's kept facts")
            }
            VcContextError::KeptOutsideRow => {
                write!(f, "a record identified with no row names a spine's kept facts")
            }
            VcContextError::Merkle(error) => write!(f, "{error}"),
            VcContextError::Dag(error) => write!(f, "{error}"),
            VcContextError::Full(table) => {
                write!(f, "this context's {table} table is full (2^32 entries)")
            }
        }
    }
}

impl std::error::Error for VcContextError {}

impl From<MerkleError> for VcContextError {
    fn from(error: MerkleError) -> Self {
        VcContextError::Merkle(error)
    }
}

impl From<DagError> for VcContextError {
    fn from(error: DagError) -> Self {
        VcContextError::Dag(error)
    }
}

/// One body's verification conditions, held once (module docs).
pub struct VcContext {
    brand: u64,
    dag: FormulaDag,
    seqs: SeqStore,
    spans: SpanTable,
    spines: SpineStore,
    memo: ContextMemos,
    vars: RelevanceVars,
    relevance: RelevanceCache,
    merkle: MerkleCache,
    stats: StatsCell,
    rows: Vec<VcRow>,
    /// Each row's formula digest, once computed (32 bytes a row).
    row_digests: Vec<Option<FormulaDigest>>,
}

impl fmt::Debug for VcContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VcContext")
            .field("brand", &self.brand)
            .field("rows", &self.rows.len())
            .field("dag_nodes", &self.dag.len())
            .finish_non_exhaustive()
    }
}

impl Default for VcContext {
    fn default() -> Self {
        Self::new()
    }
}

impl VcContext {
    /// An empty context, with a brand no other context of this process has.
    #[must_use]
    pub fn new() -> Self {
        let brand = NEXT_CONTEXT_BRAND.fetch_add(1, Ordering::Relaxed);
        VcContext {
            brand,
            dag: FormulaDag::new(),
            seqs: SeqStore::new(brand),
            spans: SpanTable::new(brand),
            spines: SpineStore::new(brand),
            memo: ContextMemos::default(),
            vars: RelevanceVars::default(),
            relevance: RelevanceCache::default(),
            merkle: MerkleCache::new(),
            stats: StatsCell::default(),
            rows: Vec::new(),
            row_digests: Vec::new(),
        }
    }

    /// The DAG every row's formulas live in (read-only).
    #[must_use]
    pub fn dag(&self) -> &FormulaDag {
        &self.dag
    }

    /// The per-owner memo slots.
    #[must_use]
    pub fn memo(&self) -> &ContextMemos {
        &self.memo
    }

    /// The relevance names spines are closed under.
    #[must_use]
    pub fn vars(&self) -> &RelevanceVars {
        &self.vars
    }

    /// The relevance names, to fill (vcgen supplies them as data). The kept lists computed
    /// under the old names are forgotten.
    pub fn vars_mut(&mut self) -> &mut RelevanceVars {
        self.relevance.forget_kept();
        &mut self.vars
    }

    /// The number of rows.
    #[must_use]
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    /// Whether the context holds no row.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    /// The ids of every row, in push order.
    pub fn row_ids(&self) -> impl Iterator<Item = RowId> + '_ {
        (0..self.rows.len())
            .filter_map(|index| u32::try_from(index).ok())
            .map(|index| RowId { brand: self.brand, index })
    }

    /// Row `id`.
    ///
    /// # Errors
    ///
    /// [`VcContextError::UnknownRow`] for a row of another context.
    pub fn row(&self, id: RowId) -> Result<&VcRow, VcContextError> {
        if id.brand != self.brand {
            return Err(VcContextError::UnknownRow(id));
        }
        self.rows.get(id.index()).ok_or(VcContextError::UnknownRow(id))
    }

    /// The span `id` stands for.
    ///
    /// # Errors
    ///
    /// [`VcContextError::UnknownSpan`] for a span of another context.
    pub fn span(&self, id: SpanId) -> Result<&SourceSpan, VcContextError> {
        self.spans.get(id)
    }

    /// The spine `id` stands for.
    ///
    /// # Errors
    ///
    /// [`VcContextError::UnknownSpine`] for a spine of another context.
    pub fn spine(&self, id: SpineId) -> Result<&Spine, VcContextError> {
        self.spines.get(id)
    }

    /// Intern a formula tree; equal subtrees become one node.
    pub fn intern(&mut self, formula: &Formula) -> NodeId {
        self.dag.intern(formula)
    }

    /// The hash-consed sequence of `nodes`, in order.
    ///
    /// # Errors
    ///
    /// [`VcContextError::UnknownNode`] for a node of another DAG.
    pub fn seq(&mut self, nodes: &[NodeId]) -> Result<SeqId, VcContextError> {
        if let Some(&node) = nodes.iter().find(|node| !self.dag.contains(**node)) {
            return Err(VcContextError::UnknownNode(node));
        }
        self.seqs.from_nodes(nodes)
    }

    /// `seq` with `node` appended: shares every cell of `seq`.
    ///
    /// # Errors
    ///
    /// [`VcContextError::UnknownSeq`] or [`VcContextError::UnknownNode`] for an id of
    /// another context.
    pub fn seq_push(&mut self, seq: SeqId, node: NodeId) -> Result<SeqId, VcContextError> {
        if !self.dag.contains(node) {
            return Err(VcContextError::UnknownNode(node));
        }
        self.seqs.push(seq, node)
    }

    /// The nodes of `seq`, in order.
    ///
    /// # Errors
    ///
    /// [`VcContextError::UnknownSeq`] for a sequence of another context.
    pub fn seq_nodes(&self, seq: SeqId) -> Result<Vec<NodeId>, VcContextError> {
        self.seqs.nodes(seq)
    }

    /// Push the row `vc` is: its formula and the record's formulas interned, its span
    /// interned by value. A Node row (spines are pushed by [`Self::push_spine_row`]).
    ///
    /// # Errors
    ///
    /// [`VcContextError::Full`] when a table it needs is full.
    pub fn push_node_row(&mut self, vc: &VerificationCondition) -> Result<RowId, VcContextError> {
        let location = self.spans.intern(&vc.location)?;
        let formula = RowFormula::Node(self.dag.intern(&vc.formula));
        let obligation = match &vc.obligation {
            Some(record) => Some(self.intern_record(record)?),
            None => None,
        };
        self.push(VcRow {
            kind: vc.kind.clone(),
            function: vc.function,
            location,
            formula,
            contract_metadata: vc.contract_metadata,
            obligation,
        })
    }

    /// Push a Spine row. Its record, if any, may name the spine's kept facts
    /// ([`WrapperRef::SpineKept`]); they are derived from the spine whenever the row is
    /// read, never stored.
    ///
    /// # Errors
    ///
    /// An id of another context in the spine or the record, or
    /// [`VcContextError::Full`] when a table it needs is full.
    pub fn push_spine_row(&mut self, row: SpineRow) -> Result<RowId, VcContextError> {
        self.seqs.validate(row.spine.candidates)?;
        if !self.dag.contains(row.spine.body) {
            return Err(VcContextError::UnknownNode(row.spine.body));
        }
        if let Some(record) = &row.obligation {
            record.validate(&self.dag, &self.seqs)?;
        }
        let location = self.spans.intern(&row.location)?;
        let spine = self.spines.intern(row.spine)?;
        self.push(VcRow {
            kind: row.kind,
            function: row.function,
            location,
            formula: RowFormula::Spine(spine),
            contract_metadata: row.contract_metadata,
            obligation: row.obligation,
        })
    }

    fn push(&mut self, row: VcRow) -> Result<RowId, VcContextError> {
        let index = next_index(self.rows.len(), "row")?;
        self.rows.push(row);
        self.row_digests.push(None);
        Ok(RowId { brand: self.brand, index })
    }

    /// The counters of design §13, as of now ([`ContextStats`]).
    #[must_use]
    pub fn stats(&self) -> ContextStats {
        self.stats.snapshot(self)
    }

    /// Count one row an L4 oracle compared, and whether it disagreed (from C07).
    pub fn record_parity(&self, oracle: Oracle, mismatch: bool) {
        self.stats.record_parity(oracle, mismatch);
    }

    /// Count one row whose cone vcgen knows, `blocks` blocks wide (from C08: a Spine row,
    /// whose candidate facts are one block's).
    pub fn record_cone_blocks(&self, blocks: u64) {
        self.stats.record_cone_blocks(blocks);
    }
}

#[cfg(test)]
mod tests;
