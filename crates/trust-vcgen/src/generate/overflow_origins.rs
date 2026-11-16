// trust_vcgen/generate/overflow_origins.rs: the overflow-check origins of the
// production generation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Trust (T3 C05, 2026-10-11; design
//! `docs/design/2026-10-08-t3-memory-proportional-reconstruction.md` §9.1): the
//! origin block of each Add/Sub/Mul overflow row, carried by the generation the
//! compiler consumes.
//!
//! # What the consumer does with it
//!
//! `rustc_mir_transform::trust_verify::elide_kernel_certified_checks` deletes the
//! panic edge of an overflow `Assert` when a `KernelCertified` row proves it cannot
//! fire. It finds the block by joining the row's exact identity (its sealed canonical
//! string) to this inventory, and only a key that ONE block produced is joined:
//! a key two blocks produced is `Ambiguous` and its checks are kept.
//!
//! Until C05 the inventory came from a replay (`overflow_vc_block_origins`): a second
//! safety-VC generation after the compiler's own, outside every per-function analysis
//! memo, under a fresh step budget, whose rows were meant to equal the production rows
//! byte for byte. It is deleted. The production walk already pairs each row with its
//! block ([`super::safety::generate_v2_safety_vcs_impl_with_origins_checked`]); the
//! pairing is now kept through the rest of the generation instead of dropped.
//!
//! # What an inventory claims
//!
//! * **Exactly the emitted row.** Each pair is the row as the generation returned it,
//!   after every per-row rewrite (SSA-token normalization, `Ite` elimination, the
//!   interval discharge or the abstract-state augment) and before the compiler's
//!   dedupe. The compiler keys its table by that row's exact identity, the same string
//!   a `KernelCertified` row seals, so a row that is not rewritten after generation
//!   joins its own origin by construction.
//! * **Every Add/Sub/Mul overflow row of the safety walk, with the arm that minted
//!   it.** Those are the rows the seam joins and the rows whose collisions make a key
//!   `Ambiguous`. A row a later pass rewrote into another kind (`UnsupportedMir`, for a
//!   self-referential definition or a havoc-only refutation) is no longer one, and is
//!   not listed. Each row says whether its block's `Assert(Overflow)` terminator minted
//!   it ([`OriginSite::Assert`]) or an arithmetic statement in the block did
//!   ([`OriginSite::Statement`]): only the first is the origin of a check, and the
//!   compiler never resolves a key a statement produced to a block (it still counts
//!   toward `Ambiguous`). Without the distinction a block ending in
//!   `Assert(Overflow(Add))` that also holds a plain integer `Add` (inlined from a crate
//!   built without overflow checks) would lose its `Assert` on the other operation's
//!   proof: the seam's live re-confirm checks only the op.
//! * **Completeness, or no table.** `Unique` is a claim about the whole enumeration: a
//!   key is `Ambiguous` only because a second block produced it. A walk cut short by
//!   the budget or the row cap, a work-meter trip, a body the generator refuses, or an
//!   origin that no longer lines up with its row gives NO table
//!   ([`OverflowOrigins::complete`] is `None`), and every check is kept.
//!
//! # Rows by id (T3 C07)
//!
//! The consumed generation interns every row it returns into the body's
//! [`VcContext`](trust_types::vc_context::VcContext), and an inventory row names its row
//! by that [`RowId`] instead of holding a second copy of the tree. Inside the generation
//! an origin names its row by its index in the list it left in ([`PendingOrigins`]); the
//! entry resolves the indices to ids. An origin whose row the context could not hold gives
//! no table, like any other origin that no longer lines up.
//!
//! Since T3 C08s each row is interned as it joins the generation's row sink
//! (`super::row_sink`), and carries its id through the discharge split: a discharged
//! row and a solver row the abstract-state augment left as it was keep the id their row
//! got, and an augmented row joins the context again as it leaves. The origins move with
//! the sink's entries ([`RowOrigins::sort_by`] over any carrier of one row each), and a lane
//! that joins the sink out of its phase refuses the table ([`RowOrigins::refuse`]).

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};

use trust_types::fx::FxHasher;
use trust_types::vc_context::RowId;
use trust_types::{BinOp, BlockId, SourceSpan, VcKind, VerificationCondition};

/// Whether a generation keeps its overflow-check origins. Only the compiler's consumed
/// generation reads them ([`super::generate_vcs_with_discharge_and_overflow_origins`]);
/// every other entry drops them, so it does not tag, sort or clone them either.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum KeepOrigins {
    Yes,
    No,
}

/// Which arm of the safety walk minted an overflow row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OriginSite {
    /// The block's `Assert(Overflow(op))` terminator: the check the elision seam removes.
    Assert,
    /// An arithmetic statement in the block (a plain `BinaryOp`), which guards no check.
    Statement,
}

/// One inventory row: an Add/Sub/Mul overflow row exactly as the generation emitted it,
/// named by its id in the body's context (T3 C07), its origin block, and the arm that
/// minted it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OriginRow {
    pub block: BlockId,
    pub site: OriginSite,
    pub vc: RowId,
}

/// The overflow-check origins of one production generation: an [`OriginRow`] for every
/// Add/Sub/Mul overflow row it emitted, or no table (see the module docs).
#[derive(Debug, Clone)]
pub struct OverflowOrigins {
    rows: Vec<OriginRow>,
    truncated: bool,
}

impl OverflowOrigins {
    /// The complete inventory, or `None` when there is no table. `Some(&[])` is a
    /// complete enumeration that found no Add/Sub/Mul overflow row.
    #[must_use]
    pub fn complete(&self) -> Option<&[OriginRow]> {
        (!self.truncated).then_some(self.rows.as_slice())
    }
}

/// Which list an emitted row left in, and its index there (T3 C07).
#[derive(Debug, Clone, Copy)]
pub(super) enum EmittedRow {
    /// `solver_vcs[index]`.
    Solver(usize),
    /// `discharged[index]`.
    Discharged(usize),
}

/// An inventory row before the generation's rows are interned: its row by index.
#[derive(Debug, Clone, Copy)]
pub(super) struct PendingOriginRow {
    pub(super) block: BlockId,
    pub(super) site: OriginSite,
    pub(super) row: EmittedRow,
}

/// The overflow-check origins of a generation whose rows are not interned yet. Rows are
/// only appended to either list after the inventory is taken (the callsite rows), so an
/// index names the same row when the entry resolves it.
#[derive(Debug, Clone)]
pub(super) struct PendingOrigins {
    rows: Vec<PendingOriginRow>,
    truncated: bool,
}

impl PendingOrigins {
    /// No table: the generation could not show its enumeration complete.
    pub(super) fn no_table() -> Self {
        Self { rows: Vec::new(), truncated: true }
    }

    /// Drop the table (an overrun the caller observed after the walk).
    pub(super) fn mark_truncated(&mut self) {
        self.truncated = true;
        self.rows = Vec::new();
    }

    /// Name each origin's row by its id in the body's context: `solver_rows[i]` is the id
    /// of `solver_vcs[i]`, `discharged_rows[i]` that of `discharged[i]`. An origin whose
    /// row has no id (the context refused it) or names no row gives no table.
    pub(super) fn resolve(
        self,
        solver_rows: &[Option<RowId>],
        discharged_rows: &[Option<RowId>],
    ) -> OverflowOrigins {
        let refused = OverflowOrigins { rows: Vec::new(), truncated: true };
        if self.truncated {
            return refused;
        }
        let mut rows = Vec::with_capacity(self.rows.len());
        for pending in self.rows {
            let id = match pending.row {
                EmittedRow::Solver(index) => solver_rows.get(index).copied().flatten(),
                EmittedRow::Discharged(index) => discharged_rows.get(index).copied().flatten(),
            };
            let Some(vc) = id else {
                return refused;
            };
            rows.push(OriginRow { block: pending.block, site: pending.site, vc });
        }
        OverflowOrigins { rows, truncated: false }
    }
}

/// Is `kind` one the elision seam joins: arithmetic overflow over `Add`, `Sub` or `Mul`?
///
/// `UncheckedArithmeticOverflow` is excluded on purpose: an `unchecked_{add,sub,mul}`
/// block has no `Assert(Overflow)` to remove.
fn elision_op(kind: &VcKind) -> Option<BinOp> {
    match kind {
        VcKind::ArithmeticOverflow { op: op @ (BinOp::Add | BinOp::Sub | BinOp::Mul), .. } => {
            Some(*op)
        }
        _ => None,
    }
}

fn location_fingerprint(location: &SourceSpan) -> u64 {
    let mut hasher = FxHasher::default();
    location.hash(&mut hasher);
    hasher.finish()
}

/// One row's origin, with what the row looked like when it was tagged. Every pass
/// between the walk and the inventory keeps a row's location, and keeps its kind or
/// demotes it to `UnsupportedMir` in place (a self-referential definition, a havoc-only
/// refutation). So an origin that lands on a row with another location, another
/// operation, or any other kind is a misalignment, and the inventory is refused.
#[derive(Debug, Clone, Copy)]
struct Origin {
    block: BlockId,
    site: OriginSite,
    op: BinOp,
    location: u64,
}

/// The origin of each row of a generated obligation list, by index: row `i` has
/// `origins[i]`, and rows past the end have none. Built from the safety walk, which
/// emits the first rows, and kept aligned by the operations that move rows
/// ([`Self::sort_by`], [`Self::inserted`]). Appending rows needs nothing.
pub(super) struct RowOrigins {
    origins: Vec<Option<Origin>>,
    truncated: bool,
}

impl RowOrigins {
    /// For a generation whose rows cannot be joined at all (a refused or degraded body).
    pub(super) fn no_table() -> Self {
        Self { origins: Vec::new(), truncated: true }
    }

    /// Split the safety walk's `(block, row)` pairs into the rows and their origins. Only
    /// an elision-kind row keeps its origin, tagged with the arm that minted it.
    pub(super) fn from_walk(walk: super::safety::SafetyWalk) -> (Vec<VerificationCondition>, Self) {
        let super::safety::SafetyWalk { rows, overflow_assert_rows, truncated, .. } = walk;
        let mut origins = Vec::with_capacity(rows.len());
        let mut vcs = Vec::with_capacity(rows.len());
        let mut assert_rows = overflow_assert_rows.into_iter().peekable();
        for (index, (block, vc)) in rows.into_iter().enumerate() {
            // `overflow_assert_rows` is ascending, so one pass pairs it with the rows.
            let site = if assert_rows.next_if_eq(&index).is_some() {
                OriginSite::Assert
            } else {
                OriginSite::Statement
            };
            origins.push(elision_op(&vc.kind).map(|op| Origin {
                block,
                site,
                op,
                location: location_fingerprint(&vc.location),
            }));
            vcs.push(vc);
        }
        // An index the walk named that is not a row (or not ascending) means the two
        // lists no longer describe one walk: no table.
        let truncated = truncated || assert_rows.next().is_some();
        // Rows past the last origin need no entry.
        while origins.last().is_some_and(Option::is_none) {
            origins.pop();
        }
        (vcs, Self { origins, truncated })
    }

    fn any(&self) -> bool {
        self.origins.iter().any(Option::is_some)
    }

    /// Stable-sort `vcs` by `compare` and permute the origins with it. The rows end in
    /// the order `vcs.sort_by(compare)` gives: a stable sort's result is fixed by the
    /// comparator and the input order, and the comparator reads only the row. The rows are
    /// any carrier of one row each (T3 C08s: the sink's entries), the origin of row `i`
    /// being that of `vcs[i]`.
    pub(super) fn sort_by<T>(
        &mut self,
        vcs: &mut Vec<T>,
        mut compare: impl FnMut(&T, &T) -> Ordering,
    ) {
        if self.origins.len() > vcs.len() {
            // More origins than rows: some pass dropped a row without telling us.
            self.refuse();
        }
        if !self.any() {
            vcs.sort_by(compare);
            return;
        }
        self.origins.resize(vcs.len(), None);
        let mut paired: Vec<(T, Option<Origin>)> =
            std::mem::take(vcs).into_iter().zip(std::mem::take(&mut self.origins)).collect();
        paired.sort_by(|a, b| compare(&a.0, &b.0));
        let (sorted, origins): (Vec<_>, Vec<_>) = paired.into_iter().unzip();
        *vcs = sorted;
        self.origins = origins;
        while self.origins.last().is_some_and(Option::is_none) {
            self.origins.pop();
        }
    }

    /// `count` rows with no origin were inserted at index `at`.
    pub(super) fn inserted(&mut self, at: usize, count: usize) {
        if at < self.origins.len() {
            self.origins.splice(at..at, std::iter::repeat_n(None, count));
        }
    }

    /// The inventory of `vcs`, the generation's final list. A tagged row a pass demoted
    /// to `UnsupportedMir` is dropped (it can no longer be joined, and an identical row
    /// of another block is demoted the same way). A tagged row with another location,
    /// another operation or any other kind means the origins no longer line up, and
    /// gives no table: dropping it instead could leave its twin `Unique`.
    pub(super) fn finish(self, vcs: &[VerificationCondition]) -> RowInventory {
        let refused = RowInventory { origins: Vec::new(), truncated: true };
        if self.truncated || self.origins.len() > vcs.len() {
            return refused;
        }
        let mut origins = Vec::with_capacity(self.origins.len());
        for (vc, origin) in vcs.iter().zip(self.origins) {
            let kept = match origin {
                None => None,
                Some(origin) if location_fingerprint(&vc.location) != origin.location => {
                    return refused;
                }
                Some(origin) => match elision_op(&vc.kind) {
                    Some(op) if op == origin.op => Some((origin.block, origin.site)),
                    None if matches!(vc.kind, VcKind::UnsupportedMir { .. }) => None,
                    _ => return refused,
                },
            };
            origins.push(kept);
        }
        RowInventory { origins, truncated: false }
    }

    /// Drop the table: the origins can no longer be shown to line up with the rows (T3
    /// C08s: a lane joined the generation's sink out of its phase).
    pub(super) fn refuse(&mut self) {
        self.origins.clear();
        self.truncated = true;
    }
}

/// The checked origins of a finished obligation list, by index, for the discharge
/// pass to turn into an [`OverflowOrigins`] as it splits and augments the rows.
pub(super) struct RowInventory {
    origins: Vec<Option<(BlockId, OriginSite)>>,
    truncated: bool,
}

impl RowInventory {
    /// No origins at all, for a caller that wants the rows and not the table.
    pub(super) fn none() -> Self {
        Self { origins: Vec::new(), truncated: true }
    }

    /// The origin block of row `index` and the arm that minted it, if it is a joinable
    /// row.
    pub(super) fn origin(&self, index: usize) -> Option<(BlockId, OriginSite)> {
        self.origins.get(index).copied().flatten()
    }

    /// Collect the inventory from the final rows.
    pub(super) fn into_origins(self, rows: Vec<PendingOriginRow>) -> PendingOrigins {
        if self.truncated {
            return PendingOrigins::no_table();
        }
        PendingOrigins { rows, truncated: false }
    }

    pub(super) fn is_truncated(&self) -> bool {
        self.truncated
    }
}
