// trust_vcgen/generate/row_sink.rs: the row sink of the production generation
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

//! Trust (T3 L4, C08s, 2026-10-17; plan `docs/design/2026-10-11-t3-l4-commit-plan.md` C08s
//! and L4-PIPE-1, design `docs/design/2026-10-08-t3-memory-proportional-reconstruction.md`
//! §1 and D-VC-2): where `generate_vcs_impl_with_origins` puts every row it generates.
//!
//! # What the sink does with a row
//!
//! A lane hands the sink its rows as it returns them. As each row joins, the sink runs the
//! passes that ran over the finished list until C08s, in their old order:
//!
//! 1. SSA version-token normalization (`normalize_ssa_version_tokens`), on every row that
//!    is not `UnsupportedMir`;
//! 2. term-`Ite` elimination (`eliminate_term_ites`) and its mirror on the record
//!    (`ob_record_eliminate_ites`), on such a row whose normalized formula has an `Ite`;
//! 3. the havoc decline ([`HavocTables::reclassify`]), from tables built once per
//!    function;
//! 4. the self-referential-definition refusal ([`self_referential_definition`]).
//!
//! Each reads only the row it rewrites and the function, and none moves a row or changes
//! the list's length (the C05 census classified each as an in-place loop over `&mut vcs`
//! or a call taking `&mut [VerificationCondition]`), and none changes a row's location,
//! which is all the sort reads. So running them on each row as it joins gives exactly the
//! rows that running them over the sorted, spliced list gave (L4-C08s-1). A separation
//! row's fact wrappers ([`SepFacts`]) were applied per row already, before the passes; the
//! sink applies them at the same point ([`RowSink::append_sep`]).
//!
//! # Order
//!
//! The rows keep the order the list had. The safety walk's rows come first, with their
//! overflow-check origins ([`RowSink::walk`]); the lanes the stable sort orders join with
//! [`RowSink::lane`]; [`RowSink::sort_by_location`] sorts them, moving each origin with its
//! row (`RowOrigins::sort_by`); the lanes after the sort join with [`RowSink::append`]; and
//! the unsafe-site rows are inserted at the position [`RowSink::mark`] took before the
//! separation rows ([`RowSink::splice_at`]). A lane that joins in the wrong phase (a sorted
//! lane after the sort, an appended one before it, a walk after any row) is caught: its rows
//! are kept where it put them, the origin table is refused, so every overflow check is
//! kept (fail-closed), and the count is there for the tests.
//!
//! # Handles and the row oracle (C07, moved here)
//!
//! When the generation writes into a context, each row is interned through the row oracle
//! (`VcContext::push_checked_row`) as it joins, after its passes, and its id rides with it
//! through the sort and the splice: an entry is the row and its handle (L4-C08s-2).
//! [`RowSink::finish`] returns each row's id beside the eager rows, which stay
//! authoritative (L4-ORACLE-1); every consumer reads them until C10a. A generation refused
//! after its lanes ran (the work-meter trip, [`RowSink::refuse`]) returns its refusal row
//! alone, and the rows it interned stay in the context, named by no id. The oracle charges
//! no work meter and polls no budget (L4-METER-1), so it decides nothing about the
//! generation although it now runs inside the generation's scope (L4-C08s-3).
//!
//! Once the work meter has tripped, a joining row skips its passes and the oracle
//! ([`RowSink::take`]): the trip latches for the generation's scope, and the generation is
//! refused before it finishes, so the row is never returned. [`RowSink::finish`] fails
//! closed on a skipped row all the same: a skipped row missed the self-referential-definition
//! refusal, so the generation is the one work-budget refusal row ([`work_budget_refusal`]).
//!
//! # Memory
//!
//! The sink keeps every joined row's eager tree in its entries until [`RowSink::finish`]
//! returns them, so the generation's whole eager list is alive at its end, as it was before
//! C08s; a lane's own list is alive while the lane builds it. The context's `trees_alive`
//! counts the oracle's materialized read-backs, not these trees. Lanes hand the sink their
//! lists when they return (L4-C08s-6); the per-row push from inside the lanes, and a sink
//! that stops keeping a joined row's tree, are C10a's.
//!
//! # Spine rows (C08)
//!
//! A row whose formula was, as it joined, a block-def combination the generation recorded
//! (a recipe, [`super::recipes`]) joins as a Spine row when the row after its passes is
//! still that combination: the sink looks the recipe up before the passes and tries the
//! Spine after them, through the same row oracle. Every other row, and every block-def row
//! it declines, joins as a Node row, as before.

use std::cmp::Ordering;

use trust_types::vc_context::{RowId, VcContext};

use super::havoc_decline::HavocTables;
use super::recipes::{self, SpineMemo};
use super::*;
use crate::unsafe_verify::{MirOp, UnsafeCoverage};

/// Which lanes may join: the ones the stable sort orders, or the ones after it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// Before the sort: the walk and the lanes it orders.
    BeforeSort,
    /// After the sort: the lanes appended in generation order, and the unsafe-site rows.
    AfterSort,
}

/// One row in the sink: the row as its per-row passes left it, and its id in the context
/// the sink writes into (`None` without a context, or for a row the context refused).
struct SinkRow {
    vc: VerificationCondition,
    id: Option<RowId>,
}

/// The rows of one generation, with their origins (module docs).
pub(super) struct RowSink<'g> {
    /// The view every lane reads, which every per-row pass reads too.
    func: &'g VerifiableFunction,
    /// The context the rows join through the row oracle, when the caller keeps one.
    rows: Option<&'g mut VcContext>,
    /// The havoc decline's tables, built when the first row needs them.
    havoc: Option<HavocTables>,
    /// What the Spine attempts share (C08).
    spines: SpineMemo,
    entries: Vec<SinkRow>,
    /// The origin of each entry, by index, moved with the entries.
    origins: RowOrigins,
    phase: Phase,
    /// Rows (and walks) that joined in the wrong phase (module docs).
    out_of_phase: usize,
    /// Rows that joined after the work meter tripped, so skipped their passes (module docs).
    skipped: usize,
}

/// What a generation hands on: its rows, the id of each in the context the sink wrote into
/// (`None` for a row the context refused, and for every row when there was no context),
/// and the rows' origins.
pub(super) struct SinkOutput {
    pub(super) vcs: Vec<VerificationCondition>,
    /// `ids[i]` is the id of `vcs[i]`.
    pub(super) ids: Vec<Option<RowId>>,
    pub(super) origins: RowOrigins,
}

impl SinkOutput {
    /// A generation that is the one row `vc` (a refused or degraded body), with no origin
    /// table, `vc` interned into `rows` through the row oracle.
    pub(super) fn single(rows: Option<&mut VcContext>, vc: VerificationCondition) -> SinkOutput {
        let vcs = vec![vc];
        let ids = checked_ids(rows, &vcs);
        SinkOutput { vcs, ids, origins: RowOrigins::no_table() }
    }
}

/// Each of `vcs` interned into `rows` through the row oracle, in order: its id, or `None`
/// where the context refused it or there is no context.
pub(super) fn checked_ids<'a>(
    mut rows: Option<&mut VcContext>,
    vcs: impl IntoIterator<Item = &'a VerificationCondition>,
) -> Vec<Option<RowId>> {
    vcs.into_iter()
        .map(|vc| rows.as_deref_mut().and_then(|rows| rows.push_checked_row(vc).ok()))
        .collect()
}

/// The generation's order: by file, then line, then column.
fn by_location(a: &VerificationCondition, b: &VerificationCondition) -> Ordering {
    a.location
        .file
        .cmp(&b.location.file)
        .then(a.location.line_start.cmp(&b.location.line_start))
        .then(a.location.col_start.cmp(&b.location.col_start))
}

impl<'g> RowSink<'g> {
    /// An empty sink for a generation over `func` (the view every lane reads), writing into
    /// `rows` when the caller keeps a context.
    pub(super) fn new(func: &'g VerifiableFunction, rows: Option<&'g mut VcContext>) -> Self {
        RowSink {
            func,
            rows,
            havoc: None,
            spines: SpineMemo::default(),
            entries: Vec::new(),
            origins: RowOrigins::no_table(),
            phase: Phase::BeforeSort,
            out_of_phase: 0,
            skipped: 0,
        }
    }

    /// The safety walk's rows, with their origin blocks when `keep` says so. The origins
    /// index the generation's rows from its first, so the walk joins first.
    pub(super) fn walk(&mut self, walk: super::safety::SafetyWalk, keep: KeepOrigins) {
        let (vcs, origins) = match keep {
            KeepOrigins::Yes => RowOrigins::from_walk(walk),
            KeepOrigins::No => {
                (walk.rows.into_iter().map(|(_, vc)| vc).collect(), RowOrigins::no_table())
            }
        };
        if self.entries.is_empty() && self.phase == Phase::BeforeSort {
            self.origins = origins;
        } else {
            self.out_of_phase += 1;
        }
        self.join(Phase::BeforeSort, vcs);
    }

    /// The rows of a lane the stable sort orders.
    pub(super) fn lane(&mut self, rows: impl IntoIterator<Item = VerificationCondition>) {
        self.join(Phase::BeforeSort, rows);
    }

    /// The rows of a lane after the sort, appended in order.
    pub(super) fn append(&mut self, rows: impl IntoIterator<Item = VerificationCondition>) {
        self.join(Phase::AfterSort, rows);
    }

    /// One separation-engine row of `block`'s operation `op`, after the sort: its fact
    /// wrappers applied ([`SepFacts::wrap`]), the unsafe-site coverage told about the
    /// wrapped row (before the per-row passes, where the separation loop told it), then
    /// appended.
    pub(super) fn append_sep(
        &mut self,
        vc: VerificationCondition,
        facts: &SepFacts,
        block: BlockId,
        op: MirOp,
        coverage: &mut UnsafeCoverage,
    ) {
        let vc = facts.wrap(self.func, vc, block, op);
        coverage.record_sep_row(&vc, block, op);
        self.join(Phase::AfterSort, std::iter::once(vc));
    }

    /// Stable-sort the rows by location ([`by_location`]), each origin moving with its row.
    /// Every later row is appended.
    pub(super) fn sort_by_location(&mut self) {
        self.check_phase(Phase::BeforeSort);
        self.origins.sort_by(&mut self.entries, |a, b| by_location(&a.vc, &b.vc));
        self.phase = Phase::AfterSort;
    }

    /// The position the next appended row will take.
    pub(super) fn mark(&self) -> usize {
        self.entries.len()
    }

    /// Insert `rows` at `at`, a position [`Self::mark`] took after the sort: each row
    /// through its passes, the insertion recorded in the origins.
    pub(super) fn splice_at(&mut self, at: usize, rows: Vec<VerificationCondition>) {
        self.check_phase(Phase::AfterSort);
        let mut taken = Vec::with_capacity(rows.len());
        for vc in rows {
            taken.push(self.take(vc));
        }
        let at = at.min(self.entries.len());
        self.origins.inserted(at, taken.len());
        self.entries.splice(at..at, taken);
    }

    /// The generation is refused after its lanes ran: its output is `vc` alone, interned
    /// into the context, with no origin table. The rows that joined stay in the context,
    /// named by no id.
    pub(super) fn refuse(self, vc: VerificationCondition) -> SinkOutput {
        self.note_recorded();
        SinkOutput::single(self.rows, vc)
    }

    /// The generation's rows in order, the id each got as it joined (module docs), and
    /// their origins.
    pub(super) fn finish(self) -> SinkOutput {
        self.note_recorded();
        // Unreachable: a row is skipped only after the work meter tripped, which latches for
        // the generation's scope, and the generation refuses before it finishes. Fail closed
        // all the same, since a skipped row missed its passes (module docs).
        debug_assert_eq!(self.skipped, 0, "a row sink finished with rows it skipped");
        if self.skipped > 0 {
            return SinkOutput::single(self.rows, work_budget_refusal(self.func));
        }
        let RowSink { entries, mut origins, out_of_phase, .. } = self;
        // A lane out of its phase is a misordered `generate_vcs_impl_with_origins`: loud in a
        // debug build. The crate's own tests join out of phase on purpose, and read the count
        // instead (`seam::out_of_phase_joins`).
        #[cfg(not(test))]
        debug_assert_eq!(out_of_phase, 0, "rows joined the row sink out of their phase");
        #[cfg(test)]
        seam::OUT_OF_PHASE.with(|joins| joins.set(joins.get() + out_of_phase));
        if out_of_phase > 0 {
            // A lane joined out of its phase, so an origin may sit beside another row.
            origins.refuse();
        }
        let (vcs, ids): (Vec<VerificationCondition>, Vec<Option<RowId>>) =
            entries.into_iter().map(|row| (row.vc, row.id)).unzip();
        // Trust diagnostic (debug-only, no effect on verification): dump each
        // generated VC's location + formula when TRUST_DUMP_V2_VC is set, so the
        // exact SMT goal ay receives can be inspected (e.g. why a loop-body
        // `index += 1` overflow VC lacks its `index < n-1` guard).
        static DUMP_V2_VC: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        if *DUMP_V2_VC
            .get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_DUMP_V2_VC"))
        {
            for vc in &vcs {
                eprintln!(
                    "[V2_VC] {}:{}:{}-{}:{} formula={:?}",
                    vc.location.file,
                    vc.location.line_start,
                    vc.location.col_start,
                    vc.location.line_end,
                    vc.location.col_end,
                    vc.formula,
                );
            }
        }
        SinkOutput { vcs, ids, origins }
    }

    /// Rows (and walks) that joined in the wrong phase.
    #[cfg(test)]
    pub(super) fn out_of_phase(&self) -> usize {
        self.out_of_phase
    }

    fn join(&mut self, phase: Phase, rows: impl IntoIterator<Item = VerificationCondition>) {
        for vc in rows {
            self.check_phase(phase);
            let row = self.take(vc);
            self.entries.push(row);
        }
    }

    fn check_phase(&mut self, phase: Phase) {
        if self.phase != phase {
            self.out_of_phase += 1;
        }
    }

    /// Count the combinations the generation recorded into the context's recipe counts.
    fn note_recorded(&self) {
        if let Some(rows) = self.rows.as_deref() {
            recipes::note_recorded(rows);
        }
    }

    /// `vc` through its passes, interned into the context through the row oracle: as a
    /// Spine row when it is a block-def row the sink can join as one (module docs). Once the
    /// work meter has tripped, `vc` as it came, skipped (module docs).
    fn take(&mut self, vc: VerificationCondition) -> SinkRow {
        if crate::gen_work_tripped() {
            self.skipped += 1;
            return SinkRow { vc, id: None };
        }
        let found =
            if self.rows.is_some() { recipes::recipes_for(&vc.formula) } else { Vec::new() };
        let (mut vc, ite) = self.passes(vc);
        let func = self.func;
        let spines = &mut self.spines;
        let id = self.rows.as_deref_mut().and_then(|rows| {
            let joined = if found.is_empty() {
                rows.push_checked_row(&vc)
            } else {
                recipes::join_block_def_row(func, rows, spines, &found, &mut vc, ite)
            };
            joined.ok()
        });
        SinkRow { vc, id }
    }

    /// The per-row passes (module docs), in their old order; and whether term-`Ite`
    /// elimination rewrote the row.
    fn passes(&mut self, mut vc: VerificationCondition) -> (VerificationCondition, bool) {
        let func = self.func;
        let run = passes_run();
        // OUTERMOST SSA version-token normalization: every lane aggregated here
        // (block VCs, allocation/memory lanes, contract lanes, FFI/memory-model
        // extends) gets the same collapse, so no lane can leave a single-valued
        // local split across token spellings (the per-lane passes proved to be
        // whack-a-mole — an allocation-lane VC kept `h#s6_t` free of the bare-`h`
        // min-fact and minted a spurious refutation). Identity for SSA locals
        // under `local_versions_collapse_to_bare` (parameter-aware; reassigned
        // locals keep their load-bearing token disjointness).
        let supported = !v2_is_unsupported_mir_vc(&vc);
        if run >= 1 && supported {
            vc.formula = normalize_ssa_version_tokens_owned(func, vc.formula);
        }
        // GENERAL term-`Ite` elimination (backend-agnostic): a term-level
        // `Ite` in ANY obligation — postcondition, arithmetic-safety, bounds,
        // assert — is undischargeable (trust-mc's PDR prunes it → a
        // "violation-pruned" UNKNOWN; trust-wp does not route the
        // Ite-carrying bundle). Lift each to formula-level guards so the
        // obligation proves. Verdict-preserving (an `Ite` IS its guarded
        // case-split) and fail-open past `ITE_ELIM_CASE_CAP`; guarded by a
        // cheap containment check so an `Ite`-free VC pays no rewrite.
        let ite = run >= 2 && supported && formula_contains_ite(&vc.formula);
        if ite {
            vc.formula = eliminate_term_ites_owned(
                std::mem::replace(&mut vc.formula, Formula::Bool(false)),
                ITE_ELIM_CASE_CAP,
            );
            // Trust (GAP 2): apply the SAME term-`Ite` elimination to the recorded
            // obligation's body/subject/wrappers, so an `Ite`-carrying VC's record
            // still reconstructs to the REWRITTEN `formula` rather than the
            // pre-elimination form. No-op when the VC carries no obligation.
            ob_record_eliminate_ites(&mut vc, ITE_ELIM_CASE_CAP);
        }
        // GROUP 3: an unmodelled callee's return is a free variable, and a solver
        // model over it is not an execution. Reclassify every safety row whose
        // verdict rests on such a value to `UnsupportedMir` (→ Unknown) instead of
        // letting it be reported as a refutation with a witness no run can produce.
        // Runs after the SSA-token normalization above, so it sees each row's final
        // formula; DROP-ONLY — it can only turn a row into an Unknown.
        if run >= 3 {
            let havoc = self.havoc.get_or_insert_with(|| HavocTables::for_function(func));
            havoc.reclassify(&mut vc);
        }
        // A conjoined `Eq(v, f(v))` with `v` free in `f` is a recurrence, not a
        // definition: UNSAT for every program, so it vacuously discharges EVERY
        // obligation it accompanies. It appears when a fact established BEFORE a write
        // is read back at the POST-write version — the mint/kill fork this lane is
        // built to avoid. `i += 100` emits `_5.0 == i + 100` (pre) and `i == _5.0`
        // (post) over ONE symbol `i`, i.e. `i == i + 100` (2026-08-26: a guarded
        // out-of-bounds index read `proved` under certify while the binary panicked at
        // index 101). Fail closed — keep the obligation, refuse the proof.
        // SOUNDNESS: DROP-ONLY. `UnsupportedMir` preclassifies to Unknown and is never
        // Proved, so this can only LOSE proofs, never manufacture one.
        if run >= 4
            && let Some(detail) = self_referential_definition(&vc.formula)
        {
            vc = unsupported_mir_vc(
                func,
                "SelfReferentialDefinition".to_string(),
                detail,
                vc.location.clone(),
            );
        }
        (vc, ite)
    }
}

/// The number of per-row passes, every one of which runs outside the tests.
const PASSES: usize = 4;

/// How many of the per-row passes run, in order: all of them.
#[cfg(not(test))]
fn passes_run() -> usize {
    PASSES
}

/// How many of the per-row passes run, in order: all of them, unless a per-pass parity
/// test stops this thread's sinks after the first few (`seam::passes_through`).
#[cfg(test)]
fn passes_run() -> usize {
    seam::PASSES_RUN.with(std::cell::Cell::get)
}

/// The one row of a generation the work meter refused: a fail-closed `UnsupportedMir`
/// marker for the whole function, its formula `Bool(true)` (moved from
/// `generate_vcs_impl_with_origins`, which refuses with it, T3 C08s).
pub(super) fn work_budget_refusal(func: &VerifiableFunction) -> VerificationCondition {
    unsupported_mir_vc(
        func,
        "TrustVcGenWorkBudgetExceeded".to_string(),
        format!(
            "function `{}` exceeded the VC-generation work budget (recursive-datatype \
             clone explosion during generation); its obligations are left Unknown \
             (fail-closed) to keep the rest of the crate verifiable",
            func.name
        ),
        func.span.clone(),
    )
}

/// The first `Eq(Var(v), rhs)` in `f` where `v` occurs free in `rhs` and `rhs` is
/// not `v` itself, rendered for the refusal detail.
///
/// `x == x` is a harmless tautology and is deliberately not reported; `x == x + k`
/// is unsatisfiable and is what poisons a block.
pub(super) fn self_referential_definition(f: &Formula) -> Option<String> {
    #[inline]
    fn is_eq_free_leaf(node: &Formula) -> bool {
        matches!(
            node,
            Formula::Int(_)
                | Formula::UInt(_)
                | Formula::Bool(_)
                | Formula::Rat(_)
                | Formula::BitVec { .. }
                | Formula::Var(..)
                | Formula::SymVar(..)
                | Formula::FpConst { .. }
                | Formula::FpNaN { .. }
                | Formula::FpInf { .. }
                | Formula::FpZero { .. }
                | Formula::FpRoundingMode(_)
        )
    }

    fn walk(node: &Formula, found: &mut Option<String>) -> bool {
        if is_eq_free_leaf(node) {
            return true;
        }
        match node {
            Formula::Eq(l, r) => {
                if let Some(name) = l.var_name()
                    && !matches!(
                        r.as_ref(),
                        Formula::Int(_)
                            | Formula::UInt(_)
                            | Formula::Bool(_)
                            | Formula::BitVec { .. }
                            | Formula::Var(..)
                            | Formula::SymVar(..)
                    )
                    && r.var_name() != Some(name)
                    && trust_types::any_free_variable_name(r, &mut |v| v == name)
                {
                    *found = Some(format!("`{name}` is defined in terms of itself: {node:?}"));
                    return false;
                }
                walk(l, found) && walk(r, found)
            }
            Formula::Lt(l, r) | Formula::Le(l, r) | Formula::Gt(l, r) | Formula::Ge(l, r) => {
                walk(l, found) && walk(r, found)
            }
            other => trust_types::all_formula_children(other, |child| walk(child, found)),
        }
    }

    let mut found = None;
    let _ = walk(f, &mut found);
    found
}

/// The per-function fact tables a separation-engine row is wrapped with (moved from
/// `generate_vcs_impl_with_origins`'s separation loop, T3 C08s): built once per function,
/// in the order that loop built them, and applied to each row by [`Self::wrap`].
pub(super) struct SepFacts {
    /// The path-guard map whose paths a row's guards are conjoined over.
    guard_paths: std::rc::Rc<PathGuardMap>,
    /// Trust (lane-A CSE): the statement-version oracle, built ONCE for this function and
    /// reused across every sep VC's `v2_formula_with_path_guards`.
    sv: std::rc::Rc<StmtVersionCtx>,
    /// The path DEFINITIONS of each block.
    path_defs: std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>,
    /// Semantic assert-passed guards capture CheckedBinaryOp results (e.g.
    /// `sum == start + len` from `let sum = start + len`) that the regular
    /// def extraction skips — required so a guard `sum <= N` connects to an
    /// obligation over `start + len`.
    sem_guards: std::rc::Rc<FxHashMap<BlockId, Vec<Formula>>>,
    /// Facts from `a.checked_add(b)?` — the unwrapped value equals `a + b` on
    /// the success path. The library `checked_add` is a CALL + `Try::branch` +
    /// `Continue(.0)` read that the per-block CheckedBinaryOp semantics miss;
    /// these connect a `checked_add(...)? <= self.len` guard to an obligation
    /// over `start + len` (aterm's `slice` offset case).
    checked_facts: Vec<Formula>,
    /// Memory-model unsafe beachhead: the div-exact material implication
    /// `¬(a%c==0) ∨ (dest*c==a)` (a tautology) discharges a `from_raw_parts(p, a/c)`
    /// byte-bounds obligation over the extent `c*(a/c)` once the real `a.is_multiple_of(c)`
    /// path guard supplies `a%c==0`. See `build_division_exact_facts`.
    div_exact: Vec<Formula>,
}

impl SepFacts {
    /// The tables of `func`.
    pub(super) fn for_function(func: &VerifiableFunction) -> SepFacts {
        let guard_paths = super::guard_map_for(func);
        let sv = super::stmt_versions_for(func);
        let path_defs = super::path_definition_map_for(func);
        let sem_guards = super::semantic_guard_map_for(func, None);
        let checked_facts = crate::guards::build_checked_arith_facts(func);
        let div_exact = build_division_exact_facts(func);
        SepFacts { guard_paths, sv, path_defs, sem_guards, checked_facts, div_exact }
    }

    /// Conjoin a separation row's block path DEFINITIONS and path GUARDS (the same
    /// machinery the V2 VCs use) so a guarded unsafe op — e.g.
    /// `if len <= N { from_raw_parts(p, len) }` — can be discharged. The defs
    /// (`_3 = (_1 <= N)`) are required for the guard (`_3` is true) to connect
    /// to the obligation's variables; guards alone are insufficient.
    pub(super) fn wrap(
        &self,
        func: &VerifiableFunction,
        mut vc: VerificationCondition,
        block_id: BlockId,
        sep_op: MirOp,
    ) -> VerificationCondition {
        // Trust (2026-10-03, KNOWN_HAZARDS "SOURCE REPAIR 2026-09-25 — concrete
        // pointer-offset bounds"): the row's OWN block's definitions before its
        // operation, versioned at that use point, as the numeric-panic call rows get
        // them (`v2_build_divrem_vc_raw`). The path definitions below are the
        // DOMINATING blocks' facts; `s.as_ptr().add(s.len())` defines its count
        // `_3 = PtrMetadata(copy _1)` in the SAME block as the `add` call, so the
        // offset row `_3 > s__slice_len` had no tie to the slice's length and was
        // refuted for an in-bounds one-past pointer.
        if let Some(block) = func.body.blocks.get(block_id.0) {
            let end = match sep_op {
                MirOp::Statement(index) => index,
                MirOp::Terminator => block.stmts.len(),
            };
            vc.formula = super::block_defs::v2_formula_with_block_defs_at_point(
                func, block, end, vc.formula,
            );
        }
        if let Some(path_defs) = self.path_defs.get(&block_id)
            && !path_defs.is_empty()
        {
            let live = v2_live_path_defs(func, &func.body.blocks[block_id.0], path_defs);
            if !live.is_empty() {
                let mut conjuncts = live;
                conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
                vc.formula = Formula::And(conjuncts);
            }
        }
        if let Some(paths) = self.guard_paths.get(&block_id) {
            vc.formula = v2_formula_with_path_guards(func, &self.sv, block_id, paths, vc.formula);
        }
        if let Some(sem) = self.sem_guards.get(&block_id)
            && !sem.is_empty()
        {
            let mut conjuncts = Vec::with_capacity(sem.len() + 1);
            conjuncts.extend_from_slice(sem);
            conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
            vc.formula = Formula::And(conjuncts);
        }
        if !self.checked_facts.is_empty() {
            let mut conjuncts = Vec::with_capacity(self.checked_facts.len() + 1);
            conjuncts.extend_from_slice(&self.checked_facts);
            conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
            vc.formula = Formula::And(conjuncts);
        }
        if !self.div_exact.is_empty() {
            let mut conjuncts = Vec::with_capacity(self.div_exact.len() + 1);
            conjuncts.extend_from_slice(&self.div_exact);
            conjuncts.push(std::mem::replace(&mut vc.formula, Formula::Bool(true)));
            vc.formula = Formula::And(conjuncts);
        }
        vc
    }
}

/// The per-pass parity tests' seam (`super::row_sink_tests`): stop every sink of this
/// thread after its first `n` passes while some work runs.
#[cfg(test)]
pub(super) mod seam {
    use std::cell::Cell;

    /// The number of per-row passes.
    pub(crate) const PASSES: usize = super::PASSES;

    thread_local! {
        pub(super) static PASSES_RUN: Cell<usize> = const { Cell::new(PASSES) };
        /// Rows (and walks) that joined out of their phase, summed over this thread's
        /// finished sinks.
        pub(super) static OUT_OF_PHASE: Cell<usize> = const { Cell::new(0) };
    }

    /// The rows (and walks) that joined out of their phase in every sink this thread has
    /// finished: a test that reads it before and after a generation sees that
    /// generation's.
    pub(crate) fn out_of_phase_joins() -> usize {
        OUT_OF_PHASE.with(Cell::get)
    }

    /// Run `work` with every sink of this thread running only its first `n` passes; the
    /// count is restored when `work` returns or unwinds.
    pub(crate) fn passes_through<R>(n: usize, work: impl FnOnce() -> R) -> R {
        struct Restore(usize);
        impl Drop for Restore {
            fn drop(&mut self) {
                PASSES_RUN.with(|cell| cell.set(self.0));
            }
        }
        let _restore = Restore(PASSES_RUN.with(|cell| cell.replace(n)));
        work()
    }
}
