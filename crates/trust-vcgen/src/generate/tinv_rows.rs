//! TINV step 7, increment 7.5: the crate-private shim that turns TINV obligation points
//! into SITUATED verification conditions inside the ordinary safety walk
//! (`docs/design/2026-10-04-type-invariant-tinv.md` §2 P4).
//!
//! THERE IS NO SECOND DECORATION PIPELINE. A request ([`TinvRowRequest`]) is installed on a
//! thread-local stack ([`enter_tinv_rows`]); two hooks in
//! `generate_v2_safety_vcs_impl_with_origins_checked` push one raw row per requested
//! `(type, conjunct, point)` at the row's own point — terminator rows before the
//! terminator pad, statement rows at their statement — and every shared pass of that
//! walk then decorates the row exactly as it decorates an ordinary safety row: live
//! inter-block path defs at the point, the range-yield/str/global facts, the entry
//! (precondition) conjoin with the whole-row version rename at the point, path guards
//! (or the degraded replacement), semantic guards, the type-range battery and the final
//! SSA-token normalize. Each pass mirrors itself onto the row's `ObligationRecord`, so
//! the record replays to the formula.
//!
//! THE RAW ROW, built here at the row's point `(block, row_point)`:
//! * the core `I(σ)` is instantiated by the caller (`obligations::type_invariant_check_vcs`)
//!   from UNVERSIONED field terms;
//! * a U row's state is applied here, from the terminator's own
//!   [`terminator_def_names_structured`] havoc list (the list the normal successor's
//!   versioning reads, under the same `callee_write_set` scope): every σ name it
//!   rebinds becomes `n#tinvu_s{b}`, a havoc symbol that no rename stamps (it carries
//!   `#`) and no SSA collapse folds (`version_token_is_tinv_unwind_havoc`). A
//!   drop-and-replace then overwrites the names under its place with fresh
//!   `n#tinvu_a{b}` bound to the (havocked) replacement operand; an `Assert` adds its
//!   failure condition;
//! * post-call facts: every alive conjunct at the root an inventory call received,
//!   versioned and SEALED at the call's single-predecessor target `(T, 0)` with the
//!   walk's own version oracle, attached only where `(T, 0)` dominates the row point
//!   (where equal tokens are equal values);
//! * `raw = And([post-call facts.., binding/failure.., Not(core)])` (or `Not(core)`),
//!   which goes through [`v2_formula_with_block_defs_at_point_recorded`] at
//!   `row_rename_point`, the same-block defs each stamped at its establish point, and
//!   the record is seeded `{renamed body, [ConjoinFactsLast { kept }]}` exactly as the
//!   recorded safety rows are.
//!
//! R ROWS AT JOINS (TINV-9(a)). An R row at a block `J` with two or more predecessors is
//! SPLIT, before the walk, into one EDGE PART per predecessor edge `p -> J`
//! ([`TinvRowRequest::split_join_returns`], gates in [`join_parts`]). Each part is built by
//! the terminator hook at `(p, terminal)`, so the walk decorates it exactly as any
//! terminator row at `p`, with the edge's guard as its FIRST raw conjunct (`true` for an
//! unguarded edge; the situatedness gate skips that slot, so the guard never counts as
//! binding the core's names); it carries
//! `edge: Some(p)` in its key and kind. CONTRACT: the point `(ty, R, J, conjunct, ordinal)`
//! is discharged only when EVERY part is (UNSAT, and since 7.7 kernel-certified); one
//! proved part discharges nothing. Houdini aggregates parts with AND (any failing part
//! drops the conjunct) and refuses the type when a point's part set is not exactly
//! `J`'s predecessor set. Any gate failure keeps the single row, which stays unsituated
//! (fail-closed).
//!
//! WHY A PART IS SOUND. Every execution reaching `(J, terminal)` enters `J` along exactly
//! one edge `p -> J` (G1: every entering edge is a real, reachable block edge, so none is
//! missed). Along it the state at `J`'s entry is the state at `p`'s terminal: G3 admits only
//! Goto, SwitchInt and Assert-success edges whose terminator rebinds no name the core
//! reads. G2 makes every such name's value at `J`'s terminal its value at `J`'s entry. So a
//! violation at `J` exists iff, for some `p`, a violation at `p`'s terminal together with
//! the edge condition does. The edge guard is the RAW discriminant (never a predicate
//! substituted for it, see [`join_edge_guard`]) and exact or weakened (the routing values
//! OR-ed, never conjoined: G6), so it is true on every execution the part covers.
//!
//! NO AUTHORITY. Since 7.7 the kernel kind gate admits `VcKind::TypeInvariant` and the
//! row-level situatedness gate decides each row (TINV-9(j)); a row is still not
//! authority until Houdini certifies it, and nothing here publishes a row: the caller gets them back keyed by
//! [`TinvRowKey`] through the coverage match of [`tinv_check_rows`], which refuses the
//! whole body unless EVERY requested row came back undegraded.

use std::cell::RefCell;
use std::rc::Rc;

use super::*;
use crate::type_invariant::Sigma;
use crate::type_invariant::obligations::{
    TinvObligationRefusal, TinvPointRow, TinvRowKey, TinvStateSpec, field_terms,
};

/// One requested row: a point of one candidate type, checked for one conjunct.
#[derive(Debug, Clone)]
pub(crate) struct RequestRow {
    pub(crate) key: TinvRowKey,
    /// Index into [`TinvRowRequest::types`].
    pub(crate) ty: usize,
    pub(crate) point: TinvPointRow,
    /// The UNVERSIONED field terms of the row's root (or aggregate operands).
    pub(crate) sigma: Sigma,
    /// `I(σ)` for the row's conjunct, over `sigma`'s terms.
    pub(crate) core: Formula,
    /// An edge part's guard (TINV-9(a)): the UNVERSIONED condition under which the
    /// predecessor `key.edge` routes to the join, renamed with the row at the
    /// predecessor's terminal. `Some` for every edge part (`true` for an unguarded or
    /// weakened edge), `None` for an unsplit row.
    pub(crate) edge_guard: Option<Formula>,
}

/// The block whose terminator hook builds `row`: the predecessor of an edge part, the
/// row's own block otherwise.
fn emit_block(row: &RequestRow) -> usize {
    row.key.edge.unwrap_or(row.point.site.block)
}

/// What every row of one candidate type shares.
#[derive(Debug, Clone)]
pub(crate) struct RequestType {
    pub(crate) def_path: String,
    /// `(target, facts)`: the single-predecessor normal target of an inventory call and
    /// every alive conjunct instantiated, UNVERSIONED, at a root that call received.
    pub(crate) post_calls: Vec<(BlockId, Vec<Formula>)>,
    /// The type's E points in this body, each with the field equations its aggregate
    /// statement makes true (see [`Construction`]).
    pub(crate) constructions: Vec<Construction>,
    /// TINV-21: the ARM FACTS of this body (see [`ArmFact`]). Always empty in a lemma
    /// probe (`type_invariant::arm_lemma`): lemmas never consume lemmas.
    pub(crate) arm_facts: Vec<ArmFact>,
}

/// TINV-21 (2026-10-06): the instantiated `Some`-arm lemmas of one inventory call.
///
/// `facts` are UNVERSIONED instances, at the root the call received, of formulas a
/// kernel-certified lemma about the CALLEE's body states: "when the callee returns
/// `Some`, its `*param` satisfies φ" (`type_invariant::arm_lemma`). The callee's
/// `*param` at its `Return` is the caller's root at `(seal, 0)` — `seal` is the call's
/// single-predecessor normal target, and nothing runs between the callee's `Return` and
/// it — so each fact is versioned and SEALED at `(seal, 0)` like a post-call fact. It
/// is true only on executions where the call returned `Some`: `region` is the `Some`
/// arm of a clean switch on the call's destination at `seal`, or the `Continue` arm of
/// core's authenticated `Try::branch` hop from `seal` (`guards::option_some_arm`), each
/// hop entered only from the previous one. So a fact is attached only to rows whose hook
/// block `region` dominates — for an EDGE PART that block is the predecessor
/// `key.edge`, not the join ([`emit_block`]) — and only when the row's own rename leaves
/// the sealed fact unchanged ([`tinv_sealed_region_hyps`]). No discriminant term is
/// introduced or read: the `Some`-ness is carried by the CFG region alone.
#[derive(Debug, Clone)]
pub(crate) struct ArmFact {
    pub(crate) seal: BlockId,
    pub(crate) region: BlockId,
    pub(crate) facts: Vec<Formula>,
    /// Index-aligned with `facts`: which lemma each fact instantiates (callee, type,
    /// parameter, φ). Recorded per row when the fact is attached ([`RowArmUse`]), so a
    /// certificate can tie each carried lemma to the hypothesis a row assumed.
    pub(crate) uses: Vec<crate::type_invariant::arm_lemma::ArmLemmaUse>,
}

/// TINV-21: one arm fact a row ASSUMED: the lemma it instantiates and the sealed,
/// versioned hypothesis the row carries for it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RowArmUse {
    pub lemma: crate::type_invariant::arm_lemma::ArmLemmaUse,
    pub sealed: Formula,
}

/// The CONSTRUCTION FACTS of one E point `root = S { ops.. }` at `(block, stmt)`: for
/// every field term both sides render, `term(root.f) == term(op_f)`, UNVERSIONED. The
/// aggregate statement makes each equation true of the root's value just after it and
/// the operands' values just before it, and [`construction_facts`] attaches them, so
/// versioned, only to rows the construction provably still describes.
///
/// WHY THIS IS NOT THE SAFETY LANE'S SUPPRESSED FIELD DEF. The ordinary walk drops an
/// aggregate's field defs when the local is mutably borrowed ANYWHERE
/// (`guards::extract_block_definitions`, hunt-7): a write through the `&mut` (`*r = b`)
/// does not bump the field's version token, so a token-keyed equation can be read
/// after the write and be stale. Here the equation reaches a row only when the row is
/// in the construction's own block, after it, and every statement in between is one
/// that cannot write memory behind a token ([`untracked_write_free`]): no write through
/// a `Deref`, no call (a call is a terminator, and the row checks the state BEFORE its
/// block's terminator), no discriminant, `Deinit` or intrinsic statement. A write in
/// between to the root itself is a versioned def, after which the row reads a NEW token
/// and the equation, about the old one, is merely unused.
#[derive(Debug, Clone)]
pub(crate) struct Construction {
    pub(crate) block: BlockId,
    pub(crate) stmt: usize,
    /// `(root field term, operand term)` pairs, unversioned.
    pub(crate) pairs: Vec<(Formula, Formula)>,
}

/// Whether every statement of `block` strictly after `from` and before `to` (`to`
/// clamped to the terminal) is one that writes no memory the version oracle cannot see:
/// an `Assign` whose place has no `Deref`, a storage marker of a local other than
/// `root_local`, a `PlaceMention` or a `Retag`. Anything else (a write through a
/// pointer, a discriminant write, `Deinit`, an intrinsic or `copy_nonoverlapping`
/// statement, an unknown statement) refuses.
fn untracked_write_free(
    block: &trust_types::BasicBlock,
    from: usize,
    to: usize,
    root_local: usize,
) -> bool {
    let to = to.min(block.stmts.len());
    block.stmts.iter().take(to).skip(from + 1).all(|st| match st {
        Statement::Assign { place, .. } => !place.projections.contains(&Projection::Deref),
        Statement::StorageLive(l) | Statement::StorageDead(l) => *l != root_local,
        Statement::PlaceMention(_) | Statement::Retag { .. } => true,
        _ => false,
    })
}

/// The construction facts (see [`Construction`]) a row at `(block, row_point)` may
/// assume, versioned: each equation's root side is renamed just after the aggregate
/// statement and its operand side just before it, both sealed against a later rename,
/// and an equation is kept only if the row's own rename at `end` leaves it unchanged.
/// Only constructions in `block` itself, strictly before the row, with an
/// [`untracked_write_free`] gap qualify.
fn construction_facts(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    prepared: &PreparedTypeFacts,
    row: &RequestRow,
    block: &trust_types::BasicBlock,
    end: usize,
) -> Vec<Formula> {
    let row_point = row.point.row_point;
    let clamped = row_point.min(block.stmts.len());
    let mut out = Vec::new();
    for c in &prepared.constructions {
        if c.block != block.id || c.stmt >= clamped {
            continue;
        }
        if !untracked_write_free(block, c.stmt, row_point, c.root_local) {
            continue;
        }
        for eq in &c.equations {
            if !super::path_defs::version_rename_needs_rewrite(eq, sv, func, block.id, end) {
                out.push(eq.clone());
            }
        }
    }
    out
}

#[derive(Debug)]
struct PreparedArmFact {
    seal: BlockId,
    region: BlockId,
    items: Vec<(Formula, crate::type_invariant::arm_lemma::ArmLemmaUse)>,
}

#[derive(Debug)]
struct PreparedConstruction {
    block: BlockId,
    stmt: usize,
    root_local: usize,
    equations: Vec<Formula>,
}

#[derive(Debug)]
struct PreparedTypeFacts {
    post_calls: Vec<(BlockId, Vec<Formula>)>,
    arm_facts: Vec<PreparedArmFact>,
    constructions: Vec<PreparedConstruction>,
}

#[derive(Debug, Default)]
struct WalkState {
    /// The first owner walk has started.
    consumed: bool,
    /// A block the owner walk visited twice: a second walk, which emits nothing.
    reused: bool,
    visited: FxHashSet<usize>,
    /// The first refusal a row builder hit; the request then yields nothing.
    error: Option<TinvObligationRefusal>,
    /// TINV-21: the arm facts each built row assumed, by row key.
    arm_uses: Vec<(TinvRowKey, Vec<RowArmUse>)>,
    /// Per-`RequestType` pre-renamed and pre-sealed `(seal, 0)` post-call and arm facts.
    prepared_types: FxHashMap<usize, Rc<PreparedTypeFacts>>,
}

/// The rows one walk of one body must carry, owner-checked by `def_path` and one-shot.
#[derive(Debug)]
pub(crate) struct TinvRowRequest {
    def_path: String,
    types: Vec<RequestType>,
    rows: Vec<RequestRow>,
    /// `(block, row_point)` -> indices into `rows`, in request order.
    by_point: FxHashMap<(usize, usize), Vec<usize>>,
    state: RefCell<WalkState>,
}

fn index_rows(rows: &[RequestRow]) -> FxHashMap<(usize, usize), Vec<usize>> {
    let mut by_point: FxHashMap<(usize, usize), Vec<usize>> = FxHashMap::default();
    for (i, row) in rows.iter().enumerate() {
        by_point.entry((emit_block(row), row.point.row_point)).or_default().push(i);
    }
    by_point
}

impl TinvRowRequest {
    pub(crate) fn new(def_path: String, types: Vec<RequestType>, rows: Vec<RequestRow>) -> Self {
        let by_point = index_rows(&rows);
        TinvRowRequest { def_path, types, rows, by_point, state: RefCell::default() }
    }

    /// The requested keys, in request order.
    pub(crate) fn keys(&self) -> Vec<TinvRowKey> {
        self.rows.iter().map(|r| r.key.clone()).collect()
    }

    /// TINV-9(a): replace every R row at a join that passes [`join_parts`] by its edge
    /// parts (in predecessor order, in the row's place); every other row is kept as is.
    /// `sv` must be the version oracle of the body the walk runs on.
    pub(crate) fn split_join_returns(&mut self, func: &VerifiableFunction, sv: &StmtVersionCtx) {
        let mut out: Vec<RequestRow> = Vec::with_capacity(self.rows.len());
        let mut join_cache: FxHashMap<BlockId, Result<Vec<JoinEdgeSpec>, String>> =
            FxHashMap::default();
        for row in std::mem::take(&mut self.rows) {
            match join_parts_cached(func, sv, &row, &mut join_cache) {
                Ok(parts) => out.extend(parts.into_iter().map(|(p, guard)| {
                    let mut part = row.clone();
                    part.key.edge = Some(p);
                    // Every part carries a guard slot (the situatedness gate skips it).
                    part.edge_guard = Some(guard.unwrap_or(Formula::Bool(true)));
                    part
                })),
                Err(_) => out.push(row),
            }
        }
        self.rows = out;
        self.by_point = index_rows(&self.rows);
    }
}

// ---------------------------------------------------------------------------------------
// TINV-9(a): the per-predecessor split of R rows at joins
// ---------------------------------------------------------------------------------------

/// G5: the most predecessor edges one join point is split over.
pub(crate) const MAX_JOIN_PARTS: usize = 16;

/// The predecessor blocks of `j` over the full (unwind-inclusive) block graph, the edge
/// relation the walk's CFG index is built from, sorted and deduplicated. Read from the
/// body alone, so Houdini can re-derive it independently of the split.
pub(crate) fn block_predecessors(func: &VerifiableFunction, j: BlockId) -> Vec<usize> {
    let mut preds: Vec<usize> = func
        .body
        .blocks
        .iter()
        .filter(|b| super::full_graph_terminator_has_target(&b.terminator, j))
        .map(|b| b.id.0)
        .collect();
    if preds.len() > 1 {
        preds.sort_unstable();
        preds.dedup();
    }
    preds
}

/// G3 and G6 for one edge `pred -> j`: the edge's guard (`None` for a Goto, or when a
/// routing clause has no exact form), or why the edge is not splittable. SwitchInt:
/// every clause routing to `j`, OR-ed; Assert: its success condition; a cleanup (unwind)
/// edge and every other terminator refuse.
///
/// THE GUARD IS THE RAW DISCRIMINANT ([`crate::guards::guard_to_refutation_formula`]):
/// `discr == v`, its negation for `otherwise`, a bool discriminant as its own value. It is
/// NEVER `guard_to_formula`'s predicate substitution, which replaces a bool discriminant
/// by its reaching comparison: renamed at `pred`'s terminal, that comparison reads the
/// compared places' values AT THE SWITCH, and a write to a compared FIELD between the
/// compare and the switch (`_2 = Ge((*_1).0, (*_1).1); (*_1).0 = x; switchInt(_2)`), which
/// that lane's stale-guard withhold does not see, made the guard over-strong and the
/// part a false UNSAT. The raw operand is exact at `pred`'s terminal; its definition
/// reaches the row only through the walk's establish-point-versioned block/path defs.
/// A clause with no exact form weakens the whole guard to `None` (no hypothesis).
fn join_edge_guard(
    func: &VerifiableFunction,
    pred: &trust_types::BasicBlock,
    j: BlockId,
) -> Result<Option<Formula>, String> {
    if pred.terminator.unwind_cleanup_target() == Some(j) {
        return Err(format!("G3: bb{} reaches bb{} on a cleanup edge", pred.id.0, j.0));
    }
    match &pred.terminator {
        Terminator::Goto(t) if *t == j => Ok(None),
        Terminator::SwitchInt { .. } | Terminator::Assert { .. } => {
            let mut disjuncts = Vec::new();
            let mut any_routing = false;
            for c in pred.terminator.discovered_clauses(pred.id) {
                if !matches!(c.target, trust_types::ClauseTarget::Block(t) if t == j) {
                    continue;
                }
                any_routing = true;
                let Some(f) = crate::guards::guard_to_refutation_formula(func, &c.guard) else {
                    // G6 weakened: a clause with no exact form drops the guard, never the edge.
                    return Ok(None);
                };
                disjuncts.push(f);
            }
            if !any_routing {
                return Err(format!("G3: no clause of bb{} routes to bb{}", pred.id.0, j.0));
            }
            match disjuncts.len() {
                1 => Ok(disjuncts.pop()),
                // G6: several routing values are alternatives, never a conjunction.
                _ => Ok(Some(Formula::Or(disjuncts))),
            }
        }
        _ => Err(format!(
            "G3: bb{} -> bb{} is not a Goto, SwitchInt or Assert-success edge",
            pred.id.0, j.0
        )),
    }
}

type JoinEdgeSpec = (usize, Option<Formula>, Vec<String>);

fn join_block_edges(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    j: BlockId,
) -> Result<Vec<JoinEdgeSpec>, String> {
    if !func.body.blocks.get(j.0).is_some_and(|b| b.id == j) {
        return Err(format!("bb{} is not a block of the body", j.0));
    }
    let cfg = sv.cfg();
    let n = cfg.n_blocks();
    let preds = block_predecessors(func, j);
    if preds.len() < 2 {
        return Err("not a join".into());
    }
    // G1.
    if j.0 == 0 {
        return Err("G1: the entry block has an implicit function-entry edge".into());
    }
    if j.0 >= n {
        return Err("G1: the join is outside the walk's CFG".into());
    }
    let mut cfg_preds: Vec<usize> = cfg.preds(j.0 as u32).iter().map(|&p| p as usize).collect();
    cfg_preds.sort_unstable();
    cfg_preds.dedup();
    if cfg_preds != preds {
        return Err(format!("G1: the CFG predecessors {cfg_preds:?} are not the edges {preds:?}"));
    }
    let entry = cfg.entry_def();
    if preds.iter().any(|&p| p >= n || !cfg.dom().dominates(entry, p as u32)) {
        return Err("G1: a predecessor is not a block reachable from the entry".into());
    }
    // G4.
    if preds.contains(&j.0) {
        return Err("G4: the join is its own predecessor".into());
    }
    // G5.
    if preds.len() > MAX_JOIN_PARTS {
        return Err(format!("G5: {} predecessors exceed the cap {MAX_JOIN_PARTS}", preds.len()));
    }
    let mut edges = Vec::with_capacity(preds.len());
    for &p in &preds {
        let Some(pb) = func.body.blocks.get(p).filter(|b| b.id.0 == p) else {
            return Err(format!("G1: bb{p} is not a block of the body"));
        };
        let guard = join_edge_guard(func, pb, j)?;
        let defs = terminator_def_names(func, pb);
        edges.push((p, guard, defs));
    }
    Ok(edges)
}

fn join_parts_with_edges(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    row: &RequestRow,
    j: BlockId,
    edges: &[JoinEdgeSpec],
) -> Result<Vec<(usize, Option<Formula>)>, String> {
    let Some(jb) = func.body.blocks.get(j.0).filter(|b| b.id == j) else {
        return Err(format!("bb{} is not a block of the body", j.0));
    };
    // G2.
    let mut names: Vec<&str> = Vec::new();
    if !trust_types::all_formula_nodes(&row.core, &mut |node| {
        if let Formula::Var(name, _) = node {
            if name.contains('#') {
                return false;
            }
            if !names.contains(&name.as_str()) {
                names.push(name.as_str());
            }
        }
        true
    }) || names.is_empty()
    {
        return Err("G2: the core reads no unversioned program state".into());
    }
    for &name in &names {
        if sv.version_token_at(func, j, jb.stmts.len(), name)
            != sv.version_token_at(func, j, 0, name)
        {
            return Err(format!("G2: bb{} rebinds `{name}` before its terminator", j.0));
        }
    }
    // G3 and G6.
    let mut parts = Vec::with_capacity(edges.len());
    for (p, guard, defs) in edges {
        if let Some(name) = names.iter().find(|name| defs.iter().any(|d| write_rebinds(d, name))) {
            return Err(format!("G3: bb{p}'s terminator rebinds `{name}`"));
        }
        parts.push((*p, guard.clone()));
    }
    Ok(parts)
}

fn join_parts_cached(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    row: &RequestRow,
    join_cache: &mut FxHashMap<BlockId, Result<Vec<JoinEdgeSpec>, String>>,
) -> Result<Vec<(usize, Option<Formula>)>, String> {
    if row.point.point != trust_types::TypeInvariantPoint::Return
        || row.point.row_point != usize::MAX
        || !matches!(row.point.state, TinvStateSpec::At)
        || row.point.failure.is_some()
        || row.key.edge.is_some()
    {
        return Err("not an unsplit R terminator row".into());
    }
    let j = BlockId(row.point.site.block);
    let edges = match join_cache.entry(j).or_insert_with(|| join_block_edges(func, sv, j)) {
        Ok(edges) => edges,
        Err(err) => return Err(err.clone()),
    };
    join_parts_with_edges(func, sv, row, j, edges)
}

/// The edge parts of `row`, as `(predecessor, edge guard)` in predecessor order, or why
/// the row is kept whole. Only an R terminator row in the `At` state is split, and only
/// when every gate holds:
/// * G1: `J` is not the entry block (whose implicit function-entry edge no part would
///   cover), and every predecessor on the walk's augmented CFG is a real block reachable
///   from the entry, agreeing with [`block_predecessors`];
/// * G2: for every name the core reads, the version oracle's token at `J`'s terminal is
///   its token at `J`'s entry (`J`'s statements rebind nothing the core reads);
/// * G3: each edge is a Goto, SwitchInt or Assert-success edge (no cleanup edge), and the
///   predecessor's terminator rebinds no name the core reads;
/// * G4: no predecessor is `J` itself;
/// * G5: at most [`MAX_JOIN_PARTS`] predecessors;
/// * G6: an edge guard is exact or weakened, its routing values OR-ed.
pub(crate) fn join_parts(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    row: &RequestRow,
) -> Result<Vec<(usize, Option<Formula>)>, String> {
    if row.point.point != trust_types::TypeInvariantPoint::Return
        || row.point.row_point != usize::MAX
        || !matches!(row.point.state, TinvStateSpec::At)
        || row.point.failure.is_some()
        || row.key.edge.is_some()
    {
        return Err("not an unsplit R terminator row".into());
    }
    let j = BlockId(row.point.site.block);
    let edges = join_block_edges(func, sv, j)?;
    join_parts_with_edges(func, sv, row, j, &edges)
}

thread_local! {
    static TINV_ROWS: RefCell<Vec<(u64, Rc<TinvRowRequest>)>> = const { RefCell::new(Vec::new()) };
    static TINV_ROWS_NEXT_ID: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// RAII scope of an installed request. Removes exactly the frame it owns, on normal
/// return and on unwind (the `callee_write_set::CalleeWriteSetGuard` pattern).
pub(crate) struct TinvRowGuard {
    id: u64,
    _thread_affine: std::marker::PhantomData<Rc<()>>,
}

impl Drop for TinvRowGuard {
    fn drop(&mut self) {
        let _ = TINV_ROWS.try_with(|stack| {
            let mut stack = stack.borrow_mut();
            if let Some(i) = stack.iter().rposition(|(id, _)| *id == self.id) {
                stack.remove(i);
            }
        });
    }
}

/// Install `request` for the duration of the returned guard.
pub(crate) fn enter_tinv_rows(request: Rc<TinvRowRequest>) -> TinvRowGuard {
    let id = TINV_ROWS_NEXT_ID.with(|next| {
        let id = next.get();
        next.set(id.wrapping_add(1));
        id
    });
    TINV_ROWS.with(|stack| stack.borrow_mut().push((id, request)));
    TinvRowGuard { id, _thread_affine: std::marker::PhantomData }
}

/// The installed request, if it belongs to `func`. Absent, or owned by another body (a
/// nested generation of a callee), the hooks do nothing at all: ordinary generation is
/// byte-identical.
pub(crate) fn active_request(func: &VerifiableFunction) -> Option<Rc<TinvRowRequest>> {
    TINV_ROWS.with(|stack| {
        let stack = stack.borrow();
        let (_, top) = stack.last()?;
        (top.def_path == func.def_path).then(|| Rc::clone(top))
    })
}

/// Terminator hook: push the request's terminator rows (`row_point == usize::MAX`) of
/// `block`, in request order. Called once per block by the safety walk, before the
/// terminator pad, so the rows are labelled with the terminal use point.
pub(super) fn push_tinv_terminator_rows<'a>(
    func: &VerifiableFunction,
    req: Option<&TinvRowRequest>,
    sv_for: impl FnOnce() -> &'a StmtVersionCtx,
    block: &trust_types::BasicBlock,
    block_vcs: &mut Vec<(BlockId, VerificationCondition)>,
) {
    let Some(req) = req else { return };
    {
        let mut st = req.state.borrow_mut();
        st.consumed = true;
        if !st.visited.insert(block.id.0) {
            st.reused = true;
        }
    }
    push_rows(func, sv_for, req, block, usize::MAX, block_vcs);
}

/// Statement hook: push the request's rows at statement `stmt_index` of `block` (E and
/// M rows, the state before the statement), in request order.
pub(super) fn push_tinv_statement_rows<'a>(
    func: &VerifiableFunction,
    req: Option<&TinvRowRequest>,
    sv_for: impl FnOnce() -> &'a StmtVersionCtx,
    block: &trust_types::BasicBlock,
    stmt_index: usize,
    block_vcs: &mut Vec<(BlockId, VerificationCondition)>,
) {
    let Some(req) = req else { return };
    push_rows(func, sv_for, req, block, stmt_index, block_vcs);
}

fn push_rows<'a>(
    func: &VerifiableFunction,
    sv_for: impl FnOnce() -> &'a StmtVersionCtx,
    req: &TinvRowRequest,
    block: &trust_types::BasicBlock,
    row_point: usize,
    block_vcs: &mut Vec<(BlockId, VerificationCondition)>,
) {
    let Some(indices) = req.by_point.get(&(block.id.0, row_point)) else { return };
    if indices.is_empty() {
        return;
    }
    {
        let state = req.state.borrow();
        if state.reused || state.error.is_some() {
            return;
        }
    }
    let sv = sv_for();
    let mut cached_havoc: Option<Vec<String>> = None;
    for &i in indices {
        match build_row(func, sv, req, &req.rows[i], block, &mut cached_havoc) {
            Ok(vc) => block_vcs.push((block.id, vc)),
            Err(e) => {
                req.state.borrow_mut().error.get_or_insert(e);
                return;
            }
        }
    }
}

/// The token family of TINV unwind havocs: `s{b}` for a havocked name, `a{b}` for a name
/// a drop-and-replace overwrites. Both start with `crate::TINV_UNWIND_HAVOC_TOKEN_PREFIX`.
fn tinvu_name(name: &str, kind: char, block: BlockId) -> String {
    format!("{name}#{}{kind}{}", crate::TINV_UNWIND_HAVOC_TOKEN_PREFIX, block.0)
}

/// Refuse a minted `#`-bearing spelling that a local is literally named (the `seal_bare_reads` rule).
fn check_collision(sv: &StmtVersionCtx, name: &str) -> Result<(), TinvObligationRefusal> {
    if sv.has_hash_local_named(name) {
        return Err(TinvObligationRefusal::Shim(format!(
            "the TINV unwind havoc `{name}` collides with a local of that name"
        )));
    }
    Ok(())
}

/// `f` with every variable that a name of `havoc` rebinds (`write_rebinds`, the relation
/// the normal successor's versioning uses) renamed to its `#tinvu_s{b}` havoc, and
/// every variable in `overwrite` replaced by its fresh symbol first.
fn apply_state(
    sv: &StmtVersionCtx,
    f: &Formula,
    havoc: &[String],
    overwrite: &FxHashMap<String, Formula>,
    block: BlockId,
) -> Result<Formula, TinvObligationRefusal> {
    if (havoc.is_empty() && overwrite.is_empty())
        || !trust_types::any_formula_node(f, &mut |node| {
            matches!(
                node,
                Formula::Var(name, _)
                    if !name.contains('#')
                        && (overwrite.contains_key(name)
                            || havoc.iter().any(|h| write_rebinds(h, name)))
            )
        })
    {
        return Ok(f.clone());
    }
    let mut collision: Option<TinvObligationRefusal> = None;
    let out = f.clone().map(&mut |node| match node {
        Formula::Var(name, sort) if !name.contains('#') => {
            if let Some(fresh) = overwrite.get(&name) {
                return fresh.clone();
            }
            if havoc.iter().any(|h| write_rebinds(h, &name)) {
                let spelled = tinvu_name(&name, 's', block);
                if let Err(e) = check_collision(sv, &spelled) {
                    collision.get_or_insert(e);
                }
                return Formula::Var(spelled, sort);
            }
            Formula::Var(name, sort)
        }
        other => other,
    });
    match collision {
        Some(e) => Err(e),
        None => Ok(out),
    }
}

fn place_within(inner: &Place, outer: &Place) -> bool {
    inner.local == outer.local && inner.projections.starts_with(&outer.projections)
}

/// The state-bound core and the bindings it needs, for the row's state spec.
fn situate_core(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    row: &RequestRow,
    block: &trust_types::BasicBlock,
    cached_havoc: &mut Option<Vec<String>>,
) -> Result<(Formula, Vec<Formula>), TinvObligationRefusal> {
    let b = block.id;
    let havoc = match &row.point.state {
        TinvStateSpec::At => return Ok((row.core.clone(), Vec::new())),
        _ => cached_havoc
            .get_or_insert_with(|| terminator_def_names_structured(func, block).flatten(func))
            .as_slice(),
    };
    match &row.point.state {
        TinvStateSpec::At => Ok((row.core.clone(), Vec::new())),
        // DEVIATION (conservative): `inventory_passed` is NOT exempted from the havoc.
        // Those roots owe no row at this call (obligations.rs skips them), so the
        // exemption could only reach ANOTHER root's names, and a root lying under a
        // passed one may be written by the callee. Havocking every rebound name is the
        // fail-closed reading.
        TinvStateSpec::UnwindCallHavoc { .. } | TinvStateSpec::UnwindDropHavoc(_) => {
            Ok((apply_state(sv, &row.core, havoc, &FxHashMap::default(), b)?, Vec::new()))
        }
        TinvStateSpec::UnwindDropAssign { place, rvalue } => {
            let source = match rvalue {
                Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) => Some(q),
                _ => None,
            };
            let mut overwrite: FxHashMap<String, Formula> = FxHashMap::default();
            let mut bindings = Vec::new();
            let mut fp = row.point.root.clone();
            for i in 0..row.sigma.value.len().max(row.sigma.len.len()) {
                fp.projections.push(Projection::Field(i));
                if !place_within(&fp, place) {
                    fp.projections.pop();
                    continue;
                }
                // The term the replacement value gives this field, when the rvalue is a
                // plain place read; otherwise a pure havoc.
                let src = source.map(|q| {
                    let mut qp = q.clone();
                    qp.projections
                        .extend(fp.projections[place.projections.len()..].iter().cloned());
                    field_terms(func, &qp)
                });
                fp.projections.pop();
                let pairs = [
                    (
                        row.sigma.value.get(i).cloned().flatten(),
                        src.as_ref().and_then(|s| s.0.clone()),
                    ),
                    (
                        row.sigma.len.get(i).cloned().flatten(),
                        src.as_ref().and_then(|s| s.1.clone()),
                    ),
                ];
                for (term, src_term) in pairs {
                    let Some(Formula::Var(name, sort)) = term else { continue };
                    let spelled = tinvu_name(&name, 'a', b);
                    check_collision(sv, &spelled)?;
                    let fresh = Formula::Var(spelled, sort);
                    if let Some(src_term) = src_term {
                        // The replacement operand is havocked by the drop glue too.
                        let src_term =
                            apply_state(sv, &src_term, havoc, &FxHashMap::default(), b)?;
                        bindings.push(Formula::Eq(Box::new(fresh.clone()), Box::new(src_term)));
                    }
                    overwrite.insert(name, fresh);
                }
            }
            Ok((apply_state(sv, &row.core, havoc, &overwrite, b)?, bindings))
        }
    }
}

/// Whether program point `(target, 0)` dominates `(block, _)` on the walk's own CFG
/// (the unwind-inclusive dominator tree the version oracle resolves over): the same
/// block, or `target` a reachable strict dominator of `block`.
pub(super) fn entry_dominates(sv: &StmtVersionCtx, target: BlockId, block: BlockId) -> bool {
    let cfg = sv.cfg();
    let n = cfg.n_blocks();
    if target.0 >= n || block.0 >= n {
        return false;
    }
    let dom = cfg.dom();
    if !dom.dominates(cfg.entry_def(), target.0 as u32) {
        return false;
    }
    target == block || dom.dominates(target.0 as u32, block.0 as u32)
}

pub(super) fn seal_fact_at_block_entry(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    seal: BlockId,
    f: &Formula,
) -> Option<Formula> {
    let renamed = version_rename_at(f, sv, func, seal, 0);
    seal_bare_reads(sv, func, seal, 0, renamed)
}

pub(super) fn keep_sealed_region_fact(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    seal: BlockId,
    region: BlockId,
    sealed: &Formula,
    block: BlockId,
    end: usize,
) -> bool {
    entry_dominates(sv, seal, block)
        && entry_dominates(sv, region, block)
        && !super::path_defs::version_rename_needs_rewrite(sealed, sv, func, block, end)
}

/// The post-call facts that hold at a row at `(block, end)` (`end` = the row's rename
/// point), each with the call target `T` it was sealed at: every fact of every
/// `(T, facts)` entry, in order, versioned at `(T, 0)` and SEALED there
/// ([`seal_bare_reads`]) with the walk's own oracle, kept only where `(T, 0)` dominates
/// `block` ([`entry_dominates`], the unwind-inclusive tree) and the row's own rename at
/// `end` leaves the sealed fact unchanged (a name the seal left bare that `end` would
/// version re-stamps it, and such a fact is dropped). A seal that collides with a local's
/// name drops the fact.
///
/// SHARED by the mint's TINV rows ([`build_row`]) and the step-10 use site
/// (`generate::type_invariant_facts`), so the two disciplines cannot fork. `fact` projects
/// an item to its UNVERSIONED formula; the item is handed back beside its sealed form.
#[cfg(test)]
pub(crate) fn tinv_sealed_post_call_hyps<'a, T>(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    post_calls: &'a [(BlockId, Vec<T>)],
    fact: impl Fn(&T) -> &Formula,
    block: BlockId,
    end: usize,
) -> Vec<(&'a T, BlockId, Formula)> {
    let mut out = Vec::new();
    for (target, facts) in post_calls {
        out.extend(
            tinv_sealed_region_hyps(func, sv, *target, *target, facts, &fact, block, end)
                .into_iter()
                .map(|(item, sealed)| (item, *target, sealed)),
        );
    }
    out
}

/// The generalisation of [`tinv_sealed_post_call_hyps`] to a fact that is SEALED at
/// `(seal, 0)` but TRUE only inside the region `region` dominates (TINV-21 arm facts;
/// a post-call fact is the case `region == seal`): every item of `facts` versioned at
/// `(seal, 0)` and sealed there ([`seal_bare_reads`]) with the walk's own oracle, kept
/// only where BOTH `(seal, 0)` and `(region, 0)` dominate `block` ([`entry_dominates`],
/// the unwind-inclusive tree) and the row's rename at `(block, end)` leaves the sealed
/// fact unchanged. `block` is the block whose hook builds the row: an edge part's
/// predecessor, never its join.
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn tinv_sealed_region_hyps<'a, T>(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    seal: BlockId,
    region: BlockId,
    facts: &'a [T],
    fact: &impl Fn(&T) -> &Formula,
    block: BlockId,
    end: usize,
) -> Vec<(&'a T, Formula)> {
    let mut out = Vec::new();
    if !entry_dominates(sv, seal, block) || !entry_dominates(sv, region, block) {
        return out;
    }
    for item in facts {
        let Some(sealed) = seal_fact_at_block_entry(func, sv, seal, fact(item)) else { continue };
        if keep_sealed_region_fact(func, sv, seal, region, &sealed, block, end) {
            out.push((item, sealed));
        }
    }
    out
}

fn prepared_type_facts(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    req: &TinvRowRequest,
    ty: usize,
) -> Result<Rc<PreparedTypeFacts>, TinvObligationRefusal> {
    if let Some(hit) = req.state.borrow().prepared_types.get(&ty).cloned() {
        return Ok(hit);
    }
    let req_ty = &req.types[ty];
    for a in &req_ty.arm_facts {
        if a.uses.len() != a.facts.len() {
            return Err(TinvObligationRefusal::Shim(
                "an arm fact without its lemma attribution".into(),
            ));
        }
    }
    let mut post_calls = Vec::new();
    for (target, facts) in &req_ty.post_calls {
        if facts.is_empty() || !entry_dominates(sv, *target, *target) {
            continue;
        }
        let mut sealed_facts = Vec::with_capacity(facts.len());
        for f in facts {
            if let Some(sealed) = seal_fact_at_block_entry(func, sv, *target, f) {
                sealed_facts.push(sealed);
            }
        }
        if !sealed_facts.is_empty() {
            post_calls.push((*target, sealed_facts));
        }
    }
    let mut arm_facts = Vec::new();
    for a in &req_ty.arm_facts {
        if a.facts.is_empty()
            || !entry_dominates(sv, a.seal, a.seal)
            || !entry_dominates(sv, a.region, a.region)
        {
            continue;
        }
        let mut items = Vec::with_capacity(a.facts.len());
        for (f, lemma) in a.facts.iter().zip(a.uses.iter()) {
            if let Some(sealed) = seal_fact_at_block_entry(func, sv, a.seal, f) {
                items.push((sealed, lemma.clone()));
            }
        }
        if !items.is_empty() {
            arm_facts.push(PreparedArmFact { seal: a.seal, region: a.region, items });
        }
    }
    let mut constructions = Vec::new();
    for c in &req_ty.constructions {
        let Some(block) = func
            .body
            .blocks
            .get(c.block.0)
            .filter(|b| b.id == c.block)
            .or_else(|| func.body.blocks.iter().find(|b| b.id == c.block))
        else {
            continue;
        };
        let Some(Statement::Assign { place, .. }) = block.stmts.get(c.stmt) else {
            continue;
        };
        if !req.rows.iter().any(|r| {
            r.ty == ty
                && emit_block(r) == c.block.0
                && c.stmt < r.point.row_point.min(block.stmts.len())
        }) {
            continue;
        }
        let mut equations = Vec::with_capacity(c.pairs.len());
        for (lhs, rhs) in &c.pairs {
            let l = version_rename_at(lhs, sv, func, c.block, c.stmt + 1);
            let r = version_rename_at(rhs, sv, func, c.block, c.stmt);
            let (Some(l), Some(r)) = (
                seal_bare_reads(sv, func, c.block, c.stmt + 1, l),
                seal_bare_reads(sv, func, c.block, c.stmt, r),
            ) else {
                continue;
            };
            equations.push(Formula::Eq(Box::new(l), Box::new(r)));
        }
        if !equations.is_empty() {
            constructions.push(PreparedConstruction {
                block: c.block,
                stmt: c.stmt,
                root_local: place.local,
                equations,
            });
        }
    }
    let prepared = Rc::new(PreparedTypeFacts { post_calls, arm_facts, constructions });
    req.state.borrow_mut().prepared_types.insert(ty, Rc::clone(&prepared));
    Ok(prepared)
}

fn row_span(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
    row_point: usize,
) -> SourceSpan {
    if let Some(Statement::Assign { span, .. }) = block.stmts.get(row_point) {
        return span.clone();
    }
    match &block.terminator {
        Terminator::Call { span, .. }
        | Terminator::Assert { span, .. }
        | Terminator::Drop { span, .. } => span.clone(),
        _ => func.span.clone(),
    }
}

fn build_row(
    func: &VerifiableFunction,
    sv: &StmtVersionCtx,
    req: &TinvRowRequest,
    row: &RequestRow,
    block: &trust_types::BasicBlock,
    cached_havoc: &mut Option<Vec<String>>,
) -> Result<VerificationCondition, TinvObligationRefusal> {
    let prepared = prepared_type_facts(func, sv, req, row.ty)?;
    let row_point = row.point.row_point;
    let end = row_rename_point(func, block.id, row_point);
    let mut hyps: Vec<Formula> = Vec::new();

    // An edge part's guard is ALWAYS the first raw conjunct (`true` when unguarded): the
    // situatedness gate identifies it by that position and never counts it as binding
    // the core. It is renamed with the row at the predecessor's terminal, where the
    // predecessor's terminator reads it.
    if row.key.edge.is_some() {
        hyps.push(row.edge_guard.clone().unwrap_or(Formula::Bool(true)));
    }

    // Post-call facts, pre-versioned and sealed at `(T, 0)` with the WALK's oracle,
    // filtered by `(T, 0)` dominance and no-rewrite at `(block.id, end)`.
    for (target, sealed_facts) in &prepared.post_calls {
        if !entry_dominates(sv, *target, block.id) {
            continue;
        }
        for sealed in sealed_facts {
            if !super::path_defs::version_rename_needs_rewrite(sealed, sv, func, block.id, end) {
                hyps.push(sealed.clone());
            }
        }
    }

    // TINV-21 arm facts: a kernel-certified `Some`-arm lemma of an inventory callee,
    // pre-sealed at the call target and kept only inside the `Some` region (the hook
    // block, an edge part's predecessor, must be dominated by the arm).
    let mut uses: Vec<RowArmUse> = Vec::new();
    for a in &prepared.arm_facts {
        if !entry_dominates(sv, a.seal, block.id) || !entry_dominates(sv, a.region, block.id) {
            continue;
        }
        for (sealed, lemma) in &a.items {
            if !super::path_defs::version_rename_needs_rewrite(sealed, sv, func, block.id, end) {
                hyps.push(sealed.clone());
                uses.push(RowArmUse { lemma: lemma.clone(), sealed: sealed.clone() });
            }
        }
    }
    if !uses.is_empty() {
        req.state.borrow_mut().arm_uses.push((row.key.clone(), uses));
    }

    // Construction facts: the field equations of an E point earlier in this block.
    hyps.extend(construction_facts(func, sv, &prepared, row, block, end));

    let (core, bindings) = situate_core(func, sv, row, block, cached_havoc)?;
    hyps.extend(bindings);
    if let Some((cond, expected)) = &row.point.failure {
        hyps.push(v2_assert_failure_formula(func, cond, *expected));
    }
    let negated = Formula::Not(Box::new(core));
    let raw = if hyps.is_empty() {
        negated
    } else {
        hyps.push(negated);
        Formula::And(hyps)
    };

    let (formula, body, kept) = v2_formula_with_block_defs_at_point_recorded(func, block, end, raw);
    let mut wrappers = Vec::new();
    if !kept.is_empty() {
        wrappers.push(ObligationWrapper::ConjoinFactsLast { facts: kept });
    }
    Ok(VerificationCondition {
        kind: VcKind::TypeInvariant {
            ty: req.types[row.ty].def_path.clone(),
            point: row.point.point,
            site: row.point.site,
            conjunct: row.key.conjunct,
            ordinal: row.key.ordinal,
            edge: row.key.edge,
        },
        function: func.name.as_str().into(),
        location: row_span(func, block, row_point),
        formula,
        contract_metadata: None,
        obligation: Some(ObligationRecord { body, wrappers, subject: None, width: None }),
    })
}

/// Match the walk's TINV rows back to the requested keys, by EXACT identity.
///
/// Every emitted `VcKind::TypeInvariant` carries its row's whole identity
/// `(ty, point, site, conjunct, ordinal, edge)`, so each row is paired with the one
/// requested key equal to it; emission order plays no part (the walk emits terminator
/// rows before statement rows, and the edge parts of a join point at their
/// predecessors). Refuses with `Coverage` on a duplicate requested key, an emitted row
/// no key names (or a second row for a filled key), and a key no row came back for (a
/// row the walk dropped, or degraded to `UnsupportedMir`). The result is in request
/// order.
pub(super) fn match_coverage(
    requested: &[TinvRowKey],
    emitted: Vec<(BlockId, VerificationCondition)>,
) -> Result<Vec<(TinvRowKey, VerificationCondition)>, TinvObligationRefusal> {
    let coverage = |got: usize| TinvObligationRefusal::Coverage { expected: requested.len(), got };
    type BorrowedRowKey<'a> = (
        &'a str,
        u32,
        trust_types::TypeInvariantPoint,
        trust_types::TypeInvariantSite,
        u32,
        Option<usize>,
    );
    let mut index: FxHashMap<BorrowedRowKey<'_>, usize> =
        FxHashMap::with_capacity_and_hasher(requested.len(), Default::default());
    for (i, key) in requested.iter().enumerate() {
        let borrowed_key =
            (key.ty.as_str(), key.conjunct, key.point, key.site, key.ordinal, key.edge);
        if index.insert(borrowed_key, i).is_some() {
            return Err(coverage(0));
        }
    }
    let mut matched: Vec<Option<VerificationCondition>> = vec![None; requested.len()];
    let mut got = 0usize;
    let mut extra = 0usize;
    for (_, vc) in emitted {
        let VcKind::TypeInvariant { ty, point, site, conjunct, ordinal, edge } = &vc.kind else {
            continue;
        };
        let key = (ty.as_str(), *conjunct, *point, *site, *ordinal, *edge);
        if let Some(&i) = index.get(&key)
            && matched[i].is_none()
        {
            matched[i] = Some(vc);
            got += 1;
        } else {
            extra += 1;
        }
    }
    if extra > 0 || got != requested.len() {
        return Err(coverage(got));
    }
    // Every slot is filled (`got` counts distinct request indices), in REQUEST order.
    Ok(requested.iter().cloned().zip(matched.into_iter().flatten()).collect())
}

/// Run the ordinary safety walk over `func` (the caller's probe: its preconditions are
/// the TINV entry assumption) with `request` installed, and return every requested row,
/// or why the body must be withheld.
///
/// Mirrors `generate_vcs_impl`'s preamble: a memory-image or malformed body refuses, a
/// body over the static VC-generation budget refuses, the analysis memo, work meter and
/// (empty, conservative) callee write-set scopes are entered, and the walk runs on the
/// arithmetic-sanitized view. A truncated walk (step budget, row cap, work meter) is
/// `Truncated`, or `Budget` when the clock tripped; never a partial result.
pub(crate) fn tinv_check_rows(
    func: &VerifiableFunction,
    request: TinvRowRequest,
) -> Result<Vec<(TinvRowKey, VerificationCondition)>, TinvObligationRefusal> {
    tinv_check_rows_recorded(func, request).map(|(rows, _)| rows)
}

/// The arm facts each row assumed, by row key (TINV-21).
pub(crate) type RowArmUses = Vec<(TinvRowKey, Vec<RowArmUse>)>;

/// [`tinv_check_rows`] with, beside the rows, the arm facts each row assumed.
pub(crate) fn tinv_check_rows_recorded(
    func: &VerifiableFunction,
    request: TinvRowRequest,
) -> Result<(Vec<(TinvRowKey, VerificationCondition)>, RowArmUses), TinvObligationRefusal> {
    if crate::memory_image_vc(func).is_some() {
        return Err(TinvObligationRefusal::Shim("the body holds a constant memory image".into()));
    }
    if let Err(e) = crate::validate_function(func) {
        return Err(TinvObligationRefusal::Shim(format!("the body is malformed: {e}")));
    }
    if super::cached_terminator_presence_for_body(&func.body).map_or_else(
        || func.body.blocks.iter().any(|b| matches!(b.terminator, Terminator::TailCall { .. })),
        |p| p.has_tail_call,
    ) {
        return Err(TinvObligationRefusal::U(crate::type_invariant::unwind::URefusal::TailCall));
    }
    if super::semantic_guard::func_exceeds_vcgen_budget(func) {
        return Err(TinvObligationRefusal::Budget);
    }
    let mut request = request;
    let context = crate::VcgenContext::for_function_inheriting_self_call_identity(&func.def_path);
    let (requested, request, rows, truncated, clock) =
        crate::with_function_vcgen_context(&func.def_path, &context, || {
            let _analysis_scope = super::FuncAnalysisScope::enter(func);
            let _gen_work_scope = crate::gen_work_scope();
            let _write_sets = callee_write_set::enter_callee_write_sets(None);
            let safe = super::entry::without_unmodeled_contract_arithmetic(func);
            // TINV-9(a): split R rows at joins with the oracle of the body the walk runs on.
            // Skipped once the budget has tripped (an oracle built after a trip may be
            // short): no split is the fail-closed choice, and the walk then reports the
            // trip as `Truncated`/`Budget`.
            if !trust_types::verify_budget::budget_exhausted() && !crate::gen_work_tripped() {
                let sv = super::stmt_versions_for(safe.as_ref());
                request.split_join_returns(safe.as_ref(), &sv);
            }
            let requested = request.keys();
            let request = Rc::new(request);
            let _guard = enter_tinv_rows(Rc::clone(&request));
            let super::safety::SafetyWalk { rows, truncated, .. } =
                super::safety::generate_v2_safety_vcs_impl_with_origins_checked(
                    safe.as_ref(),
                    None,
                );
            let clock = trust_types::verify_budget::exhaustion_cause()
                == Some(trust_types::determinism::StopCause::WallBackstop);
            (requested, request, rows, truncated || crate::gen_work_tripped(), clock)
        });
    let state = request.state.borrow();
    if let Some(e) = &state.error {
        return Err(e.clone());
    }
    if truncated {
        return Err(if clock {
            TinvObligationRefusal::Budget
        } else {
            TinvObligationRefusal::Truncated
        });
    }
    if !state.consumed {
        return Err(TinvObligationRefusal::Shim("the walk never reached the request".into()));
    }
    if state.reused {
        return Err(TinvObligationRefusal::Shim("the request was walked twice".into()));
    }
    let uses = state.arm_uses.clone();
    Ok((match_coverage(&requested, rows)?, uses))
}

#[cfg(test)]
#[path = "tinv_rows_tests.rs"]
mod tests;
