// trust-vcgen/src/generate/dominating_facts.rs: the dominating `var CMP const` guard
// facts of one function, built ONCE and answered per obligation in O(log).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// WHAT IT ANSWERS. For a local `x` read at program point `q = (B, k)`: the linear facts
// `x CMP c` that hold on EVERY execution reaching `q`, because a guard established them
// and nothing has changed `x` since. Four lanes ask it: the signed multiply's corner
// box, the BV/Int renderings of a multiply's operand bounds, the shift amount's upper
// bound, and (since 2026-09-21) the 128-bit negation's operand bound.
//
// WHAT IT REPLACES, AND THE TWO DEFECTS THAT MADE IT NECESSARY.
//
// The retired miner (`overflow_vc::v2_dominating_linear_facts_matching`) answered each
// row by walking every ENUMERATED path the path-guard walk recorded into the row's
// block, resolving every guard on every path, and intersecting. It compared VERSION
// TOKENS — the spelling of a name's reaching-def SET — between the guard and the use.
//
//  1. COST. Per row it visited Θ(paths × path length) guards, and for each guard leaf
//     whose subject was a copy it scanned the whole body for the copy statement
//     (`v2_live_copy_source_name_reaching`), while the guard resolution itself asked the
//     whole-body `value_local_is_unstable` up to three times. MEASURED by the
//     2026-10-01 review on `if a >= MIN+1 { acc ^= -a; .. N times }`: the miner's total
//     grew ~8x per doubling (1.9 ms at N=50 to 4.45 s at N=800) — CUBIC.
//  2. THE PATH CAP. Facts existed only on paths the walk ENUMERATED, and a block past
//     `MAX_PATHS_PER_BLOCK` (64) records one unguarded path, which empties the
//     intersection: a safe `if a >= MIN+1 { 7 diamonds; -a }` was refuted at k = 7 and
//     not at k = 6 — the verdict depended on the function's SIZE through a cap.
//  3. SOUNDNESS (found while replacing it). Equal reaching SETS are not equal VALUES.
//     In `loop { if a > MIN { if c { a = MIN; if c2 { continue } } return -a } .. }` the
//     name `a` reaches the guard and the negation as the same set `{e, a = MIN}`, so the
//     guard's `a > MIN` bounded a negation that really overflows (c, !c2). The 64-bit
//     multiply twin (`a = i64::MAX; a * a`) was PROVED by the interval backend; the
//     128-bit negation lost its refutation. See `version_ssa::ValueId`.
//
// THE CONSTRUCTION. Two exact ingredients, each linear.
//
//  * EDGE DOMINANCE instead of path enumeration. A guarded CFG edge `S -> T` DOMINATES
//    `T` when every other predecessor of `T` that can execute is dominated by `T` (back
//    edges), `S -> T` is the only way from `S` to `T` (parallel clauses are intersected;
//    an unguarded parallel successor voids the edge), and `S -> T` is not itself a back
//    edge. Such an edge's facts hold at `T`'s entry and are offered to `T`'s whole
//    dominator subtree. No path is ever enumerated, so there is no cap to fall off.
//  * SSA VALUE IDENTITY instead of token equality (`StmtVersionCtx::value_id_at`). A
//    fact is keyed on the VALUE its subject held at the guard; a use sees it only when it
//    reads that same value. The guard point dominates the use (it lies on the dominating
//    edge), which is exactly the premise under which `ValueId` equality means "the very
//    value" (see its contract).
//
// SOUNDNESS, end to end. Let edge `e = S -> T` dominate `B`, the guard compare `x` at
// `(S, i)`, and the use read `x` at `(B, k)` with the same `ValueId`.
//   (a) The last visit of `S` before `B` takes `e`: a later visit that left by another
//       edge, prefixed with the path to `S`'s first visit (which precedes every
//       traversal of `e`), would reach `B` without `e`.
//   (b) On that visit the comparison read `x`'s value at `(S, i)` and the guard held.
//   (c) `(S, i)` dominates `(B, k)` and both name the same value, so `(B, k)` reads the
//       value of the last visit of `(S, i)` — the one in (b).
// So every conjoined fact is TRUE in every execution reaching the row: conjoining it
// removes only infeasible counterexamples, and a real overflow keeps its witness.
//
// THE COPY HOP, re-founded on the same identity. Debug rustc compares a per-guard COPY
// (`_5 = copy a; _4 = Gt(move _5, c)`) and negates or multiplies another (`_6 = copy a;
// Neg(move _6)`). `_5`'s value at the guard is `a`'s when `_5`'s `ValueId` there is the
// copy statement `(C, j)` and `a` has the same `ValueId` at `(C, j)` and at the guard:
// the copy dominates the guard (a `Def` id's statement always dominates the read that
// sees it), so by the contract `a` was not changed in between. The same test ties a
// use's operand to its source. The retired resolver answered the same question with
// token equality and a whole-body scan; this one is a lookup.
//
// WHICH LOCALS TAKE PART. A value identity is only as good as the write index behind
// it, and that index stamps statement stores, not writes through an escaped `&mut` —
// so a local takes part (as the asked operand, a guard subject, or either side of a
// copy) only when it is stable (`!guards::value_local_is_unstable`) or every write to
// it is a whole-local `Assign` (`local_defs::every_write_is_whole_named`). This is the
// gate the multiply lane always applied to its operands, now applied to every name an
// identity is taken of.
//
// PRECISION, stated rather than implied. A fact that holds at a join only because
// EACH incoming path establishes it with a DIFFERENT guard is not offered (no single
// edge dominates); the retired per-path intersection did offer it, below the cap.
// Facts are kept tightest-per-comparison (`x < 5` absorbs `x < 9`), which states the
// same set of values in at most five atoms.
//
// COST. Build: one pass over the blocks; per guarded edge O(1) leaves, each an O(log)
// value-identity query; then a sort and a stack pass per key. Memory O(facts). Query:
// one value-identity query and an O(log) descent through skew-binary jump pointers
// (the `version_ssa::DefList` scheme). `dominating_facts_scaling_is_linear` pins it.

use std::cell::OnceCell;
use std::rc::Rc;

use trust_types::fx::FxHashMap;
use trust_types::{
    BlockId, ClauseTarget, GuardCondition, Operand, Place, Rvalue, Statement, VerifiableFunction,
};

use super::cfg_index::{CfgIndex, NONE};
use super::version_ssa::ValueId;
use super::{BvGuardCmp, StmtVersionCtx};

/// Trust: 2026-09-18 — how a guard's SUBJECT is allowed to meet the local a caller
/// asks about.
///
/// This is not a tuning knob and it is not a precision dial: it records which NAME
/// SPACE the caller's local is written in, and the two answers are not
/// interchangeable.
///
///   * [`Self::ExactName`] — the caller passes a RAW MIR local (the shift amount, a
///     signed multiply's operand). A raw local meets a guard only when the guard names
///     it, so only a fact about that very local may contribute.
///   * [`Self::LiveCopyOfBase`] — the caller has ALREADY walked its own operand one live
///     pure-copy hop and is asking under the SOURCE local (the multiply and negation
///     operand facts mine under both `_6` and the `b` it is a copy of). Debug rustc
///     gives the short-circuit `&&` its own copy of the same value (`_5 = copy _2; _4 =
///     Lt(move _5, 1000)`), so the guard's subject sits one hop away on the OTHER side
///     too; without resolving it the two names can never meet.
///
/// Asking for the hop where the caller did not do its own is not "more facts": it
/// silently changes what a name means for that consumer (5445c64d21b handed the hop to
/// both raw-name callers without saying so; this type made it a call-site decision).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum GuardSubject {
    ExactName,
    LiveCopyOfBase,
}

type Fact = (BvGuardCmp, i128);

/// At most one fact per comparison kind, the TIGHTEST, in first-appearance order.
/// `x < 5 ∧ x < 9` and `x < 5` admit the same values; keeping one atom per kind is
/// what bounds a site's facts by a constant whatever the nesting depth.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FactSet(Vec<Fact>);

impl FactSet {
    fn add(&mut self, (cmp, c): Fact) {
        if let Some(slot) = self.0.iter_mut().find(|(k, _)| *k == cmp) {
            slot.1 = match cmp {
                BvGuardCmp::Lt | BvGuardCmp::Le => slot.1.min(c),
                BvGuardCmp::Gt | BvGuardCmp::Ge => slot.1.max(c),
                // Two equalities with different constants describe dead code; either is
                // a true fact on every execution that gets here, so keep the outer one.
                BvGuardCmp::Eq => slot.1,
            };
        } else {
            self.0.push((cmp, c));
        }
    }

    fn extend(&mut self, other: &FactSet) {
        for &fact in &other.0 {
            self.add(fact);
        }
    }
}

/// One fact a guarded edge establishes: about `local`'s value `vid` at the guard,
/// reached through the copy hop (`hop`) or naming the local itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct EdgeFact {
    local: usize,
    vid: ValueId,
    fact: Fact,
    hop: bool,
}

/// The fact sites of ONE `(local, value)` key: the targets `T` of dominating guard
/// edges, sorted by dominator preorder, with the forest dominance induces on them,
/// skew-binary jump pointers over it, and per site the facts accumulated from every
/// listed dominator (root first). `acc_exact` holds only facts that name the local
/// itself; `acc_all` adds the copy-hop facts.
struct SiteList {
    nodes: Vec<u32>,
    pre: Vec<u32>,
    parent: Vec<u32>,
    jump: Vec<u32>,
    acc_exact: Vec<FactSet>,
    acc_all: Vec<FactSet>,
}

impl SiteList {
    /// `sites`: `(node, exact facts, all facts)`, any order, one entry per node.
    fn build(cfg: &CfgIndex, mut sites: Vec<(u32, FactSet, FactSet)>) -> SiteList {
        let dom = cfg.dom();
        sites.sort_by_key(|(v, _, _)| dom.pre(*v));
        let n = sites.len();
        let mut list = SiteList {
            nodes: Vec::with_capacity(n),
            pre: Vec::with_capacity(n),
            parent: vec![NONE; n],
            jump: vec![NONE; n],
            acc_exact: Vec::with_capacity(n),
            acc_all: Vec::with_capacity(n),
        };
        let mut depth = vec![0u32; n];
        let mut stack: Vec<u32> = Vec::new();
        for (t, (v, exact, all)) in sites.into_iter().enumerate() {
            let pv = dom.pre(v);
            while let Some(&top) = stack.last() {
                if dom.last(list.nodes[top as usize]) < pv {
                    stack.pop();
                } else {
                    break;
                }
            }
            let (mut acc_exact, mut acc_all) = match stack.last() {
                Some(&p) => {
                    list.parent[t] = p;
                    depth[t] = depth[p as usize] + 1;
                    let j = list.jump[p as usize];
                    let jj = list.jump[j as usize];
                    list.jump[t] = if depth[p as usize] - depth[j as usize]
                        == depth[j as usize] - depth[jj as usize]
                    {
                        jj
                    } else {
                        p
                    };
                    (list.acc_exact[p as usize].clone(), list.acc_all[p as usize].clone())
                }
                None => {
                    list.jump[t] = t as u32;
                    (FactSet::default(), FactSet::default())
                }
            };
            acc_exact.extend(&exact);
            acc_all.extend(&all);
            list.nodes.push(v);
            list.pre.push(pv);
            list.acc_exact.push(acc_exact);
            list.acc_all.push(acc_all);
            stack.push(t as u32);
        }
        list
    }

    /// The deepest listed node that dominates `b` (`b` itself included), as an index.
    fn deepest_dominator_or_self(&self, cfg: &CfgIndex, b: u32) -> Option<usize> {
        let dom = cfg.dom();
        let pb = dom.pre(b);
        let k = self.pre.partition_point(|&p| p <= pb);
        if k == 0 {
            return None;
        }
        // Listed dominators of `b` form a chain of forest ancestors of the last listed
        // node at or before `b` in preorder, and "covers `b`" is monotone up that chain.
        let covers = |t: u32| dom.subtree_contains_pre(self.nodes[t as usize], pb);
        let mut t = (k - 1) as u32;
        loop {
            if covers(t) {
                return Some(t as usize);
            }
            crate::fn_memo::count_query_steps(1);
            let j = self.jump[t as usize];
            if j != t && !covers(j) {
                t = j;
            } else {
                let p = self.parent[t as usize];
                if p == NONE {
                    return None;
                }
                t = p;
            }
        }
    }
}

/// The dominating guard facts of one function. Built by [`DominatingFacts::build`];
/// reached through `generate::dominating_facts_for`, which memoizes it per function.
pub(crate) struct DominatingFacts {
    sv: Rc<StmtVersionCtx>,
    keys: FxHashMap<(usize, ValueId), SiteList>,
    /// Per local: whether `keys` contains at least one `(local, _)` entry.
    has_local: Vec<bool>,
    /// Per local: may a value identity be taken of it (see the module doc)?
    admits: Vec<OnceCell<bool>>,
    /// Per local: memoized formula variable name (`place_to_var_name(func, &Place::local(l))`).
    local_names: Vec<OnceCell<String>>,
}

impl DominatingFacts {
    pub(crate) fn build(func: &VerifiableFunction) -> DominatingFacts {
        let sv = super::stmt_versions_for(func);
        let n_locals = func.body.locals.len();
        let mut this = DominatingFacts {
            sv: Rc::clone(&sv),
            keys: FxHashMap::default(),
            has_local: Vec::new(),
            admits: vec![OnceCell::new(); n_locals],
            local_names: vec![OnceCell::new(); n_locals],
        };
        if {
            let tp = super::terminator_presence_for(func);
            !tp.has_switch_int && !tp.has_assert
        } {
            return this;
        }
        let cfg = sv.cfg();
        let dom = cfg.dom();
        let entry = cfg.entry_def();
        let n = func.body.blocks.len();
        let live = |v: u32| dom.dominates(entry, v);

        // Every fact of every dominating guarded edge, in block order.
        let mut raw: Vec<(u32, EdgeFact)> = Vec::new();
        for (si, block) in func.body.blocks.iter().enumerate() {
            // The id == index invariant every analysis here keys on.
            if block.id.0 != si
                || !matches!(
                    block.terminator,
                    trust_types::Terminator::SwitchInt { .. }
                        | trust_types::Terminator::Assert { .. }
                )
                || !live(si as u32)
            {
                continue;
            }
            let clauses = block.terminator.discovered_clauses(block.id);
            if clauses.is_empty() {
                continue;
            }
            let cleanup_target = block.terminator.unwind_cleanup_target();
            let mut groups: Vec<(BlockId, Vec<GuardCondition>)> = Vec::new();
            for clause in clauses {
                let ClauseTarget::Block(t) = clause.target else { continue };
                if t.0 >= n
                    || cleanup_target == Some(t)
                    || !edge_dominates_target(cfg, si as u32, t.0 as u32)
                {
                    continue;
                }
                match groups.iter_mut().find(|(g, _)| *g == t) {
                    Some((_, guards)) => guards.push(clause.guard),
                    None => groups.push((t, vec![clause.guard])),
                }
            }
            for (target, guards) in groups {
                let t = target.0 as u32;
                // Parallel clauses into one target: a fact holds on the edge only if
                // every clause that can take it establishes it.
                let mut common: Option<Vec<EdgeFact>> = None;
                for guard in &guards {
                    let facts = this.edge_facts(func, block.id, guard);
                    let next: Vec<EdgeFact> = match common {
                        None => facts,
                        Some(prev) => prev.into_iter().filter(|f| facts.contains(f)).collect(),
                    };
                    let is_empty = next.is_empty();
                    common = Some(next);
                    if is_empty {
                        break;
                    }
                }
                for fact in common.unwrap_or_default() {
                    raw.push((t, fact));
                }
            }
        }

        // Group by key; one site per target node, facts in establishment order.
        let mut by_key: FxHashMap<(usize, ValueId), Vec<(u32, FactSet, FactSet)>> =
            FxHashMap::default();
        for (t, fact) in raw {
            let sites = by_key.entry((fact.local, fact.vid)).or_default();
            let slot = match sites.iter().position(|(v, _, _)| *v == t) {
                Some(i) => i,
                None => {
                    sites.push((t, FactSet::default(), FactSet::default()));
                    sites.len() - 1
                }
            };
            if !fact.hop {
                sites[slot].1.add(fact.fact);
            }
            sites[slot].2.add(fact.fact);
        }
        if !by_key.is_empty() {
            let mut has_local = vec![false; n_locals];
            for &(local, _) in by_key.keys() {
                if let Some(slot) = has_local.get_mut(local) {
                    *slot = true;
                }
            }
            this.has_local = has_local;
        }
        this.keys =
            by_key.into_iter().map(|(key, sites)| (key, SiteList::build(cfg, sites))).collect();
        crate::fn_memo::count_cfg_work(this.keys.len() as u64);
        this
    }

    /// May a value identity be taken of `local` (stable, or written only by whole-local
    /// `Assign`s the version oracle stamps)? Memoized per local.
    pub(super) fn admits(&self, func: &VerifiableFunction, local: usize) -> bool {
        let compute = || {
            !crate::guards::value_local_is_unstable(func, local)
                || crate::local_defs::every_write_is_whole_named(func, local)
        };
        match self.admits.get(local) {
            Some(slot) => *slot.get_or_init(compute),
            None => compute(),
        }
    }

    fn local_name<'a>(
        &'a self,
        func: &VerifiableFunction,
        local: usize,
    ) -> std::borrow::Cow<'a, str> {
        if let Some(slot) = self.local_names.get(local) {
            std::borrow::Cow::Borrowed(
                slot.get_or_init(|| crate::place_to_var_name(func, &Place::local(local))).as_str(),
            )
        } else {
            std::borrow::Cow::Owned(crate::place_to_var_name(func, &Place::local(local)))
        }
    }

    /// The facts one guarded clause out of `source` establishes, before dominance.
    fn edge_facts(
        &self,
        func: &VerifiableFunction,
        source: BlockId,
        guard: &GuardCondition,
    ) -> Vec<EdgeFact> {
        let Some(sourced) = super::overflow_vc::v2_sourced_guard_fact(func, source, guard) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for leaf in super::overflow_vc::v2_flatten_guard_conjuncts(&sourced.formula) {
            let Some((name, cmp, constant)) = super::overflow_vc::v2_linear_var_const_fact(leaf)
            else {
                continue;
            };
            // The leaf names one of the comparison's own place operands; find which.
            let Some(local) = sourced
                .subjects
                .iter()
                .copied()
                .find(|&l| self.local_name(func, l).as_ref() == name)
            else {
                continue;
            };
            if !self.admits(func, local) {
                continue;
            }
            let Some(vid) = self.sv.value_id_at(func, source, sourced.stmt_index, name) else {
                continue;
            };
            let fact = (cmp, constant);
            push_unique(&mut out, EdgeFact { local, vid, fact, hop: false });
            if let Some((src, src_vid)) =
                self.copy_source(func, local, name, source, sourced.stmt_index)
            {
                push_unique(&mut out, EdgeFact { local: src, vid: src_vid, fact, hop: true });
            }
        }
        out
    }

    /// The local `local` is a live pure copy of at `(block, before)`, with that source's
    /// value there: `local`'s value is the one a whole-local `local = copy|move src`
    /// wrote, and `src` still holds the value it copied (same [`ValueId`] at the copy
    /// and here; the copy dominates `(block, before)`, see the module doc).
    fn copy_source(
        &self,
        func: &VerifiableFunction,
        local: usize,
        name: &str,
        block: BlockId,
        before: usize,
    ) -> Option<(usize, ValueId)> {
        let ValueId::Def { block: c, stmt: j } = self.sv.value_id_at(func, block, before, name)?
        else {
            return None;
        };
        let copy = func.body.blocks.get(c as usize)?.stmts.get(j as usize)?;
        let Statement::Assign {
            place,
            rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
            ..
        } = copy
        else {
            return None;
        };
        if place.local != local
            || !place.projections.is_empty()
            || !src.projections.is_empty()
            || src.local == local
            || !self.admits(func, src.local)
        {
            return None;
        }
        let src_name = self.local_name(func, src.local);
        let at_copy =
            self.sv.value_id_at(func, BlockId(c as usize), j as usize, src_name.as_ref())?;
        let here = self.sv.value_id_at(func, block, before, src_name.as_ref())?;
        (at_copy == here).then_some((src.local, here))
    }

    /// The local `local` is a live pure copy of when read at `(block, before)`, if any —
    /// the operand side of the copy hop.
    pub(super) fn copy_source_at(
        &self,
        func: &VerifiableFunction,
        local: usize,
        block: BlockId,
        before: usize,
    ) -> Option<usize> {
        if !self.admits(func, local) {
            return None;
        }
        let name = self.local_name(func, local);
        self.copy_source(func, local, name.as_ref(), block, before).map(|(src, _)| src)
    }

    /// The `local CMP constant` facts that hold whenever `local` is read at
    /// `(block, before)` — tightest per comparison kind, outermost guard first.
    pub(super) fn facts(
        &self,
        func: &VerifiableFunction,
        local: usize,
        block: BlockId,
        before: usize,
        subject: GuardSubject,
    ) -> &[(BvGuardCmp, i128)] {
        if !self.has_local.get(local).copied().unwrap_or(false) || !self.admits(func, local) {
            return &[];
        }
        let name = self.local_name(func, local);
        let Some(vid) = self.sv.value_id_at(func, block, before, name.as_ref()) else {
            return &[];
        };
        let Some(list) = self.keys.get(&(local, vid)) else {
            return &[];
        };
        let Some(t) = list.deepest_dominator_or_self(self.sv.cfg(), block.0 as u32) else {
            return &[];
        };
        match subject {
            GuardSubject::ExactName => &list.acc_exact[t].0,
            GuardSubject::LiveCopyOfBase => &list.acc_all[t].0,
        }
    }

    /// Whether `block` can execute at all (reachable from `bb0` over the full graph).
    pub(super) fn reachable(&self, block: BlockId) -> bool {
        let cfg = self.sv.cfg();
        block.0 < cfg.n_blocks() && cfg.dom().dominates(cfg.entry_def(), block.0 as u32)
    }

    /// Is `from -> to` a GUARDED edge (one of `from`'s discovered clauses, not also an
    /// unguarded successor) that every execution reaching `to` traverses?
    pub(super) fn guarded_edge_dominates(
        &self,
        from: &trust_types::BasicBlock,
        to: BlockId,
    ) -> bool {
        let is_guarded_target = match &from.terminator {
            trust_types::Terminator::SwitchInt { targets, otherwise, .. } => {
                *otherwise == to || targets.iter().any(|(_, t)| *t == to)
            }
            trust_types::Terminator::Assert { target, unwind, .. } => {
                *target == to && unwind.cleanup_target() != Some(to)
            }
            _ => false,
        };
        if !is_guarded_target {
            return false;
        }
        let cfg = self.sv.cfg();
        let s = from.id.0;
        s < cfg.n_blocks()
            && to.0 < cfg.n_blocks()
            && self.reachable(from.id)
            && edge_dominates_target(cfg, s as u32, to.0 as u32)
    }
}

/// The guard comparisons of `func` whose BOUND side did not fold to a constant: leaves
/// comparing two variables where one side is BOUND-LIKE — after following pure
/// whole-local copies, a local that is not a parameter and holds ONE value
/// (`local_defs::holds_one_value`), i.e. a quantity the program fixes once that the fold
/// could not see through (an `&mut`-escaped `lim`, a call result, an expression over an
/// input). A parameter, or a local written more than once (a loop counter), is a
/// VARIABLE: `i < n` is a relation, not an unmined bound. Named as the program spells
/// them.
///
/// Trust (2026-10-01): what `counterexample_grounding` asks before advising a user to
/// RESPELL a bound. The advice is right only where a bound was left unmined; on a real
/// overflow whose bound is a literal (`if a >= MIN+1 { a = b; -a }`) it sent the reader
/// after a spelling that was never the problem.
pub(crate) fn unmined_guard_bounds(func: &VerifiableFunction) -> Vec<String> {
    if {
        let tp = super::terminator_presence_for(func);
        !tp.has_switch_int && !tp.has_assert
    } {
        return Vec::new();
    }
    let n_locals = func.body.locals.len();
    let local_names: Vec<OnceCell<String>> = vec![OnceCell::new(); n_locals];
    let bound_like_cache: Vec<OnceCell<bool>> = vec![OnceCell::new(); n_locals];
    let is_bound_like_uncached = |mut local: usize| {
        // Pure whole-local copies, each hop the local's one value; at most one hop per
        // local of the body, so a copy cycle ends.
        for _ in 0..=n_locals {
            if crate::local_defs::is_parameter(func, local)
                || !crate::local_defs::holds_one_value(func, local)
            {
                return false;
            }
            match crate::local_defs::unique_value_def(func, local) {
                Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                    if p.projections.is_empty() && p.local != local =>
                {
                    local = p.local;
                }
                _ => return true,
            }
        }
        false
    };
    let is_bound_like = |local: usize| -> bool {
        match bound_like_cache.get(local) {
            Some(slot) => *slot.get_or_init(|| is_bound_like_uncached(local)),
            None => is_bound_like_uncached(local),
        }
    };
    let mut out: Vec<String> = Vec::new();
    for block in &func.body.blocks {
        if !matches!(
            block.terminator,
            trust_types::Terminator::SwitchInt { .. } | trust_types::Terminator::Assert { .. }
        ) {
            continue;
        }
        for clause in block.terminator.discovered_clauses(block.id) {
            let Some(sourced) =
                super::overflow_vc::v2_sourced_guard_fact(func, block.id, &clause.guard)
            else {
                continue;
            };
            for leaf in super::overflow_vc::v2_flatten_guard_conjuncts(&sourced.formula) {
                if super::overflow_vc::v2_linear_var_const_fact(leaf).is_some() {
                    continue;
                }
                let leaf = match leaf {
                    trust_types::Formula::Not(inner) => inner.as_ref(),
                    other => other,
                };
                let (trust_types::Formula::Lt(a, b)
                | trust_types::Formula::Le(a, b)
                | trust_types::Formula::Gt(a, b)
                | trust_types::Formula::Ge(a, b)
                | trust_types::Formula::Eq(a, b)) = leaf
                else {
                    continue;
                };
                for side in [a.as_ref(), b.as_ref()] {
                    let trust_types::Formula::Var(name, _) = side else { continue };
                    let Some(local) = sourced.subjects.iter().copied().find(|&l| {
                        match local_names.get(l) {
                            Some(slot) => {
                                slot.get_or_init(|| crate::place_to_var_name(func, &Place::local(l)))
                                    == name
                            }
                            None => crate::place_to_var_name(func, &Place::local(l)) == *name,
                        }
                    }) else {
                        continue;
                    };
                    if is_bound_like(local) && !out.contains(name) {
                        out.push(name.clone());
                    }
                }
            }
        }
    }
    out
}

fn push_unique(out: &mut Vec<EdgeFact>, fact: EdgeFact) {
    if !out.contains(&fact) {
        out.push(fact);
    }
}

/// Does the edge `s -> t` dominate `t`? Every other predecessor of `t` that can
/// execute (is reachable from `bb0`) must be dominated by `t` — a back edge — and
/// `s -> t` must not itself be one. (`preds` lists each predecessor block once; the
/// caller voids an edge that also exists unguarded and intersects parallel clauses.)
fn edge_dominates_target(cfg: &CfgIndex, s: u32, t: u32) -> bool {
    let dom = cfg.dom();
    let entry = cfg.entry_def();
    if s == t || dom.dominates(t, s) {
        return false;
    }
    cfg.preds(t).iter().all(|&p| p == s || !dom.dominates(entry, p) || dom.dominates(t, p))
}
