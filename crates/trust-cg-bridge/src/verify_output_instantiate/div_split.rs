// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The guarded symbolic division split (DIV-SPLIT-1): a call-event
//! conjunction in which some side divides (unsigned) by a term with a
//! variable, proved by one kernel-checked atom case split. It runs only
//! where the branch split (BRANCH-SPLIT-1, `branch_split.rs`) declined
//! (`branch_dispatch.rs`).
//!
//! # What is proved
//!
//! For `items = [(l_1, r_1) … (l_n, r_n)]` the declared type is the branch
//! split's:
//!
//! ```text
//! G := E_1 ∧ (E_2 ∧ (… ∧ E_n))      E_i := bvfEval R(l_i) = bvfEval R(r_i)
//! ```
//!
//! with `R` the reflection under `ReflectCtx::branching_goal` (every step
//! builder off), computed from the ORIGINAL items before any other analysis
//! ([`goal_of`]). `R` states an unsigned division faithfully, at every
//! divisor, by the frozen `branch_reflect::udiv` goal arm:
//! `bvIteVal (bvIsZero ⟦b⟧) (bvNot (bvAllFalse ⟦a⟧)) (bvDiv ⟦a⟧ ⟦b⟧)`, SMT
//! `bvudiv` with all-ones at a zero divisor. G is declared as a `Theorem`
//! by `strength::admit_obligation` in `branch_theory::env`, which admits it
//! only when its axiom closure is the `BVC_LEAFBIT_*` leaves and its
//! foundational closure is empty.
//!
//! # The width and sort walk
//!
//! The walk is the FROZEN one, reused without a copy ([`in_walk`]): each
//! `BvUDiv(l, r, w)` whose divisor `r` has a variable is replaced, for the
//! walk only, by `BvAdd(l, r, w)` (whose walk arm is the `BvUDiv` arm
//! without its variable-free-divisor check), and each item is then judged by
//! `branch_split::is_condition(Eq(l', r'))` with `l'` not itself a
//! condition. For two bit-vector sides that is exactly `goal_of`'s per-item
//! check, `walk(l).is_some() && walk(l) == walk(r)`, with one node counter
//! shared by both sides (so it can only refuse more). Every other arm, and
//! every `has_var` / `closed_value` check inside the walk, is unchanged:
//! the replaced node keeps its children, so a variable stays a variable.
//! `div_walk_agrees_with_goal_of_without_symbolic_divisors` pins the
//! agreement with `goal_of` on the branch corpus, the captured fixtures and
//! the walk's refusal battery.
//!
//! # The discharge
//!
//! As the branch split's, `π_i = trans P_l (trans S_i (symm P_r))` with the
//! proving reflection (`branch_reflect::reflect_value` under
//! `ReflectCtx::branching`), with two differences in `S_i` ([`Split`]):
//!
//! - **the deep split.** Each atom is abstracted at EVERY occurrence in the
//!   rendered view, inside cores too ([`deep`]), in the statement and in the
//!   `Bool.rec` motive, not only at the condition positions `render_v`
//!   writes. A machine's own division guard `ite(b == 0, 0, U)` sits inside
//!   a core (`reflect_value` lifts only top-level `Ite`s); the deep
//!   abstraction lets the split atom `b == 0` decide it. The term
//!   `(λ v⃗. body) atoms` β-reduces to `render V_l = render V_r` exactly, so
//!   the kernel's check against G is unchanged in kind.
//! - **the leaf comparison modulo δι** ([`norm`]): `bvfEval (BvF.Const l)`
//!   reads as `l`, `bvIteVal true a e` as `a` and `bvIteVal false a e` as
//!   `e`. It only declines; the leaf proof is still `trans p_l (symm p_r)`
//!   over `Eq.refl` leaves, and the kernel discharges the remaining
//!   definitional unfolding.
//!
//! # What is trusted
//!
//! The kernel checks `π` against `G`; what `G` means is trusted residual:
//!
//! - the frozen width and sort walk, reached through `is_condition` on the
//!   substituted view above (so this module adds one walk arm: an unsigned
//!   division by a term with a variable, both operands at the width);
//! - the frozen goal reflection, and in particular `branch_reflect::udiv`
//!   at a SYMBOLIC divisor (before DIV-SPLIT-1 the goal stated it only at a
//!   variable-free one), compared with SMT-LIB by
//!   `branch_reflection_agrees_with_smt` and by this module's
//!   `goal_udiv_agrees_with_smt_on_non_power_of_two_pairs`;
//! - on the machine side, the lifter's AArch64 `UDIV` model
//!   `ite(b == 0, 0, BvUDiv(a, b))` (TCB F1-OUTPUT-TV).
//!
//! # What only declines
//!
//! The pre-filter ([`has_symbolic_divisor`]: the route runs only when some
//! side divides by a term with a variable), the caps, the check that the
//! proving reflection met the goal, the closed-data whitelist at a leaf and
//! the arm comparison at a leaf. [`BranchFilter::Off`] bypasses the last
//! four in [`prove`] so a test shows the KERNEL rejecting a wrong term; the
//! pre-filter sits in [`try_conjunction`] only. The kernel re-check runs on
//! the shared kernel pool exactly as the branch split's does, with no
//! wall-clock deadline (so a grade does not depend on machine load; the
//! kernel's own heartbeat budget bounds the work); a failed spawn or a
//! panicking kernel thread is a decline, never a verdict ([`kernel_check`]).

use std::collections::HashMap;

use clean_kernel::expr::UsedConstants;
use clean_kernel::{ConstantKind, Environment, Expr, ExprKind};
use trust_types::Formula;

use super::branch_reflect::{
    AtomVal, BExpr, VExpr, atoms_b, atoms_v, eval_b, note_closed, reflect_value, render_b, render_v,
};
use super::branch_split::{self, BranchFilter, Decline, Goal, Obligation};
use super::kterm::{Fresh, bool_rec, bool_ty, lams, lb, refl, symm, trans};
use super::{
    ReflectCtx, branch_theory, kx, on_route_stack, reflect_formula, run_recheck_thread, strength,
};
use crate::verify_output::ProvenEvidence;

/// At most this many distinct atoms per conjunction (the branch split's cap).
const MAX_ATOMS: usize = 6;
/// At most this many Bool leaves per condition (the branch split's cap).
const MAX_COND_LEAVES: usize = 32;

/// The last part of the label of a conjunction proved by this route.
pub(crate) const LABEL_TAIL: &str =
    "kernel atom case split, guarded symbolic division (DIV-SPLIT-1)";

// ── the pre-filter and the walk ──────────────────────────────────────────────

fn has_var(f: &Formula) -> bool {
    let mut found = false;
    f.visit(&mut |g| found |= matches!(g, Formula::Var(..) | Formula::SymVar(..)));
    found
}

/// Does some side contain `BvUDiv(_, r, _)` with a variable in `r`? The
/// route runs only then ([`try_conjunction`]).
pub(crate) fn has_symbolic_divisor(items: &[(Formula, Formula)]) -> bool {
    items.iter().any(|(l, r)| {
        [l, r].into_iter().any(|side| {
            let mut hit = false;
            side.visit(&mut |g| {
                if let Formula::BvUDiv(_, d, _) = g {
                    hit |= has_var(d);
                }
            });
            hit
        })
    })
}

/// `f` with each `BvUDiv(l, r, w)` whose `r` has a variable written
/// `BvAdd(l, r, w)`: the frozen walk's `BvAdd` arm is its `BvUDiv` arm
/// without the variable-free-divisor check. Used for the walk only.
pub(crate) fn walk_view(f: &Formula) -> Formula {
    f.clone().map(&mut |g| match g {
        Formula::BvUDiv(l, r, w) if has_var(&r) => Formula::BvAdd(l, r, w),
        other => other,
    })
}

/// Is every item inside the frozen width and sort walk, an unsigned division
/// by a term with a variable admitted? Per item: `is_condition(Eq(l', r'))`
/// (both sides at one width, one node counter) and `l'` not a condition.
pub(crate) fn in_walk(items: &[(Formula, Formula)]) -> bool {
    items.iter().all(|(l, r)| {
        let (l, r) = (walk_view(l), walk_view(r));
        !branch_split::is_condition(&l)
            && branch_split::is_condition(&Formula::Eq(Box::new(l), Box::new(r)))
    })
}

// ── the goal ─────────────────────────────────────────────────────────────────

/// The goal of `items`: `(G, [(bvfEval R l_i, bvfEval R r_i)], leaves)`,
/// under `ReflectCtx::branching_goal` and from the ORIGINAL items alone.
/// The loop below is a copy of `branch_split::goal_of`'s (trusted, TCB
/// F1-OUTPUT-TV): `goal_of_agrees_with_the_branch_split_goal` pins it equal
/// to the frozen one wherever that one admits, and `DIV_GOAL_PIN` pins its
/// bytes on s21.
pub(crate) fn goal_of(items: &[(Formula, Formula)]) -> Result<Goal, String> {
    if !in_walk(items) {
        return Err("div: a side is outside the width walk".into());
    }
    let mut ctx = ReflectCtx::branching_goal();
    let mut sides = Vec::with_capacity(items.len());
    for (l, r) in items {
        let rl = reflect_formula(l, &mut ctx)?;
        let rr = reflect_formula(r, &mut ctx)?;
        sides.push((kx::evalf(rl.bvf), kx::evalf(rr.bvf)));
    }
    let (last, init) = sides.split_last().ok_or("div: empty conjunction")?;
    let mut goal = kx::eq_list(last.0.clone(), last.1.clone());
    for (l, r) in init.iter().rev() {
        goal = Expr::apps(Expr::const_str("And"), [kx::eq_list(l.clone(), r.clone()), goal]);
    }
    let mut leaves: Vec<(String, u32)> = Vec::new();
    for leaf in ctx.leaves {
        if !leaves.contains(&leaf) {
            leaves.push(leaf);
        }
    }
    Ok((goal, sides, leaves))
}

// ── the deep abstraction and the leaf comparison ─────────────────────────────

/// `e` with every subterm `map` names replaced, cores included. Rust-side
/// only: the kernel checks the β-reduct of the abstraction it builds.
pub(crate) fn deep(e: &Expr, map: &dyn Fn(&Expr) -> Option<Expr>) -> Expr {
    fn go(e: &Expr, map: &dyn Fn(&Expr) -> Option<Expr>, memo: &mut HashMap<Expr, Expr>) -> Expr {
        if let Some(x) = map(e) {
            return x;
        }
        if let Some(x) = memo.get(e) {
            return x.clone();
        }
        let out = match e.kind() {
            ExprKind::App(f, a) => Expr::app(go(f, map, memo), go(a, map, memo)),
            _ => e.clone(),
        };
        memo.insert(e.clone(), out.clone());
        out
    }
    go(e, map, &mut HashMap::new())
}

fn head(e: &Expr) -> Option<String> {
    match e.get_app_fn().kind() {
        ExprKind::Const(n, _) => Some(n.to_string()),
        _ => None,
    }
}

/// The leaf comparison's reading of `e`: `bvfEval (BvF.Const l) ↦ l`,
/// `bvIteVal true a e ↦ a`, `bvIteVal false a e ↦ e`, bottom-up. It only
/// declines (two leaves whose readings differ); the kernel decides the
/// leaf by definitional unfolding.
pub(crate) fn norm(e: &Expr) -> Expr {
    fn go(e: &Expr, memo: &mut HashMap<Expr, Expr>) -> Expr {
        if let Some(x) = memo.get(e) {
            return x.clone();
        }
        let e2 = match e.kind() {
            ExprKind::App(f, a) => Expr::app(go(f, memo), go(a, memo)),
            _ => e.clone(),
        };
        let picked = {
            let args = e2.get_app_args();
            let bare = |x: &Expr, name: &str| {
                head(x).as_deref() == Some(name) && x.get_app_args().is_empty()
            };
            match head(&e2).as_deref() {
                Some("Clean.BVC.bvIteVal") if args.len() == 3 => {
                    #[cfg(test)]
                    let (t, f) = if mutant() == Mutant::NormElse { (2, 2) } else { (1, 2) };
                    #[cfg(not(test))]
                    let (t, f) = (1, 2);
                    if bare(args[0], "Bool.true") {
                        Some(args[t].clone())
                    } else if bare(args[0], "Bool.false") {
                        Some(args[f].clone())
                    } else {
                        None
                    }
                }
                Some("Clean.BVC.bvfEval")
                    if args.len() == 1
                        && head(args[0]).as_deref() == Some("Clean.BVC.BvF.Const")
                        && args[0].get_app_args().len() == 1 =>
                {
                    Some(args[0].get_app_args()[0].clone())
                }
                _ => None,
            }
        };
        let out = picked.unwrap_or(e2);
        memo.insert(e.clone(), out.clone());
        out
    }
    go(e, &mut HashMap::new())
}

// ── the case split ───────────────────────────────────────────────────────────

/// One item's split: the two proving views and the atoms. The branch
/// split's `Split` with the deep abstraction in [`Split::render`] and the
/// δι leaf comparison in [`Split::go`].
struct Split<'a> {
    atoms: &'a [Expr],
    vars: Vec<Expr>,
    left: &'a VExpr,
    right: &'a VExpr,
    filter: BranchFilter,
    fr: Fresh,
}

enum Pending {
    Atom(usize),
    Stuck,
}

impl Split<'_> {
    fn index(&self, e: &Expr) -> Option<usize> {
        self.atoms.iter().position(|a| a == e)
    }

    fn atom_value(&self, i: usize, sigma: &[Option<bool>], over: Option<(usize, &Expr)>) -> Expr {
        match (over, sigma[i]) {
            (Some((j, z)), _) if j == i => z.clone(),
            (_, Some(true)) => kx::btrue(),
            (_, Some(false)) => kx::bfalse(),
            (_, None) => self.vars[i].clone(),
        }
    }

    /// `render V` with each atom, at every occurrence (cores included),
    /// a literal when assigned, `over.1` when it is `over.0`, its variable
    /// otherwise.
    fn render(&self, v: &VExpr, sigma: &[Option<bool>], over: Option<(usize, &Expr)>) -> Expr {
        let map = |e: &Expr| Some(self.atom_value(self.index(e)?, sigma, over));
        let shallow = render_v(v, &map);
        #[cfg(test)]
        if mutant() == Mutant::DeepWrong {
            return deep(&shallow, &|e: &Expr| {
                let i = self.index(e)?;
                let n = self.atoms.len();
                Some(match (over, sigma[i]) {
                    (Some((j, z)), _) if j == i => z.clone(),
                    _ if n > 1 => self.atom_value((i + 1) % n, sigma, over),
                    (_, Some(b)) => {
                        if b {
                            kx::bfalse()
                        } else {
                            kx::btrue()
                        }
                    }
                    (_, None) => self.vars[i].clone(),
                })
            });
        }
        deep(&shallow, &map)
    }

    fn render_b(&self, b: &BExpr, sigma: &[Option<bool>]) -> Expr {
        let map = |e: &Expr| Some(self.atom_value(self.index(e)?, sigma, None));
        render_b(b, &map)
    }

    fn statement(&self, sigma: &[Option<bool>], over: Option<(usize, &Expr)>) -> Expr {
        kx::eq_list(self.render(self.left, sigma, over), self.render(self.right, sigma, over))
    }

    fn value(&self, b: &BExpr, sigma: &[Option<bool>]) -> Option<bool> {
        let val = |e: &Expr| self.index(e).and_then(|i| sigma[i]);
        let val: AtomVal<'_> = &val;
        eval_b(b, val)
    }

    fn pending(&self, v: &VExpr, sigma: &[Option<bool>]) -> Option<Pending> {
        let VExpr::Ite(c, a, e) = v else { return None };
        match self.value(c, sigma) {
            Some(true) => self.pending(a, sigma),
            Some(false) => self.pending(e, sigma),
            None => {
                let mut atoms = Vec::new();
                atoms_b(c, &mut atoms);
                Some(
                    atoms
                        .iter()
                        .filter_map(|e| self.index(e))
                        .find(|&i| sigma[i].is_none())
                        .map_or(Pending::Stuck, Pending::Atom),
                )
            }
        }
    }

    /// `(p, t)` with `p : render_σ v = t`, `t` the selected arm.
    fn select(&self, v: &VExpr, sigma: &[Option<bool>]) -> Result<(Expr, Expr), Decline> {
        match v {
            VExpr::Ite(c, a, e) => {
                let b = self.value(c, sigma).ok_or_else(|| {
                    Decline::Filter("div: an undecided condition at a leaf".into())
                })?;
                let kc = self.render_b(c, sigma);
                if self.filter == BranchFilter::On && !note_closed(&kc) {
                    return Err(Decline::Filter(
                        "div: a leaf condition off the closed-data whitelist".into(),
                    ));
                }
                let ra = self.render(a, sigma, None);
                let re = self.render(e, sigma, None);
                let lit = if b { kx::btrue() } else { kx::bfalse() };
                let to_lit = branch_theory::ite_cong_inst(
                    kc.clone(),
                    lit.clone(),
                    ra.clone(),
                    ra.clone(),
                    re.clone(),
                    re.clone(),
                    refl(bool_ty(), lit.clone()),
                    refl(lb(), ra.clone()),
                    refl(lb(), re.clone()),
                );
                let pick = branch_theory::ite_select(b, ra.clone(), re.clone());
                let start = kx::bv_ite_val(kc, ra.clone(), re.clone());
                let chosen = if b { ra.clone() } else { re.clone() };
                let mid = kx::bv_ite_val(lit, ra, re);
                let one = trans(lb(), start.clone(), mid, chosen.clone(), to_lit, pick);
                let (rest, target) = self.select(if b { a } else { e }, sigma)?;
                Ok((trans(lb(), start, chosen, target.clone(), one, rest), target))
            }
            VExpr::Core(_) | VExpr::Bits(_) => {
                let t = self.render(v, sigma, None);
                Ok((refl(lb(), t.clone()), t))
            }
        }
    }

    fn go(&mut self, sigma: &mut Vec<Option<bool>>) -> Result<Expr, Decline> {
        match self.pending(self.left, sigma).or_else(|| self.pending(self.right, sigma)) {
            Some(Pending::Stuck) => Err(Decline::Filter("div: a condition does not reduce".into())),
            Some(Pending::Atom(i)) => {
                let (z_id, z) = self.fr.local();
                let motive = lams(vec![(z_id, bool_ty())], self.statement(sigma, Some((i, &z))));
                sigma[i] = Some(false);
                let on_false = self.go(sigma);
                sigma[i] = Some(true);
                let on_true = self.go(sigma);
                sigma[i] = None;
                Ok(bool_rec(
                    clean_kernel::Level::zero(),
                    motive,
                    on_false?,
                    on_true?,
                    self.vars[i].clone(),
                ))
            }
            None => {
                let (pl, tl) = self.select(self.left, sigma)?;
                let (pr, tr) = self.select(self.right, sigma)?;
                if self.filter == BranchFilter::On && norm(&tl) != norm(&tr) {
                    return Err(Decline::Filter("div: the arms of a case differ".into()));
                }
                let ql = self.render(self.left, sigma, None);
                let qr = self.render(self.right, sigma, None);
                Ok(trans(lb(), ql, tl.clone(), qr.clone(), pl, symm(lb(), qr, tl, pr)))
            }
        }
    }
}

/// `S : render left = render right` for one item.
fn split(
    atoms: &[Expr],
    left: &VExpr,
    right: &VExpr,
    filter: BranchFilter,
) -> Result<Expr, Decline> {
    let (rl, rr) = (render_v(left, &|_| None), render_v(right, &|_| None));
    if rl == rr {
        return Ok(refl(lb(), rl));
    }
    let mut fr = Fresh::new();
    let binders: Vec<_> = atoms.iter().map(|_| fr.local()).collect();
    let vars = binders.iter().map(|(_, v)| v.clone()).collect();
    let mut s = Split { atoms, vars, left, right, filter, fr };
    let body = s.go(&mut vec![None; atoms.len()])?;
    let fun = lams(binders.into_iter().map(|(id, _)| (id, bool_ty())).collect(), body);
    Ok(Expr::apps(fun, atoms.iter().cloned()))
}

fn cond_leaves(b: &BExpr) -> usize {
    match b {
        BExpr::Lit(_) | BExpr::Atom(_) | BExpr::Beq(..) | BExpr::Ult(..) | BExpr::Ule(..) => 1,
        BExpr::Not(x) => cond_leaves(x),
        BExpr::And(x, y) | BExpr::Or(x, y) => cond_leaves(x) + cond_leaves(y),
        BExpr::Ite(c, p, q) => cond_leaves(c) + cond_leaves(p) + cond_leaves(q),
    }
}

fn conds_within_cap(v: &VExpr) -> bool {
    match v {
        VExpr::Ite(c, a, e) => {
            cond_leaves(c) <= MAX_COND_LEAVES && conds_within_cap(a) && conds_within_cap(e)
        }
        VExpr::Core(_) | VExpr::Bits(_) => true,
    }
}

// ── the route ────────────────────────────────────────────────────────────────

fn filtered(filter: BranchFilter, ok: bool, why: &str) -> Result<(), Decline> {
    if filter == BranchFilter::On && !ok { Err(Decline::Filter(why.into())) } else { Ok(()) }
}

/// Build `(G, π)` for `items`; nothing here is checked by the kernel yet.
pub(crate) fn obligation(
    items: &[(Formula, Formula)],
    filter: BranchFilter,
) -> Result<Obligation, Decline> {
    // G first, from the original items alone (the walk is part of it).
    let (goal, sides, leaves) = goal_of(items).map_err(Decline::Filter)?;
    let mut ctx = ReflectCtx::branching();
    let mut views = Vec::with_capacity(items.len());
    for ((l, r), (gl, gr)) in items.iter().zip(&sides) {
        let (lb_, vl, pl) = reflect_value(l, &mut ctx).map_err(Decline::Filter)?;
        let (rb_, vr, pr) = reflect_value(r, &mut ctx).map_err(Decline::Filter)?;
        filtered(
            filter,
            kx::evalf(lb_) == *gl && kx::evalf(rb_) == *gr,
            "div: the proving reflection left the goal",
        )?;
        filtered(filter, conds_within_cap(&vl) && conds_within_cap(&vr), "div: cap (condition)")?;
        views.push((vl, pl, vr, pr));
    }
    filtered(filter, !ctx.branch_cap_hit, "div: cap (steps)")?;
    let mut all_atoms: Vec<Expr> = Vec::new();
    for (vl, _, vr, _) in &views {
        let mut found = Vec::new();
        atoms_v(vl, &mut found);
        atoms_v(vr, &mut found);
        for a in found {
            if !all_atoms.contains(&a) {
                all_atoms.push(a);
            }
        }
    }
    filtered(filter, all_atoms.len() <= MAX_ATOMS, "div: cap (atoms)")?;
    let mut proofs = Vec::with_capacity(views.len());
    for ((vl, pl, vr, pr), (gl, gr)) in views.into_iter().zip(&sides) {
        let mut atoms = Vec::new();
        atoms_v(&vl, &mut atoms);
        atoms_v(&vr, &mut atoms);
        let atoms: Vec<Expr> = all_atoms.iter().filter(|a| atoms.contains(a)).cloned().collect();
        let s = split(&atoms, &vl, &vr, filter)?;
        let (rl, rr) = (render_v(&vl, &|_| None), render_v(&vr, &|_| None));
        let tail =
            trans(lb(), rl.clone(), rr.clone(), gr.clone(), s, symm(lb(), gr.clone(), rr, pr));
        proofs.push(trans(lb(), gl.clone(), rl, gr.clone(), pl, tail));
    }
    let last = sides.len() - 1;
    let eq = |i: usize| kx::eq_list(sides[i].0.clone(), sides[i].1.clone());
    let mut proof = proofs.pop().ok_or_else(|| Decline::Filter("div: empty".into()))?;
    let mut rest = eq(last);
    for i in (0..last).rev() {
        let pi = proofs.pop().ok_or_else(|| Decline::Filter("div: empty".into()))?;
        proof = Expr::apps(Expr::const_str("And.intro"), [eq(i), rest.clone(), pi, proof]);
        rest = Expr::apps(Expr::const_str("And"), [eq(i), rest]);
    }
    debug_assert!(rest == goal);
    Ok(Obligation { goal, proof, leaves })
}

/// The label of an admitted discharge: the `Trust.BVB` / `Trust.BVS` /
/// `Trust.BVV` / `Trust.BVC` / `Clean.BVC` THEOREMS that occur in the term
/// (sorted), then [`LABEL_TAIL`]. Built from the term only.
pub(crate) fn label(env: &Environment, proof: &Expr) -> String {
    let mut used = std::collections::HashSet::new();
    proof.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
    let mut parts: Vec<String> = used
        .into_iter()
        .filter(|n| {
            let s = n.to_string();
            ["Trust.BVB.", "Trust.BVS.", "Trust.BVV.", "Trust.BVC.", "Clean.BVC."]
                .iter()
                .any(|p| s.starts_with(p))
                && env.get_const(n).is_some_and(|info| info.kind == ConstantKind::Theorem)
        })
        .map(|n| n.to_string())
        .collect();
    parts.sort();
    parts.push(LABEL_TAIL.to_string());
    parts.join("+")
}

/// Run `check` on the shared kernel pool (`run_recheck_thread`), as the
/// branch split does: no wall-clock deadline, so whether a conjunction is
/// proved does not depend on machine load or on waiting for a permit; the
/// kernel's heartbeat budget bounds the check. A failed spawn or a panic is
/// `Decline::Environment`: nothing was decided.
pub(crate) fn kernel_check<T, F>(name: &'static str, check: F) -> Result<T, Decline>
where
    T: Send + 'static,
    F: FnOnce() -> Result<T, Decline> + Send + 'static,
{
    run_recheck_thread(name, check).map_err(|e| Decline::Environment(e.to_string())).and_then(|r| r)
}

/// Build the obligation, check it in the kernel, and name it.
pub(crate) fn prove(
    items: &[(Formula, Formula)],
    filter: BranchFilter,
) -> Result<ProvenEvidence, Decline> {
    let trace = std::env::var_os("TRUST_GATE_TRACE").is_some();
    let built = on_route_stack(|| obligation(items, filter));
    let Obligation { goal, proof, leaves } = match built {
        Ok(o) => o,
        Err(d) => {
            if trace {
                eprintln!("[div-split] declined: {d:?}");
            }
            return Err(d);
        }
    };
    let checked = kernel_check("trust-div-split", move || {
        let mut env = branch_theory::env(&leaves).map_err(Decline::Environment)?;
        let declared = cfg!(test).then(|| goal.clone());
        strength::admit_obligation(&mut env, goal, proof.clone()).map_err(Decline::Kernel)?;
        Ok((label(&env, &proof), declared))
    });
    if trace && let Err(d) = &checked {
        eprintln!("[div-split] declined: {d:?}");
    }
    checked.map(|(theorem, declared)| {
        #[cfg(test)]
        DECLARED.with(|d| *d.borrow_mut() = declared);
        #[cfg(not(test))]
        let _ = declared;
        ProvenEvidence::KernelInstantiated { theorem, original: None }
    })
}

#[cfg(test)]
thread_local! {
    /// The type the last successful [`prove`] on this thread declared through
    /// `strength::admit_obligation`.
    static DECLARED: std::cell::RefCell<Option<Expr>> = const { std::cell::RefCell::new(None) };
    /// A deliberately wrong proof builder, for the tests that show the
    /// kernel (or, for `NormElse`, the kernel behind the filter) refusing it.
    static MUTANT: std::cell::Cell<Mutant> = const { std::cell::Cell::new(Mutant::None) };
}

/// The test-only builder mutants ([`MUTANT`]).
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mutant {
    None,
    /// The deep abstraction writes a wrong value into an atom's occurrences:
    /// another atom's, or with one atom its negation (the motive keeps the
    /// right one).
    DeepWrong,
    /// The leaf comparison reads `bvIteVal true a e` as `e` (the else arm on
    /// `true`; `false` stays right).
    NormElse,
}

#[cfg(test)]
fn mutant() -> Mutant {
    MUTANT.with(std::cell::Cell::get)
}

/// The route as `branch_dispatch` calls it: only when some side divides by
/// a term with a variable; `Some(KernelInstantiated)` when the kernel
/// accepts the split, `None` otherwise.
pub(crate) fn try_conjunction(items: &[(Formula, Formula)]) -> Option<ProvenEvidence> {
    if !has_symbolic_divisor(items) {
        return None;
    }
    if std::env::var_os("TRUST_GATE_TRACE").is_some() {
        eprintln!("[div-split] conj {}", serde_json::to_string(items).unwrap_or_default());
    }
    prove(items, BranchFilter::On).ok()
}

#[cfg(test)]
#[path = "div_split/tests.rs"]
mod tests;
