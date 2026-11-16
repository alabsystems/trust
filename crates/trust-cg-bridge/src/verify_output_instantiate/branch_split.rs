// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The branch split (BRANCH-SPLIT-1): a call-event conjunction, branching or
//! not, proved by one kernel-checked term; with atoms, an atom case split.
//!
//! # What is proved
//!
//! For `items = [(l_1, r_1) … (l_n, r_n)]` the declared type is
//!
//! ```text
//! G := E_1 ∧ (E_2 ∧ (… ∧ E_n))      E_i := bvfEval R(l_i) = bvfEval R(r_i)
//! ```
//!
//! with `R` the reflection under `ReflectCtx::branching_goal` (every step
//! builder off), computed from the items before any other analysis
//! ([`goal_of`]), and only for items inside the width and sort walk ([`walk`],
//! plan §4). It is the only declared type: `strength::admit_obligation`
//! declares it as a `Theorem` in `branch_theory::env`, so `add_decl`
//! type-checks the discharge against it, and admits it only when its axiom
//! closure is the `BVC_LEAFBIT_*` leaves and its foundational closure is
//! empty.
//!
//! # The discharge
//!
//! `π_i = trans P_l (trans S_i (symm P_r))`. `P_l` and `P_r` are the proving
//! reflection (`branch_reflect::reflect_value` under `ReflectCtx::branching`),
//! which keeps each `Ite` as `bvIteVal κ A E` with `κ` a structured
//! condition over atoms and takes its kernel-checked steps (ground selection,
//! the zero-wrapper strip, the carrier identities, the bridges and the
//! strength rewrites). `S_i` proves `render V_l = render V_r`. When the two
//! rendered views are equal, `S_i` is `Eq.refl` ([`split`]). Otherwise it is
//! built by `Split::go`: the atoms (maximal Bool subterms over leaf bits, at
//! condition positions only) are abstracted simultaneously, `λ v⃗. Q(v⃗)`, the
//! variables are split by nested `Bool.rec` while one decides a pending
//! condition, and each leaf selects its arms with `ite_cong` / `ite_true` /
//! `ite_false` and closes with `Eq.refl`. The term is applied to the atoms, so
//! it states `Q(atoms)`, which is `render V_l = render V_r` exactly. The items
//! are joined by `And.intro`.
//!
//! A conjunction with no atoms at all (no side branches on a variable) is
//! attempted too. Each item closes by `Eq.refl` on equal views or, where
//! literal conditions (`Ite(true, a, e)`) decide its arms, by the same
//! kernel-checked leaf selection with no `Bool.rec`. Its label still ends with
//! `branch_theory::LABEL_TAIL`, which then names the route, not a split.
//!
//! # What is trusted
//!
//! The kernel checks `π` against `G`; what `G` means is trusted residual:
//!
//! - the width and sort walk ([`walk`]). Widths inside a comparison are not
//!   kernel-enforced (`bvBeq` / `bvUlt` / `bvZipAnd` read a common prefix), so
//!   the kernel proves an ill-sorted comparison on that prefix
//!   (`ill_sorted_comparison_is_kernel_blind_and_refused_by_the_goal`). The
//!   walk is therefore part of computing `G`: [`goal_of`] refuses an item
//!   outside it, and no filter setting bypasses it. Its arms include an
//!   equality of two conditions (a Bool equality, the AArch64 `N == V` of
//!   `b.ge` / `b.lt`), an arithmetic shift by a variable-free amount whose
//!   value ([`closed_value`]) is below the width, and a sign extension of a
//!   variable-free operand;
//! - the Rust goal reflection (`branch_reflect`'s goal arms, `B`) and the
//!   kernel's operator definitions, compared with SMT-LIB semantics and with
//!   ay on closed instances by `branch_reflection_agrees_with_smt`.
//!
//! # What only declines
//!
//! The other Rust checks (the caps, the check that the proving reflection met
//! the goal, the closed-data whitelist at a leaf, the arm comparison at a
//! leaf) only ever decline. [`BranchFilter::Off`] bypasses them, so a test
//! shows the KERNEL rejecting a wrong term. The step builders' own guards in
//! `branch_reflect` (a step is built only when its premise is a literal,
//! whitelisted fact) are not bypassed: they build a term or decline.

use clean_kernel::Expr;
use trust_types::{Formula, Sort};

use super::branch_reflect::{
    AtomVal, BExpr, VExpr, atoms_b, atoms_v, eval_b, note_closed, reflect_value, render_b, render_v,
};
use super::kterm::{Fresh, bool_rec, bool_ty, lams, lb, refl, symm, trans};
use super::{
    ReflectCtx, branch_theory, kx, on_route_stack, reflect_formula, run_recheck_thread, strength,
};
use crate::verify_output::ProvenEvidence;

/// Whether the decline-only Rust checks run. `Off` exists for tests, which
/// use it to show that the kernel, not a Rust check, rejects a wrong term.
/// The width walk is not one of them: it is part of the goal ([`goal_of`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BranchFilter {
    On,
    #[cfg_attr(not(test), expect(dead_code, reason = "a test switch"))]
    Off,
}

/// Why the route declined.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Decline {
    /// A Rust check, the reflection, or the shape of the input.
    Filter(String),
    /// `strength::admit_obligation` refused the discharge: the kernel's
    /// `add_decl` type check (`kernel: …`) or the axiom closure.
    Kernel(String),
    /// The environment could not be built, or the re-check thread failed
    /// (spawn, panic): nothing was decided about the discharge.
    Environment(String),
}

/// At most this many Formula nodes per side.
const MAX_NODES: usize = 1024;
/// At most this many distinct atoms per conjunction.
const MAX_ATOMS: usize = 6;
/// At most this many Bool leaves per condition.
const MAX_COND_LEAVES: usize = 32;
/// At most this many operands of an `And` / `Or`.
const MAX_JUNCTS: usize = 8;

// ── the width and sort walk ──────────────────────────────────────────────────

fn same(a: Option<u32>, b: Option<u32>, w: u32) -> Option<u32> {
    (a? == w && b? == w).then_some(w)
}

/// The width of a bit-vector side, or `None` outside the fragment (plan §4).
fn walk(f: &Formula, n: &mut usize) -> Option<u32> {
    *n += 1;
    if *n > MAX_NODES {
        return None;
    }
    match f {
        Formula::Var(_, Sort::BitVec(w)) | Formula::BitVec { width: w, .. } => {
            (1..=64).contains(w).then_some(*w)
        }
        Formula::BvAdd(l, r, w)
        | Formula::BvSub(l, r, w)
        | Formula::BvMul(l, r, w)
        | Formula::BvOr(l, r, w)
        | Formula::BvXor(l, r, w)
        | Formula::BvShl(l, r, w)
        | Formula::BvAnd(l, r, w) => {
            let wl = walk(l, n);
            same(wl, walk(r, n), *w)
        }
        Formula::BvLShr(l, r, w) => {
            if !matches!(&**r, Formula::BitVec { .. }) {
                return None;
            }
            let wl = walk(l, n);
            same(wl, walk(r, n), *w)
        }
        Formula::BvUDiv(l, r, w) => {
            if has_var(r) {
                return None;
            }
            let wl = walk(l, n);
            same(wl, walk(r, n), *w)
        }
        // An arithmetic shift by a variable-free amount whose value is below
        // the width. The bound only declines: `bvAShr` is faithful at any
        // amount, but `bvTwoPow` unfolds the amount's value by `Nat.rec`.
        Formula::BvAShr(l, r, w) => {
            if has_var(r) || !closed_value(r).is_some_and(|(v, _)| v < u128::from(*w)) {
                return None;
            }
            let wl = walk(l, n);
            same(wl, walk(r, n), *w)
        }
        Formula::BvZeroExt(x, k) => {
            let wx = walk(x, n)?;
            ((1..=63).contains(k) && wx + k <= 64).then_some(wx + k)
        }
        // A sign extension of a variable-free operand (the spec's `sext` of a
        // constant shift amount).
        Formula::BvSignExt(x, k) => {
            if has_var(x) {
                return None;
            }
            let wx = walk(x, n)?;
            ((1..=63).contains(k) && wx + k <= 64).then_some(wx + k)
        }
        Formula::BvExtract { inner, high, low: 0 } => {
            let wi = walk(inner, n)?;
            (*high < wi).then(|| high + 1)
        }
        Formula::BvExtract { inner, high, low } => {
            let wi = walk(inner, n)?;
            (*low < wi && high.checked_add(1) == Some(wi)).then(|| wi - low)
        }
        Formula::Ite(c, a, e) => {
            walk_bool(c, n)?;
            let wa = walk(a, n)?;
            (walk(e, n)? == wa).then_some(wa)
        }
        _ => None,
    }
}

/// A Bool condition in the fragment, or `None`.
fn walk_bool(f: &Formula, n: &mut usize) -> Option<()> {
    *n += 1;
    if *n > MAX_NODES {
        return None;
    }
    match f {
        Formula::Bool(_) => Some(()),
        Formula::Not(x) => walk_bool(x, n),
        Formula::And(xs) | Formula::Or(xs) => {
            if xs.is_empty() || xs.len() > MAX_JUNCTS {
                return None;
            }
            xs.iter().try_for_each(|x| walk_bool(x, n))
        }
        Formula::Ite(c, p, q) => {
            walk_bool(c, n)?;
            walk_bool(p, n)?;
            walk_bool(q, n)
        }
        // A bit-vector equality as before; otherwise an equality of two
        // conditions (Bool equality). Mixed sorts refuse.
        Formula::Eq(a, b) => {
            let mut probe = *n;
            if let Some(wa) = walk(a, &mut probe) {
                *n = probe;
                return (walk(b, n)? == wa).then_some(());
            }
            walk_bool(a, n)?;
            walk_bool(b, n)
        }
        Formula::BvULt(a, b, w) | Formula::BvULe(a, b, w) | Formula::BvSLt(a, b, w) => {
            let wa = walk(a, n);
            same(wa, walk(b, n), *w).map(|_| ())
        }
        _ => None,
    }
}

/// Is `f` a condition (Bool-sorted) inside the walk, and so not a
/// bit-vector? The goal's `B` and the proving reflection read an `Eq` as a
/// Bool equality exactly when its left operand is one (`walk_bool`'s `Eq`
/// arm makes the same choice).
pub(crate) fn is_condition(f: &Formula) -> bool {
    walk(f, &mut 0).is_none() && walk_bool(f, &mut 0).is_some()
}

/// The SMT-LIB value `(value, width)` of a variable-free bit-vector term of
/// at most 64 bits built from literals, `And` / `Or` / `Xor` / `Add` /
/// `Sub`, the extensions and extracts; `None` for anything else. Rust only
/// proposes this value: the walk uses it to decline an arithmetic-shift
/// amount at or past the width, and the shift-amount fold
/// (`branch_reflect::ashr_amount_fold`) as the literal whose equality the
/// kernel checks by computation.
pub(crate) fn closed_value(f: &Formula) -> Option<(u128, u32)> {
    let mask = |w: u32| (1u128 << w) - 1;
    let two = |l: &Formula, r: &Formula, w: u32| {
        let (a, wa) = closed_value(l)?;
        let (b, wb) = closed_value(r)?;
        (wa == w && wb == w).then_some((a, b))
    };
    let (v, w) = match f {
        Formula::BitVec { value, width } if (1..=64).contains(width) => {
            ((*value as u128) & mask(*width), *width)
        }
        Formula::BvAnd(l, r, w) => two(l, r, *w).map(|(a, b)| (a & b, *w))?,
        Formula::BvOr(l, r, w) => two(l, r, *w).map(|(a, b)| (a | b, *w))?,
        Formula::BvXor(l, r, w) => two(l, r, *w).map(|(a, b)| (a ^ b, *w))?,
        Formula::BvAdd(l, r, w) => two(l, r, *w).map(|(a, b)| (a.wrapping_add(b), *w))?,
        Formula::BvSub(l, r, w) => two(l, r, *w).map(|(a, b)| (a.wrapping_sub(b), *w))?,
        Formula::BvZeroExt(x, k) => {
            let (a, wx) = closed_value(x)?;
            (a, wx.checked_add(*k)?)
        }
        Formula::BvSignExt(x, k) => {
            let (a, wx) = closed_value(x)?;
            let w = wx.checked_add(*k)?;
            if w > 64 {
                return None;
            }
            if (a >> (wx - 1)) & 1 == 1 { (a | (mask(w) & !mask(wx)), w) } else { (a, w) }
        }
        Formula::BvExtract { inner, high, low } => {
            let (a, wi) = closed_value(inner)?;
            if low > high || *high >= wi {
                return None;
            }
            (a >> low, high - low + 1)
        }
        _ => return None,
    };
    (1..=64).contains(&w).then(|| (v & mask(w), w))
}

/// Is a side in the branch fragment (plan §4)? The route runs the walk on
/// both sides itself ([`obligation`]); this is the one-side view tests use.
#[cfg(test)]
pub(crate) fn branch_fragment(f: &Formula) -> bool {
    walk(f, &mut 0).is_some()
}

/// The direct children of `f` that [`has_var`] looks through.
fn children(f: &Formula) -> Vec<&Formula> {
    match f {
        Formula::Not(x)
        | Formula::BvNot(x, _)
        | Formula::BvZeroExt(x, _)
        | Formula::BvSignExt(x, _)
        | Formula::BvExtract { inner: x, .. } => vec![x],
        Formula::And(xs) | Formula::Or(xs) => xs.iter().collect(),
        Formula::Ite(a, b, c) | Formula::Store(a, b, c) => vec![a, b, c],
        Formula::Eq(l, r)
        | Formula::Implies(l, r)
        | Formula::BvAdd(l, r, _)
        | Formula::BvSub(l, r, _)
        | Formula::BvMul(l, r, _)
        | Formula::BvUDiv(l, r, _)
        | Formula::BvSDiv(l, r, _)
        | Formula::BvURem(l, r, _)
        | Formula::BvSRem(l, r, _)
        | Formula::BvAnd(l, r, _)
        | Formula::BvOr(l, r, _)
        | Formula::BvXor(l, r, _)
        | Formula::BvShl(l, r, _)
        | Formula::BvLShr(l, r, _)
        | Formula::BvAShr(l, r, _)
        | Formula::BvULt(l, r, _)
        | Formula::BvULe(l, r, _)
        | Formula::BvSLt(l, r, _)
        | Formula::BvSLe(l, r, _)
        | Formula::BvConcat(l, r)
        | Formula::Select(l, r) => vec![l, r],
        _ => Vec::new(),
    }
}

fn has_var(f: &Formula) -> bool {
    matches!(f, Formula::Var(..) | Formula::SymVar(..)) || children(f).into_iter().any(has_var)
}

// ── the goal ─────────────────────────────────────────────────────────────────

/// The goal of `items`: `(G, [(bvfEval R l_i, bvfEval R r_i)], leaves)`,
/// under `ReflectCtx::branching_goal` and from the items alone.
pub(crate) type Goal = (Expr, Vec<(Expr, Expr)>, Vec<(String, u32)>);

pub(crate) fn goal_of(items: &[(Formula, Formula)]) -> Result<Goal, String> {
    // The walk first: `G` states only well-sorted items (see "What is
    // trusted"), whatever the filter.
    for (l, r) in items {
        let (wl, wr) = (walk(l, &mut 0), walk(r, &mut 0));
        if wl.is_none() || wl != wr {
            return Err("branch: a side is outside the width walk".into());
        }
    }
    let mut ctx = ReflectCtx::branching_goal();
    let mut sides = Vec::with_capacity(items.len());
    for (l, r) in items {
        let rl = reflect_formula(l, &mut ctx)?;
        let rr = reflect_formula(r, &mut ctx)?;
        sides.push((kx::evalf(rl.bvf), kx::evalf(rr.bvf)));
    }
    let (last, init) = sides.split_last().ok_or("branch: empty conjunction")?;
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

// ── the case split ───────────────────────────────────────────────────────────

/// One item's split: the two proving views and the atoms.
struct Split<'a> {
    atoms: &'a [Expr],
    vars: Vec<Expr>,
    left: &'a VExpr,
    right: &'a VExpr,
    filter: BranchFilter,
    fr: Fresh,
}

enum Pending {
    /// Split this atom next.
    Atom(usize),
    /// A condition that does not reduce although its atoms are fixed.
    Stuck,
}

impl Split<'_> {
    fn index(&self, e: &Expr) -> Option<usize> {
        self.atoms.iter().position(|a| a == e)
    }

    /// `render V` with each assigned atom a literal, the atom `over.0` the
    /// term `over.1`, and every other atom its variable.
    fn render(&self, v: &VExpr, sigma: &[Option<bool>], over: Option<(usize, &Expr)>) -> Expr {
        let map = |e: &Expr| {
            let i = self.index(e)?;
            Some(match (over, sigma[i]) {
                (Some((j, z)), _) if j == i => z.clone(),
                (_, Some(b)) => {
                    if b {
                        kx::btrue()
                    } else {
                        kx::bfalse()
                    }
                }
                (_, None) => self.vars[i].clone(),
            })
        };
        render_v(v, &map)
    }

    fn render_b(&self, b: &BExpr, sigma: &[Option<bool>]) -> Expr {
        let map = |e: &Expr| {
            let i = self.index(e)?;
            Some(match sigma[i] {
                Some(b) => {
                    if b {
                        kx::btrue()
                    } else {
                        kx::bfalse()
                    }
                }
                None => self.vars[i].clone(),
            })
        };
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

    /// The first condition on the selected path that is not decided yet.
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

    /// `(p, t)` with `p : render_σ v = t`, `t` the selected arm's `bvfEval`.
    fn select(&self, v: &VExpr, sigma: &[Option<bool>]) -> Result<(Expr, Expr), Decline> {
        match v {
            VExpr::Ite(c, a, e) => {
                let b = self.value(c, sigma).ok_or_else(|| {
                    Decline::Filter("branch: an undecided condition at a leaf".into())
                })?;
                let kc = self.render_b(c, sigma);
                if self.filter == BranchFilter::On && !note_closed(&kc) {
                    return Err(Decline::Filter(
                        "branch: a leaf condition off the closed-data whitelist".into(),
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
            Some(Pending::Stuck) => {
                Err(Decline::Filter("branch: a condition does not reduce".into()))
            }
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
                if self.filter == BranchFilter::On && tl != tr {
                    return Err(Decline::Filter("branch: the arms of a case differ".into()));
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

/// A goal, its discharge, and the leaves the environment declares.
pub(crate) struct Obligation {
    pub(crate) goal: Expr,
    pub(crate) proof: Expr,
    pub(crate) leaves: Vec<(String, u32)>,
}

fn filtered(filter: BranchFilter, ok: bool, why: &str) -> Result<(), Decline> {
    if filter == BranchFilter::On && !ok { Err(Decline::Filter(why.into())) } else { Ok(()) }
}

/// Build `(G, π)` for `items`; nothing here is checked by the kernel yet.
pub(crate) fn obligation(
    items: &[(Formula, Formula)],
    filter: BranchFilter,
) -> Result<Obligation, Decline> {
    // G first, from the items alone (the width walk is part of it).
    let (goal, sides, leaves) = goal_of(items).map_err(Decline::Filter)?;
    let mut ctx = ReflectCtx::branching();
    let mut views = Vec::with_capacity(items.len());
    for ((l, r), (gl, gr)) in items.iter().zip(&sides) {
        let (lb_, vl, pl) = reflect_value(l, &mut ctx).map_err(Decline::Filter)?;
        let (rb_, vr, pr) = reflect_value(r, &mut ctx).map_err(Decline::Filter)?;
        filtered(
            filter,
            kx::evalf(lb_) == *gl && kx::evalf(rb_) == *gr,
            "branch: the proving reflection left the goal",
        )?;
        filtered(
            filter,
            conds_within_cap(&vl) && conds_within_cap(&vr),
            "branch: cap (condition)",
        )?;
        views.push((vl, pl, vr, pr));
    }
    filtered(filter, !ctx.branch_cap_hit, "branch: cap (steps)")?;
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
    filtered(filter, all_atoms.len() <= MAX_ATOMS, "branch: cap (atoms)")?;
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
    let mut proof = proofs.pop().ok_or_else(|| Decline::Filter("branch: empty".into()))?;
    let mut rest = eq(last);
    for i in (0..last).rev() {
        let pi = proofs.pop().ok_or_else(|| Decline::Filter("branch: empty".into()))?;
        proof = Expr::apps(Expr::const_str("And.intro"), [eq(i), rest.clone(), pi, proof]);
        rest = Expr::apps(Expr::const_str("And"), [eq(i), rest]);
    }
    debug_assert!(rest == goal);
    Ok(Obligation { goal, proof, leaves })
}

/// Build the obligation, check it in the kernel, and name it.
pub(crate) fn prove(
    items: &[(Formula, Formula)],
    filter: BranchFilter,
) -> Result<ProvenEvidence, Decline> {
    let trace = std::env::var_os("TRUST_GATE_TRACE").is_some();
    if trace {
        eprintln!("[branch-split] conj {}", serde_json::to_string(items).unwrap_or_default());
    }
    let built = on_route_stack(|| obligation(items, filter));
    let Obligation { goal, proof, leaves } = match built {
        Ok(o) => o,
        Err(d) => {
            if trace {
                eprintln!("[branch-split] declined: {d:?}");
            }
            return Err(d);
        }
    };
    let checked = run_recheck_thread("trust-branch-split", move || {
        let mut env = branch_theory::env(&leaves).map_err(Decline::Environment)?;
        // The test hook keeps a copy of exactly the type handed to admission.
        let declared = cfg!(test).then(|| goal.clone());
        strength::admit_obligation(&mut env, goal, proof.clone()).map_err(Decline::Kernel)?;
        Ok((branch_theory::label(&env, &proof), declared))
    })
    .map_err(|e| Decline::Environment(e.to_string()))
    .and_then(|r| r);
    if trace && let Err(d) = &checked {
        eprintln!("[branch-split] declined: {d:?}");
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
    /// `strength::admit_obligation` (`declared_type_is_the_independent_goal`).
    static DECLARED: std::cell::RefCell<Option<Expr>> = const { std::cell::RefCell::new(None) };
}

/// The route: `Some(KernelInstantiated)` when the kernel accepts the split,
/// `None` otherwise.
pub(crate) fn try_branch_split_conjunction(items: &[(Formula, Formula)]) -> Option<ProvenEvidence> {
    prove(items, BranchFilter::On).ok()
}

#[cfg(test)]
#[path = "branch_split/tests.rs"]
mod tests;
