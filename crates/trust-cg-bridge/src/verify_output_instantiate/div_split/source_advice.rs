// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Untrusted signed proof advice reused from the withdrawn S3d producer.
//! Nothing here returns a verdict, a checked token or a source meaning. The
//! legacy signed goal/refusal stays intact. Only canonical FMREL admission of
//! the complete original-byte relation and final ConjHoldsB proof can consume
//! these terms. All arithmetic operators remain the existing BVC operators.

use super::super::kterm::{bvlen, eq, nat};
use super::*;

#[path = "source_advice/bank.rs"]
pub(crate) mod bank;
#[path = "source_advice/shared.rs"]
mod shared;
#[path = "source_advice/transport.rs"]
pub(crate) mod transport;

fn context(proving: bool) -> ReflectCtx {
    let mut ctx = if proving { div_proving() } else { ReflectCtx::branching_goal() };
    ctx.source_goal_advice = true;
    ctx
}

/// A bounded decline filter, never the authority for Formula typing/meaning.
fn in_walk(items: &[(Formula, Formula)]) -> bool {
    let view = |f: &Formula| {
        f.clone().map(&mut |g| match g {
            Formula::BvUDiv(a, b, w) | Formula::BvSDiv(a, b, w) if has_var(&b) => {
                Formula::BvAdd(a, b, w)
            }
            Formula::BvNot(x, w) if matches!(*x, Formula::BitVec { .. }) => {
                Formula::BvXor(x, Box::new(Formula::BitVec { value: -1, width: w }), w)
            }
            other => other,
        })
    };
    items.iter().all(|(a, b)| {
        let (a, b) = (view(a), view(b));
        !branch_split::is_condition(&a)
            && branch_split::is_condition(&Formula::Eq(Box::new(a), Box::new(b)))
    })
}

fn goal_data(items: &[(Formula, Formula)]) -> Result<Goal, String> {
    if !in_walk(items) {
        return Err("original source advice: outside bounded walk".into());
    }
    let mut ctx = context(false);
    let mut sides = Vec::with_capacity(items.len());
    for (a, b) in items {
        sides.push((
            kx::evalf(reflect_formula(a, &mut ctx)?.bvf),
            kx::evalf(reflect_formula(b, &mut ctx)?.bvf),
        ));
    }
    let (last, init) = sides.split_last().ok_or("original source advice: empty conjunction")?;
    let mut goal = kx::eq_list(last.0.clone(), last.1.clone());
    for (a, b) in init.iter().rev() {
        goal = Expr::apps(Expr::const_str("And"), [kx::eq_list(a.clone(), b.clone()), goal]);
    }
    let mut leaves = Vec::new();
    for leaf in ctx.leaves {
        if !leaves.contains(&leaf) {
            leaves.push(leaf);
        }
    }
    Ok((goal, sides, leaves))
}

pub(crate) fn propose(items: &[(Formula, Formula)]) -> Result<Obligation, Decline> {
    #[cfg(any(test, feature = "test-hooks"))]
    crate::original_conjunction_certificate::require_production_allowed();
    obligation_data(items, BranchFilter::On, goal_data(items), context(true), true)
}

fn signed_zero(t: Expr) -> Expr {
    let ones = all_ones(t.clone());
    kx::bv_ite_val(kx::last_bit(t), kx::bv_neg(ones.clone()), ones)
}

pub(crate) fn sdiv(a: &Formula, b: &Formula, ctx: &mut ReflectCtx) -> Result<Reflected, String> {
    if !has_var(b) {
        return Err("original source advice: closed signed divisor".into());
    }
    let (a, b) = (reflect_formula(a, ctx)?, reflect_formula(b, ctx)?);
    let bvf = kx::const_(kx::bv_ite_val(
        kx::bv_is_zero(kx::evalf(b.bvf.clone())),
        signed_zero(kx::evalf(a.bvf.clone())),
        kx::evalf(kx::sdiv(a.bvf.clone(), b.bvf.clone())),
    ));
    Ok(
        match if ctx.div_steps && ctx.branching_steps {
            faithful_div_core(&a, &b, kx::sdiv, kx::sdiv_cong, &signed_zero)
        } else {
            None
        } {
            Some((core, proof)) => Reflected { bvf, core, proof },
            None => Reflected {
                core: bvf.clone(),
                proof: kx::eq_refl_list(kx::evalf(bvf.clone())),
                bvf,
            },
        },
    )
}

pub(crate) fn bvnot(a: &Formula, w: u32, ctx: &mut ReflectCtx) -> Result<Reflected, String> {
    if !matches!(a,Formula::BitVec{width,..} if *width==w) {
        return Err("original source advice: complemented operand is not a matching literal".into());
    }
    let bvf = kx::const_(kx::bv_not(kx::evalf(reflect_formula(a, ctx)?.bvf)));
    Ok(Reflected { core: bvf.clone(), proof: kx::eq_refl_list(kx::evalf(bvf.clone())), bvf })
}

pub(super) fn canonicalize(lhs: &Expr, view: VExpr, proof: Expr) -> (VExpr, Expr) {
    let (view, proof) = zcmp(lhs, view, proof);
    mlift(lhs, view, proof)
}

const ZCMP_EXTRA: [&str; 2] = ["Clean.BVC.bvNot", "Clean.BVC.BvF.Or"];

/// At most this many compare rewrites per view.
const MAX_ZCMP: usize = 8;

/// The arguments of `name a1 … an`, `None` for another head or arity.
fn args_of(e: &Expr, name: &str, arity: usize) -> Option<Vec<Expr>> {
    if head(e).as_deref() != Some(name) {
        return None;
    }
    let args = e.get_app_args();
    (args.len() == arity).then(|| args.iter().map(|a| (*a).clone()).collect())
}

/// Is `e` closed data the kernel may evaluate for the canonicalization:
/// applications of [`branch_reflect::CLOSED_WHITELIST`] and `extra`
/// constants only (no leaf, no binder, no literal), concrete lists of at most
/// 64 elements? Decline only.
fn closed_ok_local(e: &Expr, extra: &[&str]) -> bool {
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(n, _) => {
                let s = n.to_string();
                if !(branch_reflect::CLOSED_WHITELIST.contains(&s.as_str())
                    || extra.contains(&s.as_str()))
                {
                    return false;
                }
            }
            ExprKind::App(f, a) => {
                if head(e).as_deref() == Some("List.cons")
                    && e.get_app_args().len() == 3
                    && branch_theory::spine(e).is_none()
                {
                    return false;
                }
                stack.push(f);
                stack.push(a);
            }
            _ => return false,
        }
    }
    true
}

/// The bits (least significant first) `bvfEval k` computes to, for a closed
/// `k` over `BvF.Const` of a concrete list, `bvNot`, `bvfEval` and `BvF.And`
/// / `BvF.Or` of operands of one length. It only PROPOSES: the kernel checks
/// the fold (`Eq.refl`), so a wrong answer is refused.
fn closed_bits(k: &Expr) -> Option<Vec<bool>> {
    if let Some([l]) = args_of(k, "Clean.BVC.BvF.Const", 1).as_deref() {
        return list_bits(l);
    }
    for (op, and) in [("Clean.BVC.BvF.And", true), ("Clean.BVC.BvF.Or", false)] {
        if let Some([a, b]) = args_of(k, op, 2).as_deref() {
            let (x, y) = (closed_bits(a)?, closed_bits(b)?);
            return (x.len() == y.len())
                .then(|| x.iter().zip(&y).map(|(p, q)| if and { p & q } else { p | q }).collect());
        }
    }
    None
}

fn list_bits(l: &Expr) -> Option<Vec<bool>> {
    if let Some([x]) = args_of(l, "Clean.BVC.bvNot", 1).as_deref() {
        return Some(list_bits(x)?.into_iter().map(|b| !b).collect());
    }
    if let Some([x]) = args_of(l, "Clean.BVC.bvfEval", 1).as_deref() {
        return closed_bits(x);
    }
    branch_theory::spine(l)?.iter().map(branch_theory::bool_lit).collect()
}

/// The literal list of `bits`, as `kx::bits` writes one (byte-identical to the
/// spec's literal of the same value).
fn bits_list(bits: &[bool]) -> Expr {
    bits.iter()
        .rev()
        .fold(kx::nil(), |acc, &b| kx::cons(if b { kx::btrue() } else { kx::bfalse() }, acc))
}

/// For a candidate `t = bvBeq (bvfEval (Sub a k)) (bvfEval (Const Z))` (`Z`
/// all false at the width `w` of `a`, `k` closed and on the local list,
/// `bvfEval k` computing to `v` of length `w`): `(t', h)` with
/// `t' = bvBeq ⟦a⟧ ⟦Const v⟧` and `h : t = t'`, by
/// `congrArg (λu. bvBeq (addRecM ⟦a⟧ (bvNot u) true) ⟦Z⟧) (Eq.refl ⟦v⟧)`
/// (the fold of `k`, which the kernel computes), `Trust.BVB.beq_allFalse`
/// and `Clean.BVC.beq_eq_isZero_sub` reversed (`hi_ult`'s chain). `None`
/// for any other term.
fn zcmp_step(t: &Expr) -> Option<(Expr, Expr)> {
    let [x, y] = <[Expr; 2]>::try_from(args_of(t, "Clean.BVC.bvBeq", 2)?).ok()?;
    let [sub] = <[Expr; 1]>::try_from(args_of(&x, "Clean.BVC.bvfEval", 1)?).ok()?;
    let [a, k] = <[Expr; 2]>::try_from(args_of(&sub, "Clean.BVC.BvF.Sub", 2)?).ok()?;
    let [zc] = <[Expr; 1]>::try_from(args_of(&y, "Clean.BVC.bvfEval", 1)?).ok()?;
    let [zl] = <[Expr; 1]>::try_from(args_of(&zc, "Clean.BVC.BvF.Const", 1)?).ok()?;
    let z: Vec<bool> =
        branch_theory::spine(&zl)?.iter().map(branch_theory::bool_lit).collect::<Option<_>>()?;
    let w = u32::try_from(z.len()).ok()?;
    if w == 0 || z.iter().any(|&b| b) {
        return None;
    }
    let (ha, wa) = super::super::add_comm::core_len(&a)?;
    if wa != w || !closed_ok_local(&k, &ZCMP_EXTRA) {
        return None;
    }
    let v = closed_bits(&k)?;
    if v.len() != z.len() {
        return None;
    }
    let lit = kx::const_(bits_list(&v));
    let (hv, wv) = super::super::add_comm::core_len(&lit)?;
    if wv != w {
        return None;
    }
    let (ea, ek, ev) = (kx::evalf(a), kx::evalf(k), kx::evalf(lit));
    let d = kx::add_rec_m(ea.clone(), kx::bv_not(ev.clone()), kx::btrue());
    // h_fold : bvfEval k = ev, by computation.
    let h_fold = refl(lb(), ev.clone());
    let mut fr = Fresh::new();
    let (u_id, u) = fr.local();
    let motive = lams(
        vec![(u_id, lb())],
        kx::bv_beq(kx::add_rec_m(ea.clone(), kx::bv_not(u), kx::btrue()), y.clone()),
    );
    // s1 : t = bvBeq d ⟦Z⟧ (t is the motive at ⟦k⟧ by bvfEval's Sub case).
    let s1 = congr_arg(lb(), bool_ty(), ek, ev.clone(), motive, h_fold);
    let mid = kx::bv_beq(d.clone(), y);
    let is0 = kx::bv_is_zero(d.clone());
    // p1 : bvBeq d (AF d) = bvIsZero d, with ⟦Z⟧ ≡ AF d by computation.
    let p1 = Expr::apps(Expr::const_str(branch_theory::names::BEQ_ALL_FALSE), [d]);
    let nw = kx::nat_lit(w);
    let hlen = trans(
        nat(),
        bvlen(ea.clone()),
        nw.clone(),
        bvlen(ev.clone()),
        ha,
        symm(nat(), bvlen(ev.clone()), nw, hv),
    );
    let t2 = kx::bv_beq(ea.clone(), ev.clone());
    let (pa, pb) = (ea, ev);
    // p2 : bvBeq ea ev = bvIsZero d.
    let p2 = Expr::apps(Expr::const_str("Clean.BVC.beq_eq_isZero_sub"), [pa, pb, hlen]);
    let tail = trans(
        bool_ty(),
        mid.clone(),
        is0.clone(),
        t2.clone(),
        p1,
        symm(bool_ty(), t2.clone(), is0, p2),
    );
    Some((t2.clone(), trans(bool_ty(), t.clone(), mid, t2, s1, tail)))
}

/// Every distinct candidate subterm of `e` ([`zcmp_step`] answers it), in
/// a fixed (depth-first, left to right) order.
fn zcmp_candidates(e: &Expr) -> Vec<(Expr, Expr, Expr)> {
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::new();
    let mut stack = vec![e.clone()];
    while let Some(x) = stack.pop() {
        if !seen.insert(x.clone()) {
            continue;
        }
        if let Some((t2, h)) = zcmp_step(&x) {
            out.push((x, t2, h));
            continue;
        }
        if let ExprKind::App(f, a) = x.kind() {
            stack.push(Expr::clone(a));
            stack.push(Expr::clone(f));
        }
    }
    out
}

fn zcmp_b(b: &BExpr, t: &Expr, t2: &Expr) -> BExpr {
    let bx = |x: &BExpr| Box::new(zcmp_b(x, t, t2));
    let vx = |x: &VExpr| Box::new(zcmp_v(x, t, t2));
    match b {
        BExpr::Lit(v) => BExpr::Lit(*v),
        BExpr::Atom(e) => BExpr::Atom(deep(e, &|x| (x == t).then(|| t2.clone()))),
        BExpr::Not(x) => BExpr::Not(bx(x)),
        BExpr::And(x, y) => BExpr::And(bx(x), bx(y)),
        BExpr::Or(x, y) => BExpr::Or(bx(x), bx(y)),
        BExpr::Ite(c, p, q) => BExpr::Ite(bx(c), bx(p), bx(q)),
        BExpr::Beq(x, y) => BExpr::Beq(vx(x), vx(y)),
        BExpr::Ult(x, y) => BExpr::Ult(vx(x), vx(y)),
        BExpr::Ule(x, y) => BExpr::Ule(vx(x), vx(y)),
    }
}

fn zcmp_v(v: &VExpr, t: &Expr, t2: &Expr) -> VExpr {
    match v {
        VExpr::Ite(c, a, e) => VExpr::Ite(
            Box::new(zcmp_b(c, t, t2)),
            Box::new(zcmp_v(a, t, t2)),
            Box::new(zcmp_v(e, t, t2)),
        ),
        VExpr::Core(c) => VExpr::Core(deep(c, &|x| (x == t).then(|| t2.clone()))),
        VExpr::Bits(bs) => VExpr::Bits(bs.iter().map(|b| zcmp_b(b, t, t2)).collect()),
    }
}

/// THE COMPARE CANONICALIZATION: a proving view `(V, p : lhs = render V)`
/// with each machine compare against a closed constant `bvBeq ⟦a - k⟧ ⟦0⟧`
/// (AArch64 `cmp a, xK`'s Z flag, `K` materialized by `MOVN` / `MOVZ` /
/// `MOVK`, or `#k` in 1..4095 folded into the `cmp`) restated, at every
/// occurrence (cores and every view position included), as the spec's atom
/// `bvBeq ⟦a⟧ ⟦Const v⟧`: `(V', trans p (congrArg (λz. render V [t := z])
/// h))` with `h` from [`zcmp_step`]. A rewrite whose view does not render as
/// the substituted term is not taken. Proof construction the kernel checks:
/// it never changes G or a `bvf`.
fn zcmp(lhs: &Expr, view: VExpr, proof: Expr) -> (VExpr, Expr) {
    let (mut view, mut proof) = (view, proof);
    let mut tried = std::collections::HashSet::new();
    for _ in 0..MAX_ZCMP {
        let rv = render_v(&view, &|_| None);
        let Some((t, t2, h)) =
            zcmp_candidates(&rv).into_iter().find(|(t, _, _)| !tried.contains(t))
        else {
            break;
        };
        tried.insert(t.clone());
        let rv2 = deep(&rv, &|x| (x == &t).then(|| t2.clone()));
        let view2 = zcmp_v(&view, &t, &t2);
        if render_v(&view2, &|_| None) != rv2 {
            continue;
        }
        let mut fr = Fresh::new();
        let (z_id, z) = fr.local();
        let f = lams(vec![(z_id, bool_ty())], deep(&rv, &|x| (x == &t).then(|| z.clone())));
        let step = congr_arg(bool_ty(), lb(), t, t2, f, h);
        proof = trans(lb(), lhs.clone(), rv, rv2.clone(), proof, step);
        view = view2;
    }
    (view, proof)
}

// ── the materialized-condition lift (S3d) ────────────────────────────────────

/// The heads a lifted atom's closed instances may use besides the closed-data
/// whitelist: the canonicalization's, and the `Sub` / `Add` of an O0 compare
/// of a materialized condition (`subs xN, #0` on a `csinc` result). Decline
/// only.
const MLIFT_EXTRA: [&str; 4] =
    ["Clean.BVC.bvNot", "Clean.BVC.BvF.Or", "Clean.BVC.BvF.Sub", "Clean.BVC.BvF.Add"];

/// At most this many lifts per view.
const MAX_MLIFT: usize = 8;

fn has_leafbit(e: &Expr) -> bool {
    let mut used = std::collections::HashSet::new();
    e.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
    used.iter().any(|n| n.to_string().starts_with("BVC_LEAF"))
}

/// The bits a closed list computes to: a concrete spine, `bvNot`, `bvfEval`
/// of closed `BvF` data, or `bvIteVal` of a closed condition. It only
/// PROPOSES: the kernel computes the lifted atom's instances itself, so a
/// wrong answer is refused.
fn ceval_list(l: &Expr) -> Option<Vec<bool>> {
    if let Some([c, a, b]) = args_of(l, "Clean.BVC.bvIteVal", 3).as_deref() {
        return if ceval_bool(c)? { ceval_list(a) } else { ceval_list(b) };
    }
    if let Some([x]) = args_of(l, "Clean.BVC.bvfEval", 1).as_deref() {
        return ceval_bvf(x);
    }
    if let Some([x]) = args_of(l, "Clean.BVC.bvNot", 1).as_deref() {
        return Some(ceval_list(x)?.into_iter().map(|b| !b).collect());
    }
    branch_theory::spine(l)?.iter().map(branch_theory::bool_lit).collect()
}

/// `bvfEval f` for closed `BvF` data: `Const`, and `Add` / `Sub` / `And` /
/// `Or` / `Xor` of operands of one length (`Sub` as `addRecM a (bvNot b)
/// true`, least significant bit first).
fn ceval_bvf(f: &Expr) -> Option<Vec<bool>> {
    if let Some([l]) = args_of(f, "Clean.BVC.BvF.Const", 1).as_deref() {
        return ceval_list(l);
    }
    for op in ["Add", "Sub", "And", "Or", "Xor"] {
        let Some(ab) = args_of(f, &format!("Clean.BVC.BvF.{op}"), 2) else { continue };
        let (x, y) = (ceval_bvf(&ab[0])?, ceval_bvf(&ab[1])?);
        if x.len() != y.len() {
            return None;
        }
        let add = |y: Vec<bool>, mut carry: bool| {
            x.iter()
                .zip(y)
                .map(|(&p, q)| {
                    let s = p ^ q ^ carry;
                    carry = (p & q) | (carry & (p ^ q));
                    s
                })
                .collect::<Vec<bool>>()
        };
        let zip = |g: fn(bool, bool) -> bool| x.iter().zip(&y).map(|(&p, &q)| g(p, q)).collect();
        return Some(match op {
            "Add" => add(y.clone(), false),
            "Sub" => add(y.iter().map(|b| !b).collect(), true),
            "And" => zip(|p, q| p & q),
            "Or" => zip(|p, q| p | q),
            _ => zip(|p, q| p ^ q),
        });
    }
    None
}

/// The Bool a closed condition computes to: a literal, `Bool.not`, `bvBeq`
/// of two lists of one length, or `bvIsZero`.
fn ceval_bool(e: &Expr) -> Option<bool> {
    if let Some(b) = branch_theory::bool_lit(e) {
        return Some(b);
    }
    if let Some([x]) = args_of(e, "Bool.not", 1).as_deref() {
        return ceval_bool(x).map(|b| !b);
    }
    if let Some([x]) = args_of(e, "Clean.BVC.bvIsZero", 1).as_deref() {
        return Some(ceval_list(x)?.iter().all(|b| !b));
    }
    let [a, b] = <[Expr; 2]>::try_from(args_of(e, "Clean.BVC.bvBeq", 2)?).ok()?;
    let (x, y) = (ceval_list(&a)?, ceval_list(&b)?);
    (x.len() == y.len()).then(|| x == y)
}

/// For an atom `t` whose only leaf bits sit in ONE condition `c` of a
/// `bvIteVal c x y` inside it (`c` a `bvBeq` with a leaf bit: an atom of its
/// own, as the canonicalization leaves the machine's compare), and whose two
/// instances `t[c := b]` are closed data computing to `vb`:
/// `(c, vt, vf, h)` with `h : t = Bool.rec vf vt c` (`render_b (Ite (Atom c)
/// (Lit vt) (Lit vf))`), by `Bool.rec` on `c` with `Eq.refl` in each case,
/// which the kernel closes only by computing both instances. `None` for any
/// other atom.
fn mlift_step(t: &Expr) -> Option<(Expr, BExpr, Expr)> {
    if head(t).as_deref() != Some("Clean.BVC.bvBeq") {
        return None;
    }
    let mut conds: Vec<Expr> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut stack = vec![t.clone()];
    while let Some(x) = stack.pop() {
        if !seen.insert(x.clone()) {
            continue;
        }
        if let Some([c, _, _]) = args_of(&x, "Clean.BVC.bvIteVal", 3).as_deref() {
            if has_leafbit(c) && !conds.contains(c) {
                conds.push(c.clone());
            }
        }
        if let ExprKind::App(f, a) = x.kind() {
            stack.push(Expr::clone(a));
            stack.push(Expr::clone(f));
        }
    }
    let [c] = <[Expr; 1]>::try_from(conds).ok()?;
    if head(&c).as_deref() != Some("Clean.BVC.bvBeq") || c == *t {
        return None;
    }
    let at = |b: bool| deep(t, &|x| (x == &c).then(|| if b { kx::btrue() } else { kx::bfalse() }));
    let (tt, tf) = (at(true), at(false));
    if has_leafbit(&tt)
        || has_leafbit(&tf)
        || !closed_ok_local(&tt, &MLIFT_EXTRA)
        || !closed_ok_local(&tf, &MLIFT_EXTRA)
    {
        return None;
    }
    let (vt, vf) = (ceval_bool(&tt)?, ceval_bool(&tf)?);
    let lifted = |z: Expr| {
        BExpr::Ite(Box::new(BExpr::Atom(z)), Box::new(BExpr::Lit(vt)), Box::new(BExpr::Lit(vf)))
    };
    let lit_of = |b: bool| if b { kx::btrue() } else { kx::bfalse() };
    let mut fr = Fresh::new();
    let (z_id, z) = fr.local();
    let body = eq(
        bool_ty(),
        deep(t, &|x| (x == &c).then(|| z.clone())),
        render_b(&lifted(z.clone()), &|_| None),
    );
    let motive = lams(vec![(z_id, bool_ty())], body);
    let h = bool_rec(
        clean_kernel::Level::zero(),
        motive,
        refl(bool_ty(), lit_of(vf)),
        refl(bool_ty(), lit_of(vt)),
        c.clone(),
    );
    Some((t.clone(), lifted(c), h))
}

fn mlift_b(b: &BExpr, t: &Expr, k: &BExpr, t2: &Expr) -> BExpr {
    let bx = |x: &BExpr| Box::new(mlift_b(x, t, k, t2));
    let vx = |x: &VExpr| Box::new(mlift_v(x, t, k, t2));
    match b {
        BExpr::Lit(v) => BExpr::Lit(*v),
        BExpr::Atom(e) if e == t => k.clone(),
        BExpr::Atom(e) => BExpr::Atom(deep(e, &|x| (x == t).then(|| t2.clone()))),
        BExpr::Not(x) => BExpr::Not(bx(x)),
        BExpr::And(x, y) => BExpr::And(bx(x), bx(y)),
        BExpr::Or(x, y) => BExpr::Or(bx(x), bx(y)),
        BExpr::Ite(c, p, q) => BExpr::Ite(bx(c), bx(p), bx(q)),
        BExpr::Beq(x, y) => BExpr::Beq(vx(x), vx(y)),
        BExpr::Ult(x, y) => BExpr::Ult(vx(x), vx(y)),
        BExpr::Ule(x, y) => BExpr::Ule(vx(x), vx(y)),
    }
}

fn mlift_v(v: &VExpr, t: &Expr, k: &BExpr, t2: &Expr) -> VExpr {
    match v {
        VExpr::Ite(c, a, e) => VExpr::Ite(
            Box::new(mlift_b(c, t, k, t2)),
            Box::new(mlift_v(a, t, k, t2)),
            Box::new(mlift_v(e, t, k, t2)),
        ),
        VExpr::Core(c) => VExpr::Core(deep(c, &|x| (x == t).then(|| t2.clone()))),
        VExpr::Bits(bs) => VExpr::Bits(bs.iter().map(|b| mlift_b(b, t, k, t2)).collect()),
    }
}

/// THE MATERIALIZED-CONDITION LIFT: after [`zcmp`], each atom of the view
/// that is decided by ONE inner atom (O0's `subs xN, #0` on a `csinc` that
/// materialized the compare `c`: `bvBeq ⟦ite(c, 0, 1) - 0⟧ ⟦0⟧`) restated as
/// `Ite(c, vt, vf)` over that atom, so the split never assigns the outer
/// atom independently of `c` (an infeasible case whose arms differ):
/// `(V', trans p (congrArg (λz. render V [t := z]) h))` with `h` from
/// [`mlift_step`]. A rewrite whose view does not render as the substituted
/// term is not taken. Proof construction the kernel checks: it never changes
/// G or a `bvf`.
fn mlift(lhs: &Expr, view: VExpr, proof: Expr) -> (VExpr, Expr) {
    let (mut view, mut proof) = (view, proof);
    let mut tried = std::collections::HashSet::new();
    for _ in 0..MAX_MLIFT {
        let mut atoms = Vec::new();
        atoms_v(&view, &mut atoms);
        let mut found = None;
        for t in atoms {
            if tried.insert(t.clone()) {
                if let Some(step) = mlift_step(&t) {
                    found = Some(step);
                    break;
                }
            }
        }
        let Some((t, k, h)) = found else { break };
        let t2 = render_b(&k, &|_| None);
        let rv = render_v(&view, &|_| None);
        let rv2 = deep(&rv, &|x| (x == &t).then(|| t2.clone()));
        let view2 = mlift_v(&view, &t, &k, &t2);
        if render_v(&view2, &|_| None) != rv2 {
            continue;
        }
        let mut fr = Fresh::new();
        let (z_id, z) = fr.local();
        let f = lams(vec![(z_id, bool_ty())], deep(&rv, &|x| (x == &t).then(|| z.clone())));
        let step = congr_arg(bool_ty(), lb(), t, t2, f, h);
        proof = trans(lb(), lhs.clone(), rv, rv2.clone(), proof, step);
        view = view2;
    }
    (view, proof)
}
