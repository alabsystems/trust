// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The reflection arms of the branch split (BRANCH-SPLIT-1).
//!
//! # The goal arms (`ctx.branching`)
//!
//! `reflect_formula` dispatches here only under `ctx.branching`; every legacy
//! context reflects exactly as before (`legacy_reflection_is_byte_pinned_on_branch_corpus`).
//!
//! - bit-vector `Ite(c, a, e)` is `BvF.Const (bvIteVal B(c) (bvfEval R a) (bvfEval R e))`;
//! - `BvUDiv(a, b)` is SMT `bvudiv`, all-ones at a zero divisor:
//!   `BvF.Const (bvIteVal (bvIsZero eb) (bvNot (bvAllFalse ea)) (bvfEval (Div R a R b)))`;
//! - `B` ([`bool_goal`]) maps a Bool literal to itself, `Not` / `And` / `Or`
//!   (non-empty, right-nested) to `Bool.not` / `Bool.and` / `Bool.or`, a Bool
//!   `Ite` to `Bool.rec (fun _ => Bool) B(q) B(p) B(c)`, a bit-vector `Eq` to
//!   `bvBeq`, an `Eq` of two conditions to `Bool.not (Bool.xor B(p) B(q))`
//!   (exact Bool equality, by its truth table; not definitionally `decide`),
//!   `BvULt` / `BvULe` / `BvSLt` to `bvUlt` / `bvULe` / `bvSLtReal`.
//!   Anything else is refused;
//! - `BvExtract{x, w-1, k}`, `1 ≤ k < w ≤ 64`, is `BvF.Const (btail^k (bvfEval R x))`;
//! - `BvSignExt(x, k)`, `1 ≤ k ≤ 63`, `w + k ≤ 64`, is `BvF.Const (bvAppend v
//!   [bvLastBit v, …k times])`, `v = bvfEval R x`: the faithful sign-extension
//!   list `memory_reflection.rs` renders (`sign_extend_list`), the same term.
//!
//! The goal is built under `ReflectCtx::branching_goal`, with every step
//! builder off. The proving reflection (`ReflectCtx::branching`) builds the
//! same `bvf` (`branching_bvf_matches_the_goal`).
//!
//! # The steps (`ctx.branching_steps`)
//!
//! Each is a kernel term `bvfEval core = bvfEval core'` spliced on its own
//! counter ([`BRANCH_MAX_REWRITES`]):
//!
//! - ground selection: an `Ite` whose condition is a closed comparison of
//!   literals is replaced by its selected arm (`Eq.refl` on the condition,
//!   then `ite_true` / `ite_false`);
//! - the division guard: a faithful `BvUDiv` by a nonzero literal becomes
//!   `Div` (`Clean.BVC.divGuardBridge`, premise `Eq.refl`);
//! - `mul_add_self`: `x * c + x` is `x * (c + 1)`;
//! - `sub_zero`: `a - 0` is `a`;
//! - `zext_drop1_div2`: `ZeroExt(Extract{x, w-1, 1}, 1)` (AArch64 `lsr #1`) is
//!   `x / 2`;
//! - the shift-amount fold: the variable-free, non-literal amount of an
//!   arithmetic shift becomes its literal value (`Eq.refl`, the kernel
//!   computing the amount on whitelisted closed data; Rust only proposes the
//!   value). It changes no other operand, and skips, never fails, where it
//!   does not apply.
//!
//! # The proving view of a condition
//!
//! [`reflect_bool`] returns `B(c)`, a structured condition [`BExpr`] and a
//! kernel proof `B(c) = render κ`. [`reflect_value`] does the same for a
//! bit-vector term, keeping the `Ite` nodes visible as [`VExpr::Ite`]. The
//! bridges (machine `b.hi`, `tbz`, the signed `N == V` of `b.ge` / `b.lt`,
//! the spec's `x & 1 == 0`) are kernel theorem instances; everything else is
//! congruence or `Eq.refl`. A Bool equality has a proving view only through
//! the `N == V` bridge ([`flag_bridge`]); any other declines. Nothing
//! here decides anything: the route's kernel check of the finished term
//! against the independently built goal does.
//!
//! # Closed data (plan §2)
//!
//! A term the route has the kernel evaluate on closed data (a ground
//! condition, a premise closed by `Eq.refl`, a concrete comparison, a leaf
//! condition of the split) may mention only the heads of
//! [`CLOSED_WHITELIST`] ([`note_closed`]); anything else declines. An atom
//! must mention a leaf bit: a closed comparison that is not a literal one is
//! refused rather than abstracted.

use std::collections::HashSet;

use clean_kernel::expr::UsedConstants;
use clean_kernel::{BigNat, BinderInfo, Expr, ExprKind, Literal};
use trust_types::Formula;

use super::branch_theory::{self, const_bits, spine};
use super::kterm::{
    Fresh, bool_rec, bool_ty, btail, congr_arg, l1, lams, lb, nat, refl, succ, symm, to_nat, trans,
};
use super::{ReflectCtx, Reflected, add_comm, branch_split, kx, reflect_formula};

/// At most this many branch steps per reflection.
pub(crate) const BRANCH_MAX_REWRITES: usize = 32;

// ── the closed-data whitelist ────────────────────────────────────────────────

/// The only constants a closed term the route has the kernel evaluate may
/// mention, besides the opaque `BVC_LEAFBIT_*` bits: plan §2's list (with
/// `Clean.BVI.btail` for its `dropLow`), and the constructors and the
/// `bvfEval` that carry the data, and `BvF.And` and `bvLastBit` for the
/// shift-amount fold (an amount `sext(k) & (w-1)`). `bvMul`, `bvDiv`, `bvShl`,
/// `bvLShr`, `bvAShr`, `natToBvAux`, `Nat.div` / `Nat.mod` and every other
/// `BvF` constructor are off the list, so the kernel never evaluates them on
/// closed data for the route. `branch_split::tests::closed_data_is_whitelisted`
/// pins the list.
pub(crate) const CLOSED_WHITELIST: [&str; 36] = [
    // Bool
    "Bool",
    "Bool.true",
    "Bool.false",
    "Bool.not",
    "Bool.and",
    "Bool.or",
    "Bool.xor",
    "Bool.rec",
    // the data
    "List.cons",
    "List.nil",
    "Clean.BVC.bvfEval",
    "Clean.BVC.BvF.Const",
    "Clean.BVC.BvF.Leaf",
    "Clean.BVC.BvF.ExtractLow",
    "Clean.BVC.BvF.And",
    // comparisons and selection
    "Clean.BVC.bvIteVal",
    "Clean.BVC.bvBeq",
    "Clean.BVC.bvIsZero",
    "Clean.BVC.bvUlt",
    "Clean.BVC.carryOut",
    "Clean.BVC.bvULe",
    "Clean.BVC.bvSLtReal",
    "Clean.BVC.bvFlipMsb",
    "Clean.BVC.bvTakeLen",
    "Clean.BVC.bvZipAnd",
    // widening and the high extract
    "Clean.BVC.bvZeroExt",
    "Clean.BVC.bvAppend",
    "Clean.BVC.bvReplF",
    "Clean.BVC.bvLastBit",
    "Clean.BVI.btail",
    // premises only
    "Clean.BVC.bvLen",
    "Clean.BVC.bvToNat",
    "Nat.zero",
    "Nat.succ",
    "Nat.add",
    "Nat.mul",
];

/// Does a closed term use only [`CLOSED_WHITELIST`] heads, lists of at most
/// 64 elements and `Nat` literals below 2^64? Opaque leaf bits and the
/// split's atom variables (free variables, which a short-circuited
/// connective never reaches) are not data and are allowed.
pub(crate) fn closed_ok(e: &Expr) -> bool {
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(n, _) => {
                let s = n.to_string();
                if !(CLOSED_WHITELIST.contains(&s.as_str()) || s.starts_with("BVC_LEAFBIT_")) {
                    return false;
                }
            }
            ExprKind::Lit(Literal::Nat(BigNat::Small(_)))
            | ExprKind::BVar(_)
            | ExprKind::FVar(_) => {}
            ExprKind::Sort(_) => {}
            ExprKind::App(f, a) => {
                if head_is(e, "List.cons") && e.get_app_args().len() == 3 && spine(e).is_none() {
                    return false;
                }
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
thread_local! {
    /// Every closed term [`note_closed`] saw on this thread (the scan test).
    pub(crate) static CLOSED_SEEN: std::cell::RefCell<Vec<Expr>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// [`closed_ok`], recorded for the scan test: call it on every closed term
/// the route has the kernel evaluate, and decline when it is `false`.
pub(crate) fn note_closed(e: &Expr) -> bool {
    #[cfg(test)]
    CLOSED_SEEN.with(|seen| seen.borrow_mut().push(e.clone()));
    closed_ok(e)
}

/// Does `e` mention a leaf bit (an atom's defining property)?
fn has_leaf_bit(e: &Expr) -> bool {
    let mut used = HashSet::new();
    e.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
    used.iter().any(|n| n.to_string().starts_with("BVC_LEAF"))
}

/// Run `f` with every step builder off: a reflection whose steps would be
/// discarded (the goal condition `B(c)`), so they are neither built nor
/// counted against [`BRANCH_MAX_REWRITES`].
fn goal_only<T>(ctx: &mut ReflectCtx, f: impl FnOnce(&mut ReflectCtx) -> T) -> T {
    let branch = std::mem::replace(&mut ctx.branching_steps, false);
    let strength = std::mem::replace(&mut ctx.strength_steps, false);
    let out = f(ctx);
    ctx.branching_steps = branch;
    ctx.strength_steps = strength;
    out
}

impl ReflectCtx {
    /// Splice `step : bvfEval core = bvfEval new_core` into a node whose goal
    /// is `bvf`. Past [`BRANCH_MAX_REWRITES`] the step is dropped and
    /// `branch_cap_hit` set; the cores then fail to meet and the route
    /// declines with reason `cap`.
    fn splice_branch(
        &mut self,
        bvf: &Expr,
        step: Expr,
        new_core: Expr,
        core: &mut Expr,
        proof: &mut Expr,
    ) {
        if self.branch_rewrites >= BRANCH_MAX_REWRITES {
            self.branch_cap_hit = true;
            return;
        }
        *proof = kx::eq_trans_list(
            kx::evalf(bvf.clone()),
            kx::evalf(core.clone()),
            kx::evalf(new_core.clone()),
            proof.clone(),
            step,
        );
        *core = new_core;
        self.branch_rewrites += 1;
    }
}

// ── small helpers ────────────────────────────────────────────────────────────

fn head_is(e: &Expr, name: &str) -> bool {
    matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == name)
}

/// The arguments of `name a1 … an`, `None` for another head or arity.
fn args_of(e: &Expr, name: &str, arity: usize) -> Option<Vec<Expr>> {
    if !head_is(e, name) {
        return None;
    }
    let args = e.get_app_args();
    (args.len() == arity).then(|| args.iter().map(|a| (*a).clone()).collect())
}

fn lit(b: bool) -> Expr {
    if b { kx::btrue() } else { kx::bfalse() }
}

fn bor(x: Expr, y: Expr) -> Expr {
    branch_theory::bor(x, y)
}

/// `fun _ : Bool => Bool`, the motive of a Bool `Ite`.
fn bool_motive() -> Expr {
    Expr::lam(BinderInfo::Default, bool_ty(), bool_ty())
}

/// `Bool.rec.{1} (fun _ => Bool) q p c`: `p` when `c`, else `q`.
fn bool_ite(c: Expr, p: Expr, q: Expr) -> Expr {
    bool_rec(l1(), bool_motive(), q, p, c)
}

/// Congruence of an `n`-ary term `f`: `f lhs = f rhs` from `proofs[i] :
/// lhs[i] = rhs[i]`, one `congrArg` per argument.
fn cong(
    tys: &[Expr],
    res: &Expr,
    f: &dyn Fn(&[Expr]) -> Expr,
    lhs: &[Expr],
    rhs: &[Expr],
    proofs: &[Expr],
) -> Expr {
    let mut fr = Fresh::new();
    let start = f(lhs);
    let mut cur = lhs.to_vec();
    let mut acc: Option<Expr> = None;
    for i in 0..lhs.len() {
        let before = f(&cur);
        let (t_id, t) = fr.local();
        let mut args = cur.clone();
        args[i] = t;
        let lam = lams(vec![(t_id, tys[i].clone())], f(&args));
        let step = congr_arg(
            tys[i].clone(),
            res.clone(),
            lhs[i].clone(),
            rhs[i].clone(),
            lam,
            proofs[i].clone(),
        );
        cur[i] = rhs[i].clone();
        let after = f(&cur);
        acc = Some(match acc {
            None => step,
            Some(p) => trans(res.clone(), start.clone(), before, after, p, step),
        });
    }
    acc.unwrap_or_else(|| refl(res.clone(), start))
}

/// The value of `B` over the Formula's own reflections: the condition the
/// goal states.
pub(crate) fn bool_goal(c: &Formula, ctx: &mut ReflectCtx) -> Result<Expr, String> {
    let ev = |f: &Formula, ctx: &mut ReflectCtx| -> Result<Expr, String> {
        Ok(kx::evalf(reflect_formula(f, ctx)?.bvf))
    };
    match c {
        Formula::Bool(b) => Ok(lit(*b)),
        Formula::Not(x) => Ok(kx::bnot(bool_goal(x, ctx)?)),
        Formula::And(xs) | Formula::Or(xs) => {
            let join = if matches!(c, Formula::And(_)) { kx::band } else { bor };
            let (last, init) = xs.split_last().ok_or("branch: empty And/Or")?;
            let mut acc = bool_goal(last, ctx)?;
            let mut heads = Vec::with_capacity(init.len());
            for x in init {
                heads.push(bool_goal(x, ctx)?);
            }
            for h in heads.into_iter().rev() {
                acc = join(h, acc);
            }
            Ok(acc)
        }
        Formula::Ite(cc, p, q) => {
            let bc = bool_goal(cc, ctx)?;
            let bp = bool_goal(p, ctx)?;
            let bq = bool_goal(q, ctx)?;
            Ok(bool_ite(bc, bp, bq))
        }
        // An equality of two conditions: exact Bool equality, `not (xor p q)`.
        Formula::Eq(a, b) if branch_split::is_condition(a) => {
            Ok(kx::bnot(kx::bxor(bool_goal(a, ctx)?, bool_goal(b, ctx)?)))
        }
        Formula::Eq(a, b) => Ok(kx::bv_beq(ev(a, ctx)?, ev(b, ctx)?)),
        Formula::BvULt(a, b, _) => Ok(kx::bv_ult(ev(a, ctx)?, ev(b, ctx)?)),
        Formula::BvULe(a, b, _) => Ok(kx::bv_ule(ev(a, ctx)?, ev(b, ctx)?)),
        Formula::BvSLt(a, b, _) => Ok(kx::bv_slt_real(ev(a, ctx)?, ev(b, ctx)?)),
        other => Err(format!("branch: condition outside the fragment: {other:?}")),
    }
}

// ── the goal arms ────────────────────────────────────────────────────────────

/// The literal value of a closed comparison of bit-vector literals, as the
/// kernel computes it on the reflected terms; `None` for anything else.
fn closed_condition(c: &Formula) -> Option<bool> {
    let bits = |f: &Formula| match f {
        Formula::BitVec { value, width } if (1..=64).contains(width) => {
            Some((*width, (*value as u128) & (u128::MAX >> (128 - width))))
        }
        _ => None,
    };
    match c {
        Formula::Bool(b) => Some(*b),
        Formula::Not(x) => closed_condition(x).map(|b| !b),
        Formula::Eq(a, b) => {
            let (wa, va) = bits(a)?;
            let (wb, vb) = bits(b)?;
            (wa == wb).then_some(va == vb)
        }
        Formula::BvULt(a, b, _) | Formula::BvULe(a, b, _) => {
            let (wa, va) = bits(a)?;
            let (wb, vb) = bits(b)?;
            (wa == wb).then_some(if matches!(c, Formula::BvULt(..)) { va < vb } else { va <= vb })
        }
        _ => None,
    }
}

/// `R(Ite(c, a, e))`. Under `branching_steps` the core carries the arms'
/// cores (`ite_cong`), and a closed literal condition selects its arm.
pub(super) fn ite(
    c: &Formula,
    a: &Formula,
    e: &Formula,
    ctx: &mut ReflectCtx,
) -> Result<Reflected, String> {
    let b = goal_only(ctx, |ctx| bool_goal(c, ctx))?;
    let ra = reflect_formula(a, ctx)?;
    let re = reflect_formula(e, ctx)?;
    let (ea, ee) = (kx::evalf(ra.bvf.clone()), kx::evalf(re.bvf.clone()));
    let bvf = kx::const_(kx::bv_ite_val(b.clone(), ea.clone(), ee.clone()));
    if !ctx.branching_steps {
        return Ok(Reflected {
            bvf: bvf.clone(),
            core: bvf.clone(),
            proof: kx::eq_refl_list(kx::evalf(bvf)),
        });
    }
    let (ca, ce) = (kx::evalf(ra.core.clone()), kx::evalf(re.core.clone()));
    let Some(v) = closed_condition(c) else {
        // Congruence only: the condition stays as stated.
        let core = kx::const_(kx::bv_ite_val(b.clone(), ca.clone(), ce.clone()));
        let proof = branch_theory::ite_cong_inst(
            b.clone(),
            b.clone(),
            ea,
            ca,
            ee,
            ce,
            refl(bool_ty(), b),
            ra.proof,
            re.proof,
        );
        return Ok(Reflected { bvf, core, proof });
    };
    // Ground selection: `B(c) = lit` by computation, then the arm.
    if !note_closed(&b) {
        return Err("branch: a ground condition off the closed-data whitelist".into());
    }
    let mid = kx::bv_ite_val(lit(v), ca.clone(), ce.clone());
    let to_lit = branch_theory::ite_cong_inst(
        b.clone(),
        lit(v),
        ea,
        ca.clone(),
        ee,
        ce.clone(),
        refl(bool_ty(), lit(v)),
        ra.proof,
        re.proof,
    );
    let (sel, sel_eval) = if v { (ra.core, ca.clone()) } else { (re.core, ce.clone()) };
    let pick = branch_theory::ite_select(v, ca, ce);
    let step = trans(lb(), kx::evalf(bvf.clone()), mid, sel_eval, to_lit, pick);
    let mut core = bvf.clone();
    let mut proof = kx::eq_refl_list(kx::evalf(bvf.clone()));
    ctx.splice_branch(&bvf, step, sel, &mut core, &mut proof);
    Ok(Reflected { bvf, core, proof })
}

/// The faithful `R(BvUDiv(a, b))`. Under `branching_steps`, a divisor whose
/// goal reflection is a nonzero literal reduces to `Div` through
/// `divGuardBridge`, whose premise `bvIsZero eb = false` is `Eq.refl`.
pub(super) fn udiv(l: &Formula, r: &Formula, ctx: &mut ReflectCtx) -> Result<Reflected, String> {
    let ra = reflect_formula(l, ctx)?;
    let rb = reflect_formula(r, ctx)?;
    let (ea, eb) = (kx::evalf(ra.bvf.clone()), kx::evalf(rb.bvf.clone()));
    let div_bvf = kx::div(ra.bvf.clone(), rb.bvf.clone());
    let zero_guard = kx::bv_is_zero(eb.clone());
    let all_ones = kx::bv_not(kx::all_false(ea));
    let bvf = kx::const_(kx::bv_ite_val(zero_guard, all_ones.clone(), kx::evalf(div_bvf.clone())));
    let mut core = bvf.clone();
    let mut proof = kx::eq_refl_list(kx::evalf(bvf.clone()));
    if ctx.branching_steps
        && const_bits(&rb.bvf).is_some_and(|(_, v)| v != 0)
        && note_closed(&kx::bv_is_zero(eb.clone()))
    {
        let guard = kx::div_guard_bridge(
            eb,
            all_ones,
            kx::evalf(div_bvf.clone()),
            refl(bool_ty(), kx::bfalse()),
        );
        let div_core = kx::div(ra.core.clone(), rb.core.clone());
        let congr = kx::div_cong(ra.bvf, ra.core, rb.bvf, rb.core, ra.proof, rb.proof);
        let step = kx::eq_trans_list(
            kx::evalf(bvf.clone()),
            kx::evalf(div_bvf),
            kx::evalf(div_core.clone()),
            guard,
            congr,
        );
        ctx.splice_branch(&bvf, step, div_core, &mut core, &mut proof);
    }
    Ok(Reflected { bvf, core, proof })
}

/// `R(BvExtract{x, w-1, k})`, `1 ≤ k < w ≤ 64`, `w` the width of `x`:
/// `BvF.Const (btail^k (bvfEval R x))`, the bits above the `k` low ones.
/// Under `branching_steps` the core carries `x`'s core (congruence).
pub(super) fn high_extract(
    inner: &Formula,
    high: u32,
    low: u32,
    ctx: &mut ReflectCtx,
) -> Result<Reflected, String> {
    let w = super::memory_reflection::width(inner).ok_or("branch: extract of an unsized term")?;
    if !(1..w).contains(&low) || high.checked_add(1) != Some(w) || w > 64 {
        return Err("branch: extract outside the high-extract fragment".into());
    }
    let ri = reflect_formula(inner, ctx)?;
    let drop = |l: Expr| (0..low).fold(l, |acc, _| btail(acc));
    let bvf = kx::const_(drop(kx::evalf(ri.bvf.clone())));
    if !ctx.branching_steps || ri.core == ri.bvf {
        return Ok(Reflected {
            bvf: bvf.clone(),
            core: bvf.clone(),
            proof: kx::eq_refl_list(kx::evalf(bvf)),
        });
    }
    let core = kx::const_(drop(kx::evalf(ri.core.clone())));
    let mut fr = Fresh::new();
    let (t_id, t) = fr.local();
    let f = lams(vec![(t_id, lb())], drop(t));
    let proof = congr_arg(lb(), lb(), kx::evalf(ri.bvf), kx::evalf(ri.core), f, ri.proof);
    Ok(Reflected { bvf, core, proof })
}

/// The faithful sign extension of the LSB-first list `value` by `k` bits:
/// `bvAppend value [bvLastBit value, …k times]`, the term
/// `memory_reflection.rs` `sign_extend_list` builds (its input bits kept,
/// then `k` copies of its own sign bit).
fn sign_extend_list(value: Expr, k: u32) -> Expr {
    let sign = kx::last_bit(value.clone());
    let high = (0..k).fold(kx::nil(), |acc, _| kx::cons(sign.clone(), acc));
    Expr::apps(Expr::const_str("Clean.BVC.bvAppend"), [value, high])
}

/// `R(BvSignExt(x, k))`, `1 ≤ k ≤ 63`, `w + k ≤ 64`, `w` the width of `x`:
/// `BvF.Const (sign_extend_list (bvfEval R x) k)`. Under `branching_steps`
/// the core carries `x`'s core (congruence).
pub(super) fn sign_ext(x: &Formula, k: u32, ctx: &mut ReflectCtx) -> Result<Reflected, String> {
    let w =
        super::memory_reflection::width(x).ok_or("branch: sign extension of an unsized term")?;
    if !(1..=63).contains(&k) || w == 0 || w + k > 64 {
        return Err("branch: sign extension outside the fragment".into());
    }
    let ri = reflect_formula(x, ctx)?;
    let bvf = kx::const_(sign_extend_list(kx::evalf(ri.bvf.clone()), k));
    if !ctx.branching_steps || ri.core == ri.bvf {
        return Ok(Reflected {
            bvf: bvf.clone(),
            core: bvf.clone(),
            proof: kx::eq_refl_list(kx::evalf(bvf)),
        });
    }
    let core = kx::const_(sign_extend_list(kx::evalf(ri.core.clone()), k));
    let mut fr = Fresh::new();
    let (t_id, t) = fr.local();
    let f = lams(vec![(t_id, lb())], sign_extend_list(t, k));
    let proof = congr_arg(lb(), lb(), kx::evalf(ri.bvf), kx::evalf(ri.core), f, ri.proof);
    Ok(Reflected { bvf, core, proof })
}

// ── the post-node steps ──────────────────────────────────────────────────────

/// The `mul_add_self`, `sub_zero`, `zext_drop1_div2` and shift-amount
/// steps, after `f` is reflected.
pub(super) fn post_step(f: &Formula, out: Reflected, ctx: &mut ReflectCtx) -> Reflected {
    let step = match f {
        Formula::BvAdd(..) => mul_add_self_step(&out.core),
        Formula::BvSub(..) => sub_zero_step(&out.core),
        Formula::BvZeroExt(..) => zext_drop1_step(&out.core),
        Formula::BvAShr(_, r, w) => branch_split::closed_value(r)
            .filter(|&(_, wr)| wr == *w)
            .and_then(|(v, _)| ashr_amount_fold(&out.core, v, *w)),
        _ => None,
    };
    let Some((step, new_core)) = step else { return out };
    let Reflected { bvf, mut core, mut proof } = out;
    ctx.splice_branch(&bvf, step, new_core, &mut core, &mut proof);
    Reflected { bvf, core, proof }
}

/// `Add(Mul(x, Const c1), x)` → `Mul(x, Const (c1 + 1))`, by `mul_add_self`.
fn mul_add_self_step(core: &Expr) -> Option<(Expr, Expr)> {
    let [m, x2] = <[Expr; 2]>::try_from(args_of(core, "Clean.BVC.BvF.Add", 2)?).ok()?;
    let [x, c1] = <[Expr; 2]>::try_from(args_of(&m, "Clean.BVC.BvF.Mul", 2)?).ok()?;
    if x != x2 {
        return None;
    }
    let (w, v1) = const_bits(&c1)?;
    let (hx, wx) = add_comm::core_len(&x)?;
    if wx != w || w == 0 {
        return None;
    }
    let v2 = v1.checked_add(1)?;
    if w < 128 && v2 >> w != 0 {
        return None;
    }
    let c1l = args_of(&c1, "Clean.BVC.BvF.Const", 1)?.pop()?;
    let c2l = kx::bits(i128::try_from(v2).ok()?, w);
    // The premises the kernel closes by computation: `L c1`, `L c2`, `V c2`
    // and `succ (V c1)`.
    let premises = [
        kx::bv_len(c1l.clone()),
        kx::bv_len(c2l.clone()),
        to_nat(c2l.clone()),
        succ(to_nat(c1l.clone())),
    ];
    if !premises.iter().all(note_closed) {
        return None;
    }
    let ex = kx::evalf(x.clone());
    let lx = kx::bv_len(ex.clone());
    let nw = kx::nat_lit(w);
    // `L c = L x`: `L c` computes to `w`, and `hx : L x = w`.
    let len_eq = |c: &Expr| {
        trans(
            nat(),
            kx::bv_len(c.clone()),
            nw.clone(),
            lx.clone(),
            refl(nat(), nw.clone()),
            symm(nat(), lx.clone(), nw.clone(), hx.clone()),
        )
    };
    let hv = refl(nat(), to_nat(c2l.clone()));
    let step = branch_theory::mul_add_self_inst(
        ex,
        c1l.clone(),
        c2l.clone(),
        kx::nat_lit(w - 1),
        hx.clone(),
        len_eq(&c1l),
        len_eq(&c2l),
        hv,
    );
    Some((step, kx::mul(x, kx::const_(c2l))))
}

/// `Sub(a, Const 0)` → `a`, by `sub_zero`, when `a` has the zero's width.
fn sub_zero_step(core: &Expr) -> Option<(Expr, Expr)> {
    let [a, z] = <[Expr; 2]>::try_from(args_of(core, "Clean.BVC.BvF.Sub", 2)?).ok()?;
    let (w, v) = const_bits(&z)?;
    if v != 0 || core_width(&a)? != w {
        return None;
    }
    Some((branch_theory::sub_zero_inst(kx::evalf(a.clone())), a))
}

/// `ZeroExt(Const (btail (bvfEval (Leaf (h :: t)))), 1)` → `Div(Leaf (h :: t),
/// Const 2)`, by `zext_drop1_div2` (AArch64 `lsr #1` against `x / 2`). The
/// premise `V 2 = 2` is `Eq.refl` on a literal.
fn zext_drop1_step(core: &Expr) -> Option<(Expr, Expr)> {
    let [inner, k] = <[Expr; 2]>::try_from(args_of(core, "Clean.BVC.BvF.ZeroExt", 2)?).ok()?;
    if k != kx::nat_lit(1) {
        return None;
    }
    let dropped = args_of(&inner, "Clean.BVC.BvF.Const", 1)?.pop()?;
    let ev = args_of(&dropped, "Clean.BVI.btail", 1)?.pop()?;
    let x = args_of(&ev, "Clean.BVC.bvfEval", 1)?.pop()?;
    let list = args_of(&x, "Clean.BVC.BvF.Leaf", 1)?.pop()?;
    let w = u32::try_from(spine(&list)?.len()).ok()?;
    let [_, h, t] = <[Expr; 3]>::try_from(args_of(&list, "List.cons", 3)?).ok()?;
    if w < 2 {
        return None;
    }
    let two = kx::bits(2, w);
    if !note_closed(&to_nat(two.clone())) {
        return None;
    }
    let hv = refl(nat(), super::kterm::nlit(2));
    let step = branch_theory::zext_drop1_div2_inst(h, t, two.clone(), hv);
    Some((step, kx::div(x, kx::const_(two))))
}

/// The shift-amount fold: `AShr(x, amt)` → `AShr(x, Const v)` for a
/// variable-free amount of width `w` that is not a literal already, `v` its
/// value as Rust computes it (`branch_split::closed_value`, SMT-LIB
/// semantics). The step is
/// `bvf_ashr_cong` with `Eq.refl` for `x` and `Eq.refl (bvfEval (Const v))`
/// for the amount, which the kernel accepts only by computing `bvfEval amt`
/// to `v`'s bits, on data [`note_closed`] admits. `None` (skip, never `Err`)
/// for any other core, a literal amount, a value that does not fit `w` bits,
/// or an amount off the whitelist.
pub(crate) fn ashr_amount_fold(core: &Expr, v: u128, w: u32) -> Option<(Expr, Expr)> {
    let [x, amt] = <[Expr; 2]>::try_from(args_of(core, "Clean.BVC.BvF.AShr", 2)?).ok()?;
    if const_bits(&amt).is_some() || !(1..=64).contains(&w) || v >> w != 0 {
        return None;
    }
    if !note_closed(&kx::evalf(amt.clone())) {
        return None;
    }
    let lit = kx::const_(kx::bits(i128::try_from(v).ok()?, w));
    let hx = kx::eq_refl_list(kx::evalf(x.clone()));
    let hv = kx::eq_refl_list(kx::evalf(lit.clone()));
    let step = kx::ashr_cong(x.clone(), x.clone(), amt, lit.clone(), hx, hv);
    Some((step, kx::ashr(x, lit)))
}

/// The width of a core whose operands agree on one, read off its concrete
/// leaves and literals. A filter only: `sub_zero`'s instance is well typed
/// only when the kernel computes `bvAllFalse (bvfEval a)` to the literal.
fn core_width(core: &Expr) -> Option<u32> {
    if let Some(elems) = concrete_elems(core) {
        return u32::try_from(elems.len()).ok();
    }
    for op in [
        "Clean.BVC.BvF.And",
        "Clean.BVC.BvF.Or",
        "Clean.BVC.BvF.Xor",
        "Clean.BVC.BvF.Add",
        "Clean.BVC.BvF.Sub",
    ] {
        if let Some([a, b]) = args_of(core, op, 2).and_then(|v| <[Expr; 2]>::try_from(v).ok()) {
            let w = core_width(&a)?;
            return (core_width(&b)? == w).then_some(w);
        }
    }
    // `bvMul` takes its length from the right operand, `bvDiv` from the left.
    if let Some([_, b]) =
        args_of(core, "Clean.BVC.BvF.Mul", 2).and_then(|v| <[Expr; 2]>::try_from(v).ok())
    {
        return core_width(&b);
    }
    if let Some([a, _]) =
        args_of(core, "Clean.BVC.BvF.Div", 2).and_then(|v| <[Expr; 2]>::try_from(v).ok())
    {
        return core_width(&a);
    }
    add_comm::core_len(core).map(|(_, w)| w)
}

// ── the proving view ─────────────────────────────────────────────────────────

/// A condition the split can evaluate once its atoms are fixed.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum BExpr {
    Lit(bool),
    /// A maximal Bool subterm over a leaf bit, abstracted by the split.
    Atom(Expr),
    Not(Box<BExpr>),
    And(Box<BExpr>, Box<BExpr>),
    Or(Box<BExpr>, Box<BExpr>),
    /// `Bool.rec (fun _ => Bool) else then cond`.
    Ite(Box<BExpr>, Box<BExpr>, Box<BExpr>),
    Beq(Box<VExpr>, Box<VExpr>),
    Ult(Box<VExpr>, Box<VExpr>),
    Ule(Box<VExpr>, Box<VExpr>),
}

/// A bit-vector value with its `Ite` structure visible.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum VExpr {
    Ite(Box<BExpr>, Box<VExpr>, Box<VExpr>),
    /// `bvfEval core`.
    Core(Expr),
    /// A concrete list.
    Bits(Vec<BExpr>),
}

/// How [`render_b`] writes an atom.
pub(crate) type AtomMap<'a> = &'a dyn Fn(&Expr) -> Option<Expr>;

pub(crate) fn render_b(b: &BExpr, map: AtomMap<'_>) -> Expr {
    match b {
        BExpr::Lit(v) => lit(*v),
        BExpr::Atom(e) => map(e).unwrap_or_else(|| e.clone()),
        BExpr::Not(x) => kx::bnot(render_b(x, map)),
        BExpr::And(x, y) => kx::band(render_b(x, map), render_b(y, map)),
        BExpr::Or(x, y) => bor(render_b(x, map), render_b(y, map)),
        BExpr::Ite(c, p, q) => bool_ite(render_b(c, map), render_b(p, map), render_b(q, map)),
        BExpr::Beq(x, y) => kx::bv_beq(render_v(x, map), render_v(y, map)),
        BExpr::Ult(x, y) => kx::bv_ult(render_v(x, map), render_v(y, map)),
        BExpr::Ule(x, y) => kx::bv_ule(render_v(x, map), render_v(y, map)),
    }
}

pub(crate) fn render_v(v: &VExpr, map: AtomMap<'_>) -> Expr {
    match v {
        VExpr::Ite(c, a, e) => kx::bv_ite_val(render_b(c, map), render_v(a, map), render_v(e, map)),
        VExpr::Core(core) => kx::evalf(core.clone()),
        VExpr::Bits(bs) => {
            bs.iter().rev().fold(kx::nil(), |acc, b| kx::cons(render_b(b, map), acc))
        }
    }
}

fn no_atoms(_: &Expr) -> Option<Expr> {
    None
}

/// The literal bits of a `Const` core, least significant first.
pub(crate) fn const_list(core: &Expr) -> Option<Vec<bool>> {
    let list = args_of(core, "Clean.BVC.BvF.Const", 1)?.pop()?;
    spine(&list)?.iter().map(branch_theory::bool_lit).collect()
}

/// How the split reads an atom.
pub(crate) type AtomVal<'a> = &'a dyn Fn(&Expr) -> Option<bool>;

/// The value the kernel computes for `b` once the atoms `val` fixes are
/// literals: `Bool.not` / `and` / `or` / `Bool.rec` reduce on their first
/// (major) argument only, as their definitions do. `None` when it does not
/// reduce to a literal.
pub(crate) fn eval_b(b: &BExpr, val: AtomVal<'_>) -> Option<bool> {
    match b {
        BExpr::Lit(v) => Some(*v),
        BExpr::Atom(e) => val(e),
        BExpr::Not(x) => eval_b(x, val).map(|v| !v),
        BExpr::And(x, y) => match eval_b(x, val)? {
            false => Some(false),
            true => eval_b(y, val),
        },
        BExpr::Or(x, y) => match eval_b(x, val)? {
            true => Some(true),
            false => eval_b(y, val),
        },
        BExpr::Ite(c, p, q) => {
            if eval_b(c, val)? {
                eval_b(p, val)
            } else {
                eval_b(q, val)
            }
        }
        BExpr::Beq(x, y) => Some(beq(&eval_v(x, val)?, &eval_v(y, val)?)),
        BExpr::Ult(x, y) | BExpr::Ule(x, y) => {
            let (a, c) = (eval_v(x, val)?, eval_v(y, val)?);
            if a.len() != c.len() || a.len() > 64 {
                return None;
            }
            let num =
                |bits: &[bool]| bits.iter().rev().fold(0u128, |n, &b| (n << 1) | u128::from(b));
            let (na, nc) = (num(&a), num(&c));
            Some(if matches!(b, BExpr::Ult(..)) { na < nc } else { na <= nc })
        }
    }
}

/// `bvBeq` as `Clean.BVC` defines it: recursion on the first list; a second
/// list that runs out first compares equal (the length-blind reading).
fn beq(xs: &[bool], ys: &[bool]) -> bool {
    match (xs.split_first(), ys.split_first()) {
        (None, _) | (Some(_), None) => true,
        (Some((h, t)), Some((wh, wt))) => h == wh && beq(t, wt),
    }
}

pub(crate) fn eval_v(v: &VExpr, val: AtomVal<'_>) -> Option<Vec<bool>> {
    match v {
        VExpr::Ite(c, a, e) => {
            if eval_b(c, val)? {
                eval_v(a, val)
            } else {
                eval_v(e, val)
            }
        }
        VExpr::Core(core) => const_list(core),
        VExpr::Bits(bs) => bs.iter().map(|b| eval_b(b, val)).collect(),
    }
}

/// Every atom of `b`, in rendering order.
pub(crate) fn atoms_b(b: &BExpr, out: &mut Vec<Expr>) {
    match b {
        BExpr::Lit(_) => {}
        BExpr::Atom(e) => out.push(e.clone()),
        BExpr::Not(x) => atoms_b(x, out),
        BExpr::And(x, y) | BExpr::Or(x, y) => {
            atoms_b(x, out);
            atoms_b(y, out);
        }
        BExpr::Ite(c, p, q) => {
            atoms_b(c, out);
            atoms_b(p, out);
            atoms_b(q, out);
        }
        BExpr::Beq(x, y) | BExpr::Ult(x, y) | BExpr::Ule(x, y) => {
            atoms_v(x, out);
            atoms_v(y, out);
        }
    }
}

pub(crate) fn atoms_v(v: &VExpr, out: &mut Vec<Expr>) {
    match v {
        VExpr::Ite(c, a, e) => {
            atoms_b(c, out);
            atoms_v(a, out);
            atoms_v(e, out);
        }
        VExpr::Core(_) => {}
        VExpr::Bits(bs) => bs.iter().for_each(|b| atoms_b(b, out)),
    }
}

/// Is every `Core` in `v` a literal `Const` (the value is closed but for
/// atoms)?
fn closed_but_atoms(v: &VExpr) -> bool {
    match v {
        VExpr::Ite(_, a, e) => closed_but_atoms(a) && closed_but_atoms(e),
        VExpr::Core(core) => const_list(core).is_some(),
        VExpr::Bits(_) => true,
    }
}

/// `(bvf, V, p : bvfEval bvf = render V)` for a bit-vector term.
pub(crate) fn reflect_value(
    f: &Formula,
    ctx: &mut ReflectCtx,
) -> Result<(Expr, VExpr, Expr), String> {
    if let Formula::Ite(c, a, e) = f {
        let (bc, kc, pc) = reflect_bool(c, ctx)?;
        let (abvf, va, pa) = reflect_value(a, ctx)?;
        let (ebvf, ve, pe) = reflect_value(e, ctx)?;
        let (ea, ee) = (kx::evalf(abvf), kx::evalf(ebvf));
        let bvf = kx::const_(kx::bv_ite_val(bc.clone(), ea.clone(), ee.clone()));
        let proof = branch_theory::ite_cong_inst(
            bc,
            render_b(&kc, &no_atoms),
            ea,
            render_v(&va, &no_atoms),
            ee,
            render_v(&ve, &no_atoms),
            pc,
            pa,
            pe,
        );
        return Ok((bvf, VExpr::Ite(Box::new(kc), Box::new(va), Box::new(ve)), proof));
    }
    let r = reflect_formula(f, ctx)?;
    Ok((r.bvf, VExpr::Core(r.core), r.proof))
}

/// The bit-level elements `bvfEval core` computes to, for a `Leaf` / `Const`
/// over a concrete list and a low extract of one by a literal tag.
fn concrete_elems(core: &Expr) -> Option<Vec<Expr>> {
    if let Some(mut a) = args_of(core, "Clean.BVC.BvF.Leaf", 1) {
        return spine(&a.pop()?);
    }
    if let Some(mut a) = args_of(core, "Clean.BVC.BvF.Const", 1) {
        return spine(&a.pop()?);
    }
    let [inner, tag] = <[Expr; 2]>::try_from(args_of(core, "Clean.BVC.BvF.ExtractLow", 2)?).ok()?;
    let k = const_list(&tag)?.len();
    let elems = concrete_elems(&inner)?;
    (k <= elems.len()).then(|| elems[..k].to_vec())
}

/// A concrete element as a condition: a literal, or a leaf bit as an atom.
fn elem_b(e: &Expr) -> BExpr {
    match branch_theory::bool_lit(e) {
        Some(v) => BExpr::Lit(v),
        None => BExpr::Atom(e.clone()),
    }
}

/// At most this many leaf bits of a concrete comparison become atoms.
const MAX_BIT_ATOMS: usize = 2;

/// `(κ, p : bvBeq (render va) (render vb) = render κ)`: the comparison bridges.
fn beq_bridge(va: VExpr, vb: VExpr) -> Result<(BExpr, Expr), String> {
    let stated = kx::bv_beq(render_v(&va, &no_atoms), render_v(&vb, &no_atoms));
    if let (VExpr::Core(ca), VExpr::Core(cb)) = (&va, &vb) {
        // `tbz`: a short concrete list of leaf bits against a literal. The
        // kernel computes both `bvfEval`s to the cons lists (`Eq.refl`).
        if let (Some(xa), Some(xb)) = (concrete_elems(ca), concrete_elems(cb)) {
            let bits = |xs: &[Expr]| xs.iter().map(elem_b).collect::<Vec<_>>();
            let (ba, bb) = (bits(&xa), bits(&xb));
            let mut atoms = Vec::new();
            ba.iter().chain(&bb).for_each(|b| atoms_b(b, &mut atoms));
            let mut distinct: Vec<Expr> = Vec::new();
            for a in atoms {
                if !distinct.contains(&a) {
                    distinct.push(a);
                }
            }
            let atoms = distinct;
            if atoms.len() <= MAX_BIT_ATOMS && note_closed(&stated) {
                let k = BExpr::Beq(Box::new(VExpr::Bits(ba)), Box::new(VExpr::Bits(bb)));
                return Ok((k.clone(), refl(bool_ty(), stated)));
            }
        }
        // The spec's `x & 1 == 0`: `bvBeq (bvZipAnd (h::t) (true :: AF t))
        // (false :: AF t) = not h` (`beq_and_lowbit`), `h` the low leaf bit.
        if let Some([leaf, one]) =
            args_of(ca, "Clean.BVC.BvF.And", 2).and_then(|a| <[Expr; 2]>::try_from(a).ok())
            && let (Some(one), Some(zero)) = (const_list(&one), const_list(cb))
            && let Some(mut l) = args_of(&leaf, "Clean.BVC.BvF.Leaf", 1)
            && let Some(list) = l.pop()
            && let Some(elems) = spine(&list)
            && !elems.is_empty()
            && one.len() == elems.len()
            && zero.len() == elems.len()
            && one[0]
            && one[1..].iter().all(|b| !b)
            && zero.iter().all(|b| !b)
            && let Some([_, h, t]) =
                args_of(&list, "List.cons", 3).and_then(|a| <[Expr; 3]>::try_from(a).ok())
        {
            let k = BExpr::Not(Box::new(BExpr::Atom(h.clone())));
            return Ok((k, branch_theory::beq_and_lowbit_inst(h, t)));
        }
    }
    if closed_but_atoms(&va) && closed_but_atoms(&vb) {
        return Ok((BExpr::Beq(Box::new(va), Box::new(vb)), refl(bool_ty(), stated)));
    }
    if matches!((&va, &vb), (VExpr::Core(_), VExpr::Core(_))) {
        return Ok((atom(stated.clone())?, refl(bool_ty(), stated)));
    }
    Err("branch: a comparison mixes a branching value with a symbolic one".into())
}

/// `stated` as an atom: it must mention a leaf bit. A closed comparison that
/// is not a literal one (`Eq(BvUDiv(8, 2), 4)`) is refused, not abstracted.
fn atom(stated: Expr) -> Result<BExpr, String> {
    if has_leaf_bit(&stated) {
        Ok(BExpr::Atom(stated))
    } else {
        Err("branch: a closed comparison off the closed-data whitelist".into())
    }
}

/// `(B(c), κ, p : B(c) = render κ)`.
pub(crate) fn reflect_bool(
    c: &Formula,
    ctx: &mut ReflectCtx,
) -> Result<(Expr, BExpr, Expr), String> {
    let bool_ = bool_ty();
    match c {
        Formula::Bool(b) => Ok((lit(*b), BExpr::Lit(*b), refl(bool_, lit(*b)))),
        Formula::Not(x) => {
            let (bx, kx_, px) = reflect_bool(x, ctx)?;
            let rx = render_b(&kx_, &no_atoms);
            let p =
                congr_arg(bool_.clone(), bool_, bx.clone(), rx, Expr::const_str("Bool.not"), px);
            Ok((kx::bnot(bx), BExpr::Not(Box::new(kx_)), p))
        }
        Formula::And(xs) if hi_shape(xs).is_some() => {
            let (a, b) = hi_shape(xs).ok_or("branch: hi shape")?;
            hi_bridge(c, a, b, ctx)
        }
        Formula::And(xs) | Formula::Or(xs) => {
            let and = matches!(c, Formula::And(_));
            let (last, init) = xs.split_last().ok_or("branch: empty And/Or")?;
            let mut acc = reflect_bool(last, ctx)?;
            let mut heads = Vec::with_capacity(init.len());
            for x in init {
                heads.push(reflect_bool(x, ctx)?);
            }
            let join = |x: Expr, y: Expr| if and { kx::band(x, y) } else { bor(x, y) };
            for (bh, kh, ph) in heads.into_iter().rev() {
                let (ba, ka, pa) = acc;
                let (rh, ra) = (render_b(&kh, &no_atoms), render_b(&ka, &no_atoms));
                let f = |v: &[Expr]| join(v[0].clone(), v[1].clone());
                let p = cong(
                    &[bool_ty(), bool_ty()],
                    &bool_ty(),
                    &f,
                    &[bh.clone(), ba.clone()],
                    &[rh, ra],
                    &[ph, pa],
                );
                let k = if and {
                    BExpr::And(Box::new(kh), Box::new(ka))
                } else {
                    BExpr::Or(Box::new(kh), Box::new(ka))
                };
                acc = (join(bh, ba), k, p);
            }
            Ok(acc)
        }
        Formula::Ite(cc, p, q) => {
            let (bc, kc, pc) = reflect_bool(cc, ctx)?;
            let (bp, kp, pp) = reflect_bool(p, ctx)?;
            let (bq, kq, pq) = reflect_bool(q, ctx)?;
            let rendered =
                [render_b(&kc, &no_atoms), render_b(&kp, &no_atoms), render_b(&kq, &no_atoms)];
            let f = |v: &[Expr]| bool_ite(v[0].clone(), v[1].clone(), v[2].clone());
            let proof = cong(
                &[bool_ty(), bool_ty(), bool_ty()],
                &bool_ty(),
                &f,
                &[bc.clone(), bp.clone(), bq.clone()],
                &rendered,
                &[pc, pp, pq],
            );
            Ok((bool_ite(bc, bp, bq), BExpr::Ite(Box::new(kc), Box::new(kp), Box::new(kq)), proof))
        }
        // An equality of two conditions has a proving view only through the
        // signed flag bridge; any other declines.
        Formula::Eq(a, b) if branch_split::is_condition(a) => match flag_shape(a, b) {
            Some((x, y, d, w)) => flag_bridge(c, x, y, d, w, ctx),
            None => Err("branch: a Bool equality outside the flag bridge".into()),
        },
        Formula::Eq(a, b) => compare(a, b, ctx, Cmp::Eq),
        Formula::BvULt(a, b, _) => compare(a, b, ctx, Cmp::Ult),
        Formula::BvULe(a, b, _) => compare(a, b, ctx, Cmp::Ule),
        Formula::BvSLt(a, b, _) => compare(a, b, ctx, Cmp::Slt),
        other => Err(format!("branch: condition outside the fragment: {other:?}")),
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Cmp {
    Eq,
    Ult,
    Ule,
    Slt,
}

fn compare(
    a: &Formula,
    b: &Formula,
    ctx: &mut ReflectCtx,
    op: Cmp,
) -> Result<(Expr, BExpr, Expr), String> {
    let head = |x: Expr, y: Expr| match op {
        Cmp::Eq => kx::bv_beq(x, y),
        Cmp::Ult => kx::bv_ult(x, y),
        Cmp::Ule => kx::bv_ule(x, y),
        Cmp::Slt => kx::bv_slt_real(x, y),
    };
    let (abvf, va, pa) = reflect_value(a, ctx)?;
    let (bbvf, vb, pb) = reflect_value(b, ctx)?;
    let (ea, eb) = (kx::evalf(abvf), kx::evalf(bbvf));
    let (ra, rb) = (render_v(&va, &no_atoms), render_v(&vb, &no_atoms));
    let f = |v: &[Expr]| head(v[0].clone(), v[1].clone());
    let step1 = cong(
        &[lb(), lb()],
        &bool_ty(),
        &f,
        &[ea.clone(), eb.clone()],
        &[ra.clone(), rb.clone()],
        &[pa, pb],
    );
    let goal = head(ea, eb);
    let stated = head(ra.clone(), rb.clone());
    let (k, step2) = match op {
        Cmp::Eq => beq_bridge(va, vb)?,
        _ if closed_but_atoms(&va) && closed_but_atoms(&vb) && op != Cmp::Slt => {
            let k = if op == Cmp::Ult {
                BExpr::Ult(Box::new(va), Box::new(vb))
            } else {
                BExpr::Ule(Box::new(va), Box::new(vb))
            };
            (k, refl(bool_ty(), stated.clone()))
        }
        _ if matches!((&va, &vb), (VExpr::Core(_), VExpr::Core(_))) => {
            (atom(stated.clone())?, refl(bool_ty(), stated.clone()))
        }
        _ => return Err("branch: an ordered comparison of branching values".into()),
    };
    let rk = render_b(&k, &no_atoms);
    let proof = trans(bool_ty(), goal.clone(), stated, rk, step1, step2);
    Ok((goal, k, proof))
}

/// `And[Not(BvULt(a, b)), Not(Eq(BvSub(a, b), 0))]`, AArch64 `b.hi` after
/// `cmp a, b`: the operands `(a, b)`.
fn hi_shape(xs: &[Formula]) -> Option<(&Formula, &Formula)> {
    let [Formula::Not(lt), Formula::Not(ne)] = xs else { return None };
    let Formula::BvULt(a, b, _) = &**lt else { return None };
    let Formula::Eq(d, z) = &**ne else { return None };
    let Formula::BvSub(a2, b2, _) = &**d else { return None };
    let Formula::BitVec { value: 0, .. } = &**z else { return None };
    (a == a2 && b == b2).then_some((&**a, &**b))
}

/// `b.hi` is `b <u a`: congruence to the cores, then `hi_ult` with a length
/// premise from `core_len`.
fn hi_bridge(
    c: &Formula,
    a: &Formula,
    b: &Formula,
    ctx: &mut ReflectCtx,
) -> Result<(Expr, BExpr, Expr), String> {
    let Formula::And(xs) = c else { return Err("branch: hi shape".into()) };
    let goal = goal_only(ctx, |ctx| bool_goal(c, ctx))?;
    let ra = reflect_formula(a, ctx)?;
    let rb = reflect_formula(b, ctx)?;
    let Some(Formula::Not(ne)) = xs.get(1) else { return Err("branch: hi shape".into()) };
    let Formula::Eq(d, z) = &**ne else { return Err("branch: hi shape".into()) };
    let rd = reflect_formula(d, ctx)?;
    let rz = reflect_formula(z, ctx)?;
    if rd.core != kx::sub(ra.core.clone(), rb.core.clone()) {
        return Err("branch: hi difference is not a - b".into());
    }
    let (la, wa) = add_comm::core_len(&ra.core).ok_or("branch: hi operand length")?;
    let (lb_, wb) = add_comm::core_len(&rb.core).ok_or("branch: hi operand length")?;
    if wa != wb || const_bits(&rz.core) != Some((wa, 0)) {
        return Err("branch: hi widths".into());
    }
    let f = |v: &[Expr]| {
        kx::band(
            kx::bnot(kx::bv_ult(v[0].clone(), v[1].clone())),
            kx::bnot(kx::bv_beq(v[2].clone(), v[3].clone())),
        )
    };
    let ev = |e: &Expr| kx::evalf(e.clone());
    let lhs = [ev(&ra.bvf), ev(&rb.bvf), ev(&rd.bvf), ev(&rz.bvf)];
    let rhs = [ev(&ra.core), ev(&rb.core), ev(&rd.core), ev(&rz.core)];
    let step1 = cong(
        &[lb(), lb(), lb(), lb()],
        &bool_ty(),
        &f,
        &lhs,
        &rhs,
        &[ra.proof, rb.proof, rd.proof, rz.proof],
    );
    let (ea, eb) = (rhs[0].clone(), rhs[1].clone());
    let nw = kx::nat_lit(wa);
    let h = trans(
        nat(),
        kx::bv_len(ea.clone()),
        nw.clone(),
        kx::bv_len(eb.clone()),
        la,
        symm(nat(), kx::bv_len(eb.clone()), nw, lb_),
    );
    let swapped = kx::bv_ult(eb.clone(), ea.clone());
    let step2 = branch_theory::hi_ult_inst(ea, eb, h);
    let proof = trans(bool_ty(), goal.clone(), f(&rhs), swapped.clone(), step1, step2);
    Ok((goal, atom(swapped)?, proof))
}

/// `Eq(Eq(Extract{Sub(x, y), …}, _), And[Not(Eq(_, _)), Not(Eq(_, _))])`,
/// the skeleton of AArch64 `N == V` after `cmp x, y` (`b.ge`; under `Not`,
/// `b.lt`): `(x, y, Sub(x, y), w)`. Only the skeleton is read, and the
/// operands only from the difference: what the other positions say is the
/// kernel's to check against `slt_flags` (a wrong one is a refused term,
/// never a wrong one). `b.gt` / `b.le`, which also read `Z`, are not this
/// shape at the top.
fn flag_shape<'a>(
    a: &'a Formula,
    b: &'a Formula,
) -> Option<(&'a Formula, &'a Formula, &'a Formula, u32)> {
    let Formula::Eq(ext, _) = a else { return None };
    let Formula::BvExtract { inner, .. } = &**ext else { return None };
    let Formula::BvSub(x, y, w) = &**inner else { return None };
    let Formula::And(xs) = b else { return None };
    let [Formula::Not(p), Formula::Not(q)] = xs.as_slice() else { return None };
    if !matches!(&**p, Formula::Eq(..)) || !matches!(&**q, Formula::Eq(..)) {
        return None;
    }
    (2..=64).contains(w).then_some((&**x, &**y, &**inner, *w))
}

/// `N == V` is `not (bvSLtReal x y)`: congruence to the cores, then
/// `Bool.not` over `slt_flags` with the premises `bvIsCons x = true`
/// (`Eq.refl`) and `L x = L y` (from `core_len`). The kernel identifies the
/// goal's sign-bit extracts `btail^(w-1)` with `[bvLastBit _]` by computation.
fn flag_bridge(
    c: &Formula,
    x: &Formula,
    y: &Formula,
    d: &Formula,
    w: u32,
    ctx: &mut ReflectCtx,
) -> Result<(Expr, BExpr, Expr), String> {
    let goal = goal_only(ctx, |ctx| bool_goal(c, ctx))?;
    let rx = reflect_formula(x, ctx)?;
    let ry = reflect_formula(y, ctx)?;
    let rd = reflect_formula(d, ctx)?;
    if rd.core != kx::sub(rx.core.clone(), ry.core.clone()) {
        return Err("branch: flag difference is not x - y".into());
    }
    let (lx, wx) = add_comm::core_len(&rx.core).ok_or("branch: flag operand length")?;
    let (ly, wy) = add_comm::core_len(&ry.core).ok_or("branch: flag operand length")?;
    if wx != w || wy != w {
        return Err("branch: flag widths".into());
    }
    let sign = |l: Expr| kx::evalf(kx::const_((1..w).fold(l, |acc, _| btail(acc))));
    let one = || kx::evalf(kx::const_(kx::bits(1, 1)));
    // `N != V` as the goal's `B` states it over `[x, y, x - y]`; the goal is
    // its `Bool.not`.
    let xor = |v: &[Expr]| {
        let (sx, sy, sd) = (sign(v[0].clone()), sign(v[1].clone()), sign(v[2].clone()));
        kx::bxor(
            kx::bv_beq(sd.clone(), one()),
            kx::band(kx::bnot(kx::bv_beq(sx.clone(), sy)), kx::bnot(kx::bv_beq(sd, sx))),
        )
    };
    let f = |v: &[Expr]| kx::bnot(xor(v));
    let ev = |e: &Expr| kx::evalf(e.clone());
    let lhs = [ev(&rx.bvf), ev(&ry.bvf), ev(&rd.bvf)];
    let rhs = [ev(&rx.core), ev(&ry.core), ev(&rd.core)];
    let step1 =
        cong(&[lb(), lb(), lb()], &bool_ty(), &f, &lhs, &rhs, &[rx.proof, ry.proof, rd.proof]);
    let (ex, ey) = (rhs[0].clone(), rhs[1].clone());
    let nw = kx::nat_lit(w);
    let h_len = trans(
        nat(),
        kx::bv_len(ex.clone()),
        nw.clone(),
        kx::bv_len(ey.clone()),
        lx,
        symm(nat(), kx::bv_len(ey.clone()), nw, ly),
    );
    let h_cons = refl(bool_ty(), kx::btrue());
    let slt = kx::bv_slt_real(ex.clone(), ey.clone());
    let inst = branch_theory::slt_flags_inst(ex, ey, h_cons, h_len);
    let step2 =
        congr_arg(bool_ty(), bool_ty(), xor(&rhs), slt.clone(), Expr::const_str("Bool.not"), inst);
    let stated = kx::bnot(slt.clone());
    let proof = trans(bool_ty(), goal.clone(), f(&rhs), stated, step1, step2);
    Ok((goal, BExpr::Not(Box::new(atom(slt)?)), proof))
}
