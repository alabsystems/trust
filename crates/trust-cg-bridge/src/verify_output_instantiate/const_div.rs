// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The constant-division route (CONSTDIV): a call-event conjunction whose
//! machine side divides by a constant with the AArch64 magic multiply-high
//! (`umulh`, then `lsr` / UBFM, with or without the add-back) is proved by
//! one kernel-checked term.
//!
//! Stage B1 wires one use of it (DECISION_QUEUE CONSTDIV-1): the call-event
//! gate's step (4) hands each item's left side `m` (the machine side, under
//! reach guards that may carry spec formulas; never the right side `s`) to
//! [`step4_rewrite`],
//! which replaces each magic quotient by `BvUDiv(x, d)` under a
//! kernel-admitted certificate ([`const_div_rewrite`]), and ay decides the
//! rewritten item. Stage B2 wires the conjunction route ([`try_conjunction`])
//! as the third step-(5) branch route (`branch_dispatch.rs`): tried on the
//! ORIGINAL conjunction only after the branch and division splits decline,
//! and only when some side holds the multiply-high.
//!
//! # What is proved
//!
//! For `items = [(l_1, r_1) … (l_n, r_n)]` the declared type is
//! `E_1 ∧ (… ∧ E_n)`, `E_i := bvfEval R(l_i) = bvfEval R(r_i)`, with `R`
//! the reflection under [`ReflectCtx::const_div_goal`]: the branch split's
//! goal reflection (strength arms, the bit-vector `Ite`, the FAITHFUL
//! `BvUDiv` with all-ones at a zero divisor, the high extract) plus one goal
//! arm of this module, [`umulh`]:
//!
//! ```text
//! R(Extract{127,64}(BvMul(ZeroExt(a,64), ZeroExt(b,64), 128)))
//!   := Const (iter 64 ⟦Mul (ZeroExt R(a) 64) (ZeroExt R(b) 64)⟧)
//! ```
//!
//! `iter 64` drops the 64 low bits of the 128-bit product (lists are least
//! significant first), so the arm states SMT `bvmul` on the zero-extended
//! operands and keeps bits 127..64. It is admitted only through
//! `strength::admit_obligation` in `const_div_theory::const_div_env`.
//!
//! # The discharge
//!
//! The proving reflection ([`ReflectCtx::const_div_proving`]) reaches the
//! same goal tags and moves the cores: the closed MOVZ/MOVK multiplier folds
//! to a `Const` (kernel evaluation), each magic quotient
//! `ZeroExt (Const (iter k ⟦…umulh…⟧)) k` becomes `Div X (Const d)`
//! (`Trust.BVD.magic_noadd` / `magic_addback`, every constant premise closed
//! by `Eq.refl` on computed literals), and the remainder tail
//! `X + (q - (q << n))` becomes `X - q * (2^n - 1)` (`Trust.BVD.rem_tail`).
//! The spec side reaches `Div X (Const d)` through the faithful division's
//! guard. Each item closes by `trans P_l (symm P_r)`.
//!
//! # What is trusted
//!
//! The kernel checks the term against the goal; the goal's meaning is the
//! trusted residual:
//!
//! - the width and sort walk ([`walk`]): this module's own copy of the
//!   branch split's walk as it stood before s10 (no arithmetic shift, no
//!   sign extension, no Bool equality), plus EXACTLY the 128-bit
//!   multiply-high shape above with 64-bit operands. Every other width above
//!   64 is refused, and no filter bypasses the walk. The copy does not
//!   follow later branch-walk arms: each would widen this goal's meaning and
//!   needs its own review (`wider_shapes_are_refused_by_the_walk`);
//! - the goal arm [`umulh`] and the reflections it reuses, compared with SMT
//!   on closed instances by the tests (`reflection_agrees_with_smt`);
//! - for the step-(4) rewrite, [`replace`]: the Formula subterms it replaces
//!   are exactly the certificate's pairs (one list feeds both, and
//!   [`ConstDivCert::binds`] rebuilds the admitted goal from it).
//!
//! # What only declines
//!
//! The caps, the check that the proving reflection met the goal and that the
//! cores meet (or are closed, whitelisted and equal in Rust evaluation,
//! [`closed_meet`], for the kernel to compare by computation), the closed-data
//! whitelist ([`CONSTDIV_WHITELIST`]) and the
//! concrete-point differential ([`differential`]: both Formula sides
//! evaluated in Rust at fixed points against the reflected goal sides there,
//! read by [`GoalEval`], an independent Rust reading of the `Clean.BVC`
//! definitions that the tests compare with the kernel's evaluation).
//! `BranchFilter::Off` bypasses them so a test shows the KERNEL refusing a
//! wrong term.

use std::collections::HashMap;

use clean_kernel::expr::UsedConstants;
use clean_kernel::name::Name;
use clean_kernel::{BigNat, Expr, ExprKind, Literal};
use trust_types::{Formula, Sort};

use super::branch_reflect::{BRANCH_MAX_REWRITES, CLOSED_WHITELIST};
use super::branch_split::{BranchFilter, Decline};
use super::branch_theory::{bool_lit, const_bits, spine};
use super::const_div_theory::{
    self as theory, const_div_env, iter, lshr_k_inst, magic_addback_inst, magic_mp_inst,
    magic_noadd_inst, rem_tail_inst, ubfm_k_inst, umh,
};
use super::kterm::{
    Fresh, bvlen, congr_arg, lams, lb, nadd, nat, nble, nlit, nmul, refl, succ, symm, to_nat,
    trans, two_pow,
};
use super::{
    ReflectCtx, Reflected, add_comm, kx, memory_reflection, on_route_stack, reflect_formula,
    run_recheck_thread, strength,
};
use crate::verify_output::ProvenEvidence;

// ── the contexts ─────────────────────────────────────────────────────────────

impl ReflectCtx {
    /// The reflection the route states its goal with: the branch split's
    /// goal reflection plus the [`umulh`] arm. No step builder runs.
    pub(super) fn const_div_goal() -> Self {
        let mut ctx = Self::branching_goal();
        ctx.const_div = true;
        ctx
    }

    /// The reflection the route proves with: the branch split's proving
    /// reflection plus the [`umulh`] arm and this module's steps. Its `bvf`
    /// is the goal's.
    pub(super) fn const_div_proving() -> Self {
        let mut ctx = Self::branching();
        ctx.const_div = true;
        ctx.const_div_steps = true;
        ctx
    }

    /// Splice `step : bvfEval core = bvfEval new_core` on the branch
    /// counter (at most `BRANCH_MAX_REWRITES`; past it the cores fail to
    /// meet and the route declines).
    fn splice_const_div(&mut self, out: Reflected, step: Expr, new_core: Expr) -> Reflected {
        if self.branch_rewrites >= BRANCH_MAX_REWRITES {
            self.branch_cap_hit = true;
            return out;
        }
        let Reflected { bvf, core, proof } = out;
        let proof = kx::eq_trans_list(
            kx::evalf(bvf.clone()),
            kx::evalf(core),
            kx::evalf(new_core.clone()),
            proof,
            step,
        );
        self.branch_rewrites += 1;
        Reflected { bvf, core: new_core, proof }
    }
}

// ── the closed-data whitelist ────────────────────────────────────────────────

/// The constants a closed term the route has the kernel evaluate may
/// mention: the branch split's [`CLOSED_WHITELIST`] plus `Nat.ble` and
/// `bvTwoPow` (the magic premises). Literals stay below 2^64 and lists at 64
/// elements; the premises compute larger numbers, but never mention one.
/// The length follows [`CLOSED_WHITELIST`]'s, so a list that grows there
/// keeps every entry here, and an entry it gains reaches this filter too:
/// `constdiv_whitelist_extends_the_branch_list` names what must stay off
/// both (multiplication, division and shifts on closed data), and
/// `constdiv_closed_data_is_whitelisted` scans what the positives emit. The
/// list only declines; the kernel checks every term.
pub(crate) const CONSTDIV_WHITELIST: [&str; CLOSED_WHITELIST.len() + 2] = {
    let n = CLOSED_WHITELIST.len();
    let mut out = [""; CLOSED_WHITELIST.len() + 2];
    let mut i = 0;
    while i < n {
        out[i] = CLOSED_WHITELIST[i];
        i += 1;
    }
    out[n] = "Nat.ble";
    out[n + 1] = "Clean.BVC.bvTwoPow";
    out
};

/// Allowed besides [`CONSTDIV_WHITELIST`] only in the folded MOVZ/MOVK
/// multiplier, which must mention no leaf bit. `BvF.And`, the chain's other
/// node, needs no entry: s10 put it on [`CLOSED_WHITELIST`] (its shift-amount
/// fold), so every closed premise may mention it.
const MOVK_EXTRA: [&str; 1] = ["Clean.BVC.BvF.Or"];

fn head_is(e: &Expr, name: &str) -> bool {
    matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == name)
}

fn closed_ok_with(e: &Expr, extra: &[&str]) -> bool {
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        match e.kind() {
            ExprKind::Const(n, _) => {
                let s = n.to_string();
                if !(CONSTDIV_WHITELIST.contains(&s.as_str())
                    || extra.contains(&s.as_str())
                    || s.starts_with("BVC_LEAFBIT_"))
                {
                    return false;
                }
            }
            ExprKind::Lit(Literal::Nat(BigNat::Small(_)))
            | ExprKind::BVar(_)
            | ExprKind::Sort(_) => {}
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
    /// Every closed term [`note_closed`] (`false`) and [`movk_closed_ok`]
    /// (`true`) saw on this thread, read by
    /// `constdiv_closed_data_is_whitelisted`.
    pub(crate) static CONSTDIV_SEEN: std::cell::RefCell<Vec<(Expr, bool)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Is a closed premise inside [`CONSTDIV_WHITELIST`]? Recorded for the scan
/// test; a step builder declines when it is `false`.
pub(crate) fn note_closed(e: &Expr) -> bool {
    #[cfg(test)]
    CONSTDIV_SEEN.with(|seen| seen.borrow_mut().push((e.clone(), false)));
    closed_ok_with(e, &[])
}

fn has_leaf_bit(e: &Expr) -> bool {
    let mut used = std::collections::HashSet::new();
    e.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
    used.iter().any(|n| n.to_string().starts_with("BVC_LEAF"))
}

/// The folded MOVZ/MOVK multiplier: leaf-free, and [`MOVK_EXTRA`] allowed.
fn movk_closed_ok(e: &Expr) -> bool {
    #[cfg(test)]
    CONSTDIV_SEEN.with(|seen| seen.borrow_mut().push((e.clone(), true)));
    !has_leaf_bit(e) && closed_ok_with(e, &MOVK_EXTRA)
}

// ── the width and sort walk ──────────────────────────────────────────────────

/// At most this many Formula nodes per side.
const MAX_NODES: usize = 1024;
/// At most this many operands of an `And` / `Or`.
const MAX_JUNCTS: usize = 8;

fn same(a: Option<u32>, b: Option<u32>, w: u32) -> Option<u32> {
    (a? == w && b? == w).then_some(w)
}

/// `Extract{127,64}(BvMul(ZeroExt(a,64), ZeroExt(b,64), 128))`'s operands.
fn umulh_shape(f: &Formula) -> Option<(&Formula, &Formula)> {
    let Formula::BvExtract { inner, high: 127, low: 64 } = f else { return None };
    let Formula::BvMul(l, r, 128) = &**inner else { return None };
    match (&**l, &**r) {
        (Formula::BvZeroExt(a, 64), Formula::BvZeroExt(b, 64)) => Some((a, b)),
        _ => None,
    }
}

/// The width of a bit-vector side, or `None` outside the fragment: the
/// branch split's walk (plan §4) as it stood before s10, without its
/// arithmetic-shift, sign-extension and Bool-equality arms, plus exactly the
/// 128-bit multiply-high shape with 64-bit operands.
pub(crate) fn walk(f: &Formula, n: &mut usize) -> Option<u32> {
    *n += 1;
    if *n > MAX_NODES {
        return None;
    }
    if let Some((a, b)) = umulh_shape(f) {
        let wa = walk(a, n);
        return same(wa, walk(b, n), 64);
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
        Formula::BvZeroExt(x, k) => {
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
        Formula::Eq(a, b) => {
            let wa = walk(a, n)?;
            (walk(b, n)? == wa).then_some(())
        }
        Formula::BvULt(a, b, w) | Formula::BvULe(a, b, w) | Formula::BvSLt(a, b, w) => {
            let wa = walk(a, n);
            same(wa, walk(b, n), *w).map(|_| ())
        }
        _ => None,
    }
}

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

// ── Formula values (the differential, the multiplier fold) ───────────────────

fn mask(w: u32) -> u128 {
    if w >= 128 { u128::MAX } else { (1u128 << w) - 1 }
}

/// The SMT-LIB value of a bit-vector side under `env` (`(value, width)`),
/// widths up to 128; `None` outside the evaluated fragment.
pub(crate) fn eval_bv(f: &Formula, env: &dyn Fn(&str) -> Option<u128>) -> Option<(u128, u32)> {
    let bin = |l: &Formula, r: &Formula, w: u32, op: &dyn Fn(u128, u128) -> u128| {
        let (a, wa) = eval_bv(l, env)?;
        let (b, wb) = eval_bv(r, env)?;
        (wa == w && wb == w).then(|| (op(a, b) & mask(w), w))
    };
    match f {
        Formula::Var(name, Sort::BitVec(w)) if (1..=128).contains(w) => {
            Some((env(name)? & mask(*w), *w))
        }
        Formula::BitVec { value, width } if (1..=128).contains(width) => {
            Some(((*value as u128) & mask(*width), *width))
        }
        Formula::BvAdd(l, r, w) => bin(l, r, *w, &|a, b| a.wrapping_add(b)),
        Formula::BvSub(l, r, w) => bin(l, r, *w, &|a, b| a.wrapping_sub(b)),
        Formula::BvMul(l, r, w) => bin(l, r, *w, &|a, b| a.wrapping_mul(b)),
        Formula::BvAnd(l, r, w) => bin(l, r, *w, &|a, b| a & b),
        Formula::BvOr(l, r, w) => bin(l, r, *w, &|a, b| a | b),
        Formula::BvXor(l, r, w) => bin(l, r, *w, &|a, b| a ^ b),
        Formula::BvUDiv(l, r, w) => {
            let m = mask(*w);
            bin(l, r, *w, &|a, b| if b == 0 { m } else { a / b })
        }
        Formula::BvURem(l, r, w) => bin(l, r, *w, &|a, b| if b == 0 { a } else { a % b }),
        Formula::BvShl(l, r, w) => {
            let w2 = *w;
            bin(l, r, *w, &|a, b| if b >= u128::from(w2) { 0 } else { a << b })
        }
        Formula::BvLShr(l, r, w) => {
            let w2 = *w;
            bin(l, r, *w, &|a, b| if b >= u128::from(w2) { 0 } else { a >> b })
        }
        Formula::BvZeroExt(x, k) => {
            let (v, w) = eval_bv(x, env)?;
            let w2 = w.checked_add(*k)?;
            (w2 <= 128).then_some((v, w2))
        }
        Formula::BvExtract { inner, high, low } => {
            let (v, w) = eval_bv(inner, env)?;
            (low <= high && *high < w).then(|| ((v >> low) & mask(high - low + 1), high - low + 1))
        }
        Formula::Ite(c, a, e) => {
            if eval_bool(c, env)? {
                eval_bv(a, env)
            } else {
                eval_bv(e, env)
            }
        }
        _ => None,
    }
}

fn eval_bool(f: &Formula, env: &dyn Fn(&str) -> Option<u128>) -> Option<bool> {
    match f {
        Formula::Bool(b) => Some(*b),
        Formula::Not(x) => Some(!eval_bool(x, env)?),
        Formula::And(xs) => xs.iter().try_fold(true, |acc, x| Some(acc & eval_bool(x, env)?)),
        Formula::Or(xs) => xs.iter().try_fold(false, |acc, x| Some(acc | eval_bool(x, env)?)),
        Formula::Eq(a, b) => {
            let (va, wa) = eval_bv(a, env)?;
            let (vb, wb) = eval_bv(b, env)?;
            (wa == wb).then_some(va == vb)
        }
        Formula::BvULt(a, b, _) | Formula::BvULe(a, b, _) => {
            let (va, wa) = eval_bv(a, env)?;
            let (vb, wb) = eval_bv(b, env)?;
            (wa == wb).then_some(if matches!(f, Formula::BvULt(..)) { va < vb } else { va <= vb })
        }
        _ => None,
    }
}

fn no_vars(_: &str) -> Option<u128> {
    None
}

// ── the goal arm ─────────────────────────────────────────────────────────────

/// `R(Extract{127,64}(BvMul(ZeroExt(a,64), ZeroExt(b,64), 128)))`, under
/// `ctx.const_div` only: `Const (iter 64 ⟦Mul (ZeroExt R(a) 64) (ZeroExt R(b) 64)⟧)`.
/// Under `const_div_steps` a closed operand (the MOVZ/MOVK multiplier) is
/// folded to a literal `Const` in the core, by kernel evaluation.
pub(super) fn umulh(f: &Formula, ctx: &mut ReflectCtx) -> Result<Reflected, String> {
    let (a, b) = umulh_shape(f).ok_or("const-div: not the 64-bit multiply-high shape")?;
    // The arm walks its own operands: whatever context reaches it, an operand
    // outside the fragment (a sign extension, a wider literal, a variable
    // divisor) is refused here as well as by `goal_of`'s walk.
    if memory_reflection::width(a) != Some(64)
        || memory_reflection::width(b) != Some(64)
        || walk(a, &mut 0) != Some(64)
        || walk(b, &mut 0) != Some(64)
    {
        return Err("const-div: a multiply-high operand is outside the 64-bit fragment".into());
    }
    let ra = reflect_formula(a, ctx)?;
    let rb = reflect_formula(b, ctx)?;
    let w = kx::nat_lit(64);
    let prod = |x: &Expr, y: &Expr| {
        kx::mul(kx::zext(x.clone(), w.clone()), kx::zext(y.clone(), w.clone()))
    };
    let bvf = kx::const_(iter(w.clone(), kx::evalf(prod(&ra.bvf, &rb.bvf))));
    if !ctx.const_div_steps {
        return Ok(Reflected {
            bvf: bvf.clone(),
            core: bvf.clone(),
            proof: kx::eq_refl_list(kx::evalf(bvf)),
        });
    }
    let (ca, pa) = fold_closed(a, &ra);
    let (cb, pb) = fold_closed(b, &rb);
    let core = kx::const_(iter(w.clone(), kx::evalf(prod(&ca, &cb))));
    if core == bvf {
        return Ok(Reflected { bvf: bvf.clone(), core, proof: kx::eq_refl_list(kx::evalf(bvf)) });
    }
    let mul_eq = kx::mul_cong(
        kx::zext(ra.bvf.clone(), w.clone()),
        kx::zext(ca.clone(), w.clone()),
        kx::zext(rb.bvf.clone(), w.clone()),
        kx::zext(cb.clone(), w.clone()),
        kx::zext_cong(ra.bvf.clone(), ca.clone(), w.clone(), pa),
        kx::zext_cong(rb.bvf.clone(), cb.clone(), w.clone(), pb),
    );
    let mut fr = Fresh::new();
    let (t_id, t) = fr.local();
    let drop = lams(vec![(t_id, lb())], iter(w.clone(), t));
    let proof = congr_arg(
        lb(),
        lb(),
        kx::evalf(prod(&ra.bvf, &rb.bvf)),
        kx::evalf(prod(&ca, &cb)),
        drop,
        mul_eq,
    );
    Ok(Reflected { bvf, core, proof })
}

/// A closed 64-bit operand's core folded to `Const bits` (with
/// `bvfEval bvf = bvfEval (Const bits)`), when its core is not already a
/// literal and the kernel may evaluate it ([`movk_closed_ok`]); otherwise
/// the reflection's own core and proof.
fn fold_closed(f: &Formula, r: &Reflected) -> (Expr, Expr) {
    let keep = (r.core.clone(), r.proof.clone());
    if has_var(f) || const_bits(&r.core).is_some() {
        return keep;
    }
    let Some((v, 64)) = eval_bv(f, &no_vars) else { return keep };
    if !movk_closed_ok(&kx::evalf(r.core.clone())) {
        return keep;
    }
    let bits = kx::bits(v as i128, 64);
    let folded = kx::const_(bits.clone());
    let proof = kx::eq_trans_list(
        kx::evalf(r.bvf.clone()),
        kx::evalf(r.core.clone()),
        kx::evalf(folded.clone()),
        r.proof.clone(),
        refl(lb(), bits),
    );
    (folded, proof)
}

// ── the steps ────────────────────────────────────────────────────────────────

/// A deliberate fault in a step builder, for the mutant tests: each makes
/// the builder emit a term the kernel must refuse.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mutant {
    None,
    /// The builder's own band filter is off (a wrong magic is offered).
    NoBandFilter,
    /// The builder claims this divisor whatever the magic says.
    ForceDivisor(u128),
    /// The remainder tail claims `q * 2^n` instead of `q * (2^n - 1)`.
    RemMulPow,
    /// The band premise is an axiom of its (false) statement.
    AxiomBand,
    /// The differential is handed goal sides whose right side states zero,
    /// as a misreflected goal would (the kernel still checks the true goal).
    ForgedSides,
    /// The rewrite's certificate carries another conjunction's goal, as a
    /// prover that admitted something else would.
    ForeignGoal,
}

/// Under [`Mutant::ForgedSides`], `sides` with each right side replaced by
/// a 64-bit literal zero; otherwise `sides`.
#[cfg(test)]
fn forged_sides(sides: Vec<(Expr, Expr)>) -> Vec<(Expr, Expr)> {
    if mutant() != Mutant::ForgedSides {
        return sides;
    }
    sides.into_iter().map(|(l, _)| (l, kx::evalf(kx::const_(kx::bits(0, 64))))).collect()
}

#[cfg(test)]
fn lit64(v: i128) -> Formula {
    Formula::BitVec { value: v, width: 64 }
}

#[cfg(test)]
thread_local! {
    pub(crate) static MUTANT: std::cell::Cell<Mutant> = const { std::cell::Cell::new(Mutant::None) };
    /// Axioms the `AxiomBand` mutant needs declared: `(name, type)`.
    static MUTANT_AXIOMS: std::cell::RefCell<Vec<(Name, Expr)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

#[cfg(test)]
fn mutant() -> Mutant {
    MUTANT.with(std::cell::Cell::get)
}

/// After a node is reflected under `const_div_steps`: the magic quotient at
/// a `ZeroExt` node, the remainder tail at an `Add` node.
pub(super) fn post_step(f: &Formula, out: Reflected, ctx: &mut ReflectCtx) -> Reflected {
    let step = match f {
        Formula::BvZeroExt(..) => magic_step(&out.core),
        Formula::BvAdd(..) => rem_tail_step(&out.core),
        _ => None,
    };
    match step {
        Some((step, new_core)) => ctx.splice_const_div(out, step, new_core),
        None => out,
    }
}

fn args_of(e: &Expr, name: &str, arity: usize) -> Option<Vec<Expr>> {
    if !head_is(e, name) {
        return None;
    }
    let args = e.get_app_args();
    (args.len() == arity).then(|| args.iter().map(|a| (*a).clone()).collect())
}

fn args2(e: &Expr, name: &str) -> Option<(Expr, Expr)> {
    let mut v = args_of(e, name, 2)?;
    let b = v.pop()?;
    let a = v.pop()?;
    Some((a, b))
}

fn arg1(e: &Expr, name: &str) -> Option<Expr> {
    args_of(e, name, 1)?.pop()
}

/// The value of a `Nat.succ` chain.
fn nat_chain(mut e: &Expr) -> Option<u32> {
    let mut n = 0u32;
    loop {
        if matches!(e.kind(), ExprKind::Const(c, _) if c.to_string() == "Nat.zero") {
            return Some(n);
        }
        let ExprKind::App(f, a) = e.kind() else { return None };
        if !matches!(f.kind(), ExprKind::Const(c, _) if c.to_string() == "Nat.succ") {
            return None;
        }
        n = n.checked_add(1)?;
        e = a;
    }
}

/// The value of a concrete 64-element literal list.
fn list64(list: &Expr) -> Option<u128> {
    let bits: Vec<bool> = spine(list)?.iter().map(bool_lit).collect::<Option<_>>()?;
    (bits.len() == 64).then(|| bits.iter().rev().fold(0u128, |acc, &b| (acc << 1) | u128::from(b)))
}

/// `(X, mk, M)` of a core `UMH X mk 64` ([`umh`]).
fn decode_umh(e: &Expr) -> Option<(Expr, Expr, u128)> {
    let list = arg1(e, "Clean.BVC.BvF.Const")?;
    let rec = args_of(&list, "Nat.rec", 4)?;
    let ev = arg1(&rec[1], "Clean.BVC.bvfEval")?;
    let (za, zb) = args2(&ev, "Clean.BVC.BvF.Mul")?;
    let (x, _) = args2(&za, "Clean.BVC.BvF.ZeroExt")?;
    let (cm, _) = args2(&zb, "Clean.BVC.BvF.ZeroExt")?;
    let mk = arg1(&cm, "Clean.BVC.BvF.Const")?;
    let m = list64(&mk)?;
    (*e == umh(&x, &mk, &kx::nat_lit(64))).then_some((x, mk, m))
}

/// `(d, e)` with `d * M_eff = 2^p + e` and the band
/// `e * 2^64 + 1 ≤ 2^p + e`, where `M_eff = M` and `p = 64 + k` without
/// the add-back, `M_eff = 2^64 + M` and `p = 65 + k` with it. A filter: the
/// kernel re-checks every one of these facts.
pub(crate) fn magic_params(m: u128, k: u32, add: bool) -> Option<(u128, u128)> {
    let meff = if add { (1u128 << 64).checked_add(m)? } else { m };
    let p = 64 + k + u32::from(add);
    if meff == 0 || p > 126 {
        return None;
    }
    let two_p = 1u128 << p;
    // The forced divisor keeps the TRUE error term (not truncated), so the
    // kernel refuses at the premise that is really false: `d * M = 2^p + e`
    // when `d * M < 2^p` (no natural `e` exists; the distance is offered),
    // otherwise the band.
    #[cfg(test)]
    if let Mutant::ForceDivisor(d) = mutant() {
        let e = d.checked_mul(meff)?.abs_diff(two_p);
        return Some((d, e));
    }
    let d = two_p.div_ceil(meff);
    if d < 2 || d >= 1u128 << 64 {
        return None;
    }
    let e = d.checked_mul(meff)?.checked_sub(two_p)?;
    let band = e.checked_mul(1u128 << 64)?.checked_add(1)? <= two_p.checked_add(e)?;
    #[cfg(test)]
    if mutant() == Mutant::NoBandFilter || mutant() == Mutant::AxiomBand {
        return Some((d, e));
    }
    band.then_some((d, e))
}

/// `ZeroExt (Const (btail^k ⟦Q⟧)) k` with `Q` a magic quotient core
/// (`UMH X mk 64`, or `Add (UMH X mk 64) H` with `H` the halved difference
/// in its `lsr #1` or UBFM form) → `Div X (Const d)`.
fn magic_step(core: &Expr) -> Option<(Expr, Expr)> {
    let (inner, kk) = args2(core, "Clean.BVC.BvF.ZeroExt")?;
    let k = nat_chain(&kk)?;
    if !(1..=63).contains(&k) {
        return None;
    }
    let mut cur = arg1(&inner, "Clean.BVC.BvF.Const")?;
    for _ in 0..k {
        cur = arg1(&cur, "Clean.BVI.btail")?;
    }
    let body = arg1(&cur, "Clean.BVC.bvfEval")?;
    let (x, mk, mval, h) = match decode_umh(&body) {
        Some((x, mk, m)) => (x, mk, m, None),
        None => {
            let (u, h) = args2(&body, "Clean.BVC.BvF.Add")?;
            let (x, mk, m) = decode_umh(&u)?;
            (x, mk, m, Some((u, h)))
        }
    };
    let add = h.is_some();
    let (d, e) = magic_params(mval, k, add)?;
    let (hx, wx) = add_comm::core_len(&x)?;
    if wx != 64 {
        return None;
    }
    let c = kx::bits(i128::try_from(d).ok()?, 64);
    let m = kx::nat_lit(63);
    let j = kx::nat_lit(64 - k);
    let w64 = kx::nat_lit(64);
    let en = nat_u128(e);
    let vc = to_nat(c.clone());
    let (big_m, p) = magic_mp_inst(add, &mk, &m, &kk);
    let hdm_lhs = nmul(vc.clone(), big_m);
    let band_lo = nadd(nmul(en.clone(), two_pow(w64.clone())), nlit(1));
    let band_hi = nadd(two_pow(p), en.clone());
    let closed = [
        bvlen(mk.clone()),
        nadd(j.clone(), kk.clone()),
        nble(nlit(1), vc.clone()),
        hdm_lhs.clone(),
        band_hi.clone(),
        nble(band_lo.clone(), band_hi.clone()),
    ];
    if !closed.iter().all(note_closed) {
        return None;
    }
    let hmk = refl(nat(), w64.clone());
    let hjk = refl(nat(), w64);
    let hd = Expr::apps(
        Expr::const_str("Nat.le_of_ble_eq_true"),
        [nlit(1), vc, kx::eq_refl_bool(kx::btrue())],
    );
    let hdm = refl(nat(), hdm_lhs);
    #[allow(unused_mut)]
    let mut hble = kx::eq_refl_bool(kx::btrue());
    #[cfg(test)]
    if mutant() == Mutant::AxiomBand {
        let name = Name::from_string("Trust.BVD.mutant_band");
        let ty = kx::eq_bool(nble(band_lo, band_hi), kx::btrue());
        MUTANT_AXIOMS.with(|a| a.borrow_mut().push((name.clone(), ty)));
        hble = Expr::const_(name, vec![]);
    }
    let step = match h {
        None => {
            magic_noadd_inst([x.clone(), mk, c.clone(), m, j, kk, en, hx, hmk, hjk, hd, hdm, hble])
        }
        Some((u, h)) => {
            let s = kx::sub(x.clone(), u);
            let hhv = halved_difference(&h, &s)?;
            magic_addback_inst([
                x.clone(),
                h,
                mk,
                c.clone(),
                m,
                j,
                kk,
                en,
                hx,
                hmk,
                hjk,
                hhv,
                hd,
                hdm,
                hble,
            ])
        }
    };
    Some((step, kx::div(x, kx::const_(c))))
}

/// The natural `v` built from literals below 2^64 (`hi * 2^64 + lo` when it
/// is wider), so [`note_closed`]'s literal bound holds. A band-satisfying
/// `e` is below 2^62, so production always takes the literal; a wider `e`
/// reaches the kernel only from a mutant, which must be refused at the band.
fn nat_u128(v: u128) -> Expr {
    let (hi, lo) = ((v >> 64) as u64, v as u64);
    if hi == 0 { nlit(lo) } else { nadd(nmul(nlit(hi), two_pow(kx::nat_lit(64))), nlit(lo)) }
}

/// `V ⟦H⟧ = V ⟦S⟧ / 2` for `H = LShr S (Const 1)` (`lshr_k`) or
/// `H = ZeroExt (Const (btail ⟦S⟧)) 1` (`ubfm_k`).
fn halved_difference(h: &Expr, s: &Expr) -> Option<Expr> {
    if let Some((s2, one)) = args2(h, "Clean.BVC.BvF.LShr") {
        let (w, v) = const_bits(&one)?;
        if s2 != *s
            || w != 64
            || v != 1
            || !note_closed(&to_nat(arg1(&one, "Clean.BVC.BvF.Const")?))
        {
            return None;
        }
        let list = arg1(&one, "Clean.BVC.BvF.Const")?;
        return Some(lshr_k_inst(s.clone(), list, nlit(1), refl(nat(), nlit(1))));
    }
    let (c, k) = args2(h, "Clean.BVC.BvF.ZeroExt")?;
    let ev =
        arg1(&arg1(&arg1(&c, "Clean.BVC.BvF.Const")?, "Clean.BVI.btail")?, "Clean.BVC.bvfEval")?;
    (ev == *s && k == kx::nat_lit(1)).then(|| ubfm_k_inst(s.clone(), k))
}

/// `(p, w)` with `p : bvLen (bvfEval core) = w`: `add_comm::core_len`, and a
/// `Div` takes its dividend's length.
fn len_of(core: &Expr) -> Option<(Expr, u32)> {
    if let Some(r) = add_comm::core_len(core) {
        return Some(r);
    }
    let (a, b) = args2(core, "Clean.BVC.BvF.Div")?;
    let (pa, w) = len_of(&a)?;
    let (ea, eb) = (kx::evalf(a), kx::evalf(b));
    let step = Expr::apps(
        Expr::const_str("Trust.BVV.len_natToBv"),
        [bvlen(ea.clone()), super::kterm::ndiv(to_nat(ea.clone()), to_nat(eb))],
    );
    Some((trans(nat(), bvlen(kx::evalf(core.clone())), bvlen(ea), kx::nat_lit(w), step, pa), w))
}

/// `Add X (Sub D (Shl D (Const n)))` → `Sub X (Mul D (Const (2^n - 1)))`.
fn rem_tail_step(core: &Expr) -> Option<(Expr, Expr)> {
    let (x, sub) = args2(core, "Clean.BVC.BvF.Add")?;
    let (dd, shl) = args2(&sub, "Clean.BVC.BvF.Sub")?;
    let (dd2, nconst) = args2(&shl, "Clean.BVC.BvF.Shl")?;
    if dd != dd2 {
        return None;
    }
    let (nw, a) = const_bits(&nconst)?;
    if nw != 64 || !(1..=63).contains(&a) {
        return None;
    }
    let n_list = arg1(&nconst, "Clean.BVC.BvF.Const")?;
    #[allow(unused_mut)]
    let mut cval = (1u128 << a) - 1;
    #[cfg(test)]
    if mutant() == Mutant::RemMulPow {
        cval = 1u128 << a;
    }
    let c = kx::bits(i128::try_from(cval).ok()?, 64);
    let (px, wx) = len_of(&x)?;
    let (pd, wd) = len_of(&dd)?;
    if wx != 64 || wd != 64 {
        return None;
    }
    if !note_closed(&succ(to_nat(c.clone()))) || !note_closed(&two_pow(to_nat(n_list.clone()))) {
        return None;
    }
    let n64 = kx::nat_lit(64);
    let lx = bvlen(kx::evalf(x.clone()));
    let back = symm(nat(), lx.clone(), n64.clone(), px.clone());
    let hd = trans(nat(), bvlen(kx::evalf(dd.clone())), n64.clone(), lx.clone(), pd, back.clone());
    let hc = trans(nat(), bvlen(c.clone()), n64.clone(), lx, refl(nat(), n64), back);
    let hv = refl(nat(), succ(to_nat(c.clone())));
    let step =
        rem_tail_inst([x.clone(), dd.clone(), n_list, c.clone(), kx::nat_lit(63), px, hd, hc, hv]);
    Some((step, kx::sub(x, kx::mul(dd, kx::const_(c)))))
}

// ── the goal and the route ───────────────────────────────────────────────────

/// `(G, [(bvfEval R l_i, bvfEval R r_i)], leaves)`.
pub(crate) type Goal = (Expr, Vec<(Expr, Expr)>, Vec<(String, u32)>);

/// The goal of `items`, under [`ReflectCtx::const_div_goal`] and from the
/// items alone; the walk first, whatever the filter.
pub(crate) fn goal_of(items: &[(Formula, Formula)]) -> Result<Goal, String> {
    for (l, r) in items {
        let (wl, wr) = (walk(l, &mut 0), walk(r, &mut 0));
        if wl.is_none() || wl != wr {
            return Err("const-div: a side is outside the width walk".into());
        }
    }
    let mut ctx = ReflectCtx::const_div_goal();
    let mut sides = Vec::with_capacity(items.len());
    for (l, r) in items {
        let rl = reflect_formula(l, &mut ctx)?;
        let rr = reflect_formula(r, &mut ctx)?;
        sides.push((kx::evalf(rl.bvf), kx::evalf(rr.bvf)));
    }
    let (last, init) = sides.split_last().ok_or("const-div: empty conjunction")?;
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

/// A goal, its discharge, the goal sides and the leaves.
pub(crate) struct Obligation {
    pub(crate) goal: Expr,
    pub(crate) proof: Expr,
    pub(crate) sides: Vec<(Expr, Expr)>,
    pub(crate) leaves: Vec<(String, u32)>,
    /// Axioms a mutant test needs declared. Test builds only: a production
    /// obligation has no way to declare an axiom before admission.
    #[cfg(test)]
    pub(crate) axioms: Vec<(Name, Expr)>,
}

/// Two cores that differ but that the kernel may compare by evaluation (the
/// gate's (4b) check item `ite(fail, 1, 0) == 0` over a closed condition, and
/// a reach guard's closed comparison): both Formula sides are variable-free
/// and evaluate in Rust to one value, and neither core mentions a leaf bit or
/// leaves [`CONSTDIV_WHITELIST`]. Only declines: the kernel decides
/// `bvfEval cl ≡ bvfEval cr` by computation when it checks the item's
/// `trans`, and refuses the term otherwise.
fn closed_meet(l: &Formula, r: &Formula, cl: &Expr, cr: &Expr) -> bool {
    !has_var(l)
        && !has_var(r)
        && eval_bv(l, &no_vars).is_some_and(|v| eval_bv(r, &no_vars) == Some(v))
        && [cl, cr].into_iter().all(|c| {
            let e = kx::evalf(c.clone());
            !has_leaf_bit(&e) && note_closed(&e)
        })
}

fn filtered(filter: BranchFilter, ok: bool, why: &str) -> Result<(), Decline> {
    if filter == BranchFilter::On && !ok { Err(Decline::Filter(why.into())) } else { Ok(()) }
}

/// Build `(G, π)` for `items`; nothing here is checked by the kernel yet.
pub(crate) fn obligation(
    items: &[(Formula, Formula)],
    filter: BranchFilter,
) -> Result<Obligation, Decline> {
    #[cfg(test)]
    MUTANT_AXIOMS.with(|a| a.borrow_mut().clear());
    let (goal, sides, leaves) = goal_of(items).map_err(Decline::Filter)?;
    let mut ctx = ReflectCtx::const_div_proving();
    let mut proofs = Vec::with_capacity(items.len());
    for ((l, r), (gl, gr)) in items.iter().zip(&sides) {
        let rl = reflect_formula(l, &mut ctx).map_err(Decline::Filter)?;
        let rr = reflect_formula(r, &mut ctx).map_err(Decline::Filter)?;
        filtered(
            filter,
            kx::evalf(rl.bvf.clone()) == *gl && kx::evalf(rr.bvf.clone()) == *gr,
            "const-div: the proving reflection left the goal",
        )?;
        filtered(
            filter,
            rl.core == rr.core || closed_meet(l, r, &rl.core, &rr.core),
            "const-div: the cores do not meet",
        )?;
        let (cl, cr) = (kx::evalf(rl.core), kx::evalf(rr.core));
        let back = symm(lb(), gr.clone(), cr, rr.proof);
        proofs.push(trans(lb(), gl.clone(), cl, gr.clone(), rl.proof, back));
    }
    filtered(filter, !ctx.branch_cap_hit, "const-div: cap (steps)")?;
    let last = sides.len() - 1;
    let eq_i = |i: usize| kx::eq_list(sides[i].0.clone(), sides[i].1.clone());
    let mut proof = proofs.pop().ok_or_else(|| Decline::Filter("const-div: empty".into()))?;
    let mut rest = eq_i(last);
    for i in (0..last).rev() {
        let pi = proofs.pop().ok_or_else(|| Decline::Filter("const-div: empty".into()))?;
        proof = Expr::apps(Expr::const_str("And.intro"), [eq_i(i), rest.clone(), pi, proof]);
        rest = Expr::apps(Expr::const_str("And"), [eq_i(i), rest]);
    }
    Ok(Obligation {
        goal,
        proof,
        sides,
        leaves,
        #[cfg(test)]
        axioms: MUTANT_AXIOMS.with(|a| std::mem::take(&mut *a.borrow_mut())),
    })
}

// ── the concrete-point differential ──────────────────────────────────────────

/// How many pseudo-random points the differential adds to the edges.
const RANDOM_POINTS: usize = 16;

/// The points: the edges `0, 1, 2^63 - 1, 2^63, 2^64 - 1`; around each
/// literal divisor `d`, `d - 1, d, d + 1`, the `min(d, 64)` values just below
/// `2^64` (where a slightly wrong magic first errs: every residue mod `d`
/// there when `d ≤ 64`) and the largest multiple of `d` below `2^64` with the
/// value before it; and [`RANDOM_POINTS`] fixed pseudo-random values. Both
/// sides are evaluated in Rust at every point ([`GoalEval`]), so the set is
/// not cut down to what a kernel evaluation could afford.
fn points(divisors: &[u128]) -> Vec<u128> {
    let top = u128::from(u64::MAX);
    let mut out = vec![0, 1, (1 << 63) - 1, 1 << 63, top];
    for &d in divisors {
        out.extend([d.saturating_sub(1), d, d + 1]);
        for i in 0..d.min(64) {
            out.push(top - i);
        }
        let q = top / d * d;
        out.extend([q, q.saturating_sub(1)]);
    }
    let mut s: u64 = 0x9e37_79b9_7f4a_7c15;
    for _ in 0..RANDOM_POINTS {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        out.push(u128::from(s));
    }
    out.retain(|v| *v <= top);
    out.sort_unstable();
    out.dedup();
    out
}

fn divisors(f: &Formula, out: &mut Vec<u128>) {
    if let Formula::BvUDiv(_, r, _) = f
        && let Some((d, _)) = eval_bv(r, &no_vars)
        && d != 0
        && !out.contains(&d)
    {
        out.push(d);
    }
    for c in children(f) {
        divisors(c, out);
    }
}

/// The value of leaf `i` at point `x`.
fn leaf_value(i: usize, x: u128) -> u128 {
    if i == 0 {
        x
    } else {
        (x.rotate_left(17 * i as u32) ^ 0x5555_5555_5555_5555) & u128::from(u64::MAX)
    }
}

/// The longest list [`GoalEval`] evaluates (the 128-bit multiply-high
/// product is the widest value the walk admits).
const MAX_LIST: usize = 128;

fn as_u128(bits: &[bool]) -> Option<u128> {
    (bits.len() <= 128).then(|| bits.iter().rev().fold(0u128, |n, &b| (n << 1) | u128::from(b)))
}

fn of_u128(v: u128, len: usize) -> Vec<bool> {
    (0..len).map(|k| k < 128 && (v >> k) & 1 == 1).collect()
}

/// `a + b + c` over equal lengths (the `Clean.BVI.addRecM` ripple adder).
fn ripple(a: &[bool], b: &[bool], mut c: bool) -> Option<Vec<bool>> {
    if a.len() != b.len() {
        return None;
    }
    let mut out = Vec::with_capacity(a.len());
    for (&x, &y) in a.iter().zip(b) {
        out.push(x ^ y ^ c);
        c = (x & y) | (x & c) | (y & c);
    }
    Some(out)
}

/// The evaluator the differential reads a reflected goal side with: an
/// independent Rust reading of the `Clean.BVC` definitions on closed lists
/// (lists least significant first; every `BVC_LEAFBIT_*` fixed by `bits`).
/// It is not the kernel and decides nothing: it covers the heads the
/// const-div goal reflection emits, and only where both operands have one
/// length (a length-mismatched or unknown head is `None`, which declines).
/// `goal_evaluator_agrees_with_the_kernel` compares it with the kernel's own
/// evaluation of each head and of the positives' goal sides; that comparison
/// is what makes a disagreement here a reflection bug rather than a model one.
pub(crate) struct GoalEval<'a> {
    bits: &'a HashMap<Name, bool>,
    lists: HashMap<Expr, Option<Vec<bool>>>,
    bvfs: HashMap<Expr, Option<Vec<bool>>>,
}

fn const_name(e: &Expr) -> Option<String> {
    match e.get_app_fn().kind() {
        ExprKind::Const(n, _) => Some(n.to_string()),
        _ => None,
    }
}

/// A closed natural: a `Nat.zero` / `Nat.succ` chain or a small literal.
fn nat_value(mut e: &Expr) -> Option<u128> {
    let mut n = 0u128;
    loop {
        match e.kind() {
            ExprKind::Lit(Literal::Nat(BigNat::Small(v))) => return n.checked_add(u128::from(*v)),
            ExprKind::Const(c, _) if c.to_string() == "Nat.zero" => return Some(n),
            ExprKind::App(f, a) if matches!(f.kind(), ExprKind::Const(c, _) if c.to_string() == "Nat.succ") =>
            {
                n = n.checked_add(1)?;
                e = a;
            }
            _ => return None,
        }
    }
}

impl<'a> GoalEval<'a> {
    pub(crate) fn new(bits: &'a HashMap<Name, bool>) -> Self {
        Self { bits, lists: HashMap::new(), bvfs: HashMap::new() }
    }

    /// The value of a `List Bool` term.
    pub(crate) fn list(&mut self, e: &Expr) -> Option<Vec<bool>> {
        if let Some(v) = self.lists.get(e) {
            return v.clone();
        }
        let v = self.list_uncached(e).filter(|v| v.len() <= MAX_LIST);
        self.lists.insert(e.clone(), v.clone());
        v
    }

    fn list_uncached(&mut self, e: &Expr) -> Option<Vec<bool>> {
        let head = const_name(e)?;
        let args = e.get_app_args();
        match (head.as_str(), args.len()) {
            ("List.nil", 1) | ("List.cons", 3) => {
                let mut out = Vec::new();
                let mut cur = e;
                loop {
                    let a = cur.get_app_args();
                    match (const_name(cur)?.as_str(), a.len()) {
                        ("List.nil", 1) => return Some(out),
                        ("List.cons", 3) if out.len() < MAX_LIST => {
                            out.push(self.boolean(a[1])?);
                            cur = a[2];
                        }
                        ("List.cons", 3) => return None,
                        _ => {
                            out.extend(self.list(cur)?);
                            return Some(out);
                        }
                    }
                }
            }
            ("Clean.BVC.bvfEval", 1) => self.bvf(args[0]),
            ("Clean.BVC.bvIteVal", 3) => {
                if self.boolean(args[0])? {
                    self.list(args[1])
                } else {
                    self.list(args[2])
                }
            }
            ("Clean.BVC.bvNot", 1) => Some(self.list(args[0])?.iter().map(|b| !b).collect()),
            ("Clean.BVC.bvAllFalse", 1) => Some(vec![false; self.list(args[0])?.len()]),
            ("Clean.BVI.btail", 1) => Some(self.list(args[0])?.into_iter().skip(1).collect()),
            ("Clean.BVC.bvZeroExt", 2) => {
                let mut v = self.list(args[0])?;
                let k = usize::try_from(nat_value(args[1])?).ok()?;
                (v.len() + k <= MAX_LIST).then(|| {
                    v.resize(v.len() + k, false);
                    v
                })
            }
            ("Clean.BVC.bvTakeLen", 2) => {
                let n = self.list(args[0])?.len();
                let v = self.list(args[1])?;
                (n <= v.len()).then(|| v[..n].to_vec())
            }
            ("Clean.BVC.bvAppend", 2) => {
                let mut v = self.list(args[0])?;
                v.extend(self.list(args[1])?);
                Some(v)
            }
            // `iter k l` (`Nat.rec … btail`): `l` with its `k` low bits dropped.
            ("Nat.rec", 4) => {
                let k = nat_value(args[3])?;
                if *e != theory::iter(args[3].clone(), args[1].clone()) || k > MAX_LIST as u128 {
                    return None;
                }
                Some(self.list(args[1])?.into_iter().skip(k as usize).collect())
            }
            _ => None,
        }
    }

    fn pair(&mut self, a: &Expr, b: &Expr) -> Option<(Vec<bool>, Vec<bool>)> {
        let x = self.bvf(a)?;
        let y = self.bvf(b)?;
        (x.len() == y.len()).then_some((x, y))
    }

    /// `bvfEval f`.
    fn bvf(&mut self, f: &Expr) -> Option<Vec<bool>> {
        if let Some(v) = self.bvfs.get(f) {
            return v.clone();
        }
        let v = self.bvf_uncached(f).filter(|v| v.len() <= MAX_LIST);
        self.bvfs.insert(f.clone(), v.clone());
        v
    }

    fn bvf_uncached(&mut self, f: &Expr) -> Option<Vec<bool>> {
        let head = const_name(f)?;
        let args = f.get_app_args();
        let zip = |a: Vec<bool>, b: Vec<bool>, op: fn(bool, bool) -> bool| -> Vec<bool> {
            a.into_iter().zip(b).map(|(x, y)| op(x, y)).collect()
        };
        match (head.as_str(), args.len()) {
            ("Clean.BVC.BvF.Leaf", 1) | ("Clean.BVC.BvF.Const", 1) => self.list(args[0]),
            ("Clean.BVC.BvF.Add", 2) => {
                let (a, b) = self.pair(args[0], args[1])?;
                ripple(&a, &b, false)
            }
            ("Clean.BVC.BvF.Sub", 2) => {
                let (a, b) = self.pair(args[0], args[1])?;
                let nb: Vec<bool> = b.iter().map(|x| !x).collect();
                ripple(&a, &nb, true)
            }
            ("Clean.BVC.BvF.And", 2) => {
                let (a, b) = self.pair(args[0], args[1])?;
                Some(zip(a, b, |x, y| x & y))
            }
            ("Clean.BVC.BvF.Or", 2) => {
                let (a, b) = self.pair(args[0], args[1])?;
                Some(zip(a, b, |x, y| x | y))
            }
            ("Clean.BVC.BvF.Xor", 2) => {
                let (a, b) = self.pair(args[0], args[1])?;
                Some(zip(a, b, |x, y| x ^ y))
            }
            ("Clean.BVC.BvF.Mul", 2) => {
                let (a, b) = self.pair(args[0], args[1])?;
                let p = as_u128(&a)?.wrapping_mul(as_u128(&b)?);
                Some(of_u128(p, a.len()))
            }
            // `bvDiv`: `Nat.div`, so a zero divisor gives zero.
            ("Clean.BVC.BvF.Div", 2) => {
                let (a, b) = self.pair(args[0], args[1])?;
                let (x, y) = (as_u128(&a)?, as_u128(&b)?);
                Some(of_u128(x.checked_div(y).unwrap_or(0), a.len()))
            }
            ("Clean.BVC.BvF.Shl", 2) | ("Clean.BVC.BvF.LShr", 2) => {
                let a = self.bvf(args[0])?;
                let n = as_u128(&self.bvf(args[1])?)?;
                let x = as_u128(&a)?;
                let v = if n >= a.len() as u128 {
                    0
                } else if head.ends_with("Shl") {
                    x << n
                } else {
                    x >> n
                };
                Some(of_u128(v, a.len()))
            }
            ("Clean.BVC.BvF.ZeroExt", 2) => {
                let mut v = self.bvf(args[0])?;
                let k = usize::try_from(nat_value(args[1])?).ok()?;
                (v.len() + k <= MAX_LIST).then(|| {
                    v.resize(v.len() + k, false);
                    v
                })
            }
            // `bvTakeLen (eval tag) (eval e)`.
            ("Clean.BVC.BvF.ExtractLow", 2) => {
                let v = self.bvf(args[0])?;
                let n = self.bvf(args[1])?.len();
                (n <= v.len()).then(|| v[..n].to_vec())
            }
            _ => None,
        }
    }

    /// The value of a `Bool` term.
    fn boolean(&mut self, e: &Expr) -> Option<bool> {
        if let ExprKind::Const(n, _) = e.kind() {
            return match n.to_string().as_str() {
                "Bool.true" => Some(true),
                "Bool.false" => Some(false),
                _ => self.bits.get(n).copied(),
            };
        }
        let head = const_name(e)?;
        let args = e.get_app_args();
        let cmp = |s: &mut Self, a: &Expr, b: &Expr| -> Option<(Vec<bool>, Vec<bool>)> {
            let x = s.list(a)?;
            let y = s.list(b)?;
            (x.len() == y.len()).then_some((x, y))
        };
        match (head.as_str(), args.len()) {
            ("Bool.not", 1) => Some(!self.boolean(args[0])?),
            ("Bool.and", 2) => Some(self.boolean(args[0])? & self.boolean(args[1])?),
            ("Bool.or", 2) => Some(self.boolean(args[0])? | self.boolean(args[1])?),
            ("Bool.xor", 2) => Some(self.boolean(args[0])? ^ self.boolean(args[1])?),
            // `Bool.rec motive false_case true_case major`.
            ("Bool.rec", 4) => {
                if self.boolean(args[3])? {
                    self.boolean(args[2])
                } else {
                    self.boolean(args[1])
                }
            }
            ("Clean.BVC.bvBeq", 2) => {
                let (a, b) = cmp(self, args[0], args[1])?;
                Some(a == b)
            }
            ("Clean.BVC.bvIsZero", 1) => Some(self.list(args[0])?.iter().all(|b| !b)),
            ("Clean.BVC.bvUlt", 2) | ("Clean.BVC.bvULe", 2) => {
                let (a, b) = cmp(self, args[0], args[1])?;
                let (x, y) = (as_u128(&a)?, as_u128(&b)?);
                Some(if head.ends_with("Ult") { x < y } else { x <= y })
            }
            ("Clean.BVC.bvSLtReal", 2) => {
                let (a, b) = cmp(self, args[0], args[1])?;
                let w = a.len();
                if !(1..128).contains(&w) {
                    return None;
                }
                let signed = |v: &[bool]| {
                    as_u128(v).map(|u| if v[w - 1] { u as i128 - (1i128 << w) } else { u as i128 })
                };
                Some(signed(&a)? < signed(&b)?)
            }
            _ => None,
        }
    }
}

/// Decline-only: at each point, both Formula sides of every item evaluated
/// in Rust must equal the reflected goal side evaluated by [`GoalEval`] with
/// the leaf bits fixed. `Err` names the first disagreement (a reflection
/// bug) or a side the check cannot evaluate. `Ok` is the number of side
/// checks.
pub(crate) fn differential(
    items: &[(Formula, Formula)],
    sides: &[(Expr, Expr)],
    leaves: &[(String, u32)],
) -> Result<usize, String> {
    let mut ds = Vec::new();
    for (l, r) in items {
        divisors(l, &mut ds);
        divisors(r, &mut ds);
    }
    let mut checks = 0;
    for x in points(&ds) {
        let mut vals: HashMap<String, u128> = HashMap::new();
        let mut bits: HashMap<Name, bool> = HashMap::new();
        for (i, (name, w)) in leaves.iter().enumerate() {
            let v = leaf_value(i, x) & mask(*w);
            vals.insert(name.clone(), v);
            let list = add_comm::bit_leaf(name, *w);
            for (k, b) in
                spine(&list).ok_or("differential: a leaf wider than 64")?.iter().enumerate()
            {
                if let ExprKind::Const(n, _) = b.kind() {
                    bits.insert(n.clone(), (v >> k) & 1 == 1);
                }
            }
        }
        let lookup = |name: &str| vals.get(name).copied();
        let mut ev = GoalEval::new(&bits);
        for ((l, r), (gl, gr)) in items.iter().zip(sides) {
            for (f, g) in [(l, gl), (r, gr)] {
                let (v, w) = eval_bv(f, &lookup).ok_or("differential: a side does not evaluate")?;
                let got = ev.list(g).ok_or_else(|| {
                    format!("differential: at {x:#x} a goal side does not evaluate")
                })?;
                if got.len() != w as usize || as_u128(&got) != Some(v) {
                    return Err(format!(
                        "differential: at {x:#x} the goal side is {:?} ({} bits), the Formula \
                         {v:#x} ({w} bits)",
                        as_u128(&got),
                        got.len()
                    ));
                }
                checks += 1;
            }
        }
    }
    Ok(checks)
}

// ── admission ────────────────────────────────────────────────────────────────

/// What the kernel admitted: the label and the declared goal.
pub(crate) struct Admitted {
    pub(crate) theorem: String,
    pub(crate) goal: Expr,
}

/// Build the obligation, run the differential (filter `On`), check it in the
/// kernel and name it.
pub(crate) fn prove(
    items: &[(Formula, Formula)],
    filter: BranchFilter,
) -> Result<ProvenEvidence, Decline> {
    prove_goal(items, filter)
        .map(|a| ProvenEvidence::KernelInstantiated { theorem: a.theorem, original: None })
}

/// [`prove`], returning the admitted goal with the label.
pub(crate) fn prove_goal(
    items: &[(Formula, Formula)],
    filter: BranchFilter,
) -> Result<Admitted, Decline> {
    let trace = std::env::var_os("TRUST_GATE_TRACE").is_some();
    let built = on_route_stack(|| obligation(items, filter));
    #[allow(unused_mut)]
    let mut ob = match built {
        Ok(o) => o,
        Err(d) => {
            if trace {
                eprintln!("[const-div] declined: {d:?}");
            }
            return Err(d);
        }
    };
    #[cfg(test)]
    let axioms = std::mem::take(&mut ob.axioms);
    let Obligation { goal, proof, sides, leaves, .. } = ob;
    // The differential runs before the kernel: it is Rust evaluation only
    // (`GoalEval`), so a disagreement declines without kernel work.
    if filter == BranchFilter::On {
        #[cfg(test)]
        let sides = forged_sides(sides.clone());
        if let Err(why) = differential(items, &sides, &leaves) {
            if trace {
                eprintln!("[const-div] declined: {why}");
            }
            return Err(Decline::Filter(why));
        }
    }
    let checked = run_recheck_thread("trust-const-div", move || {
        let mut env = const_div_env(&leaves).map_err(Decline::Environment)?;
        #[cfg(test)]
        for (name, ty) in axioms {
            env.add_decl(clean_kernel::Declaration::Axiom {
                name,
                level_params: vec![],
                type_: ty,
            })
            .map_err(|e| Decline::Environment(format!("{e:?}")))?;
        }
        strength::admit_obligation(&mut env, goal.clone(), proof.clone())
            .map_err(Decline::Kernel)?;
        Ok(Admitted { theorem: theory::label(&env, &proof), goal })
    })
    .map_err(|e| Decline::Environment(e.to_string()))
    .and_then(|r| r);
    if trace && let Err(d) = &checked {
        eprintln!("[const-div] declined: {d:?}");
    }
    checked
}

/// The route: `Some(KernelInstantiated)` when the kernel accepts the
/// conjunction, `None` otherwise. The step-(5) dispatch (`branch_dispatch.rs`)
/// calls it on the ORIGINAL conjunction (stage B2).
pub(crate) fn try_conjunction(items: &[(Formula, Formula)]) -> Option<ProvenEvidence> {
    prove(items, BranchFilter::On).ok()
}

// ── the step-(4) rewrite ─────────────────────────────────────────────────────

/// What [`const_div_rewrite`] replaced, with the kernel-admitted theorem
/// that justifies it: each `(core, BvUDiv(x, d))` pair is an item of one
/// admitted conjunction `R(core) = R(BvUDiv(x, d))`, and `goal` is that
/// conjunction exactly as the kernel admitted it. A consumer checks
/// [`ConstDivCert::binds`] before it uses the rewritten formula.
#[derive(Clone, Debug)]
pub(crate) struct ConstDivCert {
    pub(crate) replaced: Vec<(Formula, Formula)>,
    /// How many subterms [`replace`] replaced: at least one per pair (the
    /// rewrite is declined otherwise), more where a quotient is shared.
    pub(crate) sites: usize,
    pub(crate) theorem: String,
    pub(crate) goal: Expr,
}

impl ConstDivCert {
    /// Is the admitted goal exactly the goal of `replaced` (rebuilt here,
    /// from the pairs alone)?
    pub(crate) fn binds(&self) -> bool {
        on_route_stack(|| goal_of(&self.replaced)).is_ok_and(|(g, _, _)| g == self.goal)
    }
}

/// The magic-quotient subterm shapes: `ZeroExt(Extract{63,k}(Q), k)` with
/// `Q` the multiply-high of a closed multiplier, or that plus the halved
/// difference (`lsr #1` or UBFM #1). Returns the replacement
/// `BvUDiv(x, d)`.
fn magic_formula(f: &Formula) -> Option<Formula> {
    let Formula::BvZeroExt(e, k) = f else { return None };
    let Formula::BvExtract { inner, high: 63, low } = &**e else { return None };
    if low != k {
        return None;
    }
    let mh = |q: &Formula| -> Option<(Formula, u128)> {
        let (a, b) = umulh_shape(q)?;
        let (mval, w) = eval_bv(b, &no_vars).filter(|_| !has_var(b))?;
        (w == 64 && memory_reflection::width(a) == Some(64)).then(|| (a.clone(), mval))
    };
    let (x, mval, add) = if let Some((x, m)) = mh(inner) {
        (x, m, false)
    } else {
        let Formula::BvAdd(u, h, 64) = &**inner else { return None };
        let (x, m) = mh(u)?;
        let diff = Formula::BvSub(Box::new(x.clone()), u.clone(), 64);
        let halved = match &**h {
            Formula::BvLShr(s, one, 64) => {
                **s == diff && matches!(**one, Formula::BitVec { value: 1, width: 64 })
            }
            Formula::BvZeroExt(s, 1) => {
                matches!(&**s, Formula::BvExtract { inner, high: 63, low: 1 } if **inner == diff)
            }
            _ => false,
        };
        if !halved {
            return None;
        }
        (x, m, true)
    };
    let (d, _) = magic_params(mval, *k, add)?;
    Some(Formula::BvUDiv(
        Box::new(x),
        Box::new(Formula::BitVec { value: i128::try_from(d).ok()?, width: 64 }),
        64,
    ))
}

fn collect_magic(f: &Formula, out: &mut Vec<(Formula, Formula)>) {
    if let Some(r) = magic_formula(f) {
        if !out.iter().any(|(c, _)| c == f) {
            out.push((f.clone(), r));
        }
        return;
    }
    for c in children(f) {
        collect_magic(c, out);
    }
}

/// `f` with every occurrence of a pair's left side replaced by its right
/// side, `hits[i]` counting the occurrences of `map[i]`. It descends into
/// exactly the nodes [`children`] lists, the nodes [`collect_magic`]
/// searches, so every pair that search found is replaced wherever it occurs
/// (`replace_reaches_every_node_the_search_reaches`); a node [`children`]
/// does not open is a leaf to both.
fn replace(f: &Formula, map: &[(Formula, Formula)], hits: &mut [usize]) -> Formula {
    if let Some(i) = map.iter().position(|(c, _)| c == f) {
        hits[i] += 1;
        return map[i].1.clone();
    }
    let mut go = |x: &Formula| Box::new(replace(x, map, hits));
    match f {
        Formula::Not(x) => Formula::Not(go(x)),
        Formula::BvNot(x, w) => Formula::BvNot(go(x), *w),
        Formula::BvZeroExt(x, k) => Formula::BvZeroExt(go(x), *k),
        Formula::BvSignExt(x, k) => Formula::BvSignExt(go(x), *k),
        Formula::BvExtract { inner, high, low } => {
            Formula::BvExtract { inner: go(inner), high: *high, low: *low }
        }
        Formula::And(xs) => Formula::And(xs.iter().map(|x| *go(x)).collect()),
        Formula::Or(xs) => Formula::Or(xs.iter().map(|x| *go(x)).collect()),
        Formula::Ite(c, x, y) => Formula::Ite(go(c), go(x), go(y)),
        Formula::Store(a, i, v) => Formula::Store(go(a), go(i), go(v)),
        Formula::Eq(l, r) => Formula::Eq(go(l), go(r)),
        Formula::Implies(l, r) => Formula::Implies(go(l), go(r)),
        Formula::BvAdd(l, r, w) => Formula::BvAdd(go(l), go(r), *w),
        Formula::BvSub(l, r, w) => Formula::BvSub(go(l), go(r), *w),
        Formula::BvMul(l, r, w) => Formula::BvMul(go(l), go(r), *w),
        Formula::BvUDiv(l, r, w) => Formula::BvUDiv(go(l), go(r), *w),
        Formula::BvSDiv(l, r, w) => Formula::BvSDiv(go(l), go(r), *w),
        Formula::BvURem(l, r, w) => Formula::BvURem(go(l), go(r), *w),
        Formula::BvSRem(l, r, w) => Formula::BvSRem(go(l), go(r), *w),
        Formula::BvAnd(l, r, w) => Formula::BvAnd(go(l), go(r), *w),
        Formula::BvOr(l, r, w) => Formula::BvOr(go(l), go(r), *w),
        Formula::BvXor(l, r, w) => Formula::BvXor(go(l), go(r), *w),
        Formula::BvShl(l, r, w) => Formula::BvShl(go(l), go(r), *w),
        Formula::BvLShr(l, r, w) => Formula::BvLShr(go(l), go(r), *w),
        Formula::BvAShr(l, r, w) => Formula::BvAShr(go(l), go(r), *w),
        Formula::BvULt(l, r, w) => Formula::BvULt(go(l), go(r), *w),
        Formula::BvULe(l, r, w) => Formula::BvULe(go(l), go(r), *w),
        Formula::BvSLt(l, r, w) => Formula::BvSLt(go(l), go(r), *w),
        Formula::BvSLe(l, r, w) => Formula::BvSLe(go(l), go(r), *w),
        Formula::BvConcat(l, r) => Formula::BvConcat(go(l), go(r)),
        Formula::Select(l, r) => Formula::Select(go(l), go(r)),
        other => other.clone(),
    }
}

/// The step-(4) rewrite: `m` with each magic quotient replaced by
/// `BvUDiv(x, d)`, and the kernel-admitted conjunction
/// `R(core_i) = R(BvUDiv(x_i, d_i))` that justifies it (the faithful
/// division on the right). `None` when there is no magic quotient, when the
/// differential or the kernel declines, or when the admitted goal does not
/// bind the replaced pairs ([`ConstDivCert::binds`], checked here and only
/// here).
pub(crate) fn const_div_rewrite(m: &Formula) -> Option<(Formula, ConstDivCert)> {
    rewrite_with(m, BranchFilter::On).ok().filter(|(_, cert)| cert.binds())
}

/// At most this many magic quotients are replaced in one left side; a
/// side with more is decided as before (the hook's kernel work stays bounded
/// by the walk's node cap and this count).
const MAX_REPLACED: usize = 8;

/// [`const_div_rewrite`] under `filter` (`Off` lets a test show the kernel,
/// not the differential, refusing a wrong replacement), without the binding
/// check; `Err(None)` when there is nothing to rewrite.
pub(crate) fn rewrite_with(
    m: &Formula,
    filter: BranchFilter,
) -> Result<(Formula, ConstDivCert), Option<Decline>> {
    let mut found = Vec::new();
    collect_magic(m, &mut found);
    if found.is_empty() {
        return Err(None);
    }
    if found.len() > MAX_REPLACED {
        return Err(Some(Decline::Filter("const-div: too many magic quotients".into())));
    }
    #[allow(unused_mut)]
    let Admitted { theorem, mut goal } = prove_goal(&found, filter).map_err(Some)?;
    #[cfg(test)]
    if mutant() == Mutant::ForeignGoal {
        goal = goal_of(&[(lit64(0), lit64(0))]).map_err(|e| Some(Decline::Filter(e)))?.0;
    }
    let mut hits = vec![0; found.len()];
    let rewritten = replace(m, &found, &mut hits);
    if hits.contains(&0) {
        // Unreachable while `replace` opens every node `collect_magic` does;
        // a certified pair left in place would make the note overclaim.
        return Err(Some(Decline::Filter(
            "const-div: a certified quotient was not replaced".into(),
        )));
    }
    let sites = hits.iter().sum();
    Ok((rewritten, ConstDivCert { replaced: found, sites, theorem, goal }))
}

// ── the step-(4) hook ────────────────────────────────────────────────────────

/// The call-event gate's step-(4) hook (`call_event.rs`, DECISION_QUEUE
/// CONSTDIV-1), called once per item on the item's LEFT side `m` only (the
/// machine side, under reach guards that may carry spec formulas; never the
/// right side `s`):
/// `Some((m', note))` when [`const_div_rewrite`] gives `m'` (every magic
/// quotient of `m` replaced by `BvUDiv(x, d)`, each replacement an item of
/// one kernel-admitted conjunction that binds the replaced pairs, after the
/// differential agreed). The gate then has ay decide `m' == s` in place of
/// `m == s`, and appends `note` to the function's O4 detail, naming the item
/// and the admitted theorems. `None` otherwise, and the gate decides
/// `m == s` exactly as before.
pub(crate) fn step4_rewrite(name: &str, m: &Formula) -> Option<(Formula, String)> {
    #[cfg(feature = "test-hooks")]
    if HOOK_OFF.with(std::cell::Cell::get) {
        record_call(name, m, None);
        return None;
    }
    let out = const_div_rewrite(m).map(|(rewritten, cert)| {
        let note = format!(
            "; {name} was decided by ay on its CONSTDIV rewrite ({} magic quotient(s) replaced \
             by `x / d` at {} site(s), the replacement kernel-admitted: {})",
            cert.replaced.len(),
            cert.sites,
            cert.theorem
        );
        (rewritten, note)
    });
    #[cfg(feature = "test-hooks")]
    record_call(name, m, out.as_ref().map(|(_, note)| note.clone()));
    out
}

#[cfg(feature = "test-hooks")]
thread_local! {
    static HOOK_OFF: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static HOOK_CALLS: std::cell::RefCell<Option<Vec<HookCall>>> =
        const { std::cell::RefCell::new(None) };
}

/// One call of [`step4_rewrite`] seen by [`record_const_div_rewrites`]: the
/// item's name, the left side it was handed and the note when it rewrote.
#[cfg(feature = "test-hooks")]
pub type HookCall = (String, Formula, Option<String>);

#[cfg(feature = "test-hooks")]
fn record_call(name: &str, m: &Formula, note: Option<String>) {
    HOOK_CALLS.with(|calls| {
        if let Some(calls) = calls.borrow_mut().as_mut() {
            calls.push((name.to_string(), m.clone(), note));
        }
    });
}

/// TEST HOOK (`test-hooks` only): run `body` and return, with its result,
/// every call the call-event gate made to the step-(4) hook on THIS thread
/// while it ran. It observes the hook; it grants nothing and changes no
/// verdict.
#[cfg(feature = "test-hooks")]
#[doc(hidden)]
pub fn record_const_div_rewrites<R>(body: impl FnOnce() -> R) -> (R, Vec<HookCall>) {
    let outer = HOOK_CALLS.with(|calls| calls.borrow_mut().replace(Vec::new()));
    let result = body();
    let calls = HOOK_CALLS.with(|calls| std::mem::replace(&mut *calls.borrow_mut(), outer));
    (result, calls.unwrap_or_default())
}

/// TEST HOOK (`test-hooks` only): run `body` with the step-(4) hook off on
/// THIS thread (every call returns `None` without looking), so a gate test
/// can pin that the gate without the hook decides as it did before it. It can
/// only take a rewrite away.
#[cfg(feature = "test-hooks")]
#[doc(hidden)]
pub fn without_const_div_rewrite<R>(body: impl FnOnce() -> R) -> R {
    let outer = HOOK_OFF.with(|off| off.replace(true));
    let result = body();
    HOOK_OFF.with(|off| off.set(outer));
    result
}

#[cfg(test)]
#[path = "const_div/tests.rs"]
mod tests;
