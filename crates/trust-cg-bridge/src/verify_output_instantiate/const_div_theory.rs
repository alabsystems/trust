// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The constant-division theory `Trust.BVD.*` (CONSTDIV, stage A): the value
//! lemmas behind the AArch64 magic-multiply division and remainder, as
//! kernel-checked `Declaration::Theorem`s.
//!
//! # What is proved
//!
//! `V` is `bvToNat`, `L` is `bvLen`, `P k` is `bvTwoPow k`, `ZX l k` is
//! `bvZeroExt l k`, and `iter k l` is `Nat.rec l (fun _ ih => btail ih) k`
//! (drop the `k` low bits; `iter 2 l` is `btail (btail l)` by iota).
//!
//! ```text
//! mod_eq_of_lt   : ∀ a n, a < n → a % n = a
//! div_one        : ∀ a, a / 1 = a
//! div_div        : ∀ a b c, 0 < b → 0 < c → a / b / c = a / (b * c)
//! div_le_self    : ∀ a c, 0 < c → a / c ≤ a
//! le_add_cancel  : ∀ a b c, a + c ≤ b + c → a ≤ b
//! mul_lt_mul     : ∀ a b c d, a < c → b < d → a * b < c * d
//! gm_div         : ∀ x d M p e n, 0 < d → d * M = P p + e →
//!                  Nat.ble (e * P n + 1) (P p + e) = true → x < P n →
//!                  x * M / P p = x / d
//! addback_split  : ∀ X M Q N, 0 < Q → M + N = Q →
//!                  X = X * M / Q + (X * M % Q + X * N) / Q
//! addback_mul    : ∀ X M Q D, 0 < Q → X = X * M / Q + D →
//!                  X * M / Q + D / 2 = X * (Q + M) / (2 * Q)
//! toNat_lt       : ∀ l, V l < P (L l)
//! btail_val      : ∀ l, V (btail l) = V l / 2
//! btail_len      : ∀ l m, L l = succ m → L (btail l) = m
//! iter_val       : ∀ k l, V (iter k l) = V l / P k
//! iter_len       : ∀ k m l, L l = m + k → L (iter k l) = m
//! zx_val         : ∀ l k, V (ZX l k) = V l
//! zx_len         : ∀ l k, L (ZX l k) = L l + k
//! n2b_div_val    : ∀ a v, 0 < v → V (natToBvAux (L a) (V a / v)) = V a / v
//! umulh_val      : ∀ x y m, L x = succ m → L y = succ m →
//!                  V (U x y m) = V x * V y / P (succ m)
//! umulh_len      : ∀ x y m, L x = succ m → L y = succ m → L (U x y m) = succ m
//!   where U x y m := iter (succ m) (bvMul (ZX x (succ m)) (ZX y (succ m)))
//! lshr_k         : ∀ S n k, V n = k → V ⟦LShr S (Const n)⟧ = V ⟦S⟧ / P k
//! ubfm_k         : ∀ S k, V ⟦ZeroExt (Const (iter k ⟦S⟧)) k⟧ = V ⟦S⟧ / P k
//! magic_noadd    : the quotient `ZeroExt (Const (iter k ⟦UMH X mk m⟧)) k`
//!                  is `Div X (Const c)` (premises below)
//! magic_addback  : the quotient `ZeroExt (Const (iter k ⟦Add (UMH X mk m) H⟧)) k`,
//!                  `V ⟦H⟧ = V ⟦Sub X (UMH X mk m)⟧ / 2`, is `Div X (Const c)`
//! rem_tail       : ⟦Add X (Sub D (Shl D (Const n)))⟧ = ⟦Sub X (Mul D (Const c))⟧
//!                  when succ (V c) = P (V n)
//! ```
//!
//! `⟦e⟧` is `bvfEval e`, and `UMH X mk m` is the AArch64 `umulh` image
//! `Const (iter (succ m) ⟦Mul (ZeroExt X (succ m)) (ZeroExt (Const mk) (succ m))⟧)`.
//! The magic theorems are stated over `BvF` terms in exactly the shape the
//! reflection builds, so an instance's type meets the reflected core by
//! `bvfEval` unfolding and iota on `iter` only.
//!
//! `magic_noadd` takes `L ⟦X⟧ = succ m`, `L mk = succ m`, `j + k = succ m`,
//! `0 < V c`, `V c * V mk = P (succ m + k) + e` and the band
//! `Nat.ble (e * P (succ m) + 1) (P (succ m + k) + e) = true`.
//! `magic_addback` takes the same with the multiplier `P (succ m) + V mk` and
//! `P (succ (succ m) + k)`. Every closed premise is checked by the kernel
//! (`Eq.refl` on computed literals), so a wrong divisor, shift, magic or
//! error term only makes an instance ill-typed.
//!
//! The add-back form's two range facts, `mh ≤ x` and `mh + h < 2^64`, are
//! derived here from `L mk = succ m` alone (`addback_split`: `x = mh + D`
//! with `D` an explicit quotient; then `V (x - mh) = D`), never taken as a
//! premise.
//!
//! # Authority
//!
//! None besides the kernel: [`register`] adds each statement and proof as a
//! `Declaration::Theorem`, so `add_decl` type-checks it, and [`build_base`]
//! audits every theorem here and every citation ([`audited`]) with
//! `add_comm::audit_theorems` (a proved `Theorem`, empty axiom and
//! foundational closure). The `+`/`*` rearrangements come from the untrusted
//! normaliser `nat_ring`; the kernel checks them inside each declaration.

use std::collections::HashSet;
use std::sync::OnceLock;

use clean_kernel::expr::UsedConstants;
use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, Declaration, Environment, Expr, FVarId};

use super::add_comm::{self, audit_theorems};
use super::bv_value::{btn, names as bvv};
use super::kterm::{
    Fresh, addm, bool_ty, btail, bv_append, bv_shl, bvlen, bvmul, congr_arg, eq, eq_subst, lams,
    lb, le_refl, le_step, list_rec_prop, nadd, nat, nat_pred, nat_rec_prop, nat_rec1, nat_to_bv,
    nble, ndiv, nle, nlit, nlt, nmod, nmul, pis, repl_f, succ, symm, to_nat, two_pow, zero,
    zero_ext,
};
use super::nat_ring::{Eqn, ring_eq};
use super::{branch_theory, kx};

/// The theorems this module proves, in registration order.
pub(crate) mod names {
    pub(crate) const MOD_EQ_OF_LT: &str = "Trust.BVD.mod_eq_of_lt";
    pub(crate) const DIV_ONE: &str = "Trust.BVD.div_one";
    pub(crate) const DIV_DIV: &str = "Trust.BVD.div_div";
    pub(crate) const DIV_LE_SELF: &str = "Trust.BVD.div_le_self";
    pub(crate) const LE_ADD_CANCEL: &str = "Trust.BVD.le_add_cancel";
    pub(crate) const MUL_LT_MUL: &str = "Trust.BVD.mul_lt_mul";
    pub(crate) const GM_DIV: &str = "Trust.BVD.gm_div";
    pub(crate) const ADDBACK_SPLIT: &str = "Trust.BVD.addback_split";
    pub(crate) const ADDBACK_MUL: &str = "Trust.BVD.addback_mul";
    pub(crate) const TO_NAT_LT: &str = "Trust.BVD.toNat_lt";
    pub(crate) const BTAIL_VAL: &str = "Trust.BVD.btail_val";
    pub(crate) const BTAIL_LEN: &str = "Trust.BVD.btail_len";
    pub(crate) const ITER_VAL: &str = "Trust.BVD.iter_val";
    pub(crate) const ITER_LEN: &str = "Trust.BVD.iter_len";
    pub(crate) const ZX_VAL: &str = "Trust.BVD.zx_val";
    pub(crate) const ZX_LEN: &str = "Trust.BVD.zx_len";
    pub(crate) const N2B_DIV_VAL: &str = "Trust.BVD.n2b_div_val";
    pub(crate) const UMULH_VAL: &str = "Trust.BVD.umulh_val";
    pub(crate) const UMULH_LEN: &str = "Trust.BVD.umulh_len";
    pub(crate) const LSHR_K: &str = "Trust.BVD.lshr_k";
    pub(crate) const UBFM_K: &str = "Trust.BVD.ubfm_k";
    pub(crate) const MAGIC_NOADD: &str = "Trust.BVD.magic_noadd";
    pub(crate) const MAGIC_ADDBACK: &str = "Trust.BVD.magic_addback";
    pub(crate) const REM_TAIL: &str = "Trust.BVD.rem_tail";
    pub(crate) const ALL: [&str; 24] = [
        MOD_EQ_OF_LT,
        DIV_ONE,
        DIV_DIV,
        DIV_LE_SELF,
        LE_ADD_CANCEL,
        MUL_LT_MUL,
        GM_DIV,
        ADDBACK_SPLIT,
        ADDBACK_MUL,
        TO_NAT_LT,
        BTAIL_VAL,
        BTAIL_LEN,
        ITER_VAL,
        ITER_LEN,
        ZX_VAL,
        ZX_LEN,
        N2B_DIV_VAL,
        UMULH_VAL,
        UMULH_LEN,
        LSHR_K,
        UBFM_K,
        MAGIC_NOADD,
        MAGIC_ADDBACK,
        REM_TAIL,
    ];
}

/// The prelude theorems the proofs and the per-obligation instances cite
/// directly; [`build_base`] audits each.
pub(crate) const CITED: [&str; 12] = [
    "Nat.div_add_mod",
    "Nat.mod_lt",
    "Nat.le_trans",
    "Nat.le_add_right",
    "Nat.succ_le_succ",
    "Nat.mul_le_mul_left",
    "Nat.le_of_succ_le_succ",
    "Nat.le_of_ble_eq_true",
    "congrArg",
    "Eq.subst",
    "Eq.trans",
    "Eq.symm",
];

/// The suffix of every label this route produces.
pub(crate) const LABEL_TAIL: &str =
    "Trust.BVD constant division (magic multiply-high, kernel-checked)";

// ── small builders ───────────────────────────────────────────────────────────

fn cite(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}
fn val(e: &Expr) -> Expr {
    to_nat(e.clone())
}
fn len(e: &Expr) -> Expr {
    bvlen(e.clone())
}
fn p2(k: &Expr) -> Expr {
    two_pow(k.clone())
}
fn nat_local(fr: &mut Fresh) -> ((FVarId, Expr), Expr) {
    let (id, v) = fr.local();
    ((id, nat()), v)
}
fn list_local(fr: &mut Fresh) -> ((FVarId, Expr), Expr) {
    let (id, v) = fr.local();
    ((id, lb()), v)
}
fn bvf_ty() -> Expr {
    Expr::const_str("Clean.BVC.BvF")
}
fn bvf_local(fr: &mut Fresh) -> ((FVarId, Expr), Expr) {
    let (id, v) = fr.local();
    ((id, bvf_ty()), v)
}
fn hyp(lhs: Expr, rhs: Expr, proof: Expr) -> Eqn {
    Eqn { lhs, rhs, proof }
}
fn le_trans(a: &Expr, b: &Expr, c: &Expr, h1: Expr, h2: Expr) -> Expr {
    cite("Nat.le_trans", [a.clone(), b.clone(), c.clone(), h1, h2])
}
/// `0 < 2`, as `Nat.le 1 (succ 1)`.
fn pos_two() -> Expr {
    le_step(nlit(1), nlit(1), le_refl(nlit(1)))
}
fn eval(e: Expr) -> Expr {
    kx::evalf(e)
}

/// From `h : a ≤ b`, `a2 ≤ b2` when `a2 = a` and `b = b2` as polynomials.
fn le_rw(fr: &mut Fresh, h: Expr, a: &Expr, b: &Expr, a2: &Expr, b2: &Expr) -> Option<Expr> {
    let h = if a == a2 {
        h
    } else {
        let pa = ring_eq(fr, a, a2)?;
        let (t_id, t) = fr.local();
        let motive = lams(vec![(t_id, nat())], nle(t, b.clone()));
        eq_subst(nat(), motive, a.clone(), a2.clone(), pa.proof, h)
    };
    if b == b2 {
        return Some(h);
    }
    let pb = ring_eq(fr, b, b2)?;
    let (t_id, t) = fr.local();
    let motive = lams(vec![(t_id, nat())], nle(a2.clone(), t));
    Some(eq_subst(nat(), motive, b.clone(), b2.clone(), pb.proof, h))
}

/// From `h : a ≤ b` and `e : b = b2`, `a ≤ b2`.
fn le_subst_right(fr: &mut Fresh, a: &Expr, h: Expr, e: Eqn) -> Expr {
    let (t_id, t) = fr.local();
    let motive = lams(vec![(t_id, nat())], nle(a.clone(), t));
    eq_subst(nat(), motive, e.lhs, e.rhs, e.proof, h)
}

/// From `h : a < b` and `e : b = b2`, `a < b2`.
fn lt_subst_right(fr: &mut Fresh, a: &Expr, h: Expr, e: Eqn) -> Expr {
    let (t_id, t) = fr.local();
    let motive = lams(vec![(t_id, nat())], nlt(a.clone(), t));
    eq_subst(nat(), motive, e.lhs, e.rhs, e.proof, h)
}

/// `congrArg (fun t : List Bool => ctx t) h`, as an equation over `Nat`.
fn under_list(fr: &mut Fresh, a: &Expr, b: &Expr, h: Expr, ctx: impl Fn(Expr) -> Expr) -> Eqn {
    let (t_id, t) = fr.local();
    let f = lams(vec![(t_id, lb())], ctx(t));
    Eqn {
        lhs: ctx(a.clone()),
        rhs: ctx(b.clone()),
        proof: congr_arg(lb(), nat(), a.clone(), b.clone(), f, h),
    }
}

/// `iter k l := Nat.rec.{1} (fun _ => List Bool) l (fun _ ih => btail ih) k`,
/// the list without its `k` low bits.
pub(crate) fn iter(k: Expr, l: Expr) -> Expr {
    let mut fr = Fresh::new();
    let motive = {
        let (w_id, _) = fr.local();
        lams(vec![(w_id, nat())], lb())
    };
    let step = {
        let (n_id, _) = fr.local();
        let (ih_id, ih) = fr.local();
        lams(vec![(n_id, nat()), (ih_id, lb())], btail(ih))
    };
    nat_rec1(motive, l, step, k)
}

/// `UMH X mk W := Const (iter W ⟦Mul (ZeroExt X W) (ZeroExt (Const mk) W)⟧)`,
/// the reflected AArch64 `umulh X, mk` core for a constant multiplier.
pub(crate) fn umh(x: &Expr, mk: &Expr, w: &Expr) -> Expr {
    kx::const_(iter(
        w.clone(),
        eval(kx::mul(kx::zext(x.clone(), w.clone()), kx::zext(kx::const_(mk.clone()), w.clone()))),
    ))
}

/// The list `U x y W := iter W (bvMul (ZX x W) (ZX y W))`.
fn umulh_list(x: &Expr, y: &Expr, w: &Expr) -> Expr {
    iter(w.clone(), bvmul(zero_ext(x.clone(), w.clone()), zero_ext(y.clone(), w.clone())))
}

// ── Nat lemmas ───────────────────────────────────────────────────────────────

fn mod_eq_of_lt() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bn, n) = nat_local(&mut fr);
    let (h_id, h) = fr.local();
    let binders = vec![ba, bn, (h_id, nlt(a.clone(), n.clone()))];
    let ty = pis(binders.clone(), eq(nat(), nmod(a.clone(), n.clone()), a.clone()));
    let split = ring_eq(&mut fr, &a, &nadd(a.clone(), nmul(n.clone(), nlit(0))))?;
    let body = cite(bvv::MOD_UNIQUE, [a.clone(), n, nlit(0), a, h, split.proof]);
    Some((ty, lams(binders, body)))
}

fn div_one() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let ty = pis(vec![ba.clone()], eq(nat(), ndiv(a.clone(), nlit(1)), a.clone()));
    let split = ring_eq(&mut fr, &a, &nadd(nlit(0), nmul(nlit(1), a.clone())))?;
    let body =
        cite(bvv::DIV_UNIQUE, [a.clone(), nlit(1), a, nlit(0), le_refl(nlit(1)), split.proof]);
    Some((ty, lams(vec![ba], body)))
}

/// `a / b / c = a / (b * c)`: with `q1 = a / b`, `r1 = a % b`,
/// `q2 = q1 / c`, `r2 = q1 % c`, `a = (r1 + b * r2) + (b * c) * q2` and
/// `r1 + b * r2 < b * c`; then `div_unique`.
fn div_div() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bb, b) = nat_local(&mut fr);
    let (bc, c) = nat_local(&mut fr);
    let (hb_id, hb) = fr.local();
    let (hc_id, hc) = fr.local();
    let binders =
        vec![ba, bb, bc, (hb_id, nlt(nlit(0), b.clone())), (hc_id, nlt(nlit(0), c.clone()))];
    let bc_ = nmul(b.clone(), c.clone());
    let ty = pis(
        binders.clone(),
        eq(nat(), ndiv(ndiv(a.clone(), b.clone()), c.clone()), ndiv(a.clone(), bc_.clone())),
    );
    let q1 = ndiv(a.clone(), b.clone());
    let r1 = nmod(a.clone(), b.clone());
    let q2 = ndiv(q1.clone(), c.clone());
    let r2 = nmod(q1.clone(), c.clone());
    let cand = nadd(r1.clone(), nmul(b.clone(), r2.clone()));
    // The bound `cand < b * c`.
    let hr1 = cite("Nat.mod_lt", [a.clone(), b.clone(), hb]);
    let hr2 = cite("Nat.mod_lt", [q1.clone(), c.clone(), hc]);
    let br2 = nmul(b.clone(), r2.clone());
    let s1 = cite(bvv::ADD_LE_ADD_RIGHT, [succ(r1.clone()), b.clone(), br2.clone(), hr1]);
    let sr2b = nmul(b.clone(), succ(r2.clone()));
    let s1 = le_rw(
        &mut fr,
        s1,
        &nadd(succ(r1.clone()), br2.clone()),
        &nadd(b.clone(), br2),
        &succ(cand.clone()),
        &sr2b,
    )?;
    let s2 = cite("Nat.mul_le_mul_left", [succ(r2.clone()), c.clone(), b.clone(), hr2]);
    let bound = le_trans(&succ(cand.clone()), &sr2b, &bc_, s1, s2);
    // `a = cand + (b * c) * q2`.
    let e1 = Eqn::cite(
        "Nat.div_add_mod",
        vec![a.clone(), b.clone()],
        nadd(nmul(q1.clone(), b.clone()), r1.clone()),
        a.clone(),
    );
    let e2 = Eqn::cite(
        "Nat.div_add_mod",
        vec![q1.clone(), c.clone()],
        nadd(nmul(q2.clone(), c.clone()), r2.clone()),
        q1.clone(),
    );
    let (bb2, r1b) = (b.clone(), r1.clone());
    let mid = nadd(nmul(nadd(nmul(q2.clone(), c.clone()), r2.clone()), b.clone()), r1.clone());
    let split = e1
        .symm()
        .then(e2.symm().under(&mut fr, |t| nadd(nmul(t, bb2.clone()), r1b.clone())))
        .then(ring_eq(&mut fr, &mid, &nadd(cand.clone(), nmul(bc_.clone(), q2.clone())))?);
    let d = cite(bvv::DIV_UNIQUE, [a.clone(), bc_.clone(), q2.clone(), cand, bound, split.proof]);
    let body = symm(nat(), ndiv(a.clone(), bc_), q2, d);
    Some((ty, lams(binders, body)))
}

/// `a / c ≤ a`: `q ≤ q * c ≤ q * c + a % c = a`.
fn div_le_self() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bc, c) = nat_local(&mut fr);
    let (hc_id, hc) = fr.local();
    let binders = vec![ba, bc, (hc_id, nlt(nlit(0), c.clone()))];
    let q = ndiv(a.clone(), c.clone());
    let r = nmod(a.clone(), c.clone());
    let ty = pis(binders.clone(), nle(q.clone(), a.clone()));
    let qc = nmul(q.clone(), c.clone());
    let s1 = cite("Nat.mul_le_mul_left", [nlit(1), c.clone(), q.clone(), hc]);
    let s1 = le_rw(&mut fr, s1, &nmul(q.clone(), nlit(1)), &qc, &q, &qc)?;
    let s2 = cite("Nat.le_add_right", [qc.clone(), r.clone()]);
    let dam =
        Eqn::cite("Nat.div_add_mod", vec![a.clone(), c.clone()], nadd(qc.clone(), r), a.clone());
    let s2 = le_subst_right(&mut fr, &qc, s2, dam);
    let body = le_trans(&q, &qc, &a, s1, s2);
    Some((ty, lams(binders, body)))
}

/// `a + c ≤ b + c → a ≤ b`, by induction on `c` (`Nat.le_of_succ_le_succ`).
fn le_add_cancel() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bb, b) = nat_local(&mut fr);
    let (bc, c) = nat_local(&mut fr);
    let (h_id, h) = fr.local();
    let prem = |t: &Expr| nle(nadd(a.clone(), t.clone()), nadd(b.clone(), t.clone()));
    let binders = vec![ba, bb, bc, (h_id, prem(&c))];
    let concl = nle(a.clone(), b.clone());
    let ty = pis(binders.clone(), concl.clone());
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        lams(vec![bt], Expr::arrow(prem(&t), concl.clone()))
    };
    let z = {
        let (h0_id, h0) = fr.local();
        lams(vec![(h0_id, prem(&zero()))], h0)
    };
    let s = {
        let (bk, k) = nat_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let (h1_id, h1) = fr.local();
        let dec = cite(
            "Nat.le_of_succ_le_succ",
            [nadd(a.clone(), k.clone()), nadd(b.clone(), k.clone()), h1],
        );
        lams(
            vec![
                bk,
                (ih_id, Expr::arrow(prem(&k), concl.clone())),
                (h1_id, prem(&succ(k.clone()))),
            ],
            Expr::app(ih, dec),
        )
    };
    let body = Expr::app(nat_rec_prop(motive, z, s, c), h);
    Some((ty, lams(binders, body)))
}

/// `a < c → b < d → a * b < c * d`:
/// `succ (a b) ≤ succ a * succ b ≤ c * succ b ≤ c * d`.
fn mul_lt_mul() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bb, b) = nat_local(&mut fr);
    let (bc, c) = nat_local(&mut fr);
    let (bd, d) = nat_local(&mut fr);
    let (h1_id, h1) = fr.local();
    let (h2_id, h2) = fr.local();
    let binders = vec![
        ba,
        bb,
        bc,
        bd,
        (h1_id, nlt(a.clone(), c.clone())),
        (h2_id, nlt(b.clone(), d.clone())),
    ];
    let ab = nmul(a.clone(), b.clone());
    let cd = nmul(c.clone(), d.clone());
    let ty = pis(binders.clone(), nlt(ab.clone(), cd.clone()));
    let (sa, sb) = (succ(a.clone()), succ(b.clone()));
    let sab = succ(ab.clone());
    let sasb = nmul(sa.clone(), sb.clone());
    let csb = nmul(c.clone(), sb.clone());
    let s0 = cite("Nat.le_add_right", [sab.clone(), nadd(a.clone(), b.clone())]);
    let s0 = le_rw(&mut fr, s0, &sab, &nadd(sab.clone(), nadd(a, b)), &sab, &sasb)?;
    let s1 = cite("Nat.mul_le_mul_left", [sa.clone(), c.clone(), sb.clone(), h1]);
    let s1 = le_rw(&mut fr, s1, &nmul(sb.clone(), sa), &nmul(sb.clone(), c.clone()), &sasb, &csb)?;
    let s2 = cite("Nat.mul_le_mul_left", [sb, d, c, h2]);
    let t1 = le_trans(&sab, &sasb, &csb, s0, s1);
    let body = le_trans(&sab, &csb, &cd, t1, s2);
    Some((ty, lams(binders, body)))
}

/// Granlund–Montgomery: `d * M = P p + e`, the band
/// `e * P n + 1 ≤ P p + e` (as `Nat.ble`) and `x < P n` give
/// `x * M / P p = x / d`.
///
/// With `Q = x M / P p`, `R = x M % P p`, `q = x / d`, `r = x % d`:
/// `(d P p) Q + d R = (d P p) q + (P p r + e x)`, `d R < d P p`, and
/// `P p r + e x < d P p` because `e x < P p` (the band and `x < P n`) and
/// `r < d`; then `div_mod_cancel` gives `Q = q`.
fn gm_div() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bx, x) = nat_local(&mut fr);
    let (bd, d) = nat_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (bp, p) = nat_local(&mut fr);
    let (be, e) = nat_local(&mut fr);
    let (bn, n) = nat_local(&mut fr);
    let (hd_id, hd) = fr.local();
    let (hdm_id, hdm) = fr.local();
    let (hb_id, hb) = fr.local();
    let (hx_id, hx) = fr.local();
    let pp = p2(&p);
    let pn = p2(&n);
    let band_lo = nadd(nmul(e.clone(), pn.clone()), nlit(1));
    let band_hi = nadd(pp.clone(), e.clone());
    let binders = vec![
        bx,
        bd,
        bm,
        bp,
        be,
        bn,
        (hd_id, nlt(nlit(0), d.clone())),
        (hdm_id, eq(nat(), nmul(d.clone(), m.clone()), nadd(pp.clone(), e.clone()))),
        (hb_id, eq(bool_ty(), nble(band_lo.clone(), band_hi.clone()), kx::btrue())),
        (hx_id, nlt(x.clone(), pn.clone())),
    ];
    let xm = nmul(x.clone(), m.clone());
    let big_q = ndiv(xm.clone(), pp.clone());
    let big_r = nmod(xm.clone(), pp.clone());
    let q = ndiv(x.clone(), d.clone());
    let r = nmod(x.clone(), d.clone());
    let ty = pis(binders.clone(), eq(nat(), big_q.clone(), q.clone()));
    let ex = nmul(e.clone(), x.clone());
    // (a) `e x < P p`.
    let t1 = cite("Nat.mul_le_mul_left", [succ(x.clone()), pn.clone(), e.clone(), hx]);
    let esx = nmul(e.clone(), succ(x.clone()));
    let epn = nmul(e.clone(), pn.clone());
    let t2 = cite(bvv::ADD_LE_ADD_RIGHT, [esx.clone(), epn.clone(), nlit(1), t1]);
    let t3 = cite("Nat.le_of_ble_eq_true", [band_lo.clone(), band_hi.clone(), hb]);
    let t4 = le_trans(&nadd(esx.clone(), nlit(1)), &band_lo, &band_hi, t2, t3);
    let t5 = le_rw(
        &mut fr,
        t4,
        &nadd(esx, nlit(1)),
        &band_hi,
        &nadd(succ(ex.clone()), e.clone()),
        &band_hi,
    )?;
    let t6 = cite(names::LE_ADD_CANCEL, [succ(ex.clone()), pp.clone(), e.clone(), t5]);
    // (b) `P p r + e x < d P p`.
    let cand = nadd(nmul(pp.clone(), r.clone()), ex.clone());
    let dpp = nmul(d.clone(), pp.clone());
    let ppr = nmul(pp.clone(), r.clone());
    let u1 = cite(bvv::ADD_LE_ADD_RIGHT, [succ(ex.clone()), pp.clone(), ppr.clone(), t6]);
    let ppsr = nmul(pp.clone(), succ(r.clone()));
    let u1 = le_rw(
        &mut fr,
        u1,
        &nadd(succ(ex.clone()), ppr.clone()),
        &nadd(pp.clone(), ppr),
        &succ(cand.clone()),
        &ppsr,
    )?;
    let hr = cite("Nat.mod_lt", [x.clone(), d.clone(), hd.clone()]);
    let u2 = cite("Nat.mul_le_mul_left", [succ(r.clone()), d.clone(), pp.clone(), hr]);
    let u2 = le_rw(&mut fr, u2, &ppsr, &nmul(pp.clone(), d.clone()), &ppsr, &dpp)?;
    let u = le_trans(&succ(cand.clone()), &ppsr, &dpp, u1, u2);
    // (c) `d R < d P p`.
    let dr = nmul(d.clone(), big_r.clone());
    let v1 = cite(bvv::ADD_LE_ADD_RIGHT, [nlit(1), d.clone(), dr.clone(), hd]);
    let dsr = nmul(d.clone(), succ(big_r.clone()));
    let v1 = le_rw(
        &mut fr,
        v1,
        &nadd(nlit(1), dr.clone()),
        &nadd(d.clone(), dr.clone()),
        &succ(dr.clone()),
        &dsr,
    )?;
    let hbig_r = cite("Nat.mod_lt", [xm.clone(), pp.clone(), cite(bvv::TWO_POW_POS, [p.clone()])]);
    let v2 = cite("Nat.mul_le_mul_left", [succ(big_r.clone()), pp.clone(), d.clone(), hbig_r]);
    let v = le_trans(&succ(dr.clone()), &dsr, &dpp, v1, v2);
    // (d) `(d P p) Q + d R = (d P p) q + cand`.
    let ea = Eqn::cite(
        "Nat.div_add_mod",
        vec![xm.clone(), pp.clone()],
        nadd(nmul(big_q.clone(), pp.clone()), big_r.clone()),
        xm.clone(),
    );
    let eb = Eqn::cite(
        "Nat.div_add_mod",
        vec![x.clone(), d.clone()],
        nadd(nmul(q.clone(), d.clone()), r.clone()),
        x.clone(),
    );
    let ec = hyp(nmul(d.clone(), m.clone()), nadd(pp.clone(), e.clone()), hdm);
    let lhs = nadd(nmul(dpp.clone(), big_q.clone()), dr.clone());
    let (d1, x1, pp1, ex1) = (d.clone(), x.clone(), pp.clone(), ex.clone());
    let chain =
        ring_eq(&mut fr, &lhs, &nmul(d.clone(), nadd(nmul(big_q.clone(), pp.clone()), big_r)))?
            .then(ea.under(&mut fr, |t| nmul(d1.clone(), t)))
            .then(ring_eq(
                &mut fr,
                &nmul(d.clone(), xm.clone()),
                &nmul(x.clone(), nmul(d.clone(), m.clone())),
            )?)
            .then(ec.under(&mut fr, |t| nmul(x1.clone(), t)))
            .then(ring_eq(
                &mut fr,
                &nmul(x.clone(), nadd(pp.clone(), e.clone())),
                &nadd(nmul(pp.clone(), x.clone()), ex.clone()),
            )?)
            .then(eb.symm().under(&mut fr, |t| nadd(nmul(pp1.clone(), t), ex1.clone())))
            .then(ring_eq(
                &mut fr,
                &nadd(nmul(pp.clone(), nadd(nmul(q.clone(), d.clone()), r.clone())), ex.clone()),
                &nadd(nmul(dpp.clone(), q.clone()), cand.clone()),
            )?);
    let body = cite(bvv::DIV_MOD_CANCEL, [dpp, big_q, q, dr, cand, v, u, chain.proof]);
    Some((ty, lams(binders, body)))
}

/// `X = X M / Q + (X M % Q + X N) / Q` when `M + N = Q`: with `D` that
/// quotient and `R2` its remainder,
/// `Q X + 0 = Q (X M / Q + D) + R2`, and `div_mod_cancel`.
fn addback_split() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bx, x) = nat_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (bq, q) = nat_local(&mut fr);
    let (bn, n) = nat_local(&mut fr);
    let (hq_id, hq) = fr.local();
    let (h_id, h) = fr.local();
    let binders = vec![
        bx,
        bm,
        bq,
        bn,
        (hq_id, nlt(nlit(0), q.clone())),
        (h_id, eq(nat(), nadd(m.clone(), n.clone()), q.clone())),
    ];
    let xm = nmul(x.clone(), m.clone());
    let xn = nmul(x.clone(), n.clone());
    let uq = ndiv(xm.clone(), q.clone());
    let r = nmod(xm.clone(), q.clone());
    let s = nadd(r.clone(), xn.clone());
    let d = ndiv(s.clone(), q.clone());
    let r2 = nmod(s.clone(), q.clone());
    let ud = nadd(uq.clone(), d.clone());
    let ty = pis(binders.clone(), eq(nat(), x.clone(), ud.clone()));
    let e1 = Eqn::cite(
        "Nat.div_add_mod",
        vec![xm.clone(), q.clone()],
        nadd(nmul(uq.clone(), q.clone()), r.clone()),
        xm.clone(),
    );
    let e2 = Eqn::cite(
        "Nat.div_add_mod",
        vec![s.clone(), q.clone()],
        nadd(nmul(d.clone(), q.clone()), r2.clone()),
        s.clone(),
    );
    let hmn = hyp(nadd(m.clone(), n.clone()), q.clone(), h);
    let uqq = nmul(uq.clone(), q.clone());
    let (uqq1, xn1, x1) = (uqq.clone(), xn.clone(), x.clone());
    let c = ring_eq(
        &mut fr,
        &nadd(nmul(q.clone(), ud.clone()), r2.clone()),
        &nadd(uqq.clone(), nadd(nmul(d.clone(), q.clone()), r2.clone())),
    )?
    .then(e2.under(&mut fr, |t| nadd(uqq1.clone(), t)))
    .then(ring_eq(
        &mut fr,
        &nadd(uqq.clone(), s.clone()),
        &nadd(nadd(uqq.clone(), r.clone()), xn.clone()),
    )?)
    .then(e1.under(&mut fr, |t| nadd(t, xn1.clone())))
    .then(ring_eq(
        &mut fr,
        &nadd(xm.clone(), xn.clone()),
        &nmul(x.clone(), nadd(m.clone(), n.clone())),
    )?)
    .then(hmn.under(&mut fr, |t| nmul(x1.clone(), t)))
    .then(ring_eq(
        &mut fr,
        &nmul(x.clone(), q.clone()),
        &nadd(nmul(q.clone(), x.clone()), nlit(0)),
    )?);
    let hr2 = cite("Nat.mod_lt", [s, q.clone(), hq.clone()]);
    let body = cite(bvv::DIV_MOD_CANCEL, [q, x, ud, nlit(0), r2, hq, hr2, c.symm().proof]);
    Some((ty, lams(binders, body)))
}

/// The add-back multiplier identity: `X = X M / Q + D` gives
/// `X M / Q + D / 2 = X (Q + M) / (2 Q)`, by `div_unique` with the
/// remainder `Q (D % 2) + X M % Q < 2 Q`.
fn addback_mul() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bx, x) = nat_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (bq, q) = nat_local(&mut fr);
    let (bd, d) = nat_local(&mut fr);
    let (hq_id, hq) = fr.local();
    let (h_id, h) = fr.local();
    let xm = nmul(x.clone(), m.clone());
    let uq = ndiv(xm.clone(), q.clone());
    let r = nmod(xm.clone(), q.clone());
    let binders = vec![
        bx,
        bm,
        bq,
        bd,
        (hq_id, nlt(nlit(0), q.clone())),
        (h_id, eq(nat(), x.clone(), nadd(uq.clone(), d.clone()))),
    ];
    let d2 = ndiv(d.clone(), nlit(2));
    let dm2 = nmod(d.clone(), nlit(2));
    let quo = nadd(uq.clone(), d2.clone());
    let a = nmul(x.clone(), nadd(q.clone(), m.clone()));
    let n2 = nmul(nlit(2), q.clone());
    let ty = pis(binders.clone(), eq(nat(), quo.clone(), ndiv(a.clone(), n2.clone())));
    let rem = nadd(nmul(q.clone(), dm2.clone()), r.clone());
    // `a = rem + (2 Q) quo`.
    let e1s = Eqn::cite(
        "Nat.div_add_mod",
        vec![xm.clone(), q.clone()],
        nadd(nmul(uq.clone(), q.clone()), r.clone()),
        xm.clone(),
    )
    .symm();
    let hd = hyp(x.clone(), nadd(uq.clone(), d.clone()), h);
    let e3 = Eqn::cite(
        "Nat.div_add_mod",
        vec![d.clone(), nlit(2)],
        nadd(nmul(d2.clone(), nlit(2)), dm2.clone()),
        d.clone(),
    )
    .symm();
    let uqq_r = nadd(nmul(uq.clone(), q.clone()), r.clone());
    let (q1, xm1, ud1, uqq_r1, uq1) =
        (q.clone(), xm.clone(), nadd(uq.clone(), d.clone()), uqq_r.clone(), uq.clone());
    let (q2, uqq_r2) = (q.clone(), uqq_r.clone());
    let split = ring_eq(&mut fr, &a, &nadd(nmul(x.clone(), q.clone()), xm.clone()))?
        .then(hd.under(&mut fr, |t| nadd(nmul(t, q1.clone()), xm1.clone())))
        .then(e1s.under(&mut fr, |t| nadd(nmul(ud1.clone(), q.clone()), t)))
        .then(e3.under(&mut fr, |t| nadd(nmul(nadd(uq1.clone(), t), q2.clone()), uqq_r2.clone())))
        .then(ring_eq(
            &mut fr,
            &nadd(
                nmul(nadd(uq.clone(), nadd(nmul(d2.clone(), nlit(2)), dm2.clone())), q.clone()),
                uqq_r1,
            ),
            &nadd(rem.clone(), nmul(n2.clone(), quo.clone())),
        )?);
    // `rem < 2 Q`.
    let hr = cite("Nat.mod_lt", [xm.clone(), q.clone(), hq]);
    let qdm = nmul(q.clone(), dm2.clone());
    let w1 = cite(bvv::ADD_LE_ADD_RIGHT, [succ(r.clone()), q.clone(), qdm.clone(), hr]);
    let qsdm = nmul(q.clone(), succ(dm2.clone()));
    let w1 = le_rw(
        &mut fr,
        w1,
        &nadd(succ(r.clone()), qdm.clone()),
        &nadd(q.clone(), qdm),
        &succ(rem.clone()),
        &qsdm,
    )?;
    let h2 = cite("Nat.mod_lt", [d.clone(), nlit(2), pos_two()]);
    let w2 = cite("Nat.mul_le_mul_left", [succ(dm2), nlit(2), q.clone(), h2]);
    let w2 = le_rw(&mut fr, w2, &qsdm, &nmul(q.clone(), nlit(2)), &qsdm, &n2)?;
    let bound = le_trans(&succ(rem.clone()), &qsdm, &n2, w1, w2);
    let du = cite(bvv::DIV_UNIQUE, [a.clone(), n2.clone(), quo.clone(), rem, bound, split.proof]);
    let body = symm(nat(), ndiv(a, n2), quo, du);
    Some((ty, lams(binders, body)))
}

// ── list lemmas ──────────────────────────────────────────────────────────────

/// `V l < P (L l)`: `V l = V (natToBvAux (L l) (V l)) = V l % P (L l)`.
fn to_nat_lt() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bl, l) = list_local(&mut fr);
    let pl = p2(&len(&l));
    let ty = pis(vec![bl.clone()], nlt(val(&l), pl.clone()));
    let n2b = nat_to_bv(len(&l), val(&l));
    let back = symm(lb(), n2b.clone(), l.clone(), cite(bvv::NAT_TO_BV_TO_NAT, [l.clone()]));
    let e = under_list(&mut fr, &l, &n2b, back, |t| to_nat(t)).then(Eqn::cite(
        bvv::TO_NAT_NAT_TO_BV,
        vec![len(&l), val(&l)],
        val(&n2b),
        nmod(val(&l), pl.clone()),
    ));
    let lt = cite("Nat.mod_lt", [val(&l), pl.clone(), cite(bvv::TWO_POW_POS, [len(&l)])]);
    let body = lt_subst_right_left(&mut fr, &pl, lt, e.symm());
    Some((ty, lams(vec![bl], body)))
}

/// From `h : a < c` and `e : a = a2`, `a2 < c`.
fn lt_subst_right_left(fr: &mut Fresh, c: &Expr, h: Expr, e: Eqn) -> Expr {
    let (t_id, t) = fr.local();
    let motive = lams(vec![(t_id, nat())], nlt(t, c.clone()));
    eq_subst(nat(), motive, e.lhs, e.rhs, e.proof, h)
}

fn btail_val() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bl, l) = list_local(&mut fr);
    let t = btail(l.clone());
    let ty = pis(vec![bl.clone()], eq(nat(), val(&t), ndiv(val(&l), nlit(2))));
    let ht = cite(bvv::TO_NAT_HEAD_TAIL, [l.clone()]);
    let hd = super::kterm::bhead(l.clone());
    let d = cite(
        bvv::DIV_UNIQUE,
        [val(&l), nlit(2), val(&t), btn(hd.clone()), cite(bvv::BTN_LT_TWO, [hd]), ht],
    );
    let body = symm(nat(), ndiv(val(&l), nlit(2)), val(&t), d);
    Some((ty, lams(vec![bl], body)))
}

fn btail_len() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bl, l) = list_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (h_id, h) = fr.local();
    let prem = |w: &Expr| eq(nat(), len(w), succ(m.clone()));
    let concl = |w: &Expr| eq(nat(), len(&btail(w.clone())), m.clone());
    let binders = vec![bl, bm, (h_id, prem(&l))];
    let ty = pis(binders.clone(), concl(&l));
    let motive = {
        let (bw, w) = list_local(&mut fr);
        lams(vec![bw], Expr::arrow(prem(&w), concl(&w)))
    };
    let nil_case = {
        let (h0_id, h0) = fr.local();
        let contra = super::kterm::absurd_zero_eq_succ(&mut fr, m.clone(), h0, concl(&kx::nil()));
        lams(vec![(h0_id, prem(&kx::nil()))], contra)
    };
    let cons_case = {
        let (hb_id, hb) = fr.local();
        let (bt, t) = list_local(&mut fr);
        let (ih_id, _) = fr.local();
        let (h1_id, h1) = fr.local();
        let w = kx::cons(hb, t.clone());
        let pred = nat_pred(&mut fr);
        let body = congr_arg(nat(), nat(), len(&w), succ(m.clone()), pred, h1);
        lams(
            vec![
                (hb_id, bool_ty()),
                bt,
                (ih_id, Expr::arrow(prem(&t), concl(&t))),
                (h1_id, prem(&w)),
            ],
            body,
        )
    };
    let body = Expr::app(list_rec_prop(motive, nil_case, cons_case, l.clone()), h);
    Some((ty, lams(binders, body)))
}

/// `V (iter k l) = V l / P k`, by induction on `k`: `btail_val`, the
/// hypothesis, `div_div` and `P k * 2 = P (succ k)`.
fn iter_val() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bk, k) = nat_local(&mut fr);
    let (bl, l) = list_local(&mut fr);
    let vl = val(&l);
    let stmt = |t: &Expr| eq(nat(), val(&iter(t.clone(), l.clone())), ndiv(vl.clone(), p2(t)));
    let ty = pis(vec![bk.clone(), bl.clone()], stmt(&k));
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        lams(vec![bt], stmt(&t))
    };
    let z = symm(nat(), ndiv(vl.clone(), nlit(1)), vl.clone(), cite(names::DIV_ONE, [vl.clone()]));
    let s = {
        let (bj, j) = nat_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let ij = iter(j.clone(), l.clone());
        let pj = p2(&j);
        let vl1 = vl.clone();
        let pj1 = pj.clone();
        let e = Eqn::by_defeq(val(&iter(succ(j.clone()), l.clone())), val(&btail(ij.clone())))
            .then(Eqn::cite(
                names::BTAIL_VAL,
                vec![ij.clone()],
                val(&btail(ij.clone())),
                ndiv(val(&ij), nlit(2)),
            ))
            .then(
                hyp(val(&ij), ndiv(vl.clone(), pj.clone()), ih)
                    .under(&mut fr, |t| ndiv(t, nlit(2))),
            )
            .then(Eqn::cite(
                names::DIV_DIV,
                vec![
                    vl.clone(),
                    pj.clone(),
                    nlit(2),
                    cite(bvv::TWO_POW_POS, [j.clone()]),
                    pos_two(),
                ],
                ndiv(ndiv(vl.clone(), pj.clone()), nlit(2)),
                ndiv(vl.clone(), nmul(pj.clone(), nlit(2))),
            ))
            .then(
                ring_eq(&mut fr, &nmul(pj.clone(), nlit(2)), &nmul(nlit(2), pj1))?
                    .under(&mut fr, |t| ndiv(vl1.clone(), t)),
            )
            .then(Eqn::by_defeq(
                ndiv(vl.clone(), nmul(nlit(2), pj)),
                ndiv(vl.clone(), p2(&succ(j.clone()))),
            ));
        lams(vec![bj, (ih_id, stmt(&j))], e.proof)
    };
    let body = nat_rec_prop(motive, z, s, k);
    Some((ty, lams(vec![bk, bl], body)))
}

/// `L l = m + k → L (iter k l) = m`, by induction on `k` generalising `m`.
fn iter_len() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bk, k) = nat_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (bl, l) = list_local(&mut fr);
    let (h_id, h) = fr.local();
    let prem = |mm: &Expr, t: &Expr| eq(nat(), len(&l), nadd(mm.clone(), t.clone()));
    let concl = |mm: &Expr, t: &Expr| eq(nat(), len(&iter(t.clone(), l.clone())), mm.clone());
    let binders = vec![bk, bm, bl.clone(), (h_id, prem(&m, &k))];
    let ty = pis(binders.clone(), concl(&m, &k));
    let all_m = |fr: &mut Fresh, t: &Expr| {
        let (bmm, mm) = nat_local(fr);
        pis(vec![bmm], Expr::arrow(prem(&mm, t), concl(&mm, t)))
    };
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        let body = all_m(&mut fr, &t);
        lams(vec![bt], body)
    };
    let z = {
        let (bmm, mm) = nat_local(&mut fr);
        let (h0_id, h0) = fr.local();
        lams(vec![bmm, (h0_id, prem(&mm, &zero()))], h0)
    };
    let s = {
        let (bj, j) = nat_local(&mut fr);
        let ih_ty = all_m(&mut fr, &j);
        let (ih_id, ih) = fr.local();
        let (bmm, mm) = nat_local(&mut fr);
        let (h1_id, h1) = fr.local();
        let sj = succ(j.clone());
        let h1e = hyp(len(&l), nadd(mm.clone(), sj.clone()), h1).then(ring_eq(
            &mut fr,
            &nadd(mm.clone(), sj.clone()),
            &nadd(succ(mm.clone()), j.clone()),
        )?);
        let r = Expr::apps(ih, [succ(mm.clone()), h1e.proof]);
        let body = cite(names::BTAIL_LEN, [iter(j.clone(), l.clone()), mm.clone(), r]);
        lams(vec![bj, (ih_id, ih_ty), bmm, (h1_id, prem(&mm, &sj))], body)
    };
    let body = Expr::apps(nat_rec_prop(motive, z, s, k), [m, h]);
    Some((ty, lams(binders, body)))
}

/// `V (ZX l k) = V l` (`toNat_append`, `toNat_replF`).
fn zx_val() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bl, l) = list_local(&mut fr);
    let (bk, k) = nat_local(&mut fr);
    let ty =
        pis(vec![bl.clone(), bk.clone()], eq(nat(), val(&zero_ext(l.clone(), k.clone())), val(&l)));
    let rf = repl_f(k.clone());
    let pl = p2(&len(&l));
    let (vl1, pl1) = (val(&l), pl.clone());
    let e = Eqn::cite(
        bvv::TO_NAT_APPEND,
        vec![l.clone(), rf.clone()],
        val(&bv_append(l.clone(), rf.clone())),
        nadd(val(&l), nmul(pl.clone(), val(&rf))),
    )
    .then(
        Eqn::cite(bvv::TO_NAT_REPL_F, vec![k.clone()], val(&rf), nlit(0))
            .under(&mut fr, |u| nadd(vl1.clone(), nmul(pl1.clone(), u))),
    )
    .then(Eqn::by_defeq(nadd(val(&l), nmul(pl, nlit(0))), val(&l)));
    Some((ty, lams(vec![bl, bk], e.proof)))
}

/// `L (ZX l k) = L l + k` (`len_append`, `len_replF`).
fn zx_len() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bl, l) = list_local(&mut fr);
    let (bk, k) = nat_local(&mut fr);
    let ty = pis(
        vec![bl.clone(), bk.clone()],
        eq(nat(), len(&zero_ext(l.clone(), k.clone())), nadd(len(&l), k.clone())),
    );
    let rf = repl_f(k.clone());
    let ll = len(&l);
    let e = Eqn::cite(
        bvv::LEN_APPEND,
        vec![l.clone(), rf.clone()],
        len(&bv_append(l.clone(), rf.clone())),
        nadd(len(&l), len(&rf)),
    )
    .then(
        Eqn::cite(bvv::LEN_REPL_F, vec![k.clone()], len(&rf), k.clone())
            .under(&mut fr, |u| nadd(ll.clone(), u)),
    );
    Some((ty, lams(vec![bl, bk], e.proof)))
}

/// `0 < v → V (natToBvAux (L a) (V a / v)) = V a / v`: the quotient is at
/// most `V a < P (L a)`, so the truncation is the identity. `bvDiv a c` and
/// `bvLShr a n` unfold to this shape.
fn n2b_div_val() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = list_local(&mut fr);
    let (bv, v) = nat_local(&mut fr);
    let (h_id, h) = fr.local();
    let binders = vec![ba, bv, (h_id, nlt(nlit(0), v.clone()))];
    let va = val(&a);
    let q = ndiv(va.clone(), v.clone());
    let pa = p2(&len(&a));
    let n2b = nat_to_bv(len(&a), q.clone());
    let ty = pis(binders.clone(), eq(nat(), val(&n2b), q.clone()));
    let hle = cite(names::DIV_LE_SELF, [va.clone(), v.clone(), h]);
    let s = cite("Nat.succ_le_succ", [q.clone(), va.clone(), hle]);
    let hq =
        le_trans(&succ(q.clone()), &succ(va.clone()), &pa, s, cite(names::TO_NAT_LT, [a.clone()]));
    let e = Eqn::cite(
        bvv::TO_NAT_NAT_TO_BV,
        vec![len(&a), q.clone()],
        val(&n2b),
        nmod(q.clone(), pa.clone()),
    )
    .then(Eqn::cite(
        names::MOD_EQ_OF_LT,
        vec![q.clone(), pa.clone(), hq],
        nmod(q.clone(), pa),
        q,
    ));
    Some((ty, lams(binders, e.proof)))
}

/// `V a < P W` from `V a < P (L a)` and `L a = W`.
fn val_lt(fr: &mut Fresh, a: &Expr, w: &Expr, hl: Expr) -> Expr {
    let e = hyp(len(a), w.clone(), hl).under(fr, |t| two_pow(t));
    lt_subst_right(fr, &val(a), cite(names::TO_NAT_LT, [a.clone()]), e)
}

/// `V (U x y m) = V x * V y / P (succ m)`: the 2W-bit product does not wrap
/// (`V x * V y < P W * P W = P (W + W)`), then `iter_val`.
fn umulh_val() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bx, x) = list_local(&mut fr);
    let (by, y) = list_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (hx_id, hx) = fr.local();
    let (hy_id, hy) = fr.local();
    let w = succ(m.clone());
    let binders = vec![
        bx,
        by,
        bm,
        (hx_id, eq(nat(), len(&x), w.clone())),
        (hy_id, eq(nat(), len(&y), w.clone())),
    ];
    let (vx, vy) = (val(&x), val(&y));
    let vxy = nmul(vx.clone(), vy.clone());
    let pw = p2(&w);
    let u = umulh_list(&x, &y, &w);
    let ty = pis(binders.clone(), eq(nat(), val(&u), ndiv(vxy.clone(), pw.clone())));
    let zx = zero_ext(x.clone(), w.clone());
    let zy = zero_ext(y.clone(), w.clone());
    let pr = bvmul(zx.clone(), zy.clone());
    let ww = nadd(w.clone(), w.clone());
    let w1 = w.clone();
    let lzy =
        Eqn::cite(names::ZX_LEN, vec![y.clone(), w.clone()], len(&zy), nadd(len(&y), w.clone()))
            .then(hyp(len(&y), w.clone(), hy.clone()).under(&mut fr, |t| nadd(t, w1.clone())));
    let hxl = val_lt(&mut fr, &x, &w, hx.clone());
    let hyl = val_lt(&mut fr, &y, &w, hy);
    let m1 = cite(names::MUL_LT_MUL, [vx.clone(), vy.clone(), pw.clone(), pw.clone(), hxl, hyl]);
    let pww = Eqn::cite(
        bvv::TWO_POW_ADD,
        vec![w.clone(), w.clone()],
        p2(&ww),
        nmul(pw.clone(), pw.clone()),
    );
    let hlt = lt_subst_right(&mut fr, &vxy, m1, pww.symm());
    let (vzx, vzy) = (val(&zx), val(&zy));
    let (vzx1, vzy1, vzy2, vx1) = (vzx.clone(), vzy.clone(), vzy.clone(), vx.clone());
    let (ww1, ww2, ww3) = (ww.clone(), ww.clone(), ww.clone());
    let vpr = Eqn::cite(
        bvv::BV_MUL_VAL,
        vec![zx.clone(), zy.clone()],
        val(&pr),
        nmod(nmul(vzx.clone(), vzy.clone()), p2(&len(&zy))),
    )
    .then(lzy.under(&mut fr, |t| nmod(nmul(vzx1.clone(), vzy1.clone()), two_pow(t))))
    .then(
        Eqn::cite(names::ZX_VAL, vec![x.clone(), w.clone()], vzx.clone(), vx.clone())
            .under(&mut fr, |t| nmod(nmul(t, vzy2.clone()), two_pow(ww1.clone()))),
    )
    .then(
        Eqn::cite(names::ZX_VAL, vec![y.clone(), w.clone()], vzy.clone(), vy.clone())
            .under(&mut fr, |t| nmod(nmul(vx1.clone(), t), two_pow(ww2.clone()))),
    )
    .then(Eqn::cite(
        names::MOD_EQ_OF_LT,
        vec![vxy.clone(), p2(&ww3), hlt],
        nmod(vxy.clone(), p2(&ww)),
        vxy.clone(),
    ));
    let pw1 = pw.clone();
    let e = Eqn::cite(
        names::ITER_VAL,
        vec![w.clone(), pr.clone()],
        val(&u),
        ndiv(val(&pr), pw.clone()),
    )
    .then(vpr.under(&mut fr, |t| ndiv(t, pw1.clone())));
    Some((ty, lams(binders, e.proof)))
}

/// `L (U x y m) = succ m`: `L (bvMul zx zy) = L zy = W + W`, then `iter_len`.
fn umulh_len() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bx, x) = list_local(&mut fr);
    let (by, y) = list_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (hx_id, hx) = fr.local();
    let (hy_id, hy) = fr.local();
    let w = succ(m.clone());
    let binders = vec![
        bx,
        by,
        bm,
        (hx_id, eq(nat(), len(&x), w.clone())),
        (hy_id, eq(nat(), len(&y), w.clone())),
    ];
    let u = umulh_list(&x, &y, &w);
    let ty = pis(binders.clone(), eq(nat(), len(&u), w.clone()));
    let zx = zero_ext(x.clone(), w.clone());
    let zy = zero_ext(y.clone(), w.clone());
    let pr = bvmul(zx.clone(), zy.clone());
    let ww = nadd(w.clone(), w.clone());
    let (w1, w2) = (w.clone(), w.clone());
    let lzx =
        Eqn::cite(names::ZX_LEN, vec![x.clone(), w.clone()], len(&zx), nadd(len(&x), w.clone()))
            .then(hyp(len(&x), w.clone(), hx).under(&mut fr, |t| nadd(t, w1.clone())))
            .then(Eqn::by_defeq(ww.clone(), succ(nadd(w.clone(), m.clone()))));
    let lzy =
        Eqn::cite(names::ZX_LEN, vec![y.clone(), w.clone()], len(&zy), nadd(len(&y), w.clone()))
            .then(hyp(len(&y), w.clone(), hy).under(&mut fr, |t| nadd(t, w2.clone())));
    let lpr = Eqn::cite(
        add_comm::names::LEN_BV_MUL,
        vec![zx, zy.clone(), nadd(w.clone(), m.clone()), lzx.proof],
        len(&pr),
        len(&zy),
    )
    .then(lzy);
    let body = cite(names::ITER_LEN, [w.clone(), w, pr, lpr.proof]);
    Some((ty, lams(binders, body)))
}

/// `V n = k → V ⟦LShr S (Const n)⟧ = V ⟦S⟧ / P k` (the shifted-register
/// `lsr #k`).
fn lshr_k() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bs, s) = bvf_local(&mut fr);
    let (bn, n) = list_local(&mut fr);
    let (bk, k) = nat_local(&mut fr);
    let (h_id, h) = fr.local();
    let binders = vec![bs, bn, bk, (h_id, eq(nat(), val(&n), k.clone()))];
    let es = eval(s.clone());
    let vs = val(&es);
    let lhs = val(&eval(kx::lshr(s.clone(), kx::const_(n.clone()))));
    let ty = pis(binders.clone(), eq(nat(), lhs.clone(), ndiv(vs.clone(), p2(&k))));
    let pn = p2(&val(&n));
    let vs1 = vs.clone();
    let e = Eqn::cite(
        names::N2B_DIV_VAL,
        vec![es.clone(), pn.clone(), cite(bvv::TWO_POW_POS, [val(&n)])],
        lhs,
        ndiv(vs.clone(), pn),
    )
    .then(hyp(val(&n), k.clone(), h).under(&mut fr, |t| ndiv(vs1.clone(), two_pow(t))));
    Some((ty, lams(binders, e.proof)))
}

/// `V ⟦ZeroExt (Const (iter k ⟦S⟧)) k⟧ = V ⟦S⟧ / P k` (the UBFM `lsr #k`).
fn ubfm_k() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bs, s) = bvf_local(&mut fr);
    let (bk, k) = nat_local(&mut fr);
    let es = eval(s.clone());
    let it = iter(k.clone(), es.clone());
    let lhs = val(&eval(kx::zext(kx::const_(it.clone()), k.clone())));
    let ty = pis(vec![bs.clone(), bk.clone()], eq(nat(), lhs.clone(), ndiv(val(&es), p2(&k))));
    let e = Eqn::cite(names::ZX_VAL, vec![it.clone(), k.clone()], lhs, val(&it)).then(Eqn::cite(
        names::ITER_VAL,
        vec![k.clone(), es.clone()],
        val(&it),
        ndiv(val(&es), p2(&k)),
    ));
    Some((ty, lams(vec![bs, bk], e.proof)))
}

/// The shared tail of the magic theorems: from `V lhs_inner = A / P p` (the
/// high bits of the scaled product, `p` the total shift), the premises of
/// `gm_div`, and the lengths, the list equation `ZX (iter k T) k = bvDiv x c`.
struct MagicTail<'a> {
    x: &'a Expr,
    c: &'a Expr,
    t: &'a Expr,
    k: &'a Expr,
    j: &'a Expr,
    w: &'a Expr,
    hx: &'a Expr,
    hjk: &'a Expr,
    /// `L t = W`.
    lt: Eqn,
    /// `V (iter k t) = V x * M / P p`.
    vt: Eqn,
    /// `M`, `p`, `e` and the three `gm_div` premises.
    big_m: Expr,
    p: Expr,
    e: Expr,
    hd: Expr,
    hdm: Expr,
    hble: Expr,
}

fn magic_tail(fr: &mut Fresh, mt: MagicTail<'_>) -> Expr {
    let MagicTail { x, c, t, k, j, w, hx, hjk, lt, vt, big_m, p, e, hd, hdm, hble } = mt;
    let it = iter(k.clone(), t.clone());
    let lhs = zero_ext(it.clone(), k.clone());
    let rhs = kx::bv_div(x.clone(), c.clone());
    let (vx, vc) = (val(x), val(c));
    let jk = hyp(nadd(j.clone(), k.clone()), w.clone(), hjk.clone());
    // Lengths.
    let lt_jk = lt.then(jk.clone().symm());
    let li = cite(names::ITER_LEN, [k.clone(), j.clone(), t.clone(), lt_jk.proof]);
    let k1 = k.clone();
    let ll =
        Eqn::cite(names::ZX_LEN, vec![it.clone(), k.clone()], len(&lhs), nadd(len(&it), k.clone()))
            .then(hyp(len(&it), j.clone(), li).under(fr, |u| nadd(u, k1.clone())))
            .then(jk);
    let q = ndiv(vx.clone(), vc.clone());
    let lr = Eqn::cite(bvv::LEN_NAT_TO_BV, vec![len(x), q.clone()], len(&rhs), len(x)).then(hyp(
        len(x),
        w.clone(),
        hx.clone(),
    ));
    let hl = ll.then(lr.symm());
    // Values.
    let hxlt = val_lt(fr, x, w, hx.clone());
    let vl = Eqn::cite(names::ZX_VAL, vec![it.clone(), k.clone()], val(&lhs), val(&it))
        .then(vt)
        .then(Eqn::cite(
            names::GM_DIV,
            vec![
                vx.clone(),
                vc.clone(),
                big_m.clone(),
                p.clone(),
                e,
                w.clone(),
                hd.clone(),
                hdm,
                hble,
                hxlt,
            ],
            ndiv(nmul(vx.clone(), big_m), two_pow(p)),
            q.clone(),
        ));
    let vr = Eqn::cite(names::N2B_DIV_VAL, vec![x.clone(), vc, hd], val(&rhs), q);
    let hv = vl.then(vr.symm());
    cite(bvv::INJ, [lhs, rhs, hl.proof, hv.proof])
}

/// The common binders of the magic theorems.
struct MagicBinders {
    binders: Vec<(FVarId, Expr)>,
    x_bvf: Expr,
    h_bvf: Option<Expr>,
    mk: Expr,
    c: Expr,
    m: Expr,
    j: Expr,
    k: Expr,
    e: Expr,
    hx: Expr,
    hmk: Expr,
    hjk: Expr,
    hhv: Option<Expr>,
    hd: Expr,
    hdm: Expr,
    hble: Expr,
}

/// `(M, p)` of a magic theorem: `M = V mk`, `p = succ m + k` without the
/// add-back; `M = P (succ m) + V mk`, `p = succ (succ m) + k` with it.
fn magic_mp(add: bool, mk: &Expr, m: &Expr, k: &Expr) -> (Expr, Expr) {
    let w = succ(m.clone());
    if add {
        (nadd(two_pow(w.clone()), val(mk)), nadd(succ(w), k.clone()))
    } else {
        (val(mk), nadd(w, k.clone()))
    }
}

fn magic_binders(fr: &mut Fresh, add: bool) -> MagicBinders {
    let (bxv, x_bvf) = bvf_local(fr);
    let h = add.then(|| bvf_local(fr));
    let (bmk, mk) = list_local(fr);
    let (bc, c) = list_local(fr);
    let (bm, m) = nat_local(fr);
    let (bj, j) = nat_local(fr);
    let (bk, k) = nat_local(fr);
    let (be, e) = nat_local(fr);
    let (hx_id, hx) = fr.local();
    let (hmk_id, hmk) = fr.local();
    let (hjk_id, hjk) = fr.local();
    let hhv = add.then(|| fr.local());
    let (hd_id, hd) = fr.local();
    let (hdm_id, hdm) = fr.local();
    let (hble_id, hble) = fr.local();
    let w = succ(m.clone());
    let ex = eval(x_bvf.clone());
    let (big_m, p) = magic_mp(add, &mk, &m, &k);
    let pp = two_pow(p.clone());
    let mut binders = vec![bxv];
    if let Some((bh, _)) = &h {
        binders.push(bh.clone());
    }
    binders.extend([bmk, bc, bm, bj, bk, be]);
    binders.push((hx_id, eq(nat(), len(&ex), w.clone())));
    binders.push((hmk_id, eq(nat(), len(&mk), w.clone())));
    binders.push((hjk_id, eq(nat(), nadd(j.clone(), k.clone()), w.clone())));
    if let (Some((hid, _)), Some((_, hv))) = (&hhv, &h) {
        let s = eval(kx::sub(x_bvf.clone(), umh(&x_bvf, &mk, &w)));
        binders.push((*hid, eq(nat(), val(&eval(hv.clone())), ndiv(val(&s), nlit(2)))));
    }
    binders.push((hd_id, nlt(nlit(0), val(&c))));
    binders.push((hdm_id, eq(nat(), nmul(val(&c), big_m), nadd(pp.clone(), e.clone()))));
    binders.push((
        hble_id,
        eq(
            bool_ty(),
            nble(nadd(nmul(e.clone(), two_pow(w)), nlit(1)), nadd(pp, e.clone())),
            kx::btrue(),
        ),
    ));
    MagicBinders {
        binders,
        x_bvf,
        h_bvf: h.map(|(_, v)| v),
        mk,
        c,
        m,
        j,
        k,
        e,
        hx,
        hmk,
        hjk,
        hhv: hhv.map(|(_, v)| v),
        hd,
        hdm,
        hble,
    }
}

/// `⟦ZeroExt (Const (iter k ⟦UMH X mk m⟧)) k⟧ = ⟦Div X (Const c)⟧`: the
/// quotient is `V x * V mk / P W / P k = V x * V mk / P (W + k)`, then
/// `gm_div`.
fn magic_noadd() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let b = magic_binders(&mut fr, false);
    let w = succ(b.m.clone());
    let core = umh(&b.x_bvf, &b.mk, &w);
    let lhs = eval(kx::zext(kx::const_(iter(b.k.clone(), eval(core))), b.k.clone()));
    let rhs = eval(kx::div(b.x_bvf.clone(), kx::const_(b.c.clone())));
    let ty = pis(b.binders.clone(), kx::eq_list(lhs, rhs));
    let x = eval(b.x_bvf.clone());
    let u = umulh_list(&x, &b.mk, &w);
    let (vx, vmk) = (val(&x), val(&b.mk));
    let a = nmul(vx.clone(), vmk.clone());
    let (pw, pk) = (two_pow(w.clone()), two_pow(b.k.clone()));
    let (pk1, a1) = (pk.clone(), a.clone());
    let p = nadd(w.clone(), b.k.clone());
    let lt = Eqn::cite(
        names::UMULH_LEN,
        vec![x.clone(), b.mk.clone(), b.m.clone(), b.hx.clone(), b.hmk.clone()],
        len(&u),
        w.clone(),
    );
    let vt = Eqn::cite(
        names::ITER_VAL,
        vec![b.k.clone(), u.clone()],
        val(&iter(b.k.clone(), u.clone())),
        ndiv(val(&u), pk.clone()),
    )
    .then(
        Eqn::cite(
            names::UMULH_VAL,
            vec![x.clone(), b.mk.clone(), b.m.clone(), b.hx.clone(), b.hmk.clone()],
            val(&u),
            ndiv(a.clone(), pw.clone()),
        )
        .under(&mut fr, |t| ndiv(t, pk1.clone())),
    )
    .then(Eqn::cite(
        names::DIV_DIV,
        vec![
            a.clone(),
            pw.clone(),
            pk.clone(),
            cite(bvv::TWO_POW_POS, [w.clone()]),
            cite(bvv::TWO_POW_POS, [b.k.clone()]),
        ],
        ndiv(ndiv(a.clone(), pw.clone()), pk.clone()),
        ndiv(a.clone(), nmul(pw.clone(), pk.clone())),
    ))
    .then(
        Eqn::cite(bvv::TWO_POW_ADD, vec![w.clone(), b.k.clone()], two_pow(p.clone()), nmul(pw, pk))
            .symm()
            .under(&mut fr, |t| ndiv(a1.clone(), t)),
    );
    let body = magic_tail(
        &mut fr,
        MagicTail {
            x: &x,
            c: &b.c,
            t: &u,
            k: &b.k,
            j: &b.j,
            w: &w,
            hx: &b.hx,
            hjk: &b.hjk,
            lt,
            vt,
            big_m: vmk,
            p,
            e: b.e.clone(),
            hd: b.hd.clone(),
            hdm: b.hdm.clone(),
            hble: b.hble.clone(),
        },
    );
    Some((ty, lams(b.binders, body)))
}

/// `⟦ZeroExt (Const (iter k ⟦Add (UMH X mk m) H⟧)) k⟧ = ⟦Div X (Const c)⟧`
/// with `V ⟦H⟧ = V ⟦Sub X (UMH X mk m)⟧ / 2`.
///
/// With `u = V x V mk / P W`: `x = u + D` (`addback_split`, from
/// `L mk = W`), so `V ⟦Sub X UMH⟧ = D` with no wrap (`D ≤ x < P W`), and
/// `V ⟦Add UMH H⟧ = u + D / 2 < P W`; `addback_mul` makes it
/// `x (P W + V mk) / (2 P W)`; then as `magic_noadd` with `p = W + 1 + k`.
fn magic_addback() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let b = magic_binders(&mut fr, true);
    let hbvf = b.h_bvf.clone()?;
    let hhv = b.hhv.clone()?;
    let w = succ(b.m.clone());
    let core = umh(&b.x_bvf, &b.mk, &w);
    let lhs = eval(kx::zext(
        kx::const_(iter(b.k.clone(), eval(kx::add(core.clone(), hbvf.clone())))),
        b.k.clone(),
    ));
    let rhs = eval(kx::div(b.x_bvf.clone(), kx::const_(b.c.clone())));
    let ty = pis(b.binders.clone(), kx::eq_list(lhs, rhs));
    let x = eval(b.x_bvf.clone());
    let eh = eval(hbvf);
    let u = umulh_list(&x, &b.mk, &w);
    let s = addm(x.clone(), kx::bv_not(u.clone()), kx::btrue());
    let t = addm(u.clone(), eh.clone(), kx::bfalse());
    let (vx, vmk, vu, veh) = (val(&x), val(&b.mk), val(&u), val(&eh));
    let pw = two_pow(w.clone());
    let a0 = nmul(vx.clone(), vmk.clone());
    let uq = ndiv(a0.clone(), pw.clone());
    let notmk = kx::bv_not(b.mk.clone());
    let n = nadd(val(&notmk), nlit(1));
    let hp = cite(bvv::TWO_POW_POS, [w.clone()]);
    let hmk_eq = hyp(len(&b.mk), w.clone(), b.hmk.clone());
    let hx_eq = hyp(len(&x), w.clone(), b.hx.clone());
    // `V mk + N = P W`.
    let hmn = ring_eq(
        &mut fr,
        &nadd(vmk.clone(), n.clone()),
        &nadd(nadd(val(&notmk), vmk.clone()), nlit(1)),
    )?
    .then(Eqn::cite(
        bvv::BV_NOT_VAL,
        vec![b.mk.clone()],
        nadd(nadd(val(&notmk), vmk.clone()), nlit(1)),
        two_pow(len(&b.mk)),
    ))
    .then(hmk_eq.under(&mut fr, |z| two_pow(z)));
    let d0 = ndiv(nadd(nmod(a0.clone(), pw.clone()), nmul(vx.clone(), n.clone())), pw.clone());
    let split = Eqn::cite(
        names::ADDBACK_SPLIT,
        vec![vx.clone(), vmk.clone(), pw.clone(), n.clone(), hp.clone(), hmn.proof],
        vx.clone(),
        nadd(uq.clone(), d0.clone()),
    );
    let umulh_args = vec![x.clone(), b.mk.clone(), b.m.clone(), b.hx.clone(), b.hmk.clone()];
    let v_u = Eqn::cite(names::UMULH_VAL, umulh_args.clone(), vu.clone(), uq.clone());
    let l_u = Eqn::cite(names::UMULH_LEN, umulh_args, len(&u), w.clone());
    let vnu = val(&kx::bv_not(u.clone()));
    // `V (not u) + uq + 1 = P W`.
    let vnu1 = vnu.clone();
    let f = v_u
        .clone()
        .symm()
        .under(&mut fr, |z| nadd(nadd(vnu1.clone(), z), nlit(1)))
        .then(Eqn::cite(
            bvv::BV_NOT_VAL,
            vec![u.clone()],
            nadd(nadd(vnu.clone(), vu.clone()), nlit(1)),
            two_pow(len(&u)),
        ))
        .then(l_u.clone().under(&mut fr, |z| two_pow(z)));
    // `D ≤ V x` and `V x < P W`.
    let hxlt = val_lt(&mut fr, &x, &w, b.hx.clone());
    let eqx = ring_eq(&mut fr, &nadd(d0.clone(), uq.clone()), &nadd(uq.clone(), d0.clone()))?
        .then(split.clone().symm());
    let a1 = cite("Nat.le_add_right", [d0.clone(), uq.clone()]);
    let a2 = le_subst_right(&mut fr, &d0, a1, eqx.clone());
    let a3 = cite("Nat.succ_le_succ", [d0.clone(), vx.clone(), a2]);
    let hd0 = le_trans(&succ(d0.clone()), &succ(vx.clone()), &pw, a3, hxlt.clone());
    // `V s = D`.
    let (vnu2, vx2, pw2, pw3, pw4, d01) =
        (vnu.clone(), vx.clone(), pw.clone(), pw.clone(), pw.clone(), d0.clone());
    let sum1 = nadd(nadd(vx.clone(), vnu.clone()), nlit(1));
    let vs = Eqn::cite(
        bvv::ADD_REC_M_VAL,
        vec![x.clone(), kx::bv_not(u.clone()), kx::btrue()],
        val(&s),
        nmod(nadd(nadd(vx.clone(), vnu.clone()), btn(kx::btrue())), two_pow(len(&x))),
    )
    .then(Eqn::by_defeq(
        nmod(nadd(nadd(vx.clone(), vnu.clone()), btn(kx::btrue())), two_pow(len(&x))),
        nmod(sum1.clone(), two_pow(len(&x))),
    ))
    .then(
        hx_eq.under(&mut fr, |z| nmod(nadd(nadd(vx2.clone(), vnu2.clone()), nlit(1)), two_pow(z))),
    )
    .then(split.clone().under(&mut fr, |z| nmod(nadd(nadd(z, vnu.clone()), nlit(1)), pw2.clone())))
    .then(
        ring_eq(
            &mut fr,
            &nadd(nadd(nadd(uq.clone(), d0.clone()), vnu.clone()), nlit(1)),
            &nadd(d0.clone(), nadd(nadd(vnu.clone(), uq.clone()), nlit(1))),
        )?
        .under(&mut fr, |z| nmod(z, pw3.clone())),
    )
    .then(f.under(&mut fr, |z| nmod(nadd(d01.clone(), z), pw4.clone())))
    .then(
        ring_eq(
            &mut fr,
            &nadd(d0.clone(), pw.clone()),
            &nadd(d0.clone(), nmul(pw.clone(), nlit(1))),
        )?
        .under(&mut fr, |z| nmod(z, pw.clone())),
    )
    .then(Eqn::cite(
        bvv::ADD_MUL_MOD_SELF,
        vec![d0.clone(), pw.clone(), nlit(1), hp.clone()],
        nmod(nadd(d0.clone(), nmul(pw.clone(), nlit(1))), pw.clone()),
        nmod(d0.clone(), pw.clone()),
    ))
    .then(Eqn::cite(
        names::MOD_EQ_OF_LT,
        vec![d0.clone(), pw.clone(), hd0],
        nmod(d0.clone(), pw.clone()),
        d0.clone(),
    ));
    // `V h = D / 2`.
    let vh =
        hyp(veh.clone(), ndiv(val(&s), nlit(2)), hhv).then(vs.under(&mut fr, |z| ndiv(z, nlit(2))));
    // `uq + D / 2 < P W`.
    let d2 = ndiv(d0.clone(), nlit(2));
    let q2 = nadd(uq.clone(), d2.clone());
    let b1 = cite(names::DIV_LE_SELF, [d0.clone(), nlit(2), pos_two()]);
    let b2 = cite(bvv::ADD_LE_ADD_RIGHT, [d2.clone(), d0.clone(), uq.clone(), b1]);
    let b3 = le_rw(
        &mut fr,
        b2,
        &nadd(d2.clone(), uq.clone()),
        &nadd(d0.clone(), uq.clone()),
        &q2,
        &nadd(d0.clone(), uq.clone()),
    )?;
    let b4 = le_subst_right(&mut fr, &q2, b3, eqx);
    let b5 = cite("Nat.succ_le_succ", [q2.clone(), vx.clone(), b4]);
    let hq2 = le_trans(&succ(q2.clone()), &succ(vx.clone()), &pw, b5, hxlt);
    // `V t = uq + D / 2`.
    let (vu1, veh1, pw5, pw6, uq1) = (vu.clone(), veh.clone(), pw.clone(), pw.clone(), uq.clone());
    let veh2 = veh.clone();
    let vt0 = Eqn::cite(
        bvv::ADD_REC_M_VAL,
        vec![u.clone(), eh.clone(), kx::bfalse()],
        val(&t),
        nmod(nadd(nadd(vu.clone(), veh.clone()), btn(kx::bfalse())), two_pow(len(&u))),
    )
    .then(Eqn::by_defeq(
        nmod(nadd(nadd(vu.clone(), veh.clone()), btn(kx::bfalse())), two_pow(len(&u))),
        nmod(nadd(vu.clone(), veh.clone()), two_pow(len(&u))),
    ))
    .then(l_u.clone().under(&mut fr, |z| nmod(nadd(vu1.clone(), veh1.clone()), two_pow(z))))
    .then(v_u.under(&mut fr, |z| nmod(nadd(z, veh2.clone()), pw5.clone())))
    .then(vh.under(&mut fr, |z| nmod(nadd(uq1.clone(), z), pw6.clone())))
    .then(Eqn::cite(
        names::MOD_EQ_OF_LT,
        vec![q2.clone(), pw.clone(), hq2],
        nmod(q2.clone(), pw.clone()),
        q2.clone(),
    ));
    // `uq + D / 2 = V x (P W + V mk) / (2 P W)`.
    let big_m = nadd(pw.clone(), vmk.clone());
    let am = nmul(vx.clone(), big_m.clone());
    let n2 = nmul(nlit(2), pw.clone());
    let mul = Eqn::cite(
        names::ADDBACK_MUL,
        vec![vx.clone(), vmk.clone(), pw.clone(), d0.clone(), hp, split.proof],
        q2,
        ndiv(am.clone(), n2.clone()),
    );
    let pk = two_pow(b.k.clone());
    let sw = succ(w.clone());
    let p = nadd(sw.clone(), b.k.clone());
    let (pk1, am1, am2) = (pk.clone(), am.clone(), am.clone());
    let it = iter(b.k.clone(), t.clone());
    let vt = Eqn::cite(
        names::ITER_VAL,
        vec![b.k.clone(), t.clone()],
        val(&it),
        ndiv(val(&t), pk.clone()),
    )
    .then(vt0.then(mul).under(&mut fr, |z| ndiv(z, pk1.clone())))
    .then(Eqn::cite(
        names::DIV_DIV,
        vec![
            am.clone(),
            n2.clone(),
            pk.clone(),
            cite(bvv::TWO_POW_POS, [sw.clone()]),
            cite(bvv::TWO_POW_POS, [b.k.clone()]),
        ],
        ndiv(ndiv(am.clone(), n2.clone()), pk.clone()),
        ndiv(am.clone(), nmul(n2.clone(), pk.clone())),
    ))
    .then(Eqn::by_defeq(
        ndiv(am1, nmul(n2, pk.clone())),
        ndiv(am.clone(), nmul(two_pow(sw.clone()), pk.clone())),
    ))
    .then(
        Eqn::cite(
            bvv::TWO_POW_ADD,
            vec![sw.clone(), b.k.clone()],
            two_pow(p.clone()),
            nmul(two_pow(sw), pk),
        )
        .symm()
        .under(&mut fr, |z| ndiv(am2.clone(), z)),
    );
    let lt = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![u.clone(), eh, kx::bfalse()],
        len(&t),
        len(&u),
    )
    .then(l_u);
    let body = magic_tail(
        &mut fr,
        MagicTail {
            x: &x,
            c: &b.c,
            t: &t,
            k: &b.k,
            j: &b.j,
            w: &w,
            hx: &b.hx,
            hjk: &b.hjk,
            lt,
            vt,
            big_m,
            p,
            e: b.e.clone(),
            hd: b.hd.clone(),
            hdm: b.hdm.clone(),
            hble: b.hble.clone(),
        },
    );
    Some((ty, lams(b.binders, body)))
}

/// The remainder tail (T3): `x + (q - q << n) = x - q * c` when
/// `c + 1 = 2^(V n)`, a ring identity modulo `P (L x)` with no range premise.
///
/// Values modulo `Q = P (L x)`: the left is `(x + q + ¬s + 1) % Q` and the
/// right `(x + ¬m + 1) % Q` (`s = q << n`, `m = q * c`, `¬v + v + 1 = Q`).
/// Adding `s` to both: `x + q + Q` against `x + q + m ≡ x + s`, since
/// `q * 2^n = q * c + q`; and `a % Q = ((a + s) % Q + ¬s + 1) % Q` cancels
/// it again.
fn rem_tail() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bxv, xb) = bvf_local(&mut fr);
    let (bdv, db) = bvf_local(&mut fr);
    let (bn, n) = list_local(&mut fr);
    let (bc, c) = list_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (hx_id, hx) = fr.local();
    let (hd_id, hd) = fr.local();
    let (hc_id, hc) = fr.local();
    let (hv_id, hv) = fr.local();
    let x = eval(xb.clone());
    let q = eval(db.clone());
    let binders = vec![
        bxv,
        bdv,
        bn,
        bc,
        bm,
        (hx_id, eq(nat(), len(&x), succ(m.clone()))),
        (hd_id, eq(nat(), len(&q), len(&x))),
        (hc_id, eq(nat(), len(&c), len(&x))),
        (hv_id, eq(nat(), succ(val(&c)), two_pow(val(&n)))),
    ];
    let lhs_bvf =
        kx::add(xb.clone(), kx::sub(db.clone(), kx::shl(db.clone(), kx::const_(n.clone()))));
    let rhs_bvf = kx::sub(xb.clone(), kx::mul(db.clone(), kx::const_(c.clone())));
    let ty = pis(binders.clone(), kx::eq_list(eval(lhs_bvf), eval(rhs_bvf)));
    let sh = bv_shl(q.clone(), n.clone());
    let mu = bvmul(q.clone(), c.clone());
    let inner = addm(q.clone(), kx::bv_not(sh.clone()), kx::btrue());
    let lhs = addm(x.clone(), inner.clone(), kx::bfalse());
    let rhs = addm(x.clone(), kx::bv_not(mu.clone()), kx::btrue());
    let lx = len(&x);
    let bq = two_pow(lx.clone());
    let pos = cite(bvv::TWO_POW_POS, [lx.clone()]);
    let hd_eq = hyp(len(&q), lx.clone(), hd);
    let hc_eq = hyp(len(&c), lx.clone(), hc);
    // Lengths.
    let hl = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![x.clone(), inner.clone(), kx::bfalse()],
        len(&lhs),
        lx.clone(),
    )
    .then(
        Eqn::cite(
            add_comm::names::LEN_ADD_REC_M,
            vec![x.clone(), kx::bv_not(mu.clone()), kx::btrue()],
            len(&rhs),
            lx.clone(),
        )
        .symm(),
    );
    // Facts.
    let (vx, vq, vc, vn) = (val(&x), val(&q), val(&c), val(&n));
    let (s_, mu_) = (val(&sh), val(&mu));
    let ns = val(&kx::bv_not(sh.clone()));
    let nm = val(&kx::bv_not(mu.clone()));
    let qpn = nmul(vq.clone(), two_pow(vn.clone()));
    let lsh = Eqn::cite(bvv::LEN_NAT_TO_BV, vec![len(&q), qpn.clone()], len(&sh), len(&q))
        .then(hd_eq.clone());
    let f1 = Eqn::cite(
        bvv::BV_NOT_VAL,
        vec![sh.clone()],
        nadd(nadd(ns.clone(), s_.clone()), nlit(1)),
        two_pow(len(&sh)),
    )
    .then(lsh.under(&mut fr, |z| two_pow(z)));
    let hq = hd_eq.clone().then(hyp(lx.clone(), succ(m.clone()), hx));
    let lmu = Eqn::cite(
        add_comm::names::LEN_BV_MUL,
        vec![q.clone(), c.clone(), m.clone(), hq.proof],
        len(&mu),
        len(&c),
    )
    .then(hc_eq.clone());
    let f2 = Eqn::cite(
        bvv::BV_NOT_VAL,
        vec![mu.clone()],
        nadd(nadd(nm.clone(), mu_.clone()), nlit(1)),
        two_pow(len(&mu)),
    )
    .then(lmu.under(&mut fr, |z| two_pow(z)));
    let qpn1 = qpn.clone();
    let f3 = Eqn::cite(
        bvv::TO_NAT_NAT_TO_BV,
        vec![len(&q), qpn.clone()],
        s_.clone(),
        nmod(qpn.clone(), two_pow(len(&q))),
    )
    .then(hd_eq.clone().under(&mut fr, |z| nmod(qpn1.clone(), two_pow(z))));
    let qc = nmul(vq.clone(), vc.clone());
    let qc1 = qc.clone();
    let f4 = Eqn::cite(
        bvv::BV_MUL_VAL,
        vec![q.clone(), c.clone()],
        mu_.clone(),
        nmod(qc.clone(), two_pow(len(&c))),
    )
    .then(hc_eq.under(&mut fr, |z| nmod(qc1.clone(), two_pow(z))));
    let f5 = hyp(succ(vc.clone()), two_pow(vn.clone()), hv);
    // `V lhs = A' % Q`.
    let a0 = nadd(nadd(vq.clone(), ns.clone()), nlit(1));
    let (vx1, bq1, bq2) = (vx.clone(), bq.clone(), bq.clone());
    let vinner = Eqn::cite(
        bvv::ADD_REC_M_VAL,
        vec![q.clone(), kx::bv_not(sh.clone()), kx::btrue()],
        val(&inner),
        nmod(nadd(nadd(vq.clone(), ns.clone()), btn(kx::btrue())), two_pow(len(&q))),
    )
    .then(Eqn::by_defeq(
        nmod(nadd(nadd(vq.clone(), ns.clone()), btn(kx::btrue())), two_pow(len(&q))),
        nmod(a0.clone(), two_pow(len(&q))),
    ))
    .then({
        let a01 = a0.clone();
        hd_eq.under(&mut fr, move |z| nmod(a01.clone(), two_pow(z)))
    });
    let vl = Eqn::cite(
        bvv::ADD_REC_M_VAL,
        vec![x.clone(), inner.clone(), kx::bfalse()],
        val(&lhs),
        nmod(nadd(nadd(vx.clone(), val(&inner)), btn(kx::bfalse())), bq.clone()),
    )
    .then(Eqn::by_defeq(
        nmod(nadd(nadd(vx.clone(), val(&inner)), btn(kx::bfalse())), bq.clone()),
        nmod(nadd(vx.clone(), val(&inner)), bq.clone()),
    ))
    .then(vinner.under(&mut fr, |z| nmod(nadd(vx1.clone(), z), bq1.clone())))
    .then(Eqn::cite(
        bvv::ADD_MOD_MOD,
        vec![vx.clone(), a0.clone(), bq.clone(), pos.clone()],
        nmod(nadd(vx.clone(), nmod(a0.clone(), bq.clone())), bq.clone()),
        nmod(nadd(vx.clone(), a0.clone()), bq2.clone()),
    ));
    let ap = nadd(vx.clone(), a0.clone());
    // `V rhs = B' % Q`.
    let bp = nadd(nadd(vx.clone(), nm.clone()), nlit(1));
    let vr = Eqn::cite(
        bvv::ADD_REC_M_VAL,
        vec![x.clone(), kx::bv_not(mu.clone()), kx::btrue()],
        val(&rhs),
        nmod(nadd(nadd(vx.clone(), nm.clone()), btn(kx::btrue())), bq.clone()),
    )
    .then(Eqn::by_defeq(
        nmod(nadd(nadd(vx.clone(), nm.clone()), btn(kx::btrue())), bq.clone()),
        nmod(bp.clone(), bq.clone()),
    ));
    // `a % Q = ((a + s) % Q + (¬s + 1)) % Q`.
    let tt = nadd(ns.clone(), nlit(1));
    let g = |fr: &mut Fresh, a: &Expr| -> Option<Eqn> {
        let (a1, a2, bq3, bq4) = (a.clone(), a.clone(), bq.clone(), bq.clone());
        Some(
            Eqn::cite(
                bvv::ADD_MUL_MOD_SELF,
                vec![a.clone(), bq.clone(), nlit(1), pos.clone()],
                nmod(nadd(a.clone(), nmul(bq.clone(), nlit(1))), bq.clone()),
                nmod(a.clone(), bq.clone()),
            )
            .symm()
            .then(
                f1.clone()
                    .symm()
                    .under(fr, move |z| nmod(nadd(a1.clone(), nmul(z, nlit(1))), bq3.clone())),
            )
            .then(
                ring_eq(
                    fr,
                    &nadd(a2.clone(), nmul(nadd(nadd(ns.clone(), s_.clone()), nlit(1)), nlit(1))),
                    &nadd(nadd(a2, s_.clone()), tt.clone()),
                )?
                .under(fr, move |z| nmod(z, bq4.clone())),
            )
            .then(
                Eqn::cite(
                    bvv::MOD_ADD_MOD,
                    vec![nadd(a.clone(), s_.clone()), tt.clone(), bq.clone(), pos.clone()],
                    nmod(
                        nadd(nmod(nadd(a.clone(), s_.clone()), bq.clone()), tt.clone()),
                        bq.clone(),
                    ),
                    nmod(nadd(nadd(a.clone(), s_.clone()), tt.clone()), bq.clone()),
                )
                .symm(),
            ),
        )
    };
    let ga = g(&mut fr, &ap)?;
    let gb = g(&mut fr, &bp)?;
    // `(A' + s) % Q = (B' + s) % Q`.
    let xq = nadd(vx.clone(), vq.clone());
    let (xq1, xq2) = (xq.clone(), xq.clone());
    let bpq = nadd(bp.clone(), vq.clone());
    let (bq5, bq6, bq7, bq8, bq9) = (bq.clone(), bq.clone(), bq.clone(), bq.clone(), bq.clone());
    let (bpq1, bp1, bp2, vq1) = (bpq.clone(), bp.clone(), bp.clone(), vq.clone());
    let h = ring_eq(
        &mut fr,
        &nadd(ap.clone(), s_.clone()),
        &nadd(xq.clone(), nadd(nadd(ns.clone(), s_.clone()), nlit(1))),
    )?
    .then(f1.under(&mut fr, move |z| nadd(xq1.clone(), z)))
    .then(f2.symm().under(&mut fr, move |z| nadd(xq2.clone(), z)))
    .then(ring_eq(
        &mut fr,
        &nadd(xq.clone(), nadd(nadd(nm.clone(), mu_.clone()), nlit(1))),
        &nadd(bpq.clone(), mu_.clone()),
    )?)
    .under(&mut fr, move |z| nmod(z, bq5.clone()))
    .then(f4.under(&mut fr, move |z| nmod(nadd(bpq1.clone(), z), bq6.clone())))
    .then(Eqn::cite(
        bvv::ADD_MOD_MOD,
        vec![bpq.clone(), qc.clone(), bq.clone(), pos.clone()],
        nmod(nadd(bpq.clone(), nmod(qc.clone(), bq.clone())), bq.clone()),
        nmod(nadd(bpq.clone(), qc.clone()), bq.clone()),
    ))
    .then(
        ring_eq(
            &mut fr,
            &nadd(bpq.clone(), qc.clone()),
            &nadd(bp.clone(), nmul(vq.clone(), succ(vc.clone()))),
        )?
        .under(&mut fr, move |z| nmod(z, bq7.clone())),
    )
    .then(f5.under(&mut fr, move |z| nmod(nadd(bp1.clone(), nmul(vq1.clone(), z)), bq8.clone())))
    .then(
        Eqn::cite(
            bvv::ADD_MOD_MOD,
            vec![bp.clone(), qpn.clone(), bq.clone(), pos.clone()],
            nmod(nadd(bp.clone(), nmod(qpn.clone(), bq.clone())), bq.clone()),
            nmod(nadd(bp.clone(), qpn.clone()), bq.clone()),
        )
        .symm(),
    )
    .then(f3.symm().under(&mut fr, move |z| nmod(nadd(bp2.clone(), z), bq9.clone())));
    let (tt1, bq10) = (tt.clone(), bq.clone());
    let hv_eq = vl
        .then(ga)
        .then(h.under(&mut fr, move |z| nmod(nadd(z, tt1.clone()), bq10.clone())))
        .then(gb.symm())
        .then(vr.symm());
    let body = cite(bvv::INJ, [lhs, rhs, hl.proof, hv_eq.proof]);
    Some((ty, lams(binders, body)))
}

// ── registration and the audited environment ─────────────────────────────────

type Builder = fn() -> Option<(Expr, Expr)>;

/// The theorems in dependency order.
fn builders() -> [(&'static str, Builder); 24] {
    [
        (names::MOD_EQ_OF_LT, mod_eq_of_lt),
        (names::DIV_ONE, div_one),
        (names::DIV_DIV, div_div),
        (names::DIV_LE_SELF, div_le_self),
        (names::LE_ADD_CANCEL, le_add_cancel),
        (names::MUL_LT_MUL, mul_lt_mul),
        (names::GM_DIV, gm_div),
        (names::ADDBACK_SPLIT, addback_split),
        (names::ADDBACK_MUL, addback_mul),
        (names::TO_NAT_LT, to_nat_lt),
        (names::BTAIL_VAL, btail_val),
        (names::BTAIL_LEN, btail_len),
        (names::ITER_VAL, iter_val),
        (names::ITER_LEN, iter_len),
        (names::ZX_VAL, zx_val),
        (names::ZX_LEN, zx_len),
        (names::N2B_DIV_VAL, n2b_div_val),
        (names::UMULH_VAL, umulh_val),
        (names::UMULH_LEN, umulh_len),
        (names::LSHR_K, lshr_k),
        (names::UBFM_K, ubfm_k),
        (names::MAGIC_NOADD, magic_noadd),
        (names::MAGIC_ADDBACK, magic_addback),
        (names::REM_TAIL, rem_tail),
    ]
}

/// `(name, statement, proof)` for every theorem; `Err` names a theorem the
/// untrusted builder (the normaliser) could not produce.
pub(crate) fn theorems() -> Result<Vec<(&'static str, Expr, Expr)>, String> {
    builders()
        .into_iter()
        .map(|(name, build)| {
            build().map(|(ty, val)| (name, ty, val)).ok_or_else(|| format!("{name}: not built"))
        })
        .collect()
}

/// Add the theorems to `env`; each is a `Declaration::Theorem`, so
/// `add_decl` type-checks its proof against its statement.
pub(crate) fn register(env: &mut Environment) -> Result<(), String> {
    for (name, type_, value) in theorems()? {
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
        })
        .map_err(|e| format!("{name}: {e:?}"))?;
    }
    Ok(())
}

/// Every theorem the constant-division environment audits: the branch
/// audit (which includes the strength audit), this module's theorems and
/// their citations.
pub(crate) fn audited() -> Vec<&'static str> {
    let mut all = branch_theory::audited();
    all.extend(names::ALL);
    all.extend(CITED);
    all
}

/// `base` plus the theorems, audited (split out so a test can hand it a
/// doctored base).
pub(crate) fn build_base(mut env: Environment) -> Result<Environment, String> {
    register(&mut env)?;
    audit_theorems(&env, &audited())?;
    Ok(env)
}

/// `strength_base` plus `Trust.BVD`, built and audited once per process
/// (an `Err` or a panic during the build is kept). Call it on a kernel
/// re-check thread. It starts from the branch base (`strength_base` plus
/// `Trust.BVB`): the goal reflection is the branch split's, whose `Ite` and
/// faithful-division steps cite `Trust.BVB`.
pub(crate) fn const_div_base() -> Result<&'static Environment, String> {
    static BASE: OnceLock<Result<Environment, String>> = OnceLock::new();
    BASE.get_or_init(|| {
        std::panic::catch_unwind(|| build_base(branch_theory::branch_base()?.clone()))
            .unwrap_or_else(|_| Err("the constant-division base build panicked".to_string()))
    })
    .as_ref()
    .map_err(Clone::clone)
}

/// The environment a constant-division discharge is checked in.
pub(crate) fn const_div_env(leaves: &[(String, u32)]) -> Result<Environment, String> {
    let mut env = const_div_base()?.clone();
    add_comm::add_leaf_bits(&mut env, leaves);
    Ok(env)
}

/// The label of an admitted discharge: the `Trust.BVD` / `Trust.BVB` /
/// `Trust.BVS` / `Trust.BVV` / `Trust.BVC` / `Clean.BVC` THEOREMS in the
/// term itself (sorted), then [`LABEL_TAIL`].
pub(crate) fn label(env: &Environment, proof: &Expr) -> String {
    let mut used = HashSet::new();
    proof.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
    let mut parts: Vec<String> = used
        .into_iter()
        .filter(|n| {
            let s = n.to_string();
            ["Trust.BVD.", "Trust.BVB.", "Trust.BVS.", "Trust.BVV.", "Trust.BVC.", "Clean.BVC."]
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

// ── per-obligation instances ─────────────────────────────────────────────────

/// `magic_noadd X mk c m j k e hx hmk hjk hd hdm hble`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn magic_noadd_inst(args: [Expr; 13]) -> Expr {
    cite(names::MAGIC_NOADD, args)
}

/// `magic_addback X H mk c m j k e hx hmk hjk hhv hd hdm hble`.
pub(crate) fn magic_addback_inst(args: [Expr; 15]) -> Expr {
    cite(names::MAGIC_ADDBACK, args)
}

/// `lshr_k S n k h`.
pub(crate) fn lshr_k_inst(s: Expr, n: Expr, k: Expr, h: Expr) -> Expr {
    cite(names::LSHR_K, [s, n, k, h])
}

/// `ubfm_k S k`.
pub(crate) fn ubfm_k_inst(s: Expr, k: Expr) -> Expr {
    cite(names::UBFM_K, [s, k])
}

/// `rem_tail X D n c m hx hd hc hv`.
pub(crate) fn rem_tail_inst(args: [Expr; 9]) -> Expr {
    cite(names::REM_TAIL, args)
}

/// `(M, p)` of an instance, as [`magic_mp`] states them (for the premises).
pub(crate) fn magic_mp_inst(add: bool, mk: &Expr, m: &Expr, k: &Expr) -> (Expr, Expr) {
    magic_mp(add, mk, m, k)
}
