// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The kernel theory of the branch split (BRANCH-SPLIT-1): the `Trust.BVB.*`
//! and `Trust.BVS.mul_add_self` theorems, the audited environment they live
//! in, the constant decoder, and the label of a proved conjunction.
//!
//! # What is proved here
//!
//! Every statement below is a `Declaration::Theorem` whose proof the Clean
//! kernel type-checks when it is added (`L = bvLen`, `V = bvToNat`,
//! `A = addRecM`, `M = bvMul`, `NOT = bvNot`, `AF = bvAllFalse`,
//! `CO = carryOut`):
//!
//! ```text
//! and_true        : ∀ x, and x true = x
//! not_not         : ∀ x, not (not x) = x
//! maj_not         : ∀ g h c, not (maj g (not h) c) = maj h (not g) (not c)
//! not_or_not      : ∀ p q, not (or (not p) q) = and p (not q)
//! ite_true        : ∀ a e, bvIteVal true a e = a
//! ite_false       : ∀ a e, bvIteVal false a e = e
//! ite_cong        : ∀ p p' a a' e e', p = p' → a = a' → e = e' →
//!                     bvIteVal p a e = bvIteVal p' a' e'
//! beq_allFalse    : ∀ y, bvBeq y (AF y) = bvIsZero y
//! carry_swap      : ∀ a b c, L a = L b →
//!                     CO b (NOT a) c = not (CO a (NOT b) (not c))
//! carry_false_true: ∀ a b, L a = L b →
//!                     CO a (NOT b) false = and (CO a (NOT b) true) (not (bvBeq a b))
//! not_ule_ult_swap: ∀ a b, L a = L b → not (bvULe a b) = bvUlt b a
//! hi_ult          : ∀ a b, L a = L b →
//!                     and (not (bvUlt a b)) (not (bvBeq D (AF D))) = bvUlt b a,
//!                     D = A a (NOT b) true            (AArch64 `b.hi` / `b.ls`)
//! zipAnd_allFalse : ∀ t, bvBeq (bvZipAnd t (AF t)) (AF t) = true
//! beq_and_lowbit  : ∀ h t, bvBeq (bvZipAnd (h::t) (true :: AF t)) (false :: AF t) = not h
//! sub_zero        : ∀ a, A a (NOT (AF a)) true = a
//! mul_add_self    : ∀ x c1 c2 m, L x = succ m → L c1 = L x → L c2 = L x →
//!                     V c2 = succ (V c1) → A (M x c1) x false = M x c2
//! zext_drop1_div2 : ∀ h t c, V c = 2 → bvZeroExt (btail (h :: t)) 1 = bvDiv (h :: t) c
//! flags3          : ∀ n x y, xor (bvBeq [n] [true]) (and (not (bvBeq [x] [y])) (not (bvBeq [n] [x])))
//!                     = xor n (and (xor x y) (xor n x))
//! slt_flags       : ∀ a b, bvIsCons a = true → L a = L b →
//!                     xor (bvBeq [N] [true]) (and (not (bvBeq [LB a] [LB b])) (not (bvBeq [N] [LB a])))
//!                     = bvSLtReal a b,  N = LB (A a (NOT b) true), LB = bvLastBit
//!                                                         (AArch64 `b.ge` / `b.lt`)
//! ```
//!
//! The Bool identities split every variable with `Bool.rec` and close each
//! case by computation. The list theorems are `List.rec` inductions in the
//! style of `add_comm`; a length premise refutes the mismatched cases
//! (`zero = succ _`). `mul_add_self` goes through the values (`bv_value`), as
//! `strength::collect_add` does, and `zext_drop1_div2` through the value
//! theory's `natToBv_toNat` and `div_unique`. No Bool-valued `Nat` comparison
//! is used. The plan's `dropLow` definition is not added: the high extract is
//! `btail` iterated (`branch_reflect::high_extract`), an existing definition,
//! so the trusted base gains no definition.
//!
//! # The audit
//!
//! [`branch_base`] is the strength base plus these theorems, built once per
//! process. Every THEOREM it cites ([`audited`]) must be a proved `Theorem`
//! with an empty domain and foundational closure (`add_comm::audit_theorems`,
//! unchanged). Definitions (`bvIteVal`, `bvBeq`, `bvUlt`, …) and recursors
//! are not theorems and are not audited by name: `strength::admit_obligation`
//! checks the transitive closure of every admitted term, through every
//! definition and recursor it reaches.
//!
//! # Authority
//!
//! Nothing here decides a grade. A theorem is checked by `add_decl`; an
//! instance is a term the caller splices into a discharge that the kernel
//! checks against a goal built independently of it.

use std::collections::HashSet;
use std::sync::OnceLock;

use clean_kernel::expr::UsedConstants;
use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, Declaration, Environment, Expr, ExprKind, FVarId, Level};

use super::add_comm::{self, audit_theorems};
use super::bv_value::{btn, names as bvv};
use super::kterm::{
    Fresh, absurd_zero_eq_succ, addm, bool_rec, bool_ty, btail, bvlen, bvmul, congr_arg, eq, lams,
    lb, list_rec_prop, maj, nadd, nat, nat_pred, nat_to_bv, ndiv, nlit, nmod, nmul, pis, refl,
    repl_f, succ, symm, to_nat, trans, two_pow, zero_ext,
};
use super::nat_ring::Eqn;
use super::{kx, strength};

/// The theorems this module proves.
pub(crate) mod names {
    pub(crate) const AND_TRUE: &str = "Trust.BVB.and_true";
    pub(crate) const NOT_NOT: &str = "Trust.BVB.not_not";
    pub(crate) const MAJ_NOT: &str = "Trust.BVB.maj_not";
    pub(crate) const NOT_OR_NOT: &str = "Trust.BVB.not_or_not";
    pub(crate) const ITE_TRUE: &str = "Trust.BVB.ite_true";
    pub(crate) const ITE_FALSE: &str = "Trust.BVB.ite_false";
    pub(crate) const ITE_CONG: &str = "Trust.BVB.ite_cong";
    pub(crate) const BEQ_ALL_FALSE: &str = "Trust.BVB.beq_allFalse";
    pub(crate) const CARRY_SWAP: &str = "Trust.BVB.carry_swap";
    pub(crate) const CARRY_FALSE_TRUE: &str = "Trust.BVB.carry_false_true";
    pub(crate) const NOT_ULE_ULT_SWAP: &str = "Trust.BVB.not_ule_ult_swap";
    pub(crate) const HI_ULT: &str = "Trust.BVB.hi_ult";
    pub(crate) const ZIP_AND_ALL_FALSE: &str = "Trust.BVB.zipAnd_allFalse";
    pub(crate) const BEQ_AND_LOWBIT: &str = "Trust.BVB.beq_and_lowbit";
    pub(crate) const SUB_ZERO: &str = "Trust.BVB.sub_zero";
    pub(crate) const MUL_ADD_SELF: &str = "Trust.BVS.mul_add_self";
    pub(crate) const ZEXT_DROP1_DIV2: &str = "Trust.BVS.zext_drop1_div2";
    pub(crate) const FLAGS3: &str = "Trust.BVB.flags3";
    pub(crate) const SLT_FLAGS: &str = "Trust.BVB.slt_flags";
    pub(crate) const ALL: [&str; 19] = [
        AND_TRUE,
        NOT_NOT,
        MAJ_NOT,
        NOT_OR_NOT,
        ITE_TRUE,
        ITE_FALSE,
        ITE_CONG,
        BEQ_ALL_FALSE,
        CARRY_SWAP,
        CARRY_FALSE_TRUE,
        NOT_ULE_ULT_SWAP,
        HI_ULT,
        ZIP_AND_ALL_FALSE,
        BEQ_AND_LOWBIT,
        SUB_ZERO,
        MUL_ADD_SELF,
        ZEXT_DROP1_DIV2,
        FLAGS3,
        SLT_FLAGS,
    ];
}

/// The pinned-layer and prelude THEOREMS the proofs and instances here cite,
/// besides [`names::ALL`] and `strength::audited`.
pub(crate) const CITED: [&str; 7] = [
    "Clean.BVC.beq_eq_isZero_sub",
    "Clean.BVC.demorgan_and_not",
    "Clean.BVC.divGuardBridge",
    "Clean.BVC.slt_flag_bridge",
    "congrArg",
    "Eq.trans",
    "Eq.symm",
];

/// The last part of the label of a conjunction proved by the branch split.
pub(crate) const LABEL_TAIL: &str =
    "kernel atom case split (O(1) branching conjunction, BRANCH-SPLIT-1)";

/// No concrete list this module decodes is longer than this.
const MAX_BITS: usize = 64;

// ── small builders ───────────────────────────────────────────────────────────

fn cite(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}
fn tt() -> Expr {
    kx::btrue()
}
fn ff() -> Expr {
    kx::bfalse()
}
fn lit(b: bool) -> Expr {
    if b { tt() } else { ff() }
}
pub(crate) fn bnot(x: Expr) -> Expr {
    kx::bnot(x)
}
pub(crate) fn band(x: Expr, y: Expr) -> Expr {
    kx::band(x, y)
}
pub(crate) fn bor(x: Expr, y: Expr) -> Expr {
    Expr::apps(Expr::const_str("Bool.or"), [x, y])
}
fn eqb(a: Expr, b: Expr) -> Expr {
    eq(bool_ty(), a, b)
}
fn eql(a: Expr, b: Expr) -> Expr {
    eq(lb(), a, b)
}
fn carry(a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.carryOut"), [a, b, c])
}
fn zip_and(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.bvZipAnd"), [a, b])
}
fn af(a: Expr) -> Expr {
    kx::all_false(a)
}
fn nt(a: Expr) -> Expr {
    kx::bv_not(a)
}
fn len(e: &Expr) -> Expr {
    bvlen(e.clone())
}
fn val(e: &Expr) -> Expr {
    to_nat(e.clone())
}
fn list_local(fr: &mut Fresh) -> ((FVarId, Expr), Expr) {
    let (id, v) = fr.local();
    ((id, lb()), v)
}
fn bool_local(fr: &mut Fresh) -> ((FVarId, Expr), Expr) {
    let (id, v) = fr.local();
    ((id, bool_ty()), v)
}
fn len_eq(a: &Expr, b: &Expr) -> Expr {
    eq(nat(), len(a), len(b))
}

/// `congrArg (fun t : A => body t) h : body lhs = body rhs` for `h : lhs = rhs`.
fn under(
    fr: &mut Fresh,
    a_ty: Expr,
    b_ty: Expr,
    lhs: Expr,
    rhs: Expr,
    h: Expr,
    body: impl Fn(Expr) -> Expr,
) -> Expr {
    let (t_id, t) = fr.local();
    let f = lams(vec![(t_id, a_ty.clone())], body(t));
    congr_arg(a_ty, b_ty, lhs, rhs, f, h)
}

/// Split the Bool variables `vars` in order with `Bool.rec` (motive into
/// `Prop`), stating `stmt` at each step; `leaf` closes each fully assigned
/// case.
fn split_bools(
    fr: &mut Fresh,
    vars: &[Expr],
    assigned: &mut Vec<bool>,
    stmt: &dyn Fn(&[Expr]) -> Expr,
    leaf: &mut dyn FnMut(&mut Fresh, &[bool]) -> Expr,
) -> Expr {
    let i = assigned.len();
    if i == vars.len() {
        return leaf(fr, assigned);
    }
    let at = |assigned: &[bool], z: Expr| -> Vec<Expr> {
        let mut v: Vec<Expr> = assigned.iter().map(|&b| lit(b)).collect();
        v.push(z);
        v.extend(vars[i + 1..].iter().cloned());
        v
    };
    let (z_id, z) = fr.local();
    let motive = lams(vec![(z_id, bool_ty())], stmt(&at(assigned, z)));
    assigned.push(false);
    let on_false = split_bools(fr, vars, assigned, stmt, leaf);
    assigned.pop();
    assigned.push(true);
    let on_true = split_bools(fr, vars, assigned, stmt, leaf);
    assigned.pop();
    bool_rec(Level::zero(), motive, on_false, on_true, vars[i].clone())
}

/// `∀ x1 … xn : Bool, lhs = rhs`, every case closed by computation.
fn bool_identity(n: usize, sides: impl Fn(&[Expr]) -> (Expr, Expr)) -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let stmt = |v: &[Expr]| {
        let (l, r) = sides(v);
        eqb(l, r)
    };
    let binders: Vec<((FVarId, Expr), Expr)> = (0..n).map(|_| bool_local(&mut fr)).collect();
    let vars: Vec<Expr> = binders.iter().map(|(_, v)| v.clone()).collect();
    let ids: Vec<(FVarId, Expr)> = binders.iter().map(|(b, _)| b.clone()).collect();
    let ty = pis(ids.clone(), stmt(&vars));
    let mut leaf = |_: &mut Fresh, bits: &[bool]| {
        let lits: Vec<Expr> = bits.iter().map(|&b| lit(b)).collect();
        refl(bool_ty(), sides(&lits).0)
    };
    let body = split_bools(&mut fr, &vars, &mut Vec::new(), &stmt, &mut leaf);
    (ty, lams(ids, body))
}

// ── Bool identities ──────────────────────────────────────────────────────────

fn and_true() -> (Expr, Expr) {
    bool_identity(1, |v| (band(v[0].clone(), tt()), v[0].clone()))
}
fn not_not() -> (Expr, Expr) {
    bool_identity(1, |v| (bnot(bnot(v[0].clone())), v[0].clone()))
}
fn maj_not() -> (Expr, Expr) {
    bool_identity(3, |v| {
        let (g, h, c) = (v[0].clone(), v[1].clone(), v[2].clone());
        (bnot(maj(g.clone(), bnot(h.clone()), c.clone())), maj(h, bnot(g), bnot(c)))
    })
}
fn not_or_not() -> (Expr, Expr) {
    bool_identity(2, |v| {
        let (p, q) = (v[0].clone(), v[1].clone());
        (bnot(bor(bnot(p.clone()), q.clone())), band(p, bnot(q)))
    })
}

// ── bvIteVal ─────────────────────────────────────────────────────────────────

fn ite_lit(which: bool) -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let (ba, a) = list_local(&mut fr);
    let (be, e) = list_local(&mut fr);
    let lhs = kx::bv_ite_val(lit(which), a.clone(), e.clone());
    let rhs = if which { a } else { e };
    let ty = pis(vec![ba.clone(), be.clone()], eql(lhs, rhs.clone()));
    (ty, lams(vec![ba, be], refl(lb(), rhs)))
}

fn ite_cong() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let (bp, p) = bool_local(&mut fr);
    let (bp2, p2) = bool_local(&mut fr);
    let (ba, a) = list_local(&mut fr);
    let (ba2, a2) = list_local(&mut fr);
    let (be, e) = list_local(&mut fr);
    let (be2, e2) = list_local(&mut fr);
    let (hp_id, hp) = fr.local();
    let (ha_id, ha) = fr.local();
    let (he_id, he) = fr.local();
    let binders = vec![
        bp,
        bp2,
        ba,
        ba2,
        be,
        be2,
        (hp_id, eqb(p.clone(), p2.clone())),
        (ha_id, eql(a.clone(), a2.clone())),
        (he_id, eql(e.clone(), e2.clone())),
    ];
    let ite = |p: &Expr, a: &Expr, e: &Expr| kx::bv_ite_val(p.clone(), a.clone(), e.clone());
    let ty = pis(binders.clone(), eql(ite(&p, &a, &e), ite(&p2, &a2, &e2)));
    let (a_, e_) = (a.clone(), e.clone());
    let s1 = under(&mut fr, bool_ty(), lb(), p.clone(), p2.clone(), hp, |t| ite(&t, &a_, &e_));
    let (p2_, e_2) = (p2.clone(), e.clone());
    let s2 = under(&mut fr, lb(), lb(), a.clone(), a2.clone(), ha, |t| ite(&p2_, &t, &e_2));
    let (p2_2, a2_) = (p2.clone(), a2.clone());
    let s3 = under(&mut fr, lb(), lb(), e.clone(), e2.clone(), he, |t| ite(&p2_2, &a2_, &t));
    let tail = trans(lb(), ite(&p2, &a, &e), ite(&p2, &a2, &e), ite(&p2, &a2, &e2), s2, s3);
    let body = trans(lb(), ite(&p, &a, &e), ite(&p2, &a, &e), ite(&p2, &a2, &e2), s1, tail);
    (ty, lams(binders, body))
}

// ── list theorems ────────────────────────────────────────────────────────────

/// A one-variable list induction `∀ y, stmt y` whose cons case splits the
/// head with `Bool.rec` and closes each head value with `cons_leaf`.
fn list_induction(
    stmt: &dyn Fn(&Expr) -> Expr,
    nil_proof: Expr,
    cons_leaf: &dyn Fn(&mut Fresh, bool, &Expr, &Expr) -> Expr,
) -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let (by, y) = list_local(&mut fr);
    let ty = pis(vec![by.clone()], stmt(&y));
    let motive = {
        let (w_id, w) = fr.local();
        lams(vec![(w_id, lb())], stmt(&w))
    };
    let cons_case = {
        let (h_id, h) = fr.local();
        let (t_id, t) = fr.local();
        let (ih_id, ih) = fr.local();
        let (z_id, z) = fr.local();
        let m = lams(vec![(z_id, bool_ty())], stmt(&kx::cons(z, t.clone())));
        let on_false = cons_leaf(&mut fr, false, &t, &ih);
        let on_true = cons_leaf(&mut fr, true, &t, &ih);
        let body = bool_rec(Level::zero(), m, on_false, on_true, h);
        lams(vec![(h_id, bool_ty()), (t_id, lb()), (ih_id, stmt(&t))], body)
    };
    (ty, lams(vec![by], list_rec_prop(motive, nil_proof, cons_case, y)))
}

/// `beq_allFalse : ∀ y, bvBeq y (AF y) = bvIsZero y`.
fn beq_all_false() -> (Expr, Expr) {
    let stmt = |y: &Expr| eqb(kx::bv_beq(y.clone(), af(y.clone())), kx::bv_is_zero(y.clone()));
    list_induction(&stmt, refl(bool_ty(), tt()), &|_, head, _, ih| {
        if head { refl(bool_ty(), ff()) } else { ih.clone() }
    })
}

/// `zipAnd_allFalse : ∀ t, bvBeq (bvZipAnd t (AF t)) (AF t) = true`.
fn zip_and_all_false() -> (Expr, Expr) {
    let stmt = |t: &Expr| eqb(kx::bv_beq(zip_and(t.clone(), af(t.clone())), af(t.clone())), tt());
    list_induction(&stmt, refl(bool_ty(), tt()), &|_, _, _, ih| ih.clone())
}

/// `sub_zero : ∀ a, A a (NOT (AF a)) true = a`.
fn sub_zero() -> (Expr, Expr) {
    let stmt = |a: &Expr| eql(addm(a.clone(), nt(af(a.clone())), tt()), a.clone());
    list_induction(&stmt, refl(lb(), kx::nil()), &|fr, head, t, ih| {
        let tail = addm(t.clone(), nt(af(t.clone())), tt());
        under(fr, lb(), lb(), tail, t.clone(), ih.clone(), |u| kx::cons(lit(head), u))
    })
}

/// `beq_and_lowbit : ∀ h t, bvBeq (bvZipAnd (h::t) (true :: AF t)) (false :: AF t) = not h`.
fn beq_and_lowbit() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let (bh, h) = bool_local(&mut fr);
    let (bt, t) = list_local(&mut fr);
    let stmt = |h: &Expr, t: &Expr| {
        eqb(
            kx::bv_beq(
                zip_and(kx::cons(h.clone(), t.clone()), kx::cons(tt(), af(t.clone()))),
                kx::cons(ff(), af(t.clone())),
            ),
            bnot(h.clone()),
        )
    };
    let ty = pis(vec![bh.clone(), bt.clone()], stmt(&h, &t));
    let (z_id, z) = fr.local();
    let motive = lams(vec![(z_id, bool_ty())], stmt(&z, &t));
    let on_false = cite(names::ZIP_AND_ALL_FALSE, [t.clone()]);
    let on_true = refl(bool_ty(), ff());
    let body = bool_rec(Level::zero(), motive, on_false, on_true, h);
    (ty, lams(vec![bh, bt], body))
}

/// The two-list induction skeleton of `carry_swap` / `carry_false_true`:
/// `∀ a, ∀ b <extra>, L a = L b → goal a b <extra>`, by induction on `a`
/// and a case split on `b`; the mismatched cases refute the length premise.
/// `nil_nil` proves `goal [] [] <extra>`; `cons_cons` gets the heads, the
/// tails, the induction hypothesis (`∀ b <extra>, L as = L b → goal as b …`),
/// the extra binders and a proof of `L as = L bs`.
struct TwoList<'a> {
    /// The binders after `b`, as types (each `Bool`).
    extra: usize,
    goal: &'a dyn Fn(&Expr, &Expr, &[Expr]) -> Expr,
    nil_nil: &'a dyn Fn(&mut Fresh, &[Expr]) -> Expr,
    #[allow(clippy::type_complexity)]
    cons_cons: &'a dyn Fn(&mut Fresh, [&Expr; 4], &Expr, &[Expr], Expr) -> Expr,
}

fn two_list(spec: &TwoList<'_>) -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let all = |fr: &mut Fresh, a: &Expr| {
        let (b_id, b) = fr.local();
        let ex: Vec<(FVarId, Expr)> = (0..spec.extra).map(|_| fr.local()).collect();
        let exv: Vec<Expr> = ex.iter().map(|(_, v)| v.clone()).collect();
        let mut binders = vec![(b_id, lb())];
        binders.extend(ex.into_iter().map(|(id, _)| (id, bool_ty())));
        pis(binders, Expr::arrow(len_eq(a, &b), (spec.goal)(a, &b, &exv)))
    };
    let ty = {
        let (a_id, a) = fr.local();
        let body = all(&mut fr, &a);
        pis(vec![(a_id, lb())], body)
    };
    let motive = {
        let (w_id, w) = fr.local();
        let body = all(&mut fr, &w);
        lams(vec![(w_id, lb())], body)
    };
    let inner_motive = |fr: &mut Fresh, left: &Expr, exv: &[Expr]| {
        let (y_id, y) = fr.local();
        lams(vec![(y_id, lb())], Expr::arrow(len_eq(left, &y), (spec.goal)(left, &y, exv)))
    };
    let nil_case = {
        let (b_id, b) = fr.local();
        let ex: Vec<(FVarId, Expr)> = (0..spec.extra).map(|_| fr.local()).collect();
        let exv: Vec<Expr> = ex.iter().map(|(_, v)| v.clone()).collect();
        let left = kx::nil();
        let on_nil = {
            let (h_id, _) = fr.local();
            let body = (spec.nil_nil)(&mut fr, &exv);
            lams(vec![(h_id, len_eq(&left, &kx::nil()))], body)
        };
        let on_cons = {
            let (g_id, g) = fr.local();
            let (bs_id, bs) = fr.local();
            let (ih_id, _) = fr.local();
            let (h_id, h) = fr.local();
            let right = kx::cons(g, bs.clone());
            let ih_ty = Expr::arrow(len_eq(&left, &bs), (spec.goal)(&left, &bs, &exv));
            let body = absurd_zero_eq_succ(&mut fr, bvlen(bs), h, (spec.goal)(&left, &right, &exv));
            lams(
                vec![
                    (g_id, bool_ty()),
                    (bs_id, lb()),
                    (ih_id, ih_ty),
                    (h_id, len_eq(&left, &right)),
                ],
                body,
            )
        };
        let m = inner_motive(&mut fr, &left, &exv);
        let mut binders = vec![(b_id, lb())];
        binders.extend(ex.into_iter().map(|(id, _)| (id, bool_ty())));
        lams(binders, list_rec_prop(m, on_nil, on_cons, b))
    };
    let cons_case = {
        let (x_id, x) = fr.local();
        let (as_id, as_) = fr.local();
        let ih_ty = all(&mut fr, &as_);
        let (ih_id, ih) = fr.local();
        let (b_id, b) = fr.local();
        let ex: Vec<(FVarId, Expr)> = (0..spec.extra).map(|_| fr.local()).collect();
        let exv: Vec<Expr> = ex.iter().map(|(_, v)| v.clone()).collect();
        let left = kx::cons(x.clone(), as_.clone());
        let on_nil = {
            let (h_id, h) = fr.local();
            let flipped = symm(nat(), len(&left), len(&kx::nil()), h);
            let body = absurd_zero_eq_succ(
                &mut fr,
                len(&as_),
                flipped,
                (spec.goal)(&left, &kx::nil(), &exv),
            );
            lams(vec![(h_id, len_eq(&left, &kx::nil()))], body)
        };
        let on_cons = {
            let (g_id, g) = fr.local();
            let (bs_id, bs) = fr.local();
            let (ihb_id, _) = fr.local();
            let (h_id, h) = fr.local();
            let right = kx::cons(g.clone(), bs.clone());
            let ihb_ty = Expr::arrow(len_eq(&left, &bs), (spec.goal)(&left, &bs, &exv));
            let pred = nat_pred(&mut fr);
            let h_tail = congr_arg(nat(), nat(), succ(len(&as_)), succ(len(&bs)), pred, h);
            let body = (spec.cons_cons)(&mut fr, [&x, &as_, &g, &bs], &ih, &exv, h_tail);
            lams(
                vec![
                    (g_id, bool_ty()),
                    (bs_id, lb()),
                    (ihb_id, ihb_ty),
                    (h_id, len_eq(&left, &right)),
                ],
                body,
            )
        };
        let m = inner_motive(&mut fr, &left, &exv);
        let mut binders = vec![(x_id, bool_ty()), (as_id, lb()), (ih_id, ih_ty), (b_id, lb())];
        binders.extend(ex.into_iter().map(|(id, _)| (id, bool_ty())));
        lams(binders, list_rec_prop(m, on_nil, on_cons, b))
    };
    let val = {
        let (a_id, a) = fr.local();
        lams(vec![(a_id, lb())], list_rec_prop(motive, nil_case, cons_case, a))
    };
    (ty, val)
}

/// `carry_swap : ∀ a b c, L a = L b → CO b (NOT a) c = not (CO a (NOT b) (not c))`.
fn carry_swap() -> (Expr, Expr) {
    let goal = |a: &Expr, b: &Expr, ex: &[Expr]| {
        let c = &ex[0];
        eqb(
            carry(b.clone(), nt(a.clone()), c.clone()),
            bnot(carry(a.clone(), nt(b.clone()), bnot(c.clone()))),
        )
    };
    let nil_nil = |_: &mut Fresh, ex: &[Expr]| {
        // `c = not (not c)`.
        let c = &ex[0];
        symm(bool_ty(), bnot(bnot(c.clone())), c.clone(), cite(names::NOT_NOT, [c.clone()]))
    };
    let cons_cons =
        |fr: &mut Fresh, [x, as_, g, bs]: [&Expr; 4], ih: &Expr, ex: &[Expr], ht: Expr| {
            let c = &ex[0];
            let c1 = maj(g.clone(), bnot(x.clone()), c.clone());
            let c2 = maj(x.clone(), bnot(g.clone()), bnot(c.clone()));
            let step1 = Expr::apps(ih.clone(), [bs.clone(), c1.clone(), ht]);
            let mn = cite(names::MAJ_NOT, [g.clone(), x.clone(), c.clone()]);
            let (as1, bs1) = (as_.clone(), bs.clone());
            let step2 = under(fr, bool_ty(), bool_ty(), bnot(c1.clone()), c2.clone(), mn, |t| {
                bnot(carry(as1.clone(), nt(bs1.clone()), t))
            });
            trans(
                bool_ty(),
                carry(bs.clone(), nt(as_.clone()), c1.clone()),
                bnot(carry(as_.clone(), nt(bs.clone()), bnot(c1))),
                bnot(carry(as_.clone(), nt(bs.clone()), c2)),
                step1,
                step2,
            )
        };
    two_list(&TwoList { extra: 1, goal: &goal, nil_nil: &nil_nil, cons_cons: &cons_cons })
}

/// `carry_false_true : ∀ a b, L a = L b →
/// CO a (NOT b) false = and (CO a (NOT b) true) (not (bvBeq a b))`.
fn carry_false_true() -> (Expr, Expr) {
    let goal = |a: &Expr, b: &Expr, _: &[Expr]| {
        eqb(
            carry(a.clone(), nt(b.clone()), ff()),
            band(carry(a.clone(), nt(b.clone()), tt()), bnot(kx::bv_beq(a.clone(), b.clone()))),
        )
    };
    let nil_nil = |_: &mut Fresh, _: &[Expr]| refl(bool_ty(), ff());
    let cons_cons =
        |fr: &mut Fresh, [x, as_, g, bs]: [&Expr; 4], ih: &Expr, _: &[Expr], ht: Expr| {
            let at = |xv: &Expr, gv: &Expr| {
                goal(&kx::cons(xv.clone(), as_.clone()), &kx::cons(gv.clone(), bs.clone()), &[])
            };
            let same = Expr::apps(ih.clone(), [bs.clone(), ht]);
            let mixed = |c: bool| {
                let k = carry(as_.clone(), nt(bs.clone()), lit(c));
                symm(bool_ty(), band(k.clone(), tt()), k.clone(), cite(names::AND_TRUE, [k]))
            };
            let split_g = |fr: &mut Fresh, xv: bool| {
                let (z_id, z) = fr.local();
                let m = lams(vec![(z_id, bool_ty())], at(&lit(xv), &z));
                // x = g: the induction hypothesis; x ≠ g: `and k true = k`, with
                // `k` the carry the head pair passes on (`x`).
                let (on_f, on_t) =
                    if xv { (mixed(true), same.clone()) } else { (same.clone(), mixed(false)) };
                bool_rec(Level::zero(), m, on_f, on_t, g.clone())
            };
            let on_f = split_g(fr, false);
            let on_t = split_g(fr, true);
            let (z_id, z) = fr.local();
            let m = lams(vec![(z_id, bool_ty())], at(&z, g));
            bool_rec(Level::zero(), m, on_f, on_t, x.clone())
        };
    two_list(&TwoList { extra: 0, goal: &goal, nil_nil: &nil_nil, cons_cons: &cons_cons })
}

/// `not_ule_ult_swap : ∀ a b, L a = L b → not (bvULe a b) = bvUlt b a`.
///
/// `not (bvULe a b)` unfolds to `not (or (not Ct) Bq)` (`Ct = CO a (NOT b)
/// true`, `Bq = bvBeq a b`), which is `and Ct (not Bq)` (`not_or_not`), which
/// is `Cf = CO a (NOT b) false` (`carry_false_true`), which is `not (not Cf)`,
/// which is `not (CO b (NOT a) true)` (`carry_swap` at `c = true`, where
/// `not true` computes to `false`), the unfolding of `bvUlt b a`.
fn not_ule_ult_swap() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let (ba, a) = list_local(&mut fr);
    let (bb, b) = list_local(&mut fr);
    let (h_id, h) = fr.local();
    let binders = vec![ba, bb, (h_id, len_eq(&a, &b))];
    let ty = pis(
        binders.clone(),
        eqb(bnot(kx::bv_ule(a.clone(), b.clone())), kx::bv_ult(b.clone(), a.clone())),
    );
    let ct = carry(a.clone(), nt(b.clone()), tt());
    let cf = carry(a.clone(), nt(b.clone()), ff());
    let bq = kx::bv_beq(a.clone(), b.clone());
    let lhs = bnot(kx::bv_ule(a.clone(), b.clone()));
    let mid1 = band(ct.clone(), bnot(bq.clone()));
    let e1 = cite(names::NOT_OR_NOT, [ct, bq]);
    let e2 = symm(
        bool_ty(),
        cf.clone(),
        mid1.clone(),
        cite(names::CARRY_FALSE_TRUE, [a.clone(), b.clone(), h.clone()]),
    );
    let nn = bnot(bnot(cf.clone()));
    let e3 = symm(bool_ty(), nn.clone(), cf.clone(), cite(names::NOT_NOT, [cf.clone()]));
    let swapped = carry(b.clone(), nt(a.clone()), tt());
    let cs = cite(names::CARRY_SWAP, [a.clone(), b.clone(), tt(), h]);
    let cs_not = congr_arg(
        bool_ty(),
        bool_ty(),
        swapped.clone(),
        bnot(carry(a.clone(), nt(b.clone()), bnot(tt()))),
        Expr::const_str("Bool.not"),
        cs,
    );
    let rhs = kx::bv_ult(b.clone(), a.clone());
    let e4 = symm(bool_ty(), bnot(swapped), nn.clone(), cs_not);
    let t34 = trans(bool_ty(), cf.clone(), nn.clone(), rhs.clone(), e3, e4);
    let t234 = trans(bool_ty(), mid1.clone(), cf, rhs.clone(), e2, t34);
    let body = trans(bool_ty(), lhs, mid1, rhs, e1, t234);
    (ty, lams(binders, body))
}

/// `hi_ult : ∀ a b, L a = L b →
/// and (not (bvUlt a b)) (not (bvBeq D (AF D))) = bvUlt b a`, `D = A a (NOT b) true`.
///
/// `bvBeq D (AF D) = bvIsZero D` (`beq_allFalse`) `= bvBeq a b`
/// (`beq_eq_isZero_sub`, reversed); then `demorgan_and_not` gives
/// `not (or (bvUlt a b) (bvBeq a b))`, the unfolding of `not (bvULe a b)`,
/// and `not_ule_ult_swap` closes it.
fn hi_ult() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let (ba, a) = list_local(&mut fr);
    let (bb, b) = list_local(&mut fr);
    let (h_id, h) = fr.local();
    let binders = vec![ba, bb, (h_id, len_eq(&a, &b))];
    let d = addm(a.clone(), nt(b.clone()), tt());
    let u = kx::bv_ult(a.clone(), b.clone());
    let z = kx::bv_beq(d.clone(), af(d.clone()));
    let bq = kx::bv_beq(a.clone(), b.clone());
    let lhs = band(bnot(u.clone()), bnot(z.clone()));
    let rhs = kx::bv_ult(b.clone(), a.clone());
    let ty = pis(binders.clone(), eqb(lhs.clone(), rhs.clone()));
    let is0 = kx::bv_is_zero(d.clone());
    let z_is0 = cite(names::BEQ_ALL_FALSE, [d.clone()]);
    let bq_is0 = cite("Clean.BVC.beq_eq_isZero_sub", [a.clone(), b.clone(), h.clone()]);
    let z_bq = trans(
        bool_ty(),
        z.clone(),
        is0.clone(),
        bq.clone(),
        z_is0,
        symm(bool_ty(), bq.clone(), is0, bq_is0),
    );
    let u1 = u.clone();
    let e1 = under(&mut fr, bool_ty(), bool_ty(), z, bq.clone(), z_bq, |t| {
        band(bnot(u1.clone()), bnot(t))
    });
    let mid = band(bnot(u.clone()), bnot(bq.clone()));
    let e2 = cite("Clean.BVC.demorgan_and_not", [u.clone(), bq.clone()]);
    let nule = bnot(kx::bv_ule(a.clone(), b.clone()));
    let e3 = cite(names::NOT_ULE_ULT_SWAP, [a.clone(), b.clone(), h]);
    let t23 = trans(bool_ty(), mid.clone(), nule, rhs.clone(), e2, e3);
    let body = trans(bool_ty(), lhs, mid, rhs, e1, t23);
    (ty, lams(binders, body))
}

/// `mul_add_self : ∀ x c1 c2 m, L x = succ m → L c1 = L x → L c2 = L x →
/// V c2 = succ (V c1) → A (M x c1) x false = M x c2`.
///
/// The `x + x * c` shape trust-cg emits for `x * (c + 1)` (`add x, x, x, lsl
/// #k` after `shl_mul`, with the operands in `add_comm`'s order). Lengths:
/// both are `L x` (`len_addRecM`, `len_bvMul`). Values, modulo `Q = P (L x)`:
/// the left is `((V x * V c1) % Q + V x) % Q` (`addRecM_val`, `bvMul_val`),
/// which is `(V x * V c1 + V x) % Q` (`mod_add_mod`); the right is
/// `(V x * succ (V c1)) % Q` (`bvMul_val`, the premise), equal by a ring step.
/// Then `inj`.
fn mul_add_self() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let (bx, x) = list_local(&mut fr);
    let (bc1, c1) = list_local(&mut fr);
    let (bc2, c2) = list_local(&mut fr);
    let (bm_id, m) = fr.local();
    let (hx_id, hx) = fr.local();
    let (h1_id, h1) = fr.local();
    let (h2_id, h2) = fr.local();
    let (hv_id, hv) = fr.local();
    let lx = len(&x);
    let binders = vec![
        bx,
        bc1,
        bc2,
        (bm_id, nat()),
        (hx_id, eq(nat(), lx.clone(), succ(m.clone()))),
        (h1_id, eq(nat(), len(&c1), lx.clone())),
        (h2_id, eq(nat(), len(&c2), lx.clone())),
        (hv_id, eq(nat(), val(&c2), succ(val(&c1)))),
    ];
    let f = ff();
    let m1 = bvmul(x.clone(), c1.clone());
    let m2 = bvmul(x.clone(), c2.clone());
    let lhs = addm(m1.clone(), x.clone(), f.clone());
    let rhs = m2.clone();
    let ty = pis(binders.clone(), eql(lhs.clone(), rhs.clone()));
    let h1 = Eqn { lhs: len(&c1), rhs: lx.clone(), proof: h1 };
    let h2 = Eqn { lhs: len(&c2), rhs: lx.clone(), proof: h2 };
    let hv = Eqn { lhs: val(&c2), rhs: succ(val(&c1)), proof: hv };
    let len_mul = |c: &Expr, hc: Eqn| {
        Eqn::cite(
            add_comm::names::LEN_BV_MUL,
            vec![x.clone(), c.clone(), m.clone(), hx.clone()],
            len(&bvmul(x.clone(), c.clone())),
            len(c),
        )
        .then(hc)
    };
    // Lengths.
    let l_lhs = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![m1.clone(), x.clone(), f.clone()],
        len(&lhs),
        len(&m1),
    )
    .then(len_mul(&c1, h1.clone()));
    let hl = l_lhs.clone().then(len_mul(&c2, h2.clone()).symm());
    // Values.
    let q = two_pow(lx.clone());
    let hq = cite(bvv::TWO_POW_POS, [lx.clone()]);
    let vx = val(&x);
    let z = nmul(vx.clone(), val(&c1));
    let zq = nmod(z.clone(), q.clone());
    let s0 = nadd(nadd(val(&m1), vx.clone()), btn(f.clone()));
    let lm1 = len_mul(&c1, h1.clone());
    let (s0c, vx1, f1, q1, z1, q2, vx2, q3) =
        (s0.clone(), vx.clone(), f.clone(), q.clone(), z.clone(), q.clone(), vx.clone(), q.clone());
    let left = Eqn::cite(
        bvv::ADD_REC_M_VAL,
        vec![m1.clone(), x.clone(), f.clone()],
        val(&lhs),
        nmod(s0, two_pow(len(&m1))),
    )
    .then(lm1.under(&mut fr, |t| nmod(s0c.clone(), two_pow(t))))
    .then(
        Eqn::cite(
            bvv::BV_MUL_VAL,
            vec![x.clone(), c1.clone()],
            val(&m1),
            nmod(z.clone(), two_pow(len(&c1))),
        )
        .then(h1.under(&mut fr, |t| nmod(z1.clone(), two_pow(t))))
        .under(&mut fr, |t| nmod(nadd(nadd(t, vx1.clone()), btn(f1.clone())), q1.clone())),
    )
    // `btn false` is `0`, and `s + 0` is `s`.
    .then(
        Eqn::by_defeq(
            nadd(nadd(zq.clone(), vx.clone()), btn(f.clone())),
            nadd(zq.clone(), vx.clone()),
        )
        .under(&mut fr, |t| nmod(t, q2.clone())),
    )
    .then(Eqn::cite(
        bvv::MOD_ADD_MOD,
        vec![z.clone(), vx.clone(), q.clone(), hq],
        nmod(nadd(zq, vx.clone()), q.clone()),
        nmod(nadd(z.clone(), vx.clone()), q.clone()),
    ));
    let z2 = nmul(vx.clone(), val(&c2));
    // `Nat.mul n (succ k)` unfolds to `Nat.add (Nat.mul n k) n`.
    let ring = Eqn::by_defeq(nmul(vx.clone(), succ(val(&c1))), nadd(z.clone(), vx.clone()));
    let q4 = q.clone();
    let right = Eqn::cite(
        bvv::BV_MUL_VAL,
        vec![x.clone(), c2.clone()],
        val(&m2),
        nmod(z2.clone(), two_pow(len(&c2))),
    )
    .then(h2.under(&mut fr, |t| nmod(z2.clone(), two_pow(t))))
    .then(hv.under(&mut fr, |t| nmod(nmul(vx2.clone(), t), q3.clone())))
    .then(ring.under(&mut fr, |t| nmod(t, q4.clone())));
    let hval = left.then(right.symm());
    let inj = cite(bvv::INJ, [lhs, rhs, hl.proof, hval.proof]);
    (ty, lams(binders, inj))
}

/// `zext_drop1_div2 : ∀ h t c, V c = 2 → bvZeroExt (btail (h :: t)) 1 = bvDiv (h :: t) c`.
///
/// AArch64 `lsr x, #1` (UBFM: `Extract[w-1:1]` zero-extended by one bit)
/// against the spec's faithful `x / 2`. `btail (h :: t)` is `t`, and
/// `z = bvZeroExt t 1` is `t ++ bvReplF 1`, so `L z = succ (L t)`
/// (`len_append`, `len_replF`) and `V z = V t` (`toNat_append`,
/// `toNat_replF`); then `z = natToBvAux (L z) (V z)` (`natToBv_toNat`). The
/// right side is `natToBvAux (succ (L t)) ((btn h + 2 * V t) / V c)`, and
/// `(btn h + 2 * V t) / 2 = V t` (`div_unique`, `btn_lt_two`).
fn zext_drop1_div2() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let (bh, h) = bool_local(&mut fr);
    let (bt, t) = list_local(&mut fr);
    let (bc, c) = list_local(&mut fr);
    let (hv_id, hv) = fr.local();
    let two = nlit(2);
    let binders = vec![bh, bt, bc, (hv_id, eq(nat(), val(&c), two.clone()))];
    let x = kx::cons(h.clone(), t.clone());
    let one = kx::nat_lit(1);
    let lhs = zero_ext(btail(x.clone()), one.clone());
    let rhs = kx::bv_div(x.clone(), c.clone());
    let ty = pis(binders.clone(), eql(lhs.clone(), rhs.clone()));
    // z, as the statements below write it.
    let z = zero_ext(t.clone(), one.clone());
    let ones = repl_f(one.clone());
    let (lt, vt) = (len(&t), val(&t));
    let (lt1, vt1, lt2) = (lt.clone(), vt.clone(), lt.clone());
    let h_len = Eqn::cite(
        bvv::LEN_APPEND,
        vec![t.clone(), ones.clone()],
        len(&z),
        nadd(lt.clone(), len(&ones)),
    )
    .then(
        Eqn::cite(bvv::LEN_REPL_F, vec![one.clone()], len(&ones), one.clone())
            .under(&mut fr, |u| nadd(lt1.clone(), u)),
    )
    .then(Eqn::by_defeq(nadd(lt.clone(), one.clone()), succ(lt.clone())));
    let h_val = Eqn::cite(
        bvv::TO_NAT_APPEND,
        vec![t.clone(), ones.clone()],
        val(&z),
        nadd(vt.clone(), nmul(two_pow(lt.clone()), val(&ones))),
    )
    .then(
        Eqn::cite(bvv::TO_NAT_REPL_F, vec![one.clone()], val(&ones), nlit(0))
            .under(&mut fr, |u| nadd(vt1.clone(), nmul(two_pow(lt2.clone()), u))),
    )
    .then(Eqn::by_defeq(nadd(vt.clone(), nmul(two_pow(lt.clone()), nlit(0))), vt.clone()));
    // `(btn h + 2 * V t) / V c = V t`.
    let vx = val(&x);
    let vx1 = vx.clone();
    let quot = Eqn { lhs: val(&c), rhs: two.clone(), proof: hv }
        .under(&mut fr, |u| ndiv(vx1.clone(), u))
        .then(Eqn::cite(
            bvv::DIV_UNIQUE,
            vec![
                vx.clone(),
                two.clone(),
                vt.clone(),
                btn(h.clone()),
                cite(bvv::BTN_LT_TWO, [h.clone()]),
                refl(nat(), vx.clone()),
            ],
            ndiv(vx.clone(), two.clone()),
            vt.clone(),
        ));
    // The list side: lhs ≡ z = natToBvAux (L z) (V z) = natToBvAux (succ L t) (V t)
    //   = natToBvAux (succ L t) (V x / V c) ≡ rhs.
    let n2b = |w: Expr, v: Expr| nat_to_bv(w, v);
    let e1 = symm(lb(), n2b(len(&z), val(&z)), z.clone(), cite(bvv::NAT_TO_BV_TO_NAT, [z.clone()]));
    let vz = val(&z);
    let on_len =
        under(&mut fr, nat(), lb(), len(&z), succ(lt.clone()), h_len.proof, |u| n2b(u, vz.clone()));
    let slt = succ(lt.clone());
    let slt1 = slt.clone();
    let on_val =
        under(&mut fr, nat(), lb(), val(&z), vt.clone(), h_val.proof, |u| n2b(slt1.clone(), u));
    let e2 = trans(
        lb(),
        n2b(len(&z), val(&z)),
        n2b(slt.clone(), val(&z)),
        n2b(slt.clone(), vt.clone()),
        on_len,
        on_val,
    );
    let slt2 = slt.clone();
    let on_quot =
        under(&mut fr, nat(), lb(), quot.lhs.clone(), quot.rhs.clone(), quot.proof, |u| {
            n2b(slt2.clone(), u)
        });
    let e3 = symm(lb(), n2b(slt.clone(), quot.lhs.clone()), n2b(slt.clone(), vt.clone()), on_quot);
    let mid = n2b(slt.clone(), vt.clone());
    let e23 = trans(lb(), n2b(len(&z), val(&z)), mid.clone(), rhs.clone(), e2, e3);
    let body = trans(lb(), lhs, n2b(len(&z), val(&z)), rhs, e1, e23);
    (ty, lams(binders, body))
}

// ── the signed flags (AArch64 `b.ge` / `b.lt`) ───────────────────────────────

/// `[x]`, a one-bit list.
fn one(x: Expr) -> Expr {
    kx::cons(x, kx::nil())
}

/// The AArch64 `N == V` flag form over Bools, as the machine semantics states
/// it after `cmp`: `xor (bvBeq [n] [true]) (and (not (bvBeq [x] [y])) (not
/// (bvBeq [n] [x])))`, with `n` the sign of the difference and `x`, `y` the
/// operands' signs. `xor` of the two sides is `N != V` (`b.lt`).
pub(crate) fn flags_lhs(n: Expr, x: Expr, y: Expr) -> Expr {
    kx::bxor(
        kx::bv_beq(one(n.clone()), one(tt())),
        band(bnot(kx::bv_beq(one(x.clone()), one(y))), bnot(kx::bv_beq(one(n), one(x)))),
    )
}

/// `slt_flag_bridge`'s right side: `xor n (and (xor x y) (xor n x))`.
fn flags_rhs(n: Expr, x: Expr, y: Expr) -> Expr {
    kx::bxor(n.clone(), band(kx::bxor(x.clone(), y), kx::bxor(n, x)))
}

/// `flags3 : ∀ n x y, flags_lhs n x y = flags_rhs n x y`, by the eight cases.
fn flags3() -> (Expr, Expr) {
    bool_identity(3, |v| {
        let (n, x, y) = (v[0].clone(), v[1].clone(), v[2].clone());
        (flags_lhs(n.clone(), x.clone(), y.clone()), flags_rhs(n, x, y))
    })
}

/// The sign of `a - b` as `addRecM` computes it: `bvLastBit (A a (NOT b) true)`.
pub(crate) fn sub_sign(a: Expr, b: Expr) -> Expr {
    kx::last_bit(addm(a, nt(b), tt()))
}

/// `slt_flags : ∀ a b, bvIsCons a = true → L a = L b →
/// flags_lhs (LB (A a (NOT b) true)) (LB a) (LB b) = bvSLtReal a b`.
///
/// `flags3` at those three Bools, then `Clean.BVC.slt_flag_bridge` (`bvSLtReal
/// a b = xor N V` with the same `N` and `V`) reversed.
fn slt_flags() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let (ba, a) = list_local(&mut fr);
    let (bb, b) = list_local(&mut fr);
    let (h1_id, h1) = fr.local();
    let (h2_id, h2) = fr.local();
    let is_cons = Expr::app(Expr::const_str("Clean.BVC.bvIsCons"), a.clone());
    let binders = vec![ba, bb, (h1_id, eqb(is_cons, tt())), (h2_id, len_eq(&a, &b))];
    let n = sub_sign(a.clone(), b.clone());
    let (x, y) = (kx::last_bit(a.clone()), kx::last_bit(b.clone()));
    let lhs = flags_lhs(n.clone(), x.clone(), y.clone());
    let mid = flags_rhs(n.clone(), x.clone(), y.clone());
    let rhs = kx::bv_slt_real(a.clone(), b.clone());
    let ty = pis(binders.clone(), eqb(lhs.clone(), rhs.clone()));
    let s1 = cite(names::FLAGS3, [n, x, y]);
    let bridge = cite("Clean.BVC.slt_flag_bridge", [a, b, h1, h2]);
    let s2 = symm(bool_ty(), rhs.clone(), mid.clone(), bridge);
    (ty, lams(binders, trans(bool_ty(), lhs, mid, rhs, s1, s2)))
}

// ── registration and the audited environment ─────────────────────────────────

/// The theorems in dependency order: `(name, statement, proof)`.
pub(crate) fn theorems() -> Vec<(&'static str, Expr, Expr)> {
    vec![
        (names::AND_TRUE, and_true()),
        (names::NOT_NOT, not_not()),
        (names::MAJ_NOT, maj_not()),
        (names::NOT_OR_NOT, not_or_not()),
        (names::ITE_TRUE, ite_lit(true)),
        (names::ITE_FALSE, ite_lit(false)),
        (names::ITE_CONG, ite_cong()),
        (names::BEQ_ALL_FALSE, beq_all_false()),
        (names::CARRY_SWAP, carry_swap()),
        (names::CARRY_FALSE_TRUE, carry_false_true()),
        (names::NOT_ULE_ULT_SWAP, not_ule_ult_swap()),
        (names::HI_ULT, hi_ult()),
        (names::ZIP_AND_ALL_FALSE, zip_and_all_false()),
        (names::BEQ_AND_LOWBIT, beq_and_lowbit()),
        (names::SUB_ZERO, sub_zero()),
        (names::MUL_ADD_SELF, mul_add_self()),
        (names::ZEXT_DROP1_DIV2, zext_drop1_div2()),
        (names::FLAGS3, flags3()),
        (names::SLT_FLAGS, slt_flags()),
    ]
    .into_iter()
    .map(|(name, (ty, val))| (name, ty, val))
    .collect()
}

/// Add the theorems to `env` (the strength base). Each is a
/// `Declaration::Theorem`, so `add_decl` type-checks its proof.
pub(crate) fn register(env: &mut Environment) -> Result<(), String> {
    for (name, type_, value) in theorems() {
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

/// Every THEOREM name the branch environment audits: the strength audit,
/// this module's theorems, and their citations.
pub(crate) fn audited() -> Vec<&'static str> {
    let mut all = strength::audited();
    all.extend(names::ALL);
    all.extend(CITED);
    all
}

/// `base` plus the theorems, audited. Split from [`branch_base`] so a test
/// can hand it a doctored base.
pub(crate) fn build_base(mut env: Environment) -> Result<Environment, String> {
    register(&mut env)?;
    audit_theorems(&env, &audited())?;
    Ok(env)
}

/// The strength base plus the branch theorems, built and audited once per
/// process; `Err`, and a panic during the build, are kept for the life of
/// the process. Call it on a kernel re-check thread.
pub(crate) fn branch_base() -> Result<&'static Environment, String> {
    static BASE: OnceLock<Result<Environment, String>> = OnceLock::new();
    BASE.get_or_init(|| {
        std::panic::catch_unwind(|| build_base(strength::strength_base()?.clone()))
            .unwrap_or_else(|_| Err("the branch base build panicked".to_string()))
    })
    .as_ref()
    .map_err(Clone::clone)
}

/// The environment a branch discharge is checked in: [`branch_base`] and one
/// opaque `Bool` per bit of each variable.
pub(crate) fn env(leaves: &[(String, u32)]) -> Result<Environment, String> {
    let mut env = branch_base()?.clone();
    add_comm::add_leaf_bits(&mut env, leaves);
    Ok(env)
}

/// The label of an admitted discharge: the `Trust.BVB` / `Trust.BVS` /
/// `Trust.BVV` / `Trust.BVC` / `Clean.BVC` THEOREMS that occur in the term
/// itself (sorted), then [`LABEL_TAIL`]. Built from the term, never from a
/// record of the steps, so it names nothing the checked term does not use.
pub(crate) fn label(env: &Environment, proof: &Expr) -> String {
    let mut used = HashSet::new();
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

// ── the constant decoder ─────────────────────────────────────────────────────

fn app_of<'a>(e: &'a Expr, head: &str, arity: usize) -> Option<Vec<&'a Expr>> {
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) if *name == Name::from_string(head) => {}
        _ => return None,
    }
    let args = e.get_app_args();
    (args.len() == arity).then(|| args.to_vec())
}

/// The elements of a concrete cons list of at most [`MAX_BITS`] elements.
pub(crate) fn spine(mut e: &Expr) -> Option<Vec<Expr>> {
    let mut out = Vec::new();
    loop {
        if app_of(e, "List.nil", 1).is_some() {
            return Some(out);
        }
        let args = app_of(e, "List.cons", 3)?;
        if out.len() == MAX_BITS {
            return None;
        }
        out.push(args[1].clone());
        e = args[2];
    }
}

/// The literal value of a Bool term, `None` unless it is `Bool.true` /
/// `Bool.false`.
pub(crate) fn bool_lit(e: &Expr) -> Option<bool> {
    match e.kind() {
        ExprKind::Const(n, _) if *n == Name::from_string("Bool.true") => Some(true),
        ExprKind::Const(n, _) if *n == Name::from_string("Bool.false") => Some(false),
        _ => None,
    }
}

/// `(width, value)` of a `BvF.Const` over a concrete list of 1 to 64 literal
/// Bools, least significant first. The contract of `strength`'s private
/// decoder, reimplemented: anything else is `None`.
pub(crate) fn const_bits(e: &Expr) -> Option<(u32, u128)> {
    let list = app_of(e, "Clean.BVC.BvF.Const", 1)?;
    let bits: Vec<bool> = spine(list[0])?.iter().map(bool_lit).collect::<Option<_>>()?;
    if bits.is_empty() {
        return None;
    }
    let v = bits.iter().rev().fold(0u128, |acc, &b| (acc << 1) | u128::from(b));
    Some((u32::try_from(bits.len()).ok()?, v))
}

// ── per-obligation instances ─────────────────────────────────────────────────

/// `ite_cong p p' a a' e e' hp ha he`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn ite_cong_inst(
    p: Expr,
    p2: Expr,
    a: Expr,
    a2: Expr,
    e: Expr,
    e2: Expr,
    hp: Expr,
    ha: Expr,
    he: Expr,
) -> Expr {
    cite(names::ITE_CONG, [p, p2, a, a2, e, e2, hp, ha, he])
}

/// `ite_true a e` / `ite_false a e`.
pub(crate) fn ite_select(which: bool, a: Expr, e: Expr) -> Expr {
    cite(if which { names::ITE_TRUE } else { names::ITE_FALSE }, [a, e])
}

/// `hi_ult a b h`.
pub(crate) fn hi_ult_inst(a: Expr, b: Expr, h: Expr) -> Expr {
    cite(names::HI_ULT, [a, b, h])
}

/// `beq_and_lowbit h t`.
pub(crate) fn beq_and_lowbit_inst(h: Expr, t: Expr) -> Expr {
    cite(names::BEQ_AND_LOWBIT, [h, t])
}

/// `sub_zero a`.
pub(crate) fn sub_zero_inst(a: Expr) -> Expr {
    cite(names::SUB_ZERO, [a])
}

/// `mul_add_self x c1 c2 m hx h1 h2 hv`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn mul_add_self_inst(
    x: Expr,
    c1: Expr,
    c2: Expr,
    m: Expr,
    hx: Expr,
    h1: Expr,
    h2: Expr,
    hv: Expr,
) -> Expr {
    cite(names::MUL_ADD_SELF, [x, c1, c2, m, hx, h1, h2, hv])
}

/// `slt_flags a b h1 h2`.
pub(crate) fn slt_flags_inst(a: Expr, b: Expr, h1: Expr, h2: Expr) -> Expr {
    cite(names::SLT_FLAGS, [a, b, h1, h2])
}

/// `zext_drop1_div2 h t c hv`.
pub(crate) fn zext_drop1_div2_inst(h: Expr, t: Expr, c: Expr, hv: Expr) -> Expr {
    cite(names::ZEXT_DROP1_DIV2, [h, t, c, hv])
}
