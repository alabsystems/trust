// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Add commutation for the O(1) structured route (PKG-C5c, the MADD shape).
//!
//! # What is missing without this
//!
//! AArch64 `madd Xd, Xn, Xm, Xa` computes `Xa + Xn * Xm`, and the machine
//! semantics render it addend first: `BvAdd(ra, BvMul(rn, rm))`. Source
//! `x * 3 + 7` renders `BvAdd(BvMul(x, 3), 7)`. The two sides of the gate's
//! return equation then differ only in the order of one `Add`'s operands. The
//! structured route pairs the two sides through a shared core that must be
//! definitionally equal, so it declines; the bit-blast route declines every
//! multiply wider than 8 bits; the function is graded [VALIDATED].
//!
//! # What this module adds
//!
//! Six theorems, each a `Declaration::Theorem` whose proof term the Clean
//! kernel type-checks when it is added to the environment, stated over the
//! definitions the pinned `Clean.BVC` / `Clean.BVI` layers already export. No
//! axiom, no `sorry`, nothing admitted: [`commuting_base`] audits at run time
//! that each, and each pinned-layer lemma the discharge term cites
//! ([`REFLECTION_LEMMAS`]), is a `Theorem` whose `axiom_deps` and
//! `foundational_axiom_deps` are both empty, and the route declines when the
//! audit fails; the test
//! `theorems_are_kernel_checked_with_an_empty_axiom_closure` re-checks each
//! proof independently.
//!
//! ```text
//! xor3_comm     : ∀ a b c, xor3 a b c = xor3 b a c
//! maj_comm      : ∀ a b c, maj a b c = maj b a c
//! len_addRecM   : ∀ xs ys c, bvLen (addRecM xs ys c) = bvLen xs
//! len_allFalse  : ∀ b, bvLen (bvAllFalse b) = bvLen b
//! len_bvMul     : ∀ a b n, bvLen a = succ n → bvLen (bvMul a b) = bvLen b
//! addRecM_comm  : ∀ xs ys c, bvLen xs = bvLen ys → addRecM xs ys c = addRecM ys xs c
//! ```
//!
//! # Why the length premise, and why per-bit leaves
//!
//! `Clean.BVC` values are untyped `List Bool`, and `addRecM` takes its length
//! from its FIRST operand. Without `bvLen xs = bvLen ys` commutation is false
//! (`addRecM [] [true] false = []`, `addRecM [true] [] false = [true]`), so the
//! premise is load-bearing and the kernel rejects an instance that lacks it
//! (test `commutation_without_equal_lengths_is_kernel_rejected`).
//!
//! The route's usual leaf, one opaque `BVC_LEAF_* : List Bool`, has no length,
//! and `bvMul nil b = nil`: over such leaves `7 + x * 3 = x * 3 + 7` is FALSE
//! at `x = nil`. The retry therefore states its goal over leaves of a known
//! width: a `Var(name, BitVec(w))` is `w` opaque `Bool` constants in a concrete
//! cons list, the rendering the compare bridges already use (`BVC_EQBIT_*`).
//! That is the statement "for every `w`-bit `x`", which is what the Formula
//! means. The constants only state the obligation; they are not dependencies
//! of the theorems.
//!
//! # Scope: an `Add` with a multiply operand, nothing else
//!
//! [`canonical_step`] reorders an `Add` only when one of its operands is a
//! multiply, the shape `madd` produces. A plain `Add` is left alone for two
//! reasons. It does not need this route: without a wide multiply the bit-blast
//! route decides the equation. And the route's declining of a plain swapped
//! add is pinned: `verify_output::tests::b4_mis_reflection_is_kernel_guarded`
//! asserts that `try_o1_instantiation_discharge` returns `None` for
//! `X0 + X1` against `X1 + X0`, and that file is frozen.
//!
//! # Authority
//!
//! Nothing here decides a grade. [`canonical_step`] returns a proof TERM; the
//! caller splices it into the discharge term and the kernel type-checks the
//! whole term against the goal built from the two original Formulas. A wrong
//! swap, a wrong length proof or a wrong ordering can only make that check
//! fail, and a failed check falls back to the route's previous behaviour.

use std::sync::OnceLock;

use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, Declaration, Environment, Expr, ExprKind, Level};

use super::kterm::{
    Fresh, absurd_zero_eq_succ, addm, bhead, bool_rec, bool_ty, btail, bvlen, bvmul, congr_arg, eq,
    gate, l1, lams, lb, list_rec_prop, maj, nat, nat_pred, pis, refl, succ, symm, trans, xor3,
    zero,
};
use super::kx;

/// The theorems this module proves. `Trust.BVC.*`, not `Clean.BVC.*`: they are
/// registered by the bridge on top of the pinned Clean layer, and a later
/// Clean theorem of the same statement must not be shadowed silently.
pub(crate) mod names {
    pub(crate) const XOR3_COMM: &str = "Trust.BVC.xor3_comm";
    pub(crate) const MAJ_COMM: &str = "Trust.BVC.maj_comm";
    pub(crate) const LEN_ADD_REC_M: &str = "Trust.BVC.len_addRecM";
    pub(crate) const LEN_ALL_FALSE: &str = "Trust.BVC.len_allFalse";
    pub(crate) const LEN_BV_MUL: &str = "Trust.BVC.len_bvMul";
    pub(crate) const ADD_REC_M_COMM: &str = "Trust.BVC.addRecM_comm";
    pub(crate) const ALL: [&str; 6] =
        [XOR3_COMM, MAJ_COMM, LEN_ADD_REC_M, LEN_ALL_FALSE, LEN_BV_MUL, ADD_REC_M_COMM];
}

/// The pinned-layer lemmas the commuted discharge term cites by name besides
/// [`names::ALL`]: every `Clean.BVC.bvf_*` lemma the reflection (`kx`,
/// `reflect_formula`) splices, and the `Eq` lemmas that chain the steps.
/// `reflection_lemmas_cover_every_spliced_bvf_lemma` FAILS if the reflection
/// starts citing a `bvf_*` lemma this list does not name.
pub(crate) const REFLECTION_LEMMAS: [&str; 20] = [
    "Clean.BVC.bvf_add_cong",
    "Clean.BVC.bvf_add_zero_id",
    "Clean.BVC.bvf_and_cong",
    "Clean.BVC.bvf_ashr_cong",
    "Clean.BVC.bvf_concat_cong",
    "Clean.BVC.bvf_div_cong",
    "Clean.BVC.bvf_extract_cong1",
    "Clean.BVC.bvf_extract_zeroext_id",
    "Clean.BVC.bvf_lshr_cong",
    "Clean.BVC.bvf_mul_cong",
    "Clean.BVC.bvf_or_cong",
    "Clean.BVC.bvf_or_cong2",
    "Clean.BVC.bvf_or_zero_id",
    "Clean.BVC.bvf_sdiv_cong",
    "Clean.BVC.bvf_shl_cong",
    "Clean.BVC.bvf_sub_cong",
    "Clean.BVC.bvf_xor_cong",
    "Clean.BVC.bvf_zext_cong",
    "Eq.trans",
    "Eq.symm",
];

/// The label a function proved through the commuted route carries.
pub(crate) const THEOREM_LABEL: &str =
    "Trust.BVC.addRecM_comm+Clean.BVC congruence (O(1) add@N, commuted Add operands)";

// ── the theorems ─────────────────────────────────────────────────────────────

/// `∀ a b c, g a b c = g b a c` for a three-input Bool gate, by an exhaustive
/// eight-leaf `Bool.rec`; each leaf is `Eq.refl` of the ground value, which the
/// kernel accepts only if both sides compute to it.
fn gate_comm(name: &str) -> (Expr, Expr) {
    let g = |a: &Expr, b: &Expr, c: &Expr| gate(name, a.clone(), b.clone(), c.clone());
    let stmt = |a: &Expr, b: &Expr, c: &Expr| eq(bool_ty(), g(a, b, c), g(b, a, c));
    let mut fr = Fresh::new();
    let ty = {
        let (a_id, a) = fr.local();
        let (b_id, b) = fr.local();
        let (c_id, c) = fr.local();
        pis(vec![(a_id, bool_ty()), (b_id, bool_ty()), (c_id, bool_ty())], stmt(&a, &b, &c))
    };
    let val = {
        let (a_id, a) = fr.local();
        let (b_id, b) = fr.local();
        let (c_id, c) = fr.local();
        // Innermost: `a` and `b` ground, split `c`.
        let split_c = |fr: &mut Fresh, ag: &Expr, bg: &Expr| {
            let (z_id, z) = fr.local();
            let motive = lams(vec![(z_id, bool_ty())], stmt(ag, bg, &z));
            let leaf = |cg: Expr| refl(bool_ty(), g(ag, bg, &cg));
            bool_rec(Level::zero(), motive, leaf(kx::bfalse()), leaf(kx::btrue()), c.clone())
        };
        // `a` ground, split `b`.
        let split_b = |fr: &mut Fresh, ag: &Expr| {
            let on_false = split_c(fr, ag, &kx::bfalse());
            let on_true = split_c(fr, ag, &kx::btrue());
            let (y_id, y) = fr.local();
            let motive = lams(vec![(y_id, bool_ty())], stmt(ag, &y, &c));
            bool_rec(Level::zero(), motive, on_false, on_true, b.clone())
        };
        let on_false = split_b(&mut fr, &kx::bfalse());
        let on_true = split_b(&mut fr, &kx::btrue());
        let (x_id, x) = fr.local();
        let motive = lams(vec![(x_id, bool_ty())], stmt(&x, &b, &c));
        let body = bool_rec(Level::zero(), motive, on_false, on_true, a.clone());
        lams(vec![(a_id, bool_ty()), (b_id, bool_ty()), (c_id, bool_ty())], body)
    };
    (ty, val)
}

/// `len_addRecM : ∀ xs ys c, bvLen (addRecM xs ys c) = bvLen xs`, by induction
/// on `xs` (the adder's result has the length of its first operand).
fn len_add_rec_m() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let stmt = |xs: &Expr, ys: &Expr, c: &Expr| {
        eq(nat(), bvlen(addm(xs.clone(), ys.clone(), c.clone())), bvlen(xs.clone()))
    };
    let all = |fr: &mut Fresh, xs: &Expr| {
        let (ys_id, ys) = fr.local();
        let (c_id, c) = fr.local();
        pis(vec![(ys_id, lb()), (c_id, bool_ty())], stmt(xs, &ys, &c))
    };
    let ty = {
        let (xs_id, xs) = fr.local();
        let body = all(&mut fr, &xs);
        pis(vec![(xs_id, lb())], body)
    };
    let val = {
        let (xs_id, xs) = fr.local();
        let motive = {
            let (w_id, w) = fr.local();
            let body = all(&mut fr, &w);
            lams(vec![(w_id, lb())], body)
        };
        let nil_case = {
            let (ys_id, _) = fr.local();
            let (c_id, _) = fr.local();
            lams(vec![(ys_id, lb()), (c_id, bool_ty())], refl(nat(), zero()))
        };
        let cons_case = {
            let (a_id, a) = fr.local();
            let (as_id, as_) = fr.local();
            let ih_ty = all(&mut fr, &as_);
            let (ih_id, ih) = fr.local();
            let (ys_id, ys) = fr.local();
            let (c_id, c) = fr.local();
            let carry = maj(a, bhead(ys.clone()), c);
            let tail = addm(as_.clone(), btail(ys.clone()), carry.clone());
            let body = congr_arg(
                nat(),
                nat(),
                bvlen(tail),
                bvlen(as_),
                Expr::const_str("Nat.succ"),
                Expr::apps(ih, [btail(ys), carry]),
            );
            lams(
                vec![
                    (a_id, bool_ty()),
                    (as_id, lb()),
                    (ih_id, ih_ty),
                    (ys_id, lb()),
                    (c_id, bool_ty()),
                ],
                body,
            )
        };
        lams(vec![(xs_id, lb())], list_rec_prop(motive, nil_case, cons_case, xs))
    };
    (ty, val)
}

/// `len_allFalse : ∀ b, bvLen (bvAllFalse b) = bvLen b`, by induction on `b`.
fn len_all_false() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let stmt = |b: &Expr| eq(nat(), bvlen(kx::all_false(b.clone())), bvlen(b.clone()));
    let ty = {
        let (b_id, b) = fr.local();
        pis(vec![(b_id, lb())], stmt(&b))
    };
    let val = {
        let (b_id, b) = fr.local();
        let motive = {
            let (w_id, w) = fr.local();
            lams(vec![(w_id, lb())], stmt(&w))
        };
        let cons_case = {
            let (h_id, _) = fr.local();
            let (t_id, t) = fr.local();
            let (ih_id, ih) = fr.local();
            let body = congr_arg(
                nat(),
                nat(),
                bvlen(kx::all_false(t.clone())),
                bvlen(t.clone()),
                Expr::const_str("Nat.succ"),
                ih,
            );
            lams(vec![(h_id, bool_ty()), (t_id, lb()), (ih_id, stmt(&t))], body)
        };
        lams(vec![(b_id, lb())], list_rec_prop(motive, refl(nat(), zero()), cons_case, b))
    };
    (ty, val)
}

/// `len_bvMul : ∀ a b n, bvLen a = succ n → bvLen (bvMul a b) = bvLen b`.
///
/// `bvMul nil b = nil`, so the non-empty premise is load-bearing: it is what
/// the `nil` case refutes. For `a = a0 :: t`, `bvMul a b` is
/// `addRecM (if a0 then b else bvAllFalse b) (false :: bvMul t b) false`, whose
/// length is that of its first operand (`len_addRecM`), which is `bvLen b` in
/// both branches (`len_allFalse`, `Eq.refl`).
fn len_bv_mul() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let concl =
        |a: &Expr, b: &Expr| eq(nat(), bvlen(bvmul(a.clone(), b.clone())), bvlen(b.clone()));
    let premise = |a: &Expr, n: &Expr| eq(nat(), bvlen(a.clone()), succ(n.clone()));
    let ty = {
        let (a_id, a) = fr.local();
        let (b_id, b) = fr.local();
        let (n_id, n) = fr.local();
        let (h_id, _) = fr.local();
        pis(vec![(a_id, lb()), (b_id, lb()), (n_id, nat()), (h_id, premise(&a, &n))], concl(&a, &b))
    };
    let val = {
        let (a_id, a) = fr.local();
        let (b_id, b) = fr.local();
        let (n_id, n) = fr.local();
        let (h_id, h) = fr.local();
        let motive = {
            let (w_id, w) = fr.local();
            lams(vec![(w_id, lb())], Expr::arrow(premise(&w, &n), concl(&w, &b)))
        };
        let nil_case = {
            let (h0_id, h0) = fr.local();
            let body = absurd_zero_eq_succ(&mut fr, n.clone(), h0, concl(&kx::nil(), &b));
            lams(vec![(h0_id, premise(&kx::nil(), &n))], body)
        };
        let cons_case = {
            let (a0_id, a0) = fr.local();
            let (t_id, t) = fr.local();
            let (ih_id, _) = fr.local();
            let (h1_id, _) = fr.local();
            let whole = kx::cons(a0.clone(), t.clone());
            // sel x := Bool.rec (fun _ => List Bool) (bvAllFalse b) b x
            let sel = |x: Expr, fr: &mut Fresh| {
                let (w_id, _) = fr.local();
                let motive = lams(vec![(w_id, bool_ty())], lb());
                bool_rec(l1(), motive, kx::all_false(b.clone()), b.clone(), x)
            };
            let sel_a0 = sel(a0.clone(), &mut fr);
            let shifted = kx::cons(kx::bfalse(), bvmul(t.clone(), b.clone()));
            let step1 = Expr::apps(
                Expr::const_str(names::LEN_ADD_REC_M),
                [sel_a0.clone(), shifted, kx::bfalse()],
            );
            let step2 = {
                let (x_id, x) = fr.local();
                let sel_x = sel(x, &mut fr);
                let motive =
                    lams(vec![(x_id, bool_ty())], eq(nat(), bvlen(sel_x), bvlen(b.clone())));
                bool_rec(
                    Level::zero(),
                    motive,
                    Expr::app(Expr::const_str(names::LEN_ALL_FALSE), b.clone()),
                    refl(nat(), bvlen(b.clone())),
                    a0.clone(),
                )
            };
            let body = trans(
                nat(),
                bvlen(bvmul(whole.clone(), b.clone())),
                bvlen(sel_a0),
                bvlen(b.clone()),
                step1,
                step2,
            );
            let ih_ty = Expr::arrow(premise(&t, &n), concl(&t, &b));
            lams(
                vec![
                    (a0_id, bool_ty()),
                    (t_id, lb()),
                    (ih_id, ih_ty),
                    (h1_id, premise(&whole, &n)),
                ],
                body,
            )
        };
        let rec = list_rec_prop(motive, nil_case, cons_case, a.clone());
        lams(
            vec![(a_id, lb()), (b_id, lb()), (n_id, nat()), (h_id, premise(&a, &n))],
            Expr::app(rec, h),
        )
    };
    (ty, val)
}

/// `addRecM_comm : ∀ xs ys c, bvLen xs = bvLen ys → addRecM xs ys c = addRecM ys xs c`.
///
/// Induction on `xs`, case split on `ys`. The two mismatched cases refute the
/// length premise (`zero = succ _`). In the cons/cons case the heads commute by
/// `xor3_comm`, the carries by `maj_comm`, and the tails by the induction
/// hypothesis at the tail lengths (`succ` is injective).
fn add_rec_m_comm() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let len_eq = |xs: &Expr, ys: &Expr| eq(nat(), bvlen(xs.clone()), bvlen(ys.clone()));
    let goal = |xs: &Expr, ys: &Expr, c: &Expr| {
        eq(lb(), addm(xs.clone(), ys.clone(), c.clone()), addm(ys.clone(), xs.clone(), c.clone()))
    };
    // ∀ ys c, bvLen xs = bvLen ys → goal xs ys c
    let all = |fr: &mut Fresh, xs: &Expr| {
        let (ys_id, ys) = fr.local();
        let (c_id, c) = fr.local();
        pis(vec![(ys_id, lb()), (c_id, bool_ty())], Expr::arrow(len_eq(xs, &ys), goal(xs, &ys, &c)))
    };
    let ty = {
        let (xs_id, xs) = fr.local();
        let body = all(&mut fr, &xs);
        pis(vec![(xs_id, lb())], body)
    };
    let val = {
        let (xs_id, xs) = fr.local();
        let motive = {
            let (w_id, w) = fr.local();
            let body = all(&mut fr, &w);
            lams(vec![(w_id, lb())], body)
        };
        // fun y => bvLen left = bvLen y → goal left y c
        let inner_motive = |fr: &mut Fresh, left: &Expr, c: &Expr| {
            let (y_id, y) = fr.local();
            lams(vec![(y_id, lb())], Expr::arrow(len_eq(left, &y), goal(left, &y, c)))
        };
        let nil_case = {
            let (ys_id, ys) = fr.local();
            let (c_id, c) = fr.local();
            let left = kx::nil();
            let on_nil = {
                let (h_id, _) = fr.local();
                lams(vec![(h_id, len_eq(&left, &kx::nil()))], refl(lb(), kx::nil()))
            };
            let on_cons = {
                let (b_id, b) = fr.local();
                let (bs_id, bs) = fr.local();
                let (ih_id, _) = fr.local();
                let (h_id, h) = fr.local();
                let right = kx::cons(b, bs.clone());
                let ih_ty = Expr::arrow(len_eq(&left, &bs), goal(&left, &bs, &c));
                let body = absurd_zero_eq_succ(&mut fr, bvlen(bs), h, goal(&left, &right, &c));
                lams(
                    vec![
                        (b_id, bool_ty()),
                        (bs_id, lb()),
                        (ih_id, ih_ty),
                        (h_id, len_eq(&left, &right)),
                    ],
                    body,
                )
            };
            let m = inner_motive(&mut fr, &left, &c);
            lams(vec![(ys_id, lb()), (c_id, bool_ty())], list_rec_prop(m, on_nil, on_cons, ys))
        };
        let cons_case = {
            let (a_id, a) = fr.local();
            let (as_id, as_) = fr.local();
            let ih_ty = all(&mut fr, &as_);
            let (ih_id, ih) = fr.local();
            let (ys_id, ys) = fr.local();
            let (c_id, c) = fr.local();
            let left = kx::cons(a.clone(), as_.clone());
            let on_nil = {
                let (h_id, h) = fr.local();
                let h_ty = len_eq(&left, &kx::nil());
                let flipped = symm(nat(), bvlen(left.clone()), bvlen(kx::nil()), h);
                let body = absurd_zero_eq_succ(
                    &mut fr,
                    bvlen(as_.clone()),
                    flipped,
                    goal(&left, &kx::nil(), &c),
                );
                lams(vec![(h_id, h_ty)], body)
            };
            let on_cons = {
                let (b_id, b) = fr.local();
                let (bs_id, bs) = fr.local();
                let (ihb_id, _) = fr.local();
                let (h_id, h) = fr.local();
                let right = kx::cons(b.clone(), bs.clone());
                let ihb_ty = Expr::arrow(len_eq(&left, &bs), goal(&left, &bs, &c));
                // succ (bvLen as) = succ (bvLen bs)  ⟹  bvLen as = bvLen bs
                let pred = nat_pred(&mut fr);
                let h_tail = congr_arg(
                    nat(),
                    nat(),
                    succ(bvlen(as_.clone())),
                    succ(bvlen(bs.clone())),
                    pred,
                    h,
                );
                let k1 = maj(a.clone(), b.clone(), c.clone());
                let k2 = maj(b.clone(), a.clone(), c.clone());
                let s1 = xor3(a.clone(), b.clone(), c.clone());
                let s2 = xor3(b.clone(), a.clone(), c.clone());
                let t1 = addm(as_.clone(), bs.clone(), k1.clone());
                let t2 = addm(bs.clone(), as_.clone(), k1.clone());
                let t3 = addm(bs.clone(), as_.clone(), k2.clone());
                // t1 = t2: the induction hypothesis at the tails.
                let e12 = Expr::apps(ih, [bs.clone(), k1.clone(), h_tail]);
                // t2 = t3: the carries commute.
                let e23 = {
                    let (k_id, k) = fr.local();
                    let f = lams(vec![(k_id, bool_ty())], addm(bs.clone(), as_.clone(), k));
                    let mc = Expr::apps(
                        Expr::const_str(names::MAJ_COMM),
                        [a.clone(), b.clone(), c.clone()],
                    );
                    congr_arg(bool_ty(), lb(), k1, k2, f, mc)
                };
                let tails = trans(lb(), t1.clone(), t2, t3.clone(), e12, e23);
                let step1 = {
                    let (t_id, t) = fr.local();
                    let f = lams(vec![(t_id, lb())], kx::cons(s1.clone(), t));
                    congr_arg(lb(), lb(), t1.clone(), t3.clone(), f, tails)
                };
                let step2 = {
                    let (s_id, s) = fr.local();
                    let f = lams(vec![(s_id, bool_ty())], kx::cons(s, t3.clone()));
                    let xc = Expr::apps(
                        Expr::const_str(names::XOR3_COMM),
                        [a.clone(), b.clone(), c.clone()],
                    );
                    congr_arg(bool_ty(), lb(), s1.clone(), s2.clone(), f, xc)
                };
                let body = trans(
                    lb(),
                    kx::cons(s1.clone(), t1),
                    kx::cons(s1, t3.clone()),
                    kx::cons(s2, t3),
                    step1,
                    step2,
                );
                lams(
                    vec![
                        (b_id, bool_ty()),
                        (bs_id, lb()),
                        (ihb_id, ihb_ty),
                        (h_id, len_eq(&left, &right)),
                    ],
                    body,
                )
            };
            let m = inner_motive(&mut fr, &left, &c);
            lams(
                vec![
                    (a_id, bool_ty()),
                    (as_id, lb()),
                    (ih_id, ih_ty),
                    (ys_id, lb()),
                    (c_id, bool_ty()),
                ],
                list_rec_prop(m, on_nil, on_cons, ys),
            )
        };
        lams(vec![(xs_id, lb())], list_rec_prop(motive, nil_case, cons_case, xs))
    };
    (ty, val)
}

/// The theorems in dependency order: `(name, statement, proof)`.
fn theorems() -> Vec<(&'static str, Expr, Expr)> {
    let named = |name: &'static str, (ty, val): (Expr, Expr)| (name, ty, val);
    vec![
        named(names::XOR3_COMM, gate_comm("Clean.BVI.xor3")),
        named(names::MAJ_COMM, gate_comm("Clean.BVI.maj")),
        named(names::LEN_ADD_REC_M, len_add_rec_m()),
        named(names::LEN_ALL_FALSE, len_all_false()),
        named(names::LEN_BV_MUL, len_bv_mul()),
        named(names::ADD_REC_M_COMM, add_rec_m_comm()),
    ]
}

/// Add the theorems to `env` (which must carry the `Clean.BVC` layer). Each is
/// a `Declaration::Theorem`, so `add_decl` type-checks its proof against its
/// statement; a wrong proof fails here and the route stays unavailable.
fn register(env: &mut Environment) -> Result<(), String> {
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

// ── per-obligation terms ─────────────────────────────────────────────────────

/// The constant standing for bit `k` (0 = least significant) of the `w`-bit
/// variable `name`. The decimal `w` and `k` are the last two `_`-separated
/// fields, so distinct `(name, w, k)` give distinct constants. Keep the
/// whole spelling in one string component: parsing dotted numeric pieces
/// would collapse distinct raw Formula identities such as `X.01.a` and `X.1.a`.
pub(super) fn bit_name(name: &str, w: u32, k: u32) -> Name {
    Name::anon().str(format!("BVC_LEAFBIT_{name}_{w}_{k}"))
}

/// A `w`-bit variable as a concrete cons list of `w` opaque `Bool` constants,
/// least significant first (the order of [`kx::bits`]).
pub(crate) fn bit_leaf(name: &str, w: u32) -> Expr {
    let mut acc = kx::nil();
    for k in (0..w).rev() {
        acc = kx::cons(Expr::const_(bit_name(name, w, k), vec![]), acc);
    }
    acc
}

/// Every name in `names` must be a `Theorem` that carries its proof and whose
/// axiom closure is empty in BOTH halves: no domain axiom (`axiom_deps`) and
/// no foundational one (`foundational_axiom_deps`: `propext`, `Quot.sound`,
/// `Classical.choice`). `add_decl` checked each proof against its statement;
/// this checks that what was checked is a proof and rests on nothing taken on
/// faith. A prelude lemma can fall back to an `Axiom` when its proof does not
/// build, so presence alone is not enough. `Err` names the first failure.
pub(crate) fn audit_theorems(env: &Environment, names: &[&str]) -> Result<(), String> {
    for name in names {
        let n = Name::from_string(name);
        let info = env.get_const(&n).ok_or_else(|| format!("audit: {name} is absent"))?;
        if info.kind != ConstantKind::Theorem || info.value.is_none() {
            return Err(format!("audit: {name} is a {:?}, not a proved theorem", info.kind));
        }
        let domain = env.axiom_deps(&n).ok_or_else(|| format!("audit: {name}: no closure"))?;
        if !domain.is_empty() {
            return Err(format!("audit: {name} reaches axioms {domain:?}"));
        }
        let foundational =
            env.foundational_axiom_deps(&n).ok_or_else(|| format!("audit: {name}: no closure"))?;
        if !foundational.is_empty() {
            return Err(format!("audit: {name} reaches foundational axioms {foundational:?}"));
        }
    }
    Ok(())
}

/// The pinned `Clean.BVC` layer plus the theorems above, built and audited
/// once per process. Every obligation clones it and adds only its own
/// variables. `Err` (the theorems did not register, or the audit of
/// [`names::ALL`] and [`REFLECTION_LEMMAS`] failed) is kept for the life of
/// the process, and every route built on this base declines.
pub(crate) fn commuting_base() -> Result<&'static Environment, String> {
    static BASE: OnceLock<Result<Environment, String>> = OnceLock::new();
    BASE.get_or_init(|| {
        let mut env = super::discharge_env(&[], &[])?;
        register(&mut env)?;
        audit_theorems(&env, &names::ALL)?;
        audit_theorems(&env, &REFLECTION_LEMMAS)?;
        Ok(env)
    })
    .as_ref()
    .map_err(Clone::clone)
}

/// The environment the commuted discharge is checked in: the `Clean.BVC` layer,
/// the theorems above, and one opaque `Bool` per bit of each variable.
pub(crate) fn commuting_env(leaves: &[(String, u32)]) -> Result<Environment, String> {
    let mut env = commuting_base()?.clone();
    add_leaf_bits(&mut env, leaves);
    Ok(env)
}

/// Add one opaque `Bool` axiom per bit of each `(name, w)` variable, the
/// constants [`bit_leaf`] lists. They only state an obligation ("for every
/// `w`-bit value"); no theorem depends on them.
pub(crate) fn add_leaf_bits(env: &mut Environment, leaves: &[(String, u32)]) {
    for (name, w) in leaves {
        for k in 0..*w {
            // A repeated variable is declared once; the second add is refused
            // and ignored, as for the `BVC_LEAF_*` axioms.
            let _ = env.add_decl(Declaration::Axiom {
                name: bit_name(name, *w, k),
                level_params: vec![],
                type_: bool_ty(),
            });
        }
    }
}

fn const_name(e: &Expr) -> Option<&Name> {
    match e.kind() {
        ExprKind::Const(name, _) => Some(name),
        _ => None,
    }
}

fn is_const(e: &Expr, name: &str) -> bool {
    const_name(e).is_some_and(|n| *n == Name::from_string(name))
}

/// The length of a concrete cons list (`List.cons Bool h t` … `List.nil Bool`).
fn spine_len(mut e: &Expr) -> Option<u32> {
    let mut n = 0u32;
    loop {
        let head = e.get_app_fn();
        let args = e.get_app_args();
        if is_const(head, "List.nil") && args.len() == 1 {
            return Some(n);
        }
        if !is_const(head, "List.cons") || args.len() != 3 {
            return None;
        }
        n = n.checked_add(1)?;
        e = args[2];
    }
}

/// `(p, w)` with `p : bvLen (bvfEval core) = w` (the numeral a `Nat.succ`
/// chain), for the node kinds whose length this module can prove. `None` for
/// every other node: the caller then leaves that `Add` in source order.
pub(crate) fn core_len(core: &Expr) -> Option<(Expr, u32)> {
    let head = const_name(core.get_app_fn())?.to_string();
    let args = core.get_app_args();
    let ev = |e: &Expr| kx::evalf(e.clone());
    match (head.as_str(), args.as_slice()) {
        // `bvfEval (Leaf l)` and `bvfEval (Const l)` reduce to `l`; on a
        // concrete list `bvLen l` computes, so `Eq.refl` closes it.
        ("Clean.BVC.BvF.Leaf" | "Clean.BVC.BvF.Const", [list]) => {
            let w = spine_len(list)?;
            Some((refl(nat(), kx::nat_lit(w)), w))
        }
        // A low extract of a concrete list by a concrete tag: `bvTakeLen`
        // computes to a concrete list of the tag's length.
        ("Clean.BVC.BvF.ExtractLow", [inner, tag]) => {
            let inner_w = leaf_spine_len(inner)?;
            let w = leaf_spine_len(tag)?;
            (w <= inner_w).then(|| (refl(nat(), kx::nat_lit(w)), w))
        }
        ("Clean.BVC.BvF.Add", [a, b]) => {
            let (pa, w) = core_len(a)?;
            let step =
                Expr::apps(Expr::const_str(names::LEN_ADD_REC_M), [ev(a), ev(b), kx::bfalse()]);
            Some((trans(nat(), bvlen(ev(core)), bvlen(ev(a)), kx::nat_lit(w), step, pa), w))
        }
        ("Clean.BVC.BvF.Sub", [a, b]) => {
            let (pa, w) = core_len(a)?;
            let step = Expr::apps(
                Expr::const_str(names::LEN_ADD_REC_M),
                [ev(a), kx::bv_not(ev(b)), kx::btrue()],
            );
            Some((trans(nat(), bvlen(ev(core)), bvlen(ev(a)), kx::nat_lit(w), step, pa), w))
        }
        ("Clean.BVC.BvF.Mul", [a, b]) => {
            let (pa, wa) = core_len(a)?;
            let (pb, wb) = core_len(b)?;
            let pred = wa.checked_sub(1)?;
            let step = Expr::apps(
                Expr::const_str(names::LEN_BV_MUL),
                [ev(a), ev(b), kx::nat_lit(pred), pa],
            );
            Some((trans(nat(), bvlen(ev(core)), bvlen(ev(b)), kx::nat_lit(wb), step, pb), wb))
        }
        _ => None,
    }
}

/// The spine length of `Leaf l` / `Const l` over a concrete list.
fn leaf_spine_len(e: &Expr) -> Option<u32> {
    let head = const_name(e.get_app_fn())?.to_string();
    let args = e.get_app_args();
    match (head.as_str(), args.as_slice()) {
        ("Clean.BVC.BvF.Leaf" | "Clean.BVC.BvF.Const", [list]) => spine_len(list),
        _ => None,
    }
}

/// A total structural key for ordering the operands of an `Add`.
fn order_key(e: &Expr, out: &mut String) {
    match e.kind() {
        ExprKind::Const(name, _) => out.push_str(&name.to_string()),
        ExprKind::App(f, a) => {
            out.push('(');
            order_key(f, out);
            out.push(' ');
            order_key(a, out);
            out.push(')');
        }
        other => out.push_str(&format!("{other:?}")),
    }
}

/// Is `core` a `BvF.Mul` node?
fn is_mul(core: &Expr) -> bool {
    is_const(core.get_app_fn(), "Clean.BVC.BvF.Mul") && core.get_app_args().len() == 2
}

/// `p : bvfEval (Add l r) = bvfEval (Add r l)` when one operand is a multiply
/// (the module's scope), `l` sorts after `r` and both lengths are provable and
/// equal; `None` when the pair is out of scope, already in order, or no proof
/// is available.
///
/// The order only has to be the same function on both sides of an obligation,
/// so that two cores differing by commuted `Add` operands become one term. It
/// carries no authority: the returned proof is an instance of
/// `addRecM_comm`, and the kernel checks it where the caller uses it.
pub(crate) fn canonical_step(l: &Expr, r: &Expr) -> Option<Expr> {
    if !is_mul(l) && !is_mul(r) {
        return None;
    }
    let (mut kl, mut kr) = (String::new(), String::new());
    order_key(l, &mut kl);
    order_key(r, &mut kr);
    if kl <= kr {
        return None;
    }
    let (pl, wl) = core_len(l)?;
    let (pr, wr) = core_len(r)?;
    if wl != wr {
        return None;
    }
    Some(commute(l, r, wl, pl, pr))
}

/// The instance `addRecM_comm (eval l) (eval r) false h`, with
/// `h : bvLen (eval l) = bvLen (eval r)` from the two length proofs.
fn commute(l: &Expr, r: &Expr, w: u32, pl: Expr, pr: Expr) -> Expr {
    let (el, er) = (kx::evalf(l.clone()), kx::evalf(r.clone()));
    let n = kx::nat_lit(w);
    let h = trans(
        nat(),
        bvlen(el.clone()),
        n.clone(),
        bvlen(er.clone()),
        pl,
        symm(nat(), bvlen(er.clone()), n, pr),
    );
    Expr::apps(Expr::const_str(names::ADD_REC_M_COMM), [el, er, kx::bfalse(), h])
}

#[cfg(test)]
mod tests {
    use clean_kernel::{ConstantKind, TypeChecker};
    use trust_types::{Formula, Sort};

    use super::super::{
        AddCommFilter, ReflectCtx, reflect_formula, run_recheck_thread, try_add_comm_discharge,
        try_shared_core_discharge,
    };
    use super::*;

    fn var(name: &str, w: u32) -> Formula {
        Formula::Var(name.into(), Sort::BitVec(w))
    }
    fn lit(value: i128, width: u32) -> Formula {
        Formula::BitVec { value, width }
    }
    fn add(l: Formula, r: Formula, w: u32) -> Formula {
        Formula::BvAdd(Box::new(l), Box::new(r), w)
    }
    fn sub(l: Formula, r: Formula, w: u32) -> Formula {
        Formula::BvSub(Box::new(l), Box::new(r), w)
    }
    fn mul(l: Formula, r: Formula, w: u32) -> Formula {
        Formula::BvMul(Box::new(l), Box::new(r), w)
    }

    /// The kernel's verdict on `proof : goal` in the commuting environment.
    fn kernel_check(leaves: &[(&str, u32)], proof: Expr, goal: Expr) -> Result<(), String> {
        let leaves: Vec<(String, u32)> =
            leaves.iter().map(|(n, w)| ((*n).to_string(), *w)).collect();
        run_recheck_thread("add-comm-test", move || {
            let env = commuting_env(&leaves)?;
            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.check_type(&proof, &goal).map_err(|e| format!("{e:?}"))
        })
        .map_err(|e| e.to_string())?
    }

    /// The commuting-mode core of `f`.
    fn core_of(f: &Formula) -> Expr {
        reflect_formula(f, &mut ReflectCtx::commuting()).expect("in fragment").core
    }

    /// Each theorem is a `Theorem` the kernel checked, reaches no axiom, and
    /// its proof re-checks against its statement in an environment that does
    /// not yet contain it. FAILS if a proof is replaced by an axiom or by a
    /// term the kernel does not accept.
    #[test]
    fn theorems_are_kernel_checked_with_an_empty_axiom_closure() {
        run_recheck_thread("add-comm-theorems", || {
            let env = commuting_env(&[]).expect("the theorems register");
            for name in names::ALL {
                let n = Name::from_string(name);
                let info = env.get_const(&n).unwrap_or_else(|| panic!("{name} is registered"));
                assert_eq!(info.kind, ConstantKind::Theorem, "{name}");
                assert!(info.value.is_some(), "{name} carries its proof");
                let deps = env.axiom_deps(&n).unwrap_or_else(|| panic!("{name}: no closure"));
                assert!(deps.is_empty(), "{name} reaches an axiom: {deps:?}");
            }
            // Independently of `add_decl`: check every proof against its
            // statement, each in the environment of the ones before it.
            let mut env = super::super::discharge_env(&[], &[]).expect("BVC layer");
            for (name, type_, value) in theorems() {
                {
                    let tc = TypeChecker::with_mode(&env, env.mode());
                    tc.check_type(&value, &type_).unwrap_or_else(|e| panic!("{name}: {e:?}"));
                }
                env.add_decl(Declaration::Theorem {
                    name: Name::from_string(name),
                    level_params: vec![],
                    type_,
                    value,
                })
                .unwrap_or_else(|e| panic!("{name}: {e:?}"));
            }
            // `add_decl` is what production relies on (`register`): it refuses
            // a theorem whose proof is not a proof of its statement.
            let one = kx::cons(kx::btrue(), kx::nil());
            let bogus = env.add_decl(Declaration::Theorem {
                name: Name::from_string("Trust.BVC.bogus"),
                level_params: vec![],
                type_: eq(lb(), kx::nil(), one),
                value: refl(lb(), kx::nil()),
            });
            assert!(bogus.is_err(), "a false theorem was admitted");
        })
        .expect("kernel thread");
    }

    /// `7 + x * 3` (what `madd` renders) against `x * 3 + 7` (the source):
    /// the shared-core route declines, the commuted retry proves it. Likewise
    /// `a + a * b` against `a * b + a`, and the 32-bit shape.
    #[test]
    fn mul_then_add_in_the_other_order_is_proved_by_the_retry_only() {
        let cases = [
            (
                add(lit(7, 64), mul(var("X0", 64), lit(3, 64), 64), 64),
                add(mul(var("X0", 64), lit(3, 64), 64), lit(7, 64), 64),
            ),
            (
                add(var("X0", 64), mul(var("X0", 64), var("X1", 64), 64), 64),
                add(mul(var("X0", 64), var("X1", 64), 64), var("X0", 64), 64),
            ),
            (
                add(lit(3, 32), mul(var("W0", 32), lit(7, 32), 32), 32),
                add(mul(var("W0", 32), lit(7, 32), 32), lit(3, 32), 32),
            ),
        ];
        for (machine, auto) in &cases {
            assert_eq!(try_shared_core_discharge(machine, auto), None, "{machine:?}");
            assert_eq!(
                try_add_comm_discharge(machine, auto, AddCommFilter::On).as_deref(),
                Some(THEOREM_LABEL),
                "{machine:?}"
            );
        }
    }

    /// The object computes `x * 3 + 7`, the specification says `x * 3 + 8`.
    /// Declined with the filter on, and with it off the KERNEL rejects the
    /// term: commuting the Add does not make 7 equal 8.
    #[test]
    fn a_wrong_addend_is_rejected_by_the_kernel() {
        let machine = add(lit(7, 64), mul(var("X0", 64), lit(3, 64), 64), 64);
        let auto = add(mul(var("X0", 64), lit(3, 64), 64), lit(8, 64), 64);
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::On), None);
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::Off), None);
        // The twin with the right addend is proved, so the two `None`s above
        // are about the addend and not about a broken harness.
        let twin = add(mul(var("X0", 64), lit(3, 64), 64), lit(7, 64), 64);
        assert!(try_add_comm_discharge(&machine, &twin, AddCommFilter::Off).is_some());
    }

    /// A wrong multiplier under the commuted Add is rejected as well.
    #[test]
    fn a_wrong_multiplier_is_rejected_by_the_kernel() {
        let machine = add(lit(7, 64), mul(var("X0", 64), lit(3, 64), 64), 64);
        let auto = add(mul(var("X0", 64), lit(5, 64), 64), lit(7, 64), 64);
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::On), None);
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::Off), None);
    }

    /// `7 - x * 3` against `x * 3 - 7`: Sub at the node the retry reorders for
    /// Add. The retry never reorders a Sub, and a term that applies the
    /// commutation theorem to a Sub's operands is not a proof of the Sub
    /// equation: the kernel rejects it.
    #[test]
    fn sub_is_not_commuted() {
        let product = mul(var("X0", 64), lit(3, 64), 64);
        let machine = sub(lit(7, 64), product.clone(), 64);
        let auto = sub(product.clone(), lit(7, 64), 64);
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::On), None);
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::Off), None);

        // Forged: `addRecM_comm` at the operands of the Sub, offered as a proof
        // of `eval (Sub 7 p) = eval (Sub p 7)`.
        let (c7, p) = (core_of(&lit(7, 64)), core_of(&product));
        let (p7, w7) = core_len(&c7).expect("constant length");
        let (pp, wp) = core_len(&p).expect("product length");
        assert_eq!((w7, wp), (64, 64));
        let forged = commute(&c7, &p, 64, p7.clone(), pp.clone());
        let sub_goal = kx::eq_list(
            kx::evalf(kx::sub(c7.clone(), p.clone())),
            kx::evalf(kx::sub(p.clone(), c7.clone())),
        );
        let leaves = [("X0", 64)];
        assert!(kernel_check(&leaves, forged.clone(), sub_goal).is_err());
        // The same term IS a proof of the Add equation, so the rejection above
        // is the kernel telling Sub from Add.
        let add_goal =
            kx::eq_list(kx::evalf(kx::add(c7.clone(), p.clone())), kx::evalf(kx::add(p, c7)));
        kernel_check(&leaves, forged, add_goal).expect("Add commutes at equal lengths");
    }

    /// Scope. A plain `Add` (no multiply operand) is never reordered: the
    /// retry declines `X0 + X1` against `X1 + X0` without the kernel, as the
    /// structured route did before the retry existed (pinned, through the
    /// public entry, by `verify_output::tests::b4_mis_reflection_is_kernel_guarded`).
    /// With the filter off the kernel is handed the unreordered pair and
    /// rejects it: the two cores are different terms and no step joins them.
    #[test]
    fn a_plain_add_is_not_reordered() {
        let machine = add(var("X0", 64), var("X1", 64), 64);
        let auto = add(var("X1", 64), var("X0", 64), 64);
        let (l, r) = (core_of(&var("X0", 64)), core_of(&var("X1", 64)));
        assert!(canonical_step(&l, &r).is_none());
        assert!(canonical_step(&r, &l).is_none());
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::On), None);
        assert_eq!(try_add_comm_discharge(&machine, &auto, AddCommFilter::Off), None);
        assert_eq!(super::super::try_o1_instantiation_discharge(&machine, &auto), None);
    }

    /// The length premise is load-bearing. An 8-bit and a 4-bit operand do not
    /// commute under `addRecM` (the result takes the first operand's length),
    /// and the kernel rejects the instance whose length proofs claim they are
    /// the same width. It also rejects the unconditional statement at the
    /// ground witness `[true]`, `[]`.
    #[test]
    fn commutation_without_equal_lengths_is_kernel_rejected() {
        let (wide, narrow) = (core_of(&lit(1, 8)), core_of(&lit(1, 4)));
        let goal = kx::eq_list(
            kx::evalf(kx::add(wide.clone(), narrow.clone())),
            kx::evalf(kx::add(narrow.clone(), wide.clone())),
        );
        let claim = |w: u32| refl(nat(), kx::nat_lit(w));
        let forged = commute(&wide, &narrow, 8, claim(8), claim(8));
        assert!(kernel_check(&[], forged, goal.clone()).is_err());
        // Not provable by computation either: the two sides are different lists.
        assert!(kernel_check(&[], refl(lb(), kx::evalf(kx::add(wide, narrow))), goal).is_err());
        // `canonical_step` refuses the pair in either order.
        let (wide, narrow) = (core_of(&lit(1, 8)), core_of(&lit(1, 4)));
        assert!(canonical_step(&wide, &narrow).is_none());
        assert!(canonical_step(&narrow, &wide).is_none());

        let one = kx::cons(kx::btrue(), kx::nil());
        let ground = kx::eq_list(
            addm(one.clone(), kx::nil(), kx::bfalse()),
            addm(kx::nil(), one.clone(), kx::bfalse()),
        );
        assert!(kernel_check(&[], refl(lb(), one), ground).is_err());
    }

    /// Prelude lemmas a bridge-side value theory over `Clean.BVC` may cite,
    /// with the kind and statement measured in `commuting_env(&[])` (Clean
    /// `4f1ed67055`); `None` means the prelude does not declare the name.
    /// Notation (`<`, `≤`, `%`) in a statement is the instance form (`LT.lt`,
    /// `LE.le`, `HMod.hMod`), not the raw `Nat.lt` / `Nat.le` / `Nat.mod`.
    #[rustfmt::skip]
    const PRELUDE_LEMMAS: &[(&str, Option<(ConstantKind, &str)>)] = &[
        (
            "Nat.div_add_mod",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> Nat.add (Nat.mul (Nat.div n n1) n1) (Nat.mod n n1) = n")),
        ),
        ("Nat.mod_add_div", None),
        (
            "Nat.mod_lt",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> Nat.lt Nat.zero n1 -> Nat.lt (Nat.mod n n1) n1")),
        ),
        (
            "Nat.mod_eq_of_lt",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> n < n1 -> n % n1 = n")),
        ),
        ("Nat.mod_self", None),
        ("Nat.mod_mod", None),
        ("Nat.add_mod", None),
        ("Nat.mod_add_mod", None),
        ("Nat.add_mul_mod_self_left", None),
        ("Nat.mul_add_mod", None),
        (
            "Nat.add_left_cancel",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> Nat.add n n1 = Nat.add n n2 -> n1 = n2")),
        ),
        (
            "Nat.add_right_cancel",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> Nat.add n n1 = Nat.add n2 n1 -> n = n2")),
        ),
        (
            "Nat.lt_irrefl",
            Some((ConstantKind::Theorem, "(n : Nat) -> Nat.lt n n -> False")),
        ),
        (
            "Nat.le_refl",
            Some((ConstantKind::Theorem, "(n : Nat) -> n ≤ n")),
        ),
        (
            "Nat.le_trans",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> n ≤ n1 -> n1 ≤ n2 -> n ≤ n2")),
        ),
        (
            "Nat.lt_trans",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> n < n1 -> n1 < n2 -> n < n2")),
        ),
        (
            "Nat.le_add_right",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> Nat.le n (Nat.add n n1)")),
        ),
        (
            "Nat.lt_of_lt_of_le",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> n < n1 -> n1 ≤ n2 -> n < n2")),
        ),
        (
            "Nat.lt_of_le_of_lt",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> n ≤ n1 -> n1 < n2 -> n < n2")),
        ),
        (
            "Nat.zero_lt_succ",
            Some((ConstantKind::Theorem, "(n : Nat) -> Nat.zero < Nat.succ n")),
        ),
        (
            "Nat.succ_le_succ",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> Nat.le n n1 -> Nat.le (Nat.succ n) (Nat.succ n1)")),
        ),
        ("Nat.le_of_lt_succ", None),
        (
            "Nat.lt_succ_self",
            Some((ConstantKind::Theorem, "(n : Nat) -> n < Nat.succ n")),
        ),
        ("Nat.succ_ne_zero", None),
        (
            "Nat.mul_le_mul_left",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> Nat.le n n1 -> Nat.le (Nat.mul n2 n) (Nat.mul n2 n1)")),
        ),
        (
            "Nat.add_comm",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> Nat.add n n1 = Nat.add n1 n")),
        ),
        (
            "Nat.add_assoc",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> Nat.add (Nat.add n n1) n2 = Nat.add n (Nat.add n1 n2)")),
        ),
        (
            "Nat.mul_comm",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> Nat.mul n n1 = Nat.mul n1 n")),
        ),
        (
            "Nat.mul_assoc",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> Nat.mul (Nat.mul n n1) n2 = Nat.mul n (Nat.mul n1 n2)")),
        ),
        (
            "Nat.left_distrib",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> Nat.mul n (Nat.add n1 n2) = Nat.add (Nat.mul n n1) (Nat.mul n n2)")),
        ),
        (
            "Nat.right_distrib",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> Nat.mul (Nat.add n n1) n2 = Nat.add (Nat.mul n n2) (Nat.mul n1 n2)")),
        ),
        (
            "Nat.mul_one",
            Some((ConstantKind::Theorem, "(n : Nat) -> Nat.mul n (Nat.succ Nat.zero) = n")),
        ),
        (
            "Nat.one_mul",
            Some((ConstantKind::Theorem, "(n : Nat) -> Nat.mul (Nat.succ Nat.zero) n = n")),
        ),
        (
            "Nat.mul_zero",
            Some((ConstantKind::Theorem, "(n : Nat) -> Nat.mul n Nat.zero = Nat.zero")),
        ),
        (
            "Nat.zero_mul",
            Some((ConstantKind::Theorem, "(n : Nat) -> Nat.mul Nat.zero n = Nat.zero")),
        ),
        (
            "Nat.add_zero",
            Some((ConstantKind::Theorem, "(n : Nat) -> Nat.add n Nat.zero = n")),
        ),
        (
            "Nat.zero_add",
            Some((ConstantKind::Theorem, "(n : Nat) -> Nat.add Nat.zero n = n")),
        ),
        (
            "Nat.add_succ",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> Nat.add n (Nat.succ n1) = Nat.succ (Nat.add n n1)")),
        ),
        (
            "Nat.succ_add",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> Nat.add (Nat.succ n) n1 = Nat.succ (Nat.add n n1)")),
        ),
        (
            "Nat.succ_mul",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> Nat.mul (Nat.succ n) n1 = Nat.add n1 (Nat.mul n n1)")),
        ),
        (
            "Nat.mul_succ",
            Some((ConstantKind::Theorem, "(n : Nat) -> (n1 : Nat) -> Nat.mul n (Nat.succ n1) = Nat.add n (Nat.mul n n1)")),
        ),
        ("Nat.pow_succ", None),
        ("Nat.succ.inj", None),
        (
            "Nat.noConfusion",
            Some((ConstantKind::Definition, "(u : Sort u) -> (n : Nat) -> (n1 : Nat) -> n = n1 -> Nat.noConfusionType u n n1")),
        ),
        (
            "congrArg",
            Some((ConstantKind::Theorem, "(u : Sort u) -> (u1 : Sort v) -> (x : u) -> (x1 : u) -> (f : u -> u1) -> x = x1 -> f x = f x1")),
        ),
        (
            "Eq.subst",
            Some((ConstantKind::Theorem, "(u : Sort u) -> (f : u -> Prop) -> (x : u) -> (x1 : u) -> x = x1 -> f x -> f x1")),
        ),
        (
            "Eq.trans",
            Some((ConstantKind::Theorem, "(u : Sort u) -> (x : u) -> (x1 : u) -> (x2 : u) -> x = x1 -> x1 = x2 -> x = x2")),
        ),
        (
            "Eq.symm",
            Some((ConstantKind::Theorem, "(u : Sort u) -> (x : u) -> (x1 : u) -> x = x1 -> x1 = x")),
        ),
        (
            "Eq.mpr",
            Some((ConstantKind::Definition, "(u : Sort u) -> (u1 : Sort u) -> u = u1 -> u1 -> u")),
        ),
        (
            "False.elim",
            Some((ConstantKind::Definition, "(u : Sort u) -> False -> u")),
        ),
    ];

    /// Definitions those lemmas and the `Clean.BVC` value theory are stated over.
    const PRELUDE_DEFS: &[&str] = &[
        "Nat.add",
        "Nat.mul",
        "Nat.mod",
        "Nat.div",
        "Nat.pow",
        "Nat.ble",
        "Nat.le",
        "Nat.lt",
        "HAdd.hAdd",
        "HMod.hMod",
        "LT.lt",
        "LE.le",
        "Clean.BVC.bvToNat",
        "Clean.BVC.bvLen",
        "Clean.BVC.bvTwoPow",
        "Clean.BVC.natToBvAux",
        "Clean.BVC.bvMul",
        "Clean.BVC.bvShl",
        "Clean.BVC.bvNot",
        "Clean.BVC.bvAllFalse",
        "Clean.BVC.bvAppend",
        "Clean.BVC.bvReplF",
        "Clean.BVC.bvZeroExt",
        "Clean.BVC.bvTakeLen",
        "Clean.BVC.idP",
        "Clean.BVI.addRecM",
        "Clean.BVI.xor3",
        "Clean.BVI.maj",
        "Clean.BVI.bhead",
        "Clean.BVI.btail",
    ];

    /// One inventory row: presence, kind, statement, and both halves of the
    /// axiom closure. `None` when the name is absent.
    fn inventory_row(
        env: &Environment,
        name: &str,
    ) -> Option<(ConstantKind, String, Vec<String>, Vec<String>)> {
        let n = Name::from_string(name);
        let info = env.get_const(&n)?;
        fn sorted(set: impl IntoIterator<Item = Name>) -> Vec<String> {
            let mut v: Vec<String> = set.into_iter().map(|n| n.to_string()).collect();
            v.sort();
            v
        }
        Some((
            info.kind,
            info.type_.to_string(),
            sorted(env.axiom_deps(&n).into_iter().flatten()),
            sorted(env.foundational_axiom_deps(&n).into_iter().flatten()),
        ))
    }

    /// Inventory of the prelude, in the environment `add_comm` builds on: for
    /// each lemma and definition a value theory may use, whether it is
    /// present, its kind, its exact statement and both halves of its axiom
    /// closure. `--nocapture` prints every row (and the value of each
    /// definition a value theory unfolds). FAILS if a lemma appears, vanishes,
    /// changes kind or statement, loses its proof, or reaches any axiom,
    /// foundational or not: a bridge-side proof citing it would then rest on
    /// something this pin did not see.
    #[test]
    fn prelude_lemma_inventory() {
        run_recheck_thread("add-comm-inventory", || {
            let env = commuting_env(&[]).expect("base");
            let print =
                |name: &str, row: &Option<(ConstantKind, String, Vec<String>, Vec<String>)>| {
                    match row {
                        None => println!("INVENTORY {name}: ABSENT"),
                        Some((kind, ty, ax, fx)) => {
                            println!(
                                "INVENTORY {name}: {kind:?} axiom_deps={ax:?} foundational={fx:?}"
                            );
                            println!("  type: {ty}");
                            let info = env.get_const(&Name::from_string(name)).expect("present");
                            if ty.contains(['<', '≤', '%']) {
                                let d: String =
                                    format!("{:?}", info.type_).chars().take(1200).collect();
                                println!("  type (structure): {d}");
                            }
                            if *kind != ConstantKind::Theorem
                                && let Some(v) = &info.value
                            {
                                let v: String = v.to_string().chars().take(1500).collect();
                                println!("  value: {v}");
                            }
                        }
                    }
                };
            let closed = |name: &str, row: &(ConstantKind, String, Vec<String>, Vec<String>)| {
                assert!(row.2.is_empty(), "{name} reaches a domain axiom: {:?}", row.2);
                assert!(row.3.is_empty(), "{name} reaches a foundational axiom: {:?}", row.3);
                if row.0 == ConstantKind::Theorem {
                    let info = env.get_const(&Name::from_string(name)).expect("present");
                    assert!(info.value.is_some(), "{name} is a theorem without a proof");
                }
            };
            for (name, expected) in PRELUDE_LEMMAS {
                let row = inventory_row(&env, name);
                print(name, &row);
                let seen = row.as_ref().map(|(kind, ty, _, _)| (*kind, ty.as_str()));
                assert_eq!(seen, *expected, "{name}");
                if let Some(row) = &row {
                    closed(name, row);
                }
            }
            for name in PRELUDE_DEFS {
                let row = inventory_row(&env, name);
                print(name, &row);
                let row = row.unwrap_or_else(|| panic!("{name} is absent"));
                assert_eq!(row.0, ConstantKind::Definition, "{name}");
                closed(name, &row);
            }
            // Every `Clean.BVC.bvf_*` lemma reflection may splice.
            let mut bvf: Vec<String> = env
                .constants()
                .map(|c| c.name.to_string())
                .filter(|n| n.starts_with("Clean.BVC.bvf_"))
                .collect();
            bvf.sort();
            assert_eq!(bvf.len(), 20, "{bvf:?}");
            for name in &bvf {
                let row = inventory_row(&env, name);
                print(name, &row);
                let row = row.expect("listed");
                assert_eq!(row.0, ConstantKind::Theorem, "{name}");
                closed(name, &row);
            }
            // Orientation of `Nat.div_add_mod`: `n / d * d + n % d = n`,
            // quotient first and multiplied on the LEFT of the divisor.
            let dam = env.get_const(&Name::from_string("Nat.div_add_mod")).expect("present");
            assert_eq!(
                dam.type_.to_string(),
                "(n : Nat) -> (n1 : Nat) -> Nat.add (Nat.mul (Nat.div n n1) n1) (Nat.mod n n1) = n"
            );
        })
        .expect("kernel thread");
    }

    /// The memoized base passes its own audit, and `commuting_env` is that
    /// base plus the leaves.
    #[test]
    fn commuting_base_is_audited() {
        run_recheck_thread("add-comm-base-audit", || {
            let base = commuting_base().expect("the base builds and passes its audit");
            audit_theorems(base, &names::ALL).expect("theorems");
            audit_theorems(base, &REFLECTION_LEMMAS).expect("reflection lemmas");
            let env = commuting_env(&[("X0".to_string(), 2)]).expect("env");
            assert!(env.get_const(&bit_name("X0", 2, 1)).is_some());
            assert!(base.get_const(&bit_name("X0", 2, 1)).is_none());
        })
        .expect("kernel thread");
    }

    /// The audit fails closed: an absent name, an `Axiom` under an audited
    /// name, a theorem that reaches a domain axiom, and a theorem that
    /// reaches the foundational `propext` are each refused, and a list is
    /// refused when any one member is.
    #[test]
    fn the_audit_refuses_axioms_and_axiom_dependent_theorems() {
        run_recheck_thread("add-comm-audit-negative", || {
            let mut env = super::super::discharge_env(&[], &[]).expect("base");
            register(&mut env).expect("theorems");
            audit_theorems(&env, &names::ALL).expect("the real theorems pass");
            let truth = Expr::const_str("True");
            env.add_decl(Declaration::Axiom {
                name: Name::from_string("Trust.BVC.audit_test_axiom"),
                level_params: vec![],
                type_: truth.clone(),
            })
            .expect("axiom");
            env.add_decl(Declaration::Theorem {
                name: Name::from_string("Trust.BVC.audit_test_on_axiom"),
                level_params: vec![],
                type_: truth.clone(),
                value: Expr::const_str("Trust.BVC.audit_test_axiom"),
            })
            .expect("theorem citing the axiom");
            let propext = env.get_const(&Name::from_string("propext")).expect("propext").clone();
            assert!(propext.level_params.is_empty());
            env.add_decl(Declaration::Theorem {
                name: Name::from_string("Trust.BVC.audit_test_on_propext"),
                level_params: vec![],
                type_: propext.type_.clone(),
                value: Expr::const_str("propext"),
            })
            .expect("theorem citing propext");
            env.add_decl(Declaration::Theorem {
                name: Name::from_string("Trust.BVC.audit_test_clean"),
                level_params: vec![],
                type_: truth,
                value: Expr::const_str("True.intro"),
            })
            .expect("clean theorem");
            audit_theorems(&env, &["Trust.BVC.audit_test_clean"]).expect("a clean theorem passes");
            for bad in [
                "Trust.BVC.audit_test_absent",
                "Trust.BVC.audit_test_axiom",
                "Trust.BVC.audit_test_on_axiom",
                "Trust.BVC.audit_test_on_propext",
                "Clean.BVC.bvLen",
            ] {
                let err = audit_theorems(&env, &[bad]).expect_err(bad);
                assert!(err.contains(bad), "{err}");
                let err = audit_theorems(&env, &[names::ADD_REC_M_COMM, bad]).expect_err(bad);
                assert!(err.contains(bad), "{err}");
            }
            let err = audit_theorems(&env, &["Trust.BVC.audit_test_on_propext"]).unwrap_err();
            assert!(err.contains("foundational"), "{err}");
        })
        .expect("kernel thread");
    }

    /// Every `Clean.BVC.bvf_*` lemma the reflection names is in
    /// [`REFLECTION_LEMMAS`], so a new splice cannot bypass the audit.
    #[test]
    fn reflection_lemmas_cover_every_spliced_bvf_lemma() {
        let source = include_str!("../verify_output_instantiate.rs");
        let mut cited: Vec<&str> = source
            .match_indices("\"Clean.BVC.bvf_")
            .map(|(i, _)| {
                let rest = &source[i + 1..];
                &rest[..rest.find('"').expect("closing quote")]
            })
            // A constant name, not a label that mentions one
            // (`"Clean.BVC.bvf_wrapper_id+congruence …"`).
            .filter(|lit| lit.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.'))
            .collect();
        cited.sort_unstable();
        cited.dedup();
        assert!(!cited.is_empty());
        for name in cited {
            assert!(REFLECTION_LEMMAS.contains(&name), "{name} is spliced but not audited");
        }
    }

    /// FNV-1a, so the pin below does not depend on std's unspecified hasher.
    fn fnv1a(s: &str) -> u64 {
        s.bytes()
            .fold(0xcbf2_9ce4_8422_2325, |h, b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3))
    }

    /// Byte-identity pin: the six statements and proofs, the per-obligation
    /// step terms (`canonical_step`, `core_len`, `bit_leaf`) and the label,
    /// rendered structurally (`Expr`'s `Debug` walks the whole term). Taken
    /// before the term helpers moved to `kterm`; FAILS if any of them changes.
    #[test]
    fn statements_proofs_steps_and_label_are_byte_pinned() {
        use std::fmt::Write as _;
        let mut s = String::new();
        for (name, ty, val) in theorems() {
            writeln!(s, "{name}\n{ty:?}\n{val:?}").unwrap();
        }
        let product = core_of(&mul(var("X0", 64), lit(3, 64), 64));
        let seven = core_of(&lit(7, 64));
        writeln!(s, "{:?}", canonical_step(&seven, &product)).unwrap();
        writeln!(s, "{:?}", canonical_step(&product, &seven)).unwrap();
        let w32 = core_of(&sub(mul(var("W0", 32), lit(7, 32), 32), lit(3, 32), 32));
        writeln!(s, "{:?}", core_len(&w32)).unwrap();
        let sum = core_of(&add(lit(7, 64), mul(var("X0", 64), lit(3, 64), 64), 64));
        writeln!(s, "{sum:?}\n{:?}", core_len(&sum)).unwrap();
        writeln!(s, "{:?}", bit_leaf("X0", 4)).unwrap();
        s.push_str(THEOREM_LABEL);
        assert_eq!((s.len(), fnv1a(&s)), (804_277, 5_210_529_916_593_216_094), "ADD_COMM_PIN");
    }

    /// The multiply's length needs a non-empty first operand: `bvMul nil b` is
    /// `nil`. The kernel rejects `len_bvMul` at an empty multiplicand.
    #[test]
    fn the_multiply_length_needs_a_non_empty_operand() {
        let b = kx::bits(3, 8);
        let goal = eq(nat(), bvlen(bvmul(kx::nil(), b.clone())), bvlen(b.clone()));
        // `bvLen nil = succ zero` has no proof; `Eq.refl` is not one.
        let forged = Expr::apps(
            Expr::const_str(names::LEN_BV_MUL),
            [kx::nil(), b.clone(), zero(), refl(nat(), succ(zero()))],
        );
        assert!(kernel_check(&[], forged, goal.clone()).is_err());
        assert!(kernel_check(&[], refl(nat(), bvlen(b)), goal).is_err());
    }
}
