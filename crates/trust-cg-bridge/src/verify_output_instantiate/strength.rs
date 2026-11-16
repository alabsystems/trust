// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Strength-reduced multiplies on the O(1) structured route: the rewrite
//! theorems `Trust.BVS.*`, the audited environment they live in, and the
//! per-obligation proof steps that splice them into a reflection.
//!
//! # What is missing without this
//!
//! trust-cg turns a multiply by a constant into shifts and adds
//! (`mul_shift_reduce`, `shift_alu_fuse`): `x * 3 + 7` is emitted as
//! `add x, x, x, lsl #1; add #7`, which the machine semantics render
//! `(x + 7) + (x << 1)`, while the source says `x * 3 + 7`. The two sides of
//! the gate's return equation then differ by an arithmetic identity, not by a
//! wrapper or an operand order, so neither the shared-core route nor the
//! add-commutation route (`add_comm`) proves it, and the function is graded
//! [VALIDATED].
//!
//! # What this module adds
//!
//! Four theorems over the pinned `Clean.BVC` / `Clean.BVI` definitions, each a
//! `Declaration::Theorem` whose proof the Clean kernel type-checks when it is
//! added (`V = bvToNat`, `L = bvLen`, `P = bvTwoPow`, `S = bvShl`,
//! `M = bvMul`, `A = addRecM`, `NOT = bvNot`, `ZX = bvZeroExt`,
//! `APP = bvAppend`):
//!
//! ```text
//! shl_mul     : ∀ x n c m, L x = succ m → L c = L x → V c = P (V n) →
//!                 S x n = M x c
//! shl_hi_out  : ∀ lo hi n, L hi = V n → S (ZX lo (L hi)) n = S (APP lo hi) n
//! collect_add : ∀ x y c1 c2 m, L x = succ m → L c1 = L x → L c2 = L x →
//!                 V c2 = succ (V c1) →
//!                 A (A x y false) (M x c1) false = A (M x c2) y false
//! collect_sub : ∀ x y c1 c2 m, L x = succ m → L c1 = L x → L c2 = L x →
//!                 V c1 = succ (V c2) →
//!                 A (A (M x c1) y false) (NOT x) true = A (M x c2) y false
//! ```
//!
//! Each proof goes through the values of both sides (`bv_value`): the value
//! and length laws of `natToBvAux`, `addRecM`, `bvMul`, `bvNot`, `bvAppend`
//! and `bvReplF`, the `%` lemmas, a ring rearrangement (`nat_ring`), and
//! finally `Trust.BVV.inj` (two lists of equal length and value are equal).
//! No Nat subtraction appears anywhere.
//!
//! - `shl_mul` is a shift by `a` as a multiply by `2^a`. `L x = succ m` is not
//!   needed for truth (both sides are `[]` at `x = []`), but `len_bvMul` needs
//!   it.
//! - `shl_hi_out` is the AArch64 `lsl #k` alias of UBFM, which the machine
//!   semantics render `Shl(ZeroExt(Extract(x, w-1-k, 0), k), k)`: the `k` high
//!   bits that the extract drops are shifted out anyway. `L hi = V n` carries
//!   the theorem; a general UBFIZ (zero-extension amount different from the
//!   shift) does not satisfy it.
//! - `collect_add` is `(x + y) + x * c1 = x * (c1 + 1) + y` (the `2^a + 1`
//!   form, addend first, as `mul_shift_reduce` folds it), and `collect_sub` is
//!   `(x * c1 + y) - x = x * (c1 - 1) + y` (the `2^a - 1` form). `y` needs no
//!   length premise: `addRecM` takes its length from its first operand.
//!
//! Deferred, and declined because no step builder matches them: `1 - 2^a`,
//! `x + (x << a)` and `(x << a) - x` with no addend, the `csel` and
//! late-addend orders, and source-level shifts (`Shl(l, And(r, w - 1))`, whose
//! amount is not a constant).
//!
//! # The audit
//!
//! [`strength_base`] is the commuting base (`add_comm::commuting_base`) plus
//! the value theory (`bv_value::register`) and the four theorems, built once
//! per process. Then every name in [`audited`] (every `Trust.BVC.*`,
//! `Trust.BVV.*` and `Trust.BVS.*` theorem, every `Clean.BVC.bvf_*` lemma the
//! reflection splices, and every prelude lemma any proof cites) must be a
//! `Theorem` that carries its proof and whose `axiom_deps` and
//! `foundational_axiom_deps` are both empty. Otherwise the memoized result is
//! `Err` and every route built on it declines for the life of the process.
//!
//! # Per-obligation steps and their guards
//!
//! [`shl_steps`], [`add_step`] and [`sub_step`] look at the CORES of a
//! reflected node's children and, when they match one of the shapes above,
//! return a [`Step`]: the new core and a proof
//! `bvfEval before = bvfEval core`, an instance of one theorem whose closed
//! premises (lengths and values of constants of at most 64 bits) the kernel
//! computes. Every constant is decoded from the `Const` list the kernel sees,
//! never from a Formula's integer. A step is offered only at width 32 or 64,
//! for a shift amount `1 ≤ a < w`, and only when the premise it needs holds
//! (`v1 + 1 < 2^w` for `collect_add`, `v1 ≥ 1` for `collect_sub`, the
//! zero-extension amount equal to the shift for `shl_hi_out`), so the kernel
//! is never handed an instance whose closed premise is false, and never
//! computes a power of two beyond `2^63`.
//!
//! # Authority
//!
//! Nothing here decides a grade. A step is a TERM; the caller splices it into
//! the discharge term and the kernel type-checks the whole term against the
//! goal built from the two original Formulas. A wrong match, constant or
//! length proof can only make that check fail.

use std::sync::OnceLock;

use clean_kernel::name::Name;
use clean_kernel::{
    BigNat, ConstantKind, Declaration, Environment, Expr, ExprKind, FVarId, Literal,
};

use super::add_comm::{self, audit_theorems, core_len};
use super::bv_value::{self, btn, names as bvv};
use super::kterm::{
    Fresh, addm, bool_ty, bv_append, bv_shl, bvlen, bvmul, eq, lams, lb, nadd, nat, nlit, nmod,
    nmul, pis, refl, repl_f, succ, symm, to_nat, trans, two_pow, zero_ext,
};
use super::kx;
use super::nat_ring::{Eqn, ring_eq};

/// The theorems this module proves.
pub(crate) mod names {
    pub(crate) const SHL_MUL: &str = "Trust.BVS.shl_mul";
    pub(crate) const SHL_HI_OUT: &str = "Trust.BVS.shl_hi_out";
    pub(crate) const COLLECT_ADD: &str = "Trust.BVS.collect_add";
    pub(crate) const COLLECT_SUB: &str = "Trust.BVS.collect_sub";
    pub(crate) const ALL: [&str; 4] = [SHL_MUL, SHL_HI_OUT, COLLECT_ADD, COLLECT_SUB];
}

/// The theorems the proofs here and the step terms cite besides
/// [`names::ALL`]. Each is also in `bv_value::audited` or `add_comm::names`;
/// listing them here keeps the audit of this module's own citations explicit
/// (test `every_citation_is_audited_and_nothing_computes_on_closed_data`).
pub(crate) const CITED: [&str; 20] = [
    bvv::INJ,
    bvv::LEN_NAT_TO_BV,
    bvv::TO_NAT_NAT_TO_BV,
    bvv::BV_MUL_VAL,
    bvv::ADD_REC_M_VAL,
    bvv::BV_NOT_VAL,
    bvv::MOD_ADD_MOD,
    bvv::ADD_MOD_MOD,
    bvv::ADD_MUL_MOD_SELF,
    bvv::TWO_POW_POS,
    bvv::TWO_POW_ADD,
    bvv::TO_NAT_APPEND,
    bvv::TO_NAT_REPL_F,
    bvv::LEN_APPEND,
    bvv::LEN_REPL_F,
    add_comm::names::LEN_BV_MUL,
    add_comm::names::LEN_ADD_REC_M,
    "congrArg",
    "Eq.trans",
    "Eq.symm",
];

/// The last part of the label of a function proved through this route.
pub(crate) const LABEL_TAIL: &str = "Clean.BVC congruence (O(1) add@N, strength-reduced multiply)";

/// At most this many rewrite steps per obligation (the caller counts).
pub(crate) const MAX_REWRITES: usize = 16;

/// The widths a step is offered at.
const WIDTHS: [u32; 2] = [32, 64];

/// No concrete list this module decodes is longer than this.
const MAX_BITS: usize = 64;

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

fn list_local(fr: &mut Fresh) -> ((FVarId, Expr), Expr) {
    let (id, v) = fr.local();
    ((id, lb()), v)
}

fn nat_local(fr: &mut Fresh) -> ((FVarId, Expr), Expr) {
    let (id, v) = fr.local();
    ((id, nat()), v)
}

/// A hypothesis `proof : lhs = rhs` as an equation.
fn hyp(lhs: Expr, rhs: Expr, proof: Expr) -> Eqn {
    Eqn { lhs, rhs, proof }
}

/// `inj xs ys hl hv : xs = ys`.
fn inj(xs: &Expr, ys: &Expr, hl: Eqn, hv: Eqn) -> Expr {
    cite(bvv::INJ, [xs.clone(), ys.clone(), hl.proof, hv.proof])
}

/// `L (M x c) = L x`, from `hx : L x = succ m` and `hc : L c = L x`.
fn len_mul(x: &Expr, c: &Expr, m: &Expr, hx: &Expr, hc: Eqn) -> Eqn {
    Eqn::cite(
        add_comm::names::LEN_BV_MUL,
        vec![x.clone(), c.clone(), m.clone(), hx.clone()],
        len(&bvmul(x.clone(), c.clone())),
        len(c),
    )
    .then(hc)
}

/// `V (A (M x c) y false) = (V x * V c + V y) % P (L x)`, the value of a
/// multiply-then-add whose multiplier has the multiplicand's length.
fn mul_add_val(fr: &mut Fresh, x: &Expr, c: &Expr, y: &Expr, m: &Expr, hx: &Expr, hc: Eqn) -> Eqn {
    let f = kx::bfalse();
    let mxc = bvmul(x.clone(), c.clone());
    let sum = addm(mxc.clone(), y.clone(), f.clone());
    let q = two_pow(len(x));
    let hq = cite(bvv::TWO_POW_POS, [len(x)]);
    let vy = val(y);
    let s0 = nadd(nadd(val(&mxc), vy.clone()), btn(f.clone()));
    let e1 = Eqn::cite(
        bvv::ADD_REC_M_VAL,
        vec![mxc.clone(), y.clone(), f.clone()],
        val(&sum),
        nmod(s0.clone(), two_pow(len(&mxc))),
    );
    let s0c = s0.clone();
    let e2 = len_mul(x, c, m, hx, hc.clone()).under(fr, |t| nmod(s0c.clone(), two_pow(t)));
    let z = nmul(val(x), val(c));
    let zc = z.clone();
    let mval = Eqn::cite(
        bvv::BV_MUL_VAL,
        vec![x.clone(), c.clone()],
        val(&mxc),
        nmod(z.clone(), two_pow(len(c))),
    )
    .then(hc.under(fr, |t| nmod(zc.clone(), two_pow(t))));
    let (vy1, f1, q1) = (vy.clone(), f.clone(), q.clone());
    let e3 = mval.under(fr, |t| nmod(nadd(nadd(t, vy1.clone()), btn(f1.clone())), q1.clone()));
    let zq = nmod(z.clone(), q.clone());
    let q2 = q.clone();
    // `btn false` is `0`, and `s + 0` is `s`.
    let e4 =
        Eqn::by_defeq(nadd(nadd(zq.clone(), vy.clone()), btn(f)), nadd(zq.clone(), vy.clone()))
            .under(fr, |t| nmod(t, q2.clone()));
    let e5 = Eqn::cite(
        bvv::MOD_ADD_MOD,
        vec![z.clone(), vy.clone(), q.clone(), hq],
        nmod(nadd(zq, vy.clone()), q.clone()),
        nmod(nadd(z, vy), q),
    );
    e1.then(e2).then(e3).then(e4).then(e5)
}

// ── the theorems ─────────────────────────────────────────────────────────────

/// `shl_mul : ∀ x n c m, L x = succ m → L c = L x → V c = P (V n) → S x n = M x c`.
///
/// Lengths: `L (S x n) = L x` (`len_natToBv`, `S` unfolds to `natToBvAux`)
/// and `L (M x c) = L c = L x` (`len_bvMul`, the premise). Values:
/// `V (S x n) = (V x * P (V n)) % P (L x) = (V x * V c) % P (L c) = V (M x c)`
/// (`toNat_natToBv`, the two premises, `bvMul_val`). Then `inj`.
fn shl_mul() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bx, x) = list_local(&mut fr);
    let (bn, n) = list_local(&mut fr);
    let (bc, c) = list_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (hx_id, hx) = fr.local();
    let (hc_id, hc) = fr.local();
    let (hv_id, hv) = fr.local();
    let (lx, lc) = (len(&x), len(&c));
    let (vx, vc) = (val(&x), val(&c));
    let pvn = two_pow(val(&n));
    let binders = vec![
        bx,
        bn,
        bc,
        bm,
        (hx_id, eq(nat(), lx.clone(), succ(m.clone()))),
        (hc_id, eq(nat(), lc.clone(), lx.clone())),
        (hv_id, eq(nat(), vc.clone(), pvn.clone())),
    ];
    let shl = bv_shl(x.clone(), n.clone());
    let mul = bvmul(x.clone(), c.clone());
    let ty = pis(binders.clone(), eq(lb(), shl.clone(), mul.clone()));
    let hc = hyp(lc.clone(), lx.clone(), hc);
    let prod = nmul(vx.clone(), pvn.clone());
    let hl = Eqn::cite(bvv::LEN_NAT_TO_BV, vec![lx.clone(), prod.clone()], len(&shl), lx.clone())
        .then(len_mul(&x, &c, &m, &hx, hc.clone()).symm());
    let (vx1, lx1) = (vx.clone(), lx.clone());
    let (vx2, vc2) = (vx.clone(), vc.clone());
    let product = nmul(vx.clone(), vc.clone());
    let hv = Eqn::cite(
        bvv::TO_NAT_NAT_TO_BV,
        vec![lx.clone(), prod.clone()],
        val(&shl),
        nmod(prod, two_pow(lx.clone())),
    )
    .then(
        hyp(vc.clone(), pvn, hv)
            .symm()
            .under(&mut fr, |t| nmod(nmul(vx1.clone(), t), two_pow(lx1.clone()))),
    )
    .then(hc.symm().under(&mut fr, |t| nmod(nmul(vx2.clone(), vc2.clone()), two_pow(t))))
    .then(
        Eqn::cite(
            bvv::BV_MUL_VAL,
            vec![x.clone(), c.clone()],
            val(&mul),
            nmod(product, two_pow(lc)),
        )
        .symm(),
    );
    Some((ty, lams(binders, inj(&shl, &mul, hl, hv))))
}

/// `shl_hi_out : ∀ lo hi n, L hi = V n → S (ZX lo (L hi)) n = S (APP lo hi) n`.
///
/// With `a = ZX lo (L hi)` (which unfolds to `lo ++ replF (L hi)`) and
/// `b = lo ++ hi`, both have length `L lo + L hi` (`len_append`,
/// `len_replF`), and `V a = V lo` (`toNat_append`, `toNat_replF`),
/// `V b = V lo + P (L lo) * V hi`. With `P (V n) = P (L hi)` (the premise) and
/// `P (L lo) * P (L hi) = P (L lo + L hi)` (`two_pow_add`), `V b * P (V n)`
/// is `V lo * P (L hi)` plus a multiple of the modulus `P (L lo + L hi)`,
/// which `add_mul_mod_self` drops. Then `inj`.
fn shl_hi_out() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (blo, lo) = list_local(&mut fr);
    let (bhi, hi) = list_local(&mut fr);
    let (bn, n) = list_local(&mut fr);
    let (h_id, h) = fr.local();
    let (llo, lhi) = (len(&lo), len(&hi));
    let (vlo, vhi, vn) = (val(&lo), val(&hi), val(&n));
    let binders = vec![blo, bhi, bn, (h_id, eq(nat(), lhi.clone(), vn.clone()))];
    let rf = repl_f(lhi.clone());
    let a = zero_ext(lo.clone(), lhi.clone());
    let b = bv_append(lo.clone(), hi.clone());
    let (sa, sb) = (bv_shl(a.clone(), n.clone()), bv_shl(b.clone(), n.clone()));
    let ty = pis(binders.clone(), eq(lb(), sa.clone(), sb.clone()));
    let pvn = two_pow(vn.clone());
    let s = nadd(llo.clone(), lhi.clone());
    let ps = two_pow(s.clone());
    let plo = two_pow(llo.clone());
    let plhi = two_pow(lhi.clone());
    let (la, lb_) = (len(&a), len(&b));

    // Lengths.
    let llo1 = llo.clone();
    let len_a = Eqn::cite(
        bvv::LEN_APPEND,
        vec![lo.clone(), rf.clone()],
        la.clone(),
        nadd(llo.clone(), len(&rf)),
    )
    .then(
        Eqn::cite(bvv::LEN_REPL_F, vec![lhi.clone()], len(&rf), lhi.clone())
            .under(&mut fr, |t| nadd(llo1.clone(), t)),
    );
    let len_b = Eqn::cite(bvv::LEN_APPEND, vec![lo.clone(), hi.clone()], lb_.clone(), s.clone());
    let pa = nmul(val(&a), pvn.clone());
    let pb = nmul(val(&b), pvn.clone());
    let hl = Eqn::cite(bvv::LEN_NAT_TO_BV, vec![la.clone(), pa.clone()], len(&sa), la.clone())
        .then(len_a.clone())
        .then(len_b.clone().symm())
        .then(
            Eqn::cite(bvv::LEN_NAT_TO_BV, vec![lb_.clone(), pb.clone()], len(&sb), lb_.clone())
                .symm(),
        );

    // V a = V lo.
    let (vlo1, plo1) = (vlo.clone(), plo.clone());
    let val_a = Eqn::cite(
        bvv::TO_NAT_APPEND,
        vec![lo.clone(), rf.clone()],
        val(&a),
        nadd(vlo.clone(), nmul(plo.clone(), val(&rf))),
    )
    .then(
        Eqn::cite(bvv::TO_NAT_REPL_F, vec![lhi.clone()], val(&rf), nlit(0))
            .under(&mut fr, |t| nadd(vlo1.clone(), nmul(plo1.clone(), t))),
    );
    let tidy = ring_eq(&mut fr, &val_a.rhs, &vlo)?;
    let val_a = val_a.then(tidy);
    // V n = L hi.
    let vn_lhi = hyp(lhi.clone(), vn, h).symm();
    let k = nmul(vlo.clone(), plhi.clone());

    // V (S a n) = (V lo * P (L hi)) % P (L lo + L hi).
    let (pvn1, la1, la2, vlo2, k1) = (pvn.clone(), la.clone(), la.clone(), vlo.clone(), k.clone());
    let left = Eqn::cite(
        bvv::TO_NAT_NAT_TO_BV,
        vec![la.clone(), pa.clone()],
        val(&sa),
        nmod(pa, two_pow(la.clone())),
    )
    .then(val_a.under(&mut fr, |t| nmod(nmul(t, pvn1.clone()), two_pow(la1.clone()))))
    .then(
        vn_lhi
            .clone()
            .under(&mut fr, |t| nmod(nmul(vlo2.clone(), two_pow(t)), two_pow(la2.clone()))),
    )
    .then(len_a.under(&mut fr, |t| nmod(k1.clone(), two_pow(t))));

    // V (S b n) = the same.
    let vb = nadd(vlo.clone(), nmul(plo.clone(), vhi.clone()));
    let inner = nmul(vb.clone(), plhi.clone());
    let split = nadd(k.clone(), nmul(nmul(plo.clone(), plhi.clone()), vhi.clone()));
    let (pvn2, lb1, lb2, vb1, inner1, ps1, ps2, k2, vhi1) = (
        pvn.clone(),
        lb_.clone(),
        lb_.clone(),
        vb.clone(),
        inner.clone(),
        ps.clone(),
        ps.clone(),
        k.clone(),
        vhi.clone(),
    );
    let ring = ring_eq(&mut fr, &inner, &split)?;
    let right = Eqn::cite(
        bvv::TO_NAT_NAT_TO_BV,
        vec![lb_.clone(), pb.clone()],
        val(&sb),
        nmod(pb, two_pow(lb_.clone())),
    )
    .then(
        Eqn::cite(bvv::TO_NAT_APPEND, vec![lo.clone(), hi.clone()], val(&b), vb.clone())
            .under(&mut fr, |t| nmod(nmul(t, pvn2.clone()), two_pow(lb1.clone()))),
    )
    .then(vn_lhi.under(&mut fr, |t| nmod(nmul(vb1.clone(), two_pow(t)), two_pow(lb2.clone()))))
    .then(len_b.under(&mut fr, |t| nmod(inner1.clone(), two_pow(t))))
    .then(ring.under(&mut fr, |t| nmod(t, ps1.clone())))
    .then(
        Eqn::cite(bvv::TWO_POW_ADD, vec![llo.clone(), lhi.clone()], ps.clone(), nmul(plo, plhi))
            .symm()
            .under(&mut fr, |t| nmod(nadd(k2.clone(), nmul(t, vhi1.clone())), ps2.clone())),
    )
    .then(Eqn::cite(
        bvv::ADD_MUL_MOD_SELF,
        vec![k.clone(), ps.clone(), vhi.clone(), cite(bvv::TWO_POW_POS, [s])],
        nmod(nadd(k.clone(), nmul(ps.clone(), vhi)), ps.clone()),
        nmod(k, ps),
    ));
    let hv = left.then(right.symm());
    Some((ty, lams(binders, inj(&sa, &sb, hl, hv))))
}

/// The binders shared by `collect_add` and `collect_sub`:
/// `x y c1 c2 : List Bool`, `m : Nat`, `hx : L x = succ m`,
/// `h1 : L c1 = L x`, `h2 : L c2 = L x`, and `hv : V big = succ (V small)`.
struct Collect {
    binders: Vec<(FVarId, Expr)>,
    x: Expr,
    y: Expr,
    c1: Expr,
    c2: Expr,
    m: Expr,
    hx: Expr,
    h1: Eqn,
    h2: Eqn,
    hv: Eqn,
}

/// `add`: `hv : V c2 = succ (V c1)`; otherwise `hv : V c1 = succ (V c2)`.
fn collect_binders(fr: &mut Fresh, add: bool) -> Collect {
    let (bx, x) = list_local(fr);
    let (by, y) = list_local(fr);
    let (bc1, c1) = list_local(fr);
    let (bc2, c2) = list_local(fr);
    let (bm, m) = nat_local(fr);
    let (hx_id, hx) = fr.local();
    let (h1_id, h1) = fr.local();
    let (h2_id, h2) = fr.local();
    let (hv_id, hv) = fr.local();
    let lx = len(&x);
    let (big, small) = if add { (&c2, &c1) } else { (&c1, &c2) };
    let hv = hyp(val(big), succ(val(small)), hv);
    let h1 = hyp(len(&c1), lx.clone(), h1);
    let h2 = hyp(len(&c2), lx.clone(), h2);
    let binders = vec![
        bx,
        by,
        bc1,
        bc2,
        bm,
        (hx_id, eq(nat(), lx, succ(m.clone()))),
        (h1_id, eq(nat(), h1.lhs.clone(), h1.rhs.clone())),
        (h2_id, eq(nat(), h2.lhs.clone(), h2.rhs.clone())),
        (hv_id, eq(nat(), hv.lhs.clone(), hv.rhs.clone())),
    ];
    Collect { binders, x, y, c1, c2, m, hx, h1, h2, hv }
}

/// `collect_add : ∀ x y c1 c2 m, L x = succ m → L c1 = L x → L c2 = L x →
/// V c2 = succ (V c1) → A (A x y false) (M x c1) false = A (M x c2) y false`.
///
/// Both lengths are `L x` (`len_addRecM`, `len_bvMul`). Both values reduce,
/// modulo `Q = P (L x)`, to `(V x + V y + V x * V c1) % Q`: the left by
/// `addRecM_val` twice, `bvMul_val` and `mod_add_mod` / `add_mod_mod` to drop
/// the inner remainders; the right by `mul_add_val`, the premise
/// `V c2 = succ (V c1)` and a ring step. Then `inj`.
fn collect_add() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let Collect { binders, x, y, c1, c2, m, hx, h1, h2, hv } = collect_binders(&mut fr, true);
    let f = kx::bfalse();
    let ax = addm(x.clone(), y.clone(), f.clone());
    let mx1 = bvmul(x.clone(), c1.clone());
    let mx2 = bvmul(x.clone(), c2.clone());
    let lhs = addm(ax.clone(), mx1.clone(), f.clone());
    let rhs = addm(mx2.clone(), y.clone(), f.clone());
    let ty = pis(binders.clone(), eq(lb(), lhs.clone(), rhs.clone()));
    let lx = len(&x);
    let q = two_pow(lx.clone());
    let hq = cite(bvv::TWO_POW_POS, [lx.clone()]);
    let (vx, vy, vc1) = (val(&x), val(&y), val(&c1));

    // Lengths.
    let len_ax = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![x.clone(), y.clone(), f.clone()],
        len(&ax),
        lx,
    );
    let l_lhs = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![ax.clone(), mx1.clone(), f.clone()],
        len(&lhs),
        len(&ax),
    )
    .then(len_ax.clone());
    let l_rhs = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![mx2.clone(), y.clone(), f.clone()],
        len(&rhs),
        len(&mx2),
    )
    .then(len_mul(&x, &c2, &m, &hx, h2.clone()));
    let hl = l_lhs.then(l_rhs.symm());

    // V lhs = (V x + V y + V x * V c1) % Q.
    let s0 = nadd(nadd(val(&ax), val(&mx1)), btn(f.clone()));
    let big_x = nadd(nadd(vx.clone(), vy.clone()), btn(f.clone()));
    let big_y = nmul(vx.clone(), vc1.clone());
    let (xq, yq) = (nmod(big_x.clone(), q.clone()), nmod(big_y.clone(), q.clone()));
    let s0c = s0.clone();
    let (vm1, f1, q1) = (val(&mx1), f.clone(), q.clone());
    let (xq1, f2, q2) = (xq.clone(), f.clone(), q.clone());
    let big_y1 = big_y.clone();
    let (q3, q4, big_y2, q5) = (q.clone(), q.clone(), big_y.clone(), q.clone());
    let left = Eqn::cite(
        bvv::ADD_REC_M_VAL,
        vec![ax.clone(), mx1.clone(), f.clone()],
        val(&lhs),
        nmod(s0, two_pow(len(&ax))),
    )
    .then(len_ax.under(&mut fr, |t| nmod(s0c.clone(), two_pow(t))))
    .then(
        Eqn::cite(bvv::ADD_REC_M_VAL, vec![x.clone(), y.clone(), f.clone()], val(&ax), xq.clone())
            .under(&mut fr, |t| nmod(nadd(nadd(t, vm1.clone()), btn(f1.clone())), q1.clone())),
    )
    .then(
        Eqn::cite(
            bvv::BV_MUL_VAL,
            vec![x.clone(), c1.clone()],
            val(&mx1),
            nmod(big_y.clone(), two_pow(len(&c1))),
        )
        .then(h1.under(&mut fr, |t| nmod(big_y1.clone(), two_pow(t))))
        .under(&mut fr, |t| nmod(nadd(nadd(xq1.clone(), t), btn(f2.clone())), q2.clone())),
    )
    .then(
        Eqn::by_defeq(
            nadd(nadd(xq.clone(), yq.clone()), btn(f.clone())),
            nadd(xq.clone(), yq.clone()),
        )
        .under(&mut fr, |t| nmod(t, q3.clone())),
    )
    .then(Eqn::cite(
        bvv::MOD_ADD_MOD,
        vec![big_x.clone(), yq.clone(), q.clone(), hq.clone()],
        nmod(nadd(xq, yq.clone()), q.clone()),
        nmod(nadd(big_x.clone(), yq.clone()), q.clone()),
    ))
    .then(Eqn::cite(
        bvv::ADD_MOD_MOD,
        vec![big_x.clone(), big_y.clone(), q.clone(), hq],
        nmod(nadd(big_x.clone(), yq), q.clone()),
        nmod(nadd(big_x.clone(), big_y.clone()), q.clone()),
    ))
    .then(
        Eqn::by_defeq(big_x, nadd(vx.clone(), vy.clone()))
            .under(&mut fr, |t| nmod(nadd(t, big_y2.clone()), q4.clone())),
    );

    // V rhs = the same.
    let (vx1, vy1, q6) = (vx.clone(), vy.clone(), q.clone());
    let ring = ring_eq(
        &mut fr,
        &nadd(nmul(vx.clone(), succ(vc1.clone())), vy.clone()),
        &nadd(nadd(vx.clone(), vy.clone()), big_y),
    )?;
    let right = mul_add_val(&mut fr, &x, &c2, &y, &m, &hx, h2)
        .then(hv.under(&mut fr, |t| nmod(nadd(nmul(vx1.clone(), t), vy1.clone()), q6.clone())))
        .then(ring.under(&mut fr, |t| nmod(t, q5.clone())));
    let hv = left.then(right.symm());
    Some((ty, lams(binders, inj(&lhs, &rhs, hl, hv))))
}

/// `collect_sub : ∀ x y c1 c2 m, L x = succ m → L c1 = L x → L c2 = L x →
/// V c1 = succ (V c2) →
/// A (A (M x c1) y false) (NOT x) true = A (M x c2) y false`.
///
/// Both lengths are `L x`. With `Q = P (L x)`, `I = V x * V c1 + V y` and
/// `J = V x * V c2 + V y`: the left value is `(I % Q + V (NOT x) + 1) % Q`
/// (`addRecM_val`, `mul_add_val`), which is `(I + V (NOT x) + 1) % Q`
/// (`mod_add_mod`); with the premise and a ring step that is
/// `(J + (V (NOT x) + V x + 1)) % Q = (J + Q * 1) % Q` (`bvNot_val`), which is
/// `J % Q` (`add_mul_mod_self`), the right value (`mul_add_val`). Then `inj`.
fn collect_sub() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let Collect { binders, x, y, c1, c2, m, hx, h1, h2, hv } = collect_binders(&mut fr, false);
    let (f, t) = (kx::bfalse(), kx::btrue());
    let mx1 = bvmul(x.clone(), c1.clone());
    let mx2 = bvmul(x.clone(), c2.clone());
    let inner = addm(mx1.clone(), y.clone(), f.clone());
    let nx = kx::bv_not(x.clone());
    let lhs = addm(inner.clone(), nx.clone(), t.clone());
    let rhs = addm(mx2.clone(), y.clone(), f.clone());
    let ty = pis(binders.clone(), eq(lb(), lhs.clone(), rhs.clone()));
    let lx = len(&x);
    let q = two_pow(lx.clone());
    let hq = cite(bvv::TWO_POW_POS, [lx.clone()]);
    let (vx, vy, vc2, vnx) = (val(&x), val(&y), val(&c2), val(&nx));
    let one = || nlit(1);

    // Lengths.
    let l_inner = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![mx1.clone(), y.clone(), f.clone()],
        len(&inner),
        len(&mx1),
    )
    .then(len_mul(&x, &c1, &m, &hx, h1.clone()));
    let l_lhs = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![inner.clone(), nx.clone(), t.clone()],
        len(&lhs),
        len(&inner),
    )
    .then(l_inner.clone());
    let l_rhs = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![mx2.clone(), y.clone(), f.clone()],
        len(&rhs),
        len(&mx2),
    )
    .then(len_mul(&x, &c2, &m, &hx, h2.clone()));
    let hl = l_lhs.then(l_rhs.symm());

    // V lhs = J % Q.
    let s0 = nadd(nadd(val(&inner), vnx.clone()), btn(t.clone()));
    let big_i = nadd(nmul(vx.clone(), val(&c1)), vy.clone());
    let iq = nmod(big_i.clone(), q.clone());
    let big_j = nadd(nmul(vx.clone(), vc2.clone()), vy.clone());
    let not_one = nadd(vnx.clone(), one());
    let s0c = s0.clone();
    let (vnx1, t1, q1) = (vnx.clone(), t.clone(), q.clone());
    let (q2, q3, q4, q5, q6, q7) =
        (q.clone(), q.clone(), q.clone(), q.clone(), q.clone(), q.clone());
    let (vx1, vy1, not_one1, big_j1) = (vx.clone(), vy.clone(), not_one.clone(), big_j.clone());
    let r1 = ring_eq(
        &mut fr,
        &nadd(nadd(iq.clone(), vnx.clone()), one()),
        &nadd(iq.clone(), not_one.clone()),
    )?;
    let r2 = ring_eq(
        &mut fr,
        &nadd(nadd(nmul(vx.clone(), succ(vc2.clone())), vy.clone()), not_one.clone()),
        &nadd(big_j.clone(), nadd(nadd(vnx.clone(), vx.clone()), one())),
    )?;
    let r3 = ring_eq(
        &mut fr,
        &nadd(big_j.clone(), q.clone()),
        &nadd(big_j.clone(), nmul(q.clone(), one())),
    )?;
    let in_val = mul_add_val(&mut fr, &x, &c1, &y, &m, &hx, h1);
    let left = Eqn::cite(
        bvv::ADD_REC_M_VAL,
        vec![inner.clone(), nx.clone(), t.clone()],
        val(&lhs),
        nmod(s0, two_pow(len(&inner))),
    )
    .then(l_inner.under(&mut fr, |u| nmod(s0c.clone(), two_pow(u))))
    .then(in_val.under(&mut fr, |u| nmod(nadd(nadd(u, vnx1.clone()), btn(t1.clone())), q1.clone())))
    // `btn true` is `1`.
    .then(
        Eqn::by_defeq(
            nadd(nadd(iq.clone(), vnx.clone()), btn(t.clone())),
            nadd(nadd(iq.clone(), vnx.clone()), one()),
        )
        .under(&mut fr, |u| nmod(u, q2.clone())),
    )
    .then(r1.under(&mut fr, |u| nmod(u, q3.clone())))
    .then(Eqn::cite(
        bvv::MOD_ADD_MOD,
        vec![big_i.clone(), not_one.clone(), q.clone(), hq.clone()],
        nmod(nadd(iq, not_one.clone()), q.clone()),
        nmod(nadd(big_i, not_one.clone()), q.clone()),
    ))
    .then(hv.under(&mut fr, |u| {
        nmod(nadd(nadd(nmul(vx1.clone(), u), vy1.clone()), not_one1.clone()), q4.clone())
    }))
    .then(r2.under(&mut fr, |u| nmod(u, q5.clone())))
    .then(
        Eqn::cite(
            bvv::BV_NOT_VAL,
            vec![x.clone()],
            nadd(nadd(vnx.clone(), vx.clone()), one()),
            q.clone(),
        )
        .under(&mut fr, |u| nmod(nadd(big_j1.clone(), u), q6.clone())),
    )
    .then(r3.under(&mut fr, |u| nmod(u, q7.clone())))
    .then(Eqn::cite(
        bvv::ADD_MUL_MOD_SELF,
        vec![big_j.clone(), q.clone(), one(), hq],
        nmod(nadd(big_j.clone(), nmul(q.clone(), one())), q.clone()),
        nmod(big_j, q),
    ));

    // V rhs = J % Q.
    let right = mul_add_val(&mut fr, &x, &c2, &y, &m, &hx, h2);
    let hv = left.then(right.symm());
    Some((ty, lams(binders, inj(&lhs, &rhs, hl, hv))))
}

// ── registration and the audited environment ─────────────────────────────────

/// The theorems in dependency order: `(name, statement, proof)`. `Err` names
/// a builder whose normaliser step declined, which is a bug here, never a
/// reason to admit anything.
pub(crate) fn theorems() -> Result<Vec<(&'static str, Expr, Expr)>, String> {
    let builders: [(&'static str, fn() -> Option<(Expr, Expr)>); 4] = [
        (names::SHL_MUL, shl_mul),
        (names::SHL_HI_OUT, shl_hi_out),
        (names::COLLECT_ADD, collect_add),
        (names::COLLECT_SUB, collect_sub),
    ];
    builders
        .into_iter()
        .map(|(name, build)| {
            let (ty, val) =
                build().ok_or_else(|| format!("{name}: the normaliser declined a step"))?;
            Ok((name, ty, val))
        })
        .collect()
}

/// Add the theorems to `env`, which must already carry the value theory
/// (`bv_value::register`). Each is a `Declaration::Theorem`, so `add_decl`
/// type-checks its proof against its statement.
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

/// Every name the strength environment audits: the commuting theorems and the
/// reflection lemmas (`add_comm`), the value theory with its normaliser
/// helpers and prelude citations (`bv_value::audited`), this module's
/// theorems, and its citations.
pub(crate) fn audited() -> Vec<&'static str> {
    let mut all: Vec<&'static str> = add_comm::names::ALL.to_vec();
    all.extend(add_comm::REFLECTION_LEMMAS);
    all.extend(bv_value::audited());
    all.extend(names::ALL);
    all.extend(CITED);
    all
}

/// `base` plus the value theory and the four theorems, audited. Split from
/// [`strength_base`] so a test can hand it a doctored base.
fn build_base(mut env: Environment) -> Result<Environment, String> {
    bv_value::register(&mut env)?;
    register(&mut env)?;
    audit_theorems(&env, &audited())?;
    Ok(env)
}

/// The commuting base plus the value theory and the strength theorems, built
/// and audited once per process. `Err` (a theorem did not register, or the
/// audit of [`audited`] failed) is kept for the life of the process, and the
/// route built on it declines. A panic inside the build is kept as `Err` too,
/// so a broken builder is not re-run by every later obligation. Call it on a
/// kernel re-check thread (the build type-checks deep terms).
pub(crate) fn strength_base() -> Result<&'static Environment, String> {
    static BASE: OnceLock<Result<Environment, String>> = OnceLock::new();
    BASE.get_or_init(|| {
        std::panic::catch_unwind(|| build_base(add_comm::commuting_base()?.clone()))
            .unwrap_or_else(|_| Err("the strength base build panicked".to_string()))
    })
    .as_ref()
    .map_err(Clone::clone)
}

/// The environment a strength discharge is checked in: [`strength_base`] and
/// one opaque `Bool` per bit of each variable (`add_comm::bit_leaf`).
pub(crate) fn strength_env(leaves: &[(String, u32)]) -> Result<Environment, String> {
    let mut env = strength_base()?.clone();
    add_comm::add_leaf_bits(&mut env, leaves);
    Ok(env)
}

/// The name a strength obligation is declared under in its own per-obligation
/// environment ([`admit_obligation`]). Never in [`strength_base`].
pub(crate) const OBLIGATION: &str = "Trust.BVS.obligation";

/// Check `discharge : goal` in `env` and admit it only when everything it
/// rests on is audited. The pair is declared as the `Declaration::Theorem`
/// [`OBLIGATION`], so `add_decl` type-checks the proof against the goal (the
/// kernel check that grants the grade). Then the TRANSITIVE axiom closure of
/// that theorem (through every theorem, definition and axiom it reaches, as
/// `Environment::axiom_deps` walks it) must hold only the per-bit
/// `BVC_LEAFBIT_*` constants of type `Bool` that state the obligation, and
/// its foundational closure must be empty. So a theorem the term cites that
/// itself rests on an axiom, or a Prop-valued definition that does, is
/// refused here even if the base audit missed it. `Err` says why.
pub(crate) fn admit_obligation(
    env: &mut Environment,
    goal: Expr,
    discharge: Expr,
) -> Result<(), String> {
    let name = Name::from_string(OBLIGATION);
    env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: goal,
        value: discharge,
    })
    .map_err(|e| format!("kernel: {e:?}"))?;
    let domain = env.axiom_deps(&name).ok_or("obligation: no closure")?;
    let mut foreign: Vec<String> = domain
        .iter()
        .filter(|c| {
            !(c.to_string().starts_with("BVC_LEAFBIT_")
                && env.get_const(c).is_some_and(|info| {
                    info.kind == ConstantKind::Axiom && info.type_ == bool_ty()
                }))
        })
        .map(ToString::to_string)
        .collect();
    foreign.sort();
    if !foreign.is_empty() {
        return Err(format!("obligation reaches axioms {foreign:?}"));
    }
    let foundational = env.foundational_axiom_deps(&name).ok_or("obligation: no closure")?;
    if !foundational.is_empty() {
        return Err(format!("obligation reaches foundational axioms {foundational:?}"));
    }
    Ok(())
}

/// The label of a function proved through this route: the strength theorems
/// used (in first-use order, each once), `Trust.BVC.addRecM_comm` only when an
/// `Add` was reordered, then [`LABEL_TAIL`].
pub(crate) fn label(used: &[&'static str], add_swaps: usize) -> String {
    let mut parts: Vec<&str> = Vec::new();
    for name in used {
        debug_assert!(names::ALL.contains(name), "{name} is not a strength theorem");
        if !parts.contains(name) {
            parts.push(name);
        }
    }
    if add_swaps > 0 {
        parts.push(add_comm::names::ADD_REC_M_COMM);
    }
    parts.push(LABEL_TAIL);
    parts.join("+")
}

// ── per-obligation steps ──────────────────────────────────────────────────────

/// One rewrite of a reflected core: `proof : bvfEval before = bvfEval core`,
/// an instance of `theorem`.
#[derive(Clone, Debug)]
pub(crate) struct Step {
    pub(crate) theorem: &'static str,
    pub(crate) before: Expr,
    pub(crate) core: Expr,
    pub(crate) proof: Expr,
}

impl Step {
    /// From `proof : bvfEval bvf = bvfEval self.before`, a proof of
    /// `bvfEval bvf = bvfEval self.core`.
    pub(crate) fn chain(&self, bvf: &Expr, proof: Expr) -> Expr {
        kx::eq_trans_list(
            kx::evalf(bvf.clone()),
            kx::evalf(self.before.clone()),
            kx::evalf(self.core.clone()),
            proof,
            self.proof.clone(),
        )
    }
}

/// The arguments of `e` when it is `head` applied to exactly `arity` of them.
fn app_of<'a>(e: &'a Expr, head: &str, arity: usize) -> Option<Vec<&'a Expr>> {
    match e.get_app_fn().kind() {
        ExprKind::Const(name, _) if *name == Name::from_string(head) => {}
        _ => return None,
    }
    let args = e.get_app_args();
    (args.len() == arity).then(|| args.to_vec())
}

/// The elements of a concrete cons list, `None` when it is not one or is
/// longer than [`MAX_BITS`].
fn spine_elems(mut e: &Expr) -> Option<Vec<Expr>> {
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

/// The bits of a concrete list of `Bool.true` / `Bool.false`, least
/// significant first, as the kernel reads them.
fn spine_bits(e: &Expr) -> Option<Vec<bool>> {
    let (t, f) = (Name::from_string("Bool.true"), Name::from_string("Bool.false"));
    spine_elems(e)?
        .iter()
        .map(|b| match b.kind() {
            ExprKind::Const(n, _) if *n == t => Some(true),
            ExprKind::Const(n, _) if *n == f => Some(false),
            _ => None,
        })
        .collect()
}

/// The value of at most 64 bits, least significant first.
fn bits_value(bits: &[bool]) -> u128 {
    bits.iter().rev().fold(0u128, |acc, &b| (acc << 1) | u128::from(b))
}

/// `(width, value)` of a `BvF.Const` over a concrete bit list.
fn const_value(e: &Expr) -> Option<(u32, u128)> {
    let list = app_of(e, "Clean.BVC.BvF.Const", 1)?;
    let bits = spine_bits(list[0])?;
    Some((u32::try_from(bits.len()).ok()?, bits_value(&bits)))
}

/// The value of a `Nat.succ` chain ending in `Nat.zero`, or of a small
/// literal, when it is at most [`MAX_BITS`].
fn nat_value(mut e: &Expr) -> Option<u32> {
    let mut n = 0u32;
    loop {
        if let ExprKind::Lit(Literal::Nat(BigNat::Small(v))) = e.kind() {
            let total = u64::from(n).checked_add(*v)?;
            return (total <= MAX_BITS as u64).then(|| total as u32);
        }
        if app_of(e, "Nat.zero", 0).is_some() {
            return Some(n);
        }
        let args = app_of(e, "Nat.succ", 1)?;
        if n as usize == MAX_BITS {
            return None;
        }
        n += 1;
        e = args[0];
    }
}

/// The concrete list `bvfEval x` computes to, for `Leaf l`, `Const l`, or
/// `ExtractLow (Leaf l | Const l) (Const tag)` with `L tag ≤ L l`.
fn concrete_value(x: &Expr) -> Option<Vec<Expr>> {
    let leaf = |e: &Expr| {
        app_of(e, "Clean.BVC.BvF.Leaf", 1)
            .or_else(|| app_of(e, "Clean.BVC.BvF.Const", 1))
            .and_then(|a| spine_elems(a[0]))
    };
    if let Some(elems) = leaf(x) {
        return Some(elems);
    }
    let args = app_of(x, "Clean.BVC.BvF.ExtractLow", 2)?;
    let elems = leaf(args[0])?;
    let tag = app_of(args[1], "Clean.BVC.BvF.Const", 1)?;
    let n = spine_elems(tag[0])?.len();
    (n <= elems.len()).then(|| elems[..n].to_vec())
}

/// A concrete cons list of `elems`.
fn list_of(elems: &[Expr]) -> Expr {
    elems.iter().rev().fold(kx::nil(), |acc, b| kx::cons(b.clone(), acc))
}

/// `(p, w)` with `p : bvLen (bvfEval x) = w`, for `w` in [`WIDTHS`].
fn width_of(x: &Expr) -> Option<(Expr, u32)> {
    core_len(x).filter(|(_, w)| WIDTHS.contains(w))
}

/// `bvLen c = bvLen (bvfEval x)` for a concrete `c` of `w` elements, from
/// `p : bvLen (bvfEval x) = w`. The kernel computes `bvLen c`.
fn same_len(c: &Expr, x: &Expr, w: u32, p: &Expr) -> Expr {
    let (wn, ex) = (kx::nat_lit(w), kx::evalf(x.clone()));
    trans(
        nat(),
        len(c),
        wn.clone(),
        len(&ex),
        refl(nat(), wn.clone()),
        symm(nat(), len(&ex), wn, p.clone()),
    )
}

/// `shl_hi_out` at a `Shl` node whose children's cores are
/// `l = ZeroExt (ExtractLow x (Const T)) K` and `r = Const n`: the AArch64
/// `lsl #K` alias, rewritten to `Shl x (Const n)`.
///
/// Offered only when `x` computes to a concrete list of `w ∈ {32, 64}` bits,
/// `L T + K = w`, `1 ≤ K < w`, `n` has `w` bits and its value is `K`. A
/// general UBFIZ (zero-extension amount different from the shift) declines.
pub(crate) fn shl_hi_out_step(l: &Expr, r: &Expr) -> Option<Step> {
    let zext = app_of(l, "Clean.BVC.BvF.ZeroExt", 2)?;
    let k = nat_value(zext[1])?;
    let extract = app_of(zext[0], "Clean.BVC.BvF.ExtractLow", 2)?;
    let x = extract[0];
    let tag = app_of(extract[1], "Clean.BVC.BvF.Const", 1)?;
    let t = u32::try_from(spine_elems(tag[0])?.len()).ok()?;
    let n = app_of(r, "Clean.BVC.BvF.Const", 1)?[0];
    let (nw, nv) = const_value(r)?;
    let elems = concrete_value(x)?;
    let w = u32::try_from(elems.len()).ok()?;
    let fits = WIDTHS.contains(&w) && t + k == w && 1 <= k && k < w;
    if !fits || nw != w || nv != u128::from(k) {
        return None;
    }
    let split = (w - k) as usize;
    let (lo, hi) = (list_of(&elems[..split]), list_of(&elems[split..]));
    // `L hi = V n`: both compute to `K`.
    let h = refl(nat(), len(&hi));
    Some(Step {
        theorem: names::SHL_HI_OUT,
        before: kx::shl(l.clone(), r.clone()),
        core: kx::shl(x.clone(), r.clone()),
        proof: cite(names::SHL_HI_OUT, [lo, hi, n.clone(), h]),
    })
}

/// `shl_mul` at a `Shl` node whose children's cores are `l = x` (of provable
/// length `w ∈ {32, 64}`) and `r = Const n` with `n` of `w` bits and value
/// `1 ≤ a < w`: rewritten to `Mul x (Const (2^a))`.
pub(crate) fn shl_mul_step(l: &Expr, r: &Expr) -> Option<Step> {
    let n = app_of(r, "Clean.BVC.BvF.Const", 1)?[0];
    let (nw, a) = const_value(r)?;
    let (p, w) = width_of(l)?;
    if nw != w || a < 1 || a >= u128::from(w) {
        return None;
    }
    let c = kx::bits(1i128 << a, w);
    let x = kx::evalf(l.clone());
    // `V c = P (V n)`: both compute to `2^a`.
    let hv = refl(nat(), val(&c));
    let hc = same_len(&c, l, w, &p);
    Some(Step {
        theorem: names::SHL_MUL,
        before: kx::shl(l.clone(), r.clone()),
        core: kx::mul(l.clone(), kx::const_(c.clone())),
        proof: cite(names::SHL_MUL, [x, n.clone(), c, kx::nat_lit(w - 1), p, hc, hv]),
    })
}

/// The shift rewrites at a `Shl` node with children's cores `l` and `r`, in
/// order: `shl_hi_out` when it applies, then `shl_mul` on the result. Each
/// step's `before` is the previous step's `core` (the first's is `Shl l r`).
pub(crate) fn shl_steps(l: &Expr, r: &Expr) -> Vec<Step> {
    let mut steps = Vec::new();
    let mut left = l.clone();
    if let Some(s) = shl_hi_out_step(l, r) {
        // `shl_hi_out_step` builds a `Shl` core; any other shape declines every step.
        let Some(args) = app_of(&s.core, "Clean.BVC.BvF.Shl", 2) else {
            return Vec::new();
        };
        left = args[0].clone();
        steps.push(s);
    }
    if let Some(s) = shl_mul_step(&left, r) {
        steps.push(s);
    }
    steps
}

/// `collect_add` at an `Add` node whose children's cores are
/// `l = Add x y` and `r = Mul x (Const c1)` (the same `x`, structurally), with
/// `x` of provable length `w ∈ {32, 64}`, `c1` of `w` bits and
/// `V c1 + 1 < 2^w`: rewritten to `Add (Mul x (Const (c1 + 1))) y`.
pub(crate) fn add_step(l: &Expr, r: &Expr) -> Option<Step> {
    let xy = app_of(l, "Clean.BVC.BvF.Add", 2)?;
    let (x, y) = (xy[0], xy[1]);
    let xc = app_of(r, "Clean.BVC.BvF.Mul", 2)?;
    if xc[0] != x {
        return None;
    }
    let c1 = app_of(xc[1], "Clean.BVC.BvF.Const", 1)?[0];
    let (cw, v1) = const_value(xc[1])?;
    let (p, w) = width_of(x)?;
    if cw != w || v1 + 1 >= 1u128 << w {
        return None;
    }
    let c2 = kx::bits(i128::try_from(v1 + 1).ok()?, w);
    // `V c2 = succ (V c1)`: both compute to `v1 + 1`.
    let hv = refl(nat(), val(&c2));
    let proof = cite(
        names::COLLECT_ADD,
        [
            kx::evalf(x.clone()),
            kx::evalf(y.clone()),
            c1.clone(),
            c2.clone(),
            kx::nat_lit(w - 1),
            p.clone(),
            same_len(c1, x, w, &p),
            same_len(&c2, x, w, &p),
            hv,
        ],
    );
    Some(Step {
        theorem: names::COLLECT_ADD,
        before: kx::add(l.clone(), r.clone()),
        core: kx::add(kx::mul(x.clone(), kx::const_(c2)), y.clone()),
        proof,
    })
}

/// `collect_sub` at a `Sub` node whose children's cores are
/// `l = Add (Mul x (Const c1)) y` and `r = x` (structurally), with `x` of
/// provable length `w ∈ {32, 64}`, `c1` of `w` bits and `V c1 ≥ 1`:
/// rewritten to `Add (Mul x (Const (c1 - 1))) y`.
pub(crate) fn sub_step(l: &Expr, r: &Expr) -> Option<Step> {
    let my = app_of(l, "Clean.BVC.BvF.Add", 2)?;
    let (mxc, y) = (my[0], my[1]);
    let xc = app_of(mxc, "Clean.BVC.BvF.Mul", 2)?;
    let x = xc[0];
    if x != r {
        return None;
    }
    let c1 = app_of(xc[1], "Clean.BVC.BvF.Const", 1)?[0];
    let (cw, v1) = const_value(xc[1])?;
    let (p, w) = width_of(x)?;
    if cw != w || v1 < 1 {
        return None;
    }
    let c2 = kx::bits(i128::try_from(v1 - 1).ok()?, w);
    // `V c1 = succ (V c2)`: both compute to `v1`.
    let hv = refl(nat(), val(c1));
    let proof = cite(
        names::COLLECT_SUB,
        [
            kx::evalf(x.clone()),
            kx::evalf(y.clone()),
            c1.clone(),
            c2.clone(),
            kx::nat_lit(w - 1),
            p.clone(),
            same_len(c1, x, w, &p),
            same_len(&c2, x, w, &p),
            hv,
        ],
    );
    Some(Step {
        theorem: names::COLLECT_SUB,
        before: kx::sub(l.clone(), r.clone()),
        core: kx::add(kx::mul(x.clone(), kx::const_(c2)), y.clone()),
        proof,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::sync::mpsc;
    use std::time::{Duration, Instant};

    use clean_kernel::TypeChecker;
    use clean_kernel::expr::UsedConstants;
    use trust_types::{Formula, Sort};

    use super::super::{ReflectCtx, reflect_formula, run_recheck_thread};
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
    fn shl(l: Formula, r: Formula, w: u32) -> Formula {
        Formula::BvShl(Box::new(l), Box::new(r), w)
    }
    fn low(x: Formula, high: u32) -> Formula {
        Formula::BvExtract { inner: Box::new(x), high, low: 0 }
    }

    /// The commuting-mode reflection of `f` (variables as concrete bit lists).
    fn reflect(f: &Formula) -> super::super::Reflected {
        reflect_formula(f, &mut ReflectCtx::commuting()).expect("in fragment")
    }
    fn core(f: &Formula) -> Expr {
        reflect(f).core
    }
    fn owned(leaves: &[(&str, u32)]) -> Vec<(String, u32)> {
        leaves.iter().map(|(n, w)| ((*n).to_string(), *w)).collect()
    }

    /// The kernel's verdict on `val : ty` in the strength environment.
    fn kernel_check(leaves: &[(&str, u32)], val: Expr, ty: Expr) -> Result<(), String> {
        let leaves = owned(leaves);
        run_recheck_thread("strength-test", move || {
            let env = strength_env(&leaves)?;
            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.check_type(&val, &ty).map_err(|e| format!("{e:?}"))
        })
        .map_err(|e| e.to_string())?
    }

    /// [`kernel_check`] under a watchdog: PANICS if the kernel has not
    /// answered within `limit`. The memoized base is built first, outside
    /// the limit, so the limit bounds the check alone.
    fn kernel_check_bounded(
        what: &str,
        leaves: &[(&str, u32)],
        val: Expr,
        ty: Expr,
    ) -> Result<(), String> {
        const LIMIT: Duration = Duration::from_secs(180);
        run_recheck_thread("strength-warm", || strength_base().map(|_| ()))
            .expect("kernel thread")
            .expect("the strength base builds");
        let leaves: Vec<(&'static str, u32)> =
            leaves.iter().map(|(n, w)| (&*String::leak((*n).to_string()), *w)).collect();
        let (tx, rx) = mpsc::channel();
        let start = Instant::now();
        std::thread::spawn(move || {
            let _ = tx.send(kernel_check(&leaves, val, ty));
        });
        let verdict = rx
            .recv_timeout(LIMIT)
            .unwrap_or_else(|_| panic!("{what}: the kernel ran past the {LIMIT:?} watchdog"));
        let shown = verdict.as_ref().err().map(|e| e.chars().take(300).collect::<String>());
        println!("WATCHDOG {what}: {shown:?} in {:?}", start.elapsed());
        verdict
    }

    /// `bvfEval step.before = bvfEval step.core`.
    fn step_goal(s: &Step) -> Expr {
        kx::eq_list(kx::evalf(s.before.clone()), kx::evalf(s.core.clone()))
    }

    /// A concrete bit list, least significant bit first.
    fn bl(bits: &[bool]) -> Expr {
        bits.iter()
            .rev()
            .fold(kx::nil(), |acc, &b| kx::cons(if b { kx::btrue() } else { kx::bfalse() }, acc))
    }

    /// T-U1. Every theorem registers and the whole environment passes its
    /// audit: each audited name is a `Theorem` carrying its proof whose
    /// domain and foundational axiom closures are empty. Independently of
    /// `add_decl`, each strength proof re-checks against its statement in the
    /// environment of the ones before it.
    #[test]
    fn strength_theorems_are_kernel_checked_and_audited() {
        run_recheck_thread("strength-theorems", || {
            let env = strength_base().expect("the strength base builds and passes its audit");
            for name in audited() {
                let n = Name::from_string(name);
                let info = env.get_const(&n).unwrap_or_else(|| panic!("{name} is present"));
                assert_eq!(info.kind, ConstantKind::Theorem, "{name}");
                assert!(info.value.is_some(), "{name} carries its proof");
                let deps = env.axiom_deps(&n).unwrap_or_else(|| panic!("{name}: no closure"));
                assert!(deps.is_empty(), "{name} reaches an axiom: {deps:?}");
                let found =
                    env.foundational_axiom_deps(&n).unwrap_or_else(|| panic!("{name}: no closure"));
                assert!(found.is_empty(), "{name} reaches a foundational axiom: {found:?}");
            }
            for name in names::ALL {
                assert!(audited().contains(&name), "{name} is audited");
            }
            let mut env = add_comm::commuting_base().expect("base").clone();
            bv_value::register(&mut env).expect("value theory");
            for (name, type_, value) in theorems().expect("builders") {
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
        })
        .expect("kernel thread");
    }

    /// The one-time cost of the strength environment, printed for STATUS.md:
    /// the commuting base (memoized per process, so the time is its first
    /// build only when this test runs alone), then a fresh, unmemoized build
    /// of the value theory and the four theorems on it, with the audit.
    #[test]
    fn strength_base_build_time() {
        run_recheck_thread("strength-build-time", || {
            let start = Instant::now();
            let base = add_comm::commuting_base().expect("commuting base").clone();
            let commuting = start.elapsed();
            let start = Instant::now();
            build_base(base).expect("the strength layer builds and passes its audit");
            let layer = start.elapsed();
            println!("BUILD-TIME commuting_base {commuting:?}; strength layer on it {layer:?}");
        })
        .expect("kernel thread");
    }

    /// The statements, as text: a change to what a theorem says is a visible
    /// diff here and not only in the proof builders.
    #[test]
    fn statements_are_pinned() {
        let expected = [
            (
                names::SHL_MUL,
                "(x : List Bool) -> (x1 : List Bool) -> (x2 : List Bool) -> (n : Nat) -> Clean.BVC.bvLen x = Nat.succ n -> Clean.BVC.bvLen x2 = Clean.BVC.bvLen x -> Clean.BVC.bvToNat x2 = Clean.BVC.bvTwoPow (Clean.BVC.bvToNat x1) -> Clean.BVC.bvShl x x1 = Clean.BVC.bvMul x x2",
            ),
            (
                names::SHL_HI_OUT,
                "(x : List Bool) -> (x1 : List Bool) -> (x2 : List Bool) -> Clean.BVC.bvLen x1 = Clean.BVC.bvToNat x2 -> Clean.BVC.bvShl (Clean.BVC.bvZeroExt x (Clean.BVC.bvLen x1)) x2 = Clean.BVC.bvShl (Clean.BVC.bvAppend x x1) x2",
            ),
            (
                names::COLLECT_ADD,
                "(x : List Bool) -> (x1 : List Bool) -> (x2 : List Bool) -> (x3 : List Bool) -> (n : Nat) -> Clean.BVC.bvLen x = Nat.succ n -> Clean.BVC.bvLen x2 = Clean.BVC.bvLen x -> Clean.BVC.bvLen x3 = Clean.BVC.bvLen x -> Clean.BVC.bvToNat x3 = Nat.succ (Clean.BVC.bvToNat x2) -> Clean.BVI.addRecM (Clean.BVI.addRecM x x1 Bool.false) (Clean.BVC.bvMul x x2) Bool.false = Clean.BVI.addRecM (Clean.BVC.bvMul x x3) x1 Bool.false",
            ),
            (
                names::COLLECT_SUB,
                "(x : List Bool) -> (x1 : List Bool) -> (x2 : List Bool) -> (x3 : List Bool) -> (n : Nat) -> Clean.BVC.bvLen x = Nat.succ n -> Clean.BVC.bvLen x2 = Clean.BVC.bvLen x -> Clean.BVC.bvLen x3 = Clean.BVC.bvLen x -> Clean.BVC.bvToNat x2 = Nat.succ (Clean.BVC.bvToNat x3) -> Clean.BVI.addRecM (Clean.BVI.addRecM (Clean.BVC.bvMul x x2) x1 Bool.false) (Clean.BVC.bvNot x) Bool.true = Clean.BVI.addRecM (Clean.BVC.bvMul x x3) x1 Bool.false",
            ),
        ];
        let all = theorems().expect("builders");
        for (name, text) in expected {
            let (_, ty, _) = all.iter().find(|(n, _, _)| *n == name).expect("listed");
            assert_eq!(ty.to_string(), text, "{name}");
        }
    }

    /// T-U2. The audit fails closed. A reflection lemma replaced by an axiom
    /// of the same statement, a prelude lemma a value proof cites replaced
    /// the same way, and a strength theorem's name already taken by an
    /// axiom: each makes the build `Err`. The untouched base builds.
    #[test]
    fn the_strength_audit_fails_closed() {
        run_recheck_thread("strength-audit-negative", || {
            let base = add_comm::commuting_base().expect("base").clone();
            build_base(base.clone()).expect("the untouched base builds");
            let axiomatize = |env: &mut Environment, name: &str| {
                let n = Name::from_string(name);
                let type_ = env.get_const(&n).expect("present").type_.clone();
                assert!(env.forget_decl(&n), "{name} removed");
                env.add_decl(Declaration::Axiom { name: n, level_params: vec![], type_ })
                    .expect("axiom of the same statement");
            };
            for name in ["Clean.BVC.bvf_shl_cong", "Nat.mul_le_mul_left", "Nat.div_add_mod"] {
                let mut env = base.clone();
                axiomatize(&mut env, name);
                let err = build_base(env).expect_err(name);
                assert!(err.starts_with("audit:"), "{name}: {err}");
            }
            let mut env = base.clone();
            env.add_decl(Declaration::Axiom {
                name: Name::from_string(names::COLLECT_SUB),
                level_params: vec![],
                type_: Expr::const_str("True"),
            })
            .expect("axiom");
            let err = build_base(env).expect_err("name taken");
            assert!(err.contains(names::COLLECT_SUB), "{err}");
        })
        .expect("kernel thread");
    }

    /// T-U2, the route half. In an environment whose audit fails (a prelude
    /// lemma the value theory cites replaced by an axiom of the same
    /// statement), the strength route declines the s02 obligation it proves
    /// in the real environment.
    #[test]
    fn a_failed_audit_makes_the_route_decline() {
        use super::super::{StrengthFilter, strength_discharge_in};
        fn doctored(leaves: &[(String, u32)]) -> Result<Environment, String> {
            let mut base = add_comm::commuting_base()?.clone();
            let n = Name::from_string("Nat.div_add_mod");
            let type_ = base.get_const(&n).ok_or("Nat.div_add_mod is absent")?.type_.clone();
            if !base.forget_decl(&n) {
                return Err("not removed".into());
            }
            base.add_decl(Declaration::Axiom { name: n, level_params: vec![], type_ })
                .map_err(|e| format!("{e:?}"))?;
            let mut env = build_base(base)?;
            add_comm::add_leaf_bits(&mut env, leaves);
            Ok(env)
        }
        let x = var("X0", 64);
        let machine = add(add(x.clone(), lit(7, 64), 64), shl(x.clone(), lit(1, 64), 64), 64);
        let auto = add(mul(x, lit(3, 64), 64), lit(7, 64), 64);
        let err = run_recheck_thread("strength-doctored", || doctored(&[]).map(|_| ()))
            .expect("kernel thread")
            .expect_err("the doctored base fails its audit");
        assert!(err.starts_with("audit:"), "{err}");
        assert_eq!(strength_discharge_in(&machine, &auto, StrengthFilter::On, doctored), None);
        assert!(
            strength_discharge_in(&machine, &auto, StrengthFilter::On, strength_env).is_some(),
            "the real environment proves it"
        );
    }

    /// T-U3. Each premise is needed: at small concrete lists where every
    /// OTHER premise holds (checked by the kernel), the conclusion is false
    /// and the kernel refuses `Eq.refl` for it; at a witness where every
    /// premise holds, the theorem's instance is accepted.
    #[test]
    fn premises_are_needed_kernel_counterexamples() {
        let holds = |val: Expr, ty: Expr, what: &str| {
            kernel_check(&[], val, ty).unwrap_or_else(|e| panic!("{what} should hold: {e}"));
        };
        // At every accepted witness below, `Eq.refl` of the conclusion is
        // accepted too: a refusal of `Eq.refl` is the conclusion's falsity,
        // not an ill-formed term.
        let computes = |lhs: Expr, rhs: Expr, what: &str| {
            kernel_check(&[], refl(lb(), lhs.clone()), eq(lb(), lhs, rhs))
                .unwrap_or_else(|e| panic!("{what}: the true conclusion was refused: {e}"));
        };
        let refuted = |lhs: Expr, rhs: Expr, what: &str| {
            assert!(
                kernel_check(&[], refl(lb(), lhs.clone()), eq(lb(), lhs, rhs)).is_err(),
                "{what}: the conclusion was accepted"
            );
        };
        let nat_eq = |a: Expr, b: Expr| eq(nat(), a, b);
        let (t, f) = (true, false);
        let one = || succ(super::super::kterm::zero());

        // shl_mul without `L c = L x`: x=[t], c=[f,t], n=[t].
        let (x, c, n) = (bl(&[t]), bl(&[f, t]), bl(&[t]));
        holds(refl(nat(), one()), nat_eq(len(&x), one()), "L [t] = succ 0");
        holds(refl(nat(), nlit(2)), nat_eq(val(&c), two_pow(val(&n))), "V c = P (V n)");
        refuted(bv_shl(x.clone(), n.clone()), bvmul(x, c), "shl_mul without L c = L x");
        // shl_mul without `V c = P (V n)`: x=1, n=1, c=4 at width 4.
        let (x, n, c) = (bl(&[t, f, f, f]), bl(&[t, f, f, f]), bl(&[f, f, t, f]));
        holds(refl(nat(), nlit(4)), nat_eq(len(&c), len(&x)), "L c = L x");
        refuted(bv_shl(x.clone(), n.clone()), bvmul(x.clone(), c), "shl_mul without the value");
        // ... and with the right multiplier the instance is accepted.
        let c2 = bl(&[f, t, f, f]);
        let m3 = nlit(3);
        holds(
            cite(
                names::SHL_MUL,
                [
                    x.clone(),
                    n.clone(),
                    c2.clone(),
                    m3.clone(),
                    refl(nat(), nlit(4)),
                    refl(nat(), nlit(4)),
                    refl(nat(), nlit(2)),
                ],
            ),
            eq(lb(), bv_shl(x.clone(), n.clone()), bvmul(x.clone(), c2.clone())),
            "shl_mul at 1 << 1",
        );
        computes(bv_shl(x.clone(), n.clone()), bvmul(x.clone(), c2), "shl_mul at 1 << 1");

        // shl_hi_out without `L hi = V n`: lo=[t], hi=[t], n=[] (shift by 0).
        let (lo, hi, n) = (bl(&[t]), bl(&[t]), bl(&[]));
        refuted(
            bv_shl(zero_ext(lo.clone(), len(&hi)), n.clone()),
            bv_shl(bv_append(lo.clone(), hi.clone()), n),
            "shl_hi_out without L hi = V n",
        );
        // ... and at `n = [t]` (shift by 1 = L hi) the instance is accepted.
        let n = bl(&[t]);
        holds(
            cite(names::SHL_HI_OUT, [lo.clone(), hi.clone(), n.clone(), refl(nat(), nlit(1))]),
            eq(
                lb(),
                bv_shl(zero_ext(lo.clone(), len(&hi)), n.clone()),
                bv_shl(bv_append(lo.clone(), hi.clone()), n.clone()),
            ),
            "shl_hi_out at [t] [t] by 1",
        );
        computes(
            bv_shl(zero_ext(lo.clone(), len(&hi)), n.clone()),
            bv_shl(bv_append(lo, hi), n),
            "shl_hi_out at [t] [t] by 1",
        );

        // collect_add with `V c2 = V c1`: x=1, y=0, c1=c2=1 at width 2.
        let (x, y, c1) = (bl(&[t, f]), bl(&[f, f]), bl(&[t, f]));
        let fb = kx::bfalse();
        let add_lhs = |c1: &Expr| {
            addm(addm(x.clone(), y.clone(), fb.clone()), bvmul(x.clone(), c1.clone()), fb.clone())
        };
        let add_rhs = |c2: &Expr| addm(bvmul(x.clone(), c2.clone()), y.clone(), fb.clone());
        refuted(add_lhs(&c1), add_rhs(&c1), "collect_add with V c2 = V c1");
        let c2 = bl(&[f, t]);
        holds(
            cite(
                names::COLLECT_ADD,
                [
                    x.clone(),
                    y.clone(),
                    c1.clone(),
                    c2.clone(),
                    nlit(1),
                    refl(nat(), nlit(2)),
                    refl(nat(), nlit(2)),
                    refl(nat(), nlit(2)),
                    refl(nat(), nlit(2)),
                ],
            ),
            eq(lb(), add_lhs(&c1), add_rhs(&c2)),
            "collect_add at x=1, c1=1",
        );
        computes(add_lhs(&c1), add_rhs(&c2), "collect_add at x=1, c1=1");

        // collect_sub with `V c1 = V c2`: x=1, y=0, c1=c2=2 at width 2.
        let tb = kx::btrue();
        let sub_lhs = |c1: &Expr| {
            addm(
                addm(bvmul(x.clone(), c1.clone()), y.clone(), fb.clone()),
                kx::bv_not(x.clone()),
                tb.clone(),
            )
        };
        let c1 = bl(&[f, t]);
        refuted(sub_lhs(&c1), add_rhs(&c1), "collect_sub with V c1 = V c2");
        let c2 = bl(&[t, f]);
        holds(
            cite(
                names::COLLECT_SUB,
                [
                    x.clone(),
                    y.clone(),
                    c1.clone(),
                    c2.clone(),
                    nlit(1),
                    refl(nat(), nlit(2)),
                    refl(nat(), nlit(2)),
                    refl(nat(), nlit(2)),
                    refl(nat(), nlit(2)),
                ],
            ),
            eq(lb(), sub_lhs(&c1), add_rhs(&c2)),
            "collect_sub at x=1, c1=2",
        );
        computes(sub_lhs(&c1), add_rhs(&c2), "collect_sub at x=1, c1=2");

        // The value lemmas the proofs rest on need their `%` and their carry:
        // `V (bvMul a b) = V a * V b` is false at a = b = 3 (width 2), and
        // `V (addRecM xs ys true) = V xs + V ys` is false at xs = ys = [f].
        let three = bl(&[t, t]);
        let prod = val(&bvmul(three.clone(), three.clone()));
        let no_mod = nmul(val(&three), val(&three));
        assert!(
            kernel_check(&[], refl(nat(), prod.clone()), nat_eq(prod.clone(), no_mod.clone()))
                .is_err(),
            "bvMul_val without %: accepted"
        );
        holds(
            refl(nat(), prod.clone()),
            nat_eq(prod, nmod(no_mod, two_pow(len(&three)))),
            "bvMul_val at 3 * 3",
        );
        let z = bl(&[f]);
        let sum = val(&addm(z.clone(), z.clone(), tb.clone()));
        let no_carry = nadd(val(&z), val(&z));
        assert!(
            kernel_check(
                &[],
                refl(nat(), sum.clone()),
                nat_eq(sum.clone(), nmod(no_carry.clone(), two_pow(len(&z))))
            )
            .is_err(),
            "addRecM_val without the carry: accepted"
        );
        holds(
            refl(nat(), sum.clone()),
            nat_eq(sum, nmod(nadd(no_carry, btn(tb.clone())), two_pow(len(&z)))),
            "addRecM_val at 0 + 0 + 1",
        );
    }

    /// The 64-bit leaf `X0` and its length proof.
    fn x64() -> (Expr, Expr) {
        let l = core(&var("X0", 64));
        let (p, w) = core_len(&l).expect("leaf length");
        assert_eq!(w, 64);
        (l, p)
    }

    /// T-U6. Forged instances fail at a CLOSED premise, under a watchdog:
    /// `shl_mul` with `c = 4` for a shift by 1, `shl_hi_out` with a two-bit
    /// `hi` for a shift by 1 (the UBFIZ shape the builder declines), and
    /// `collect_add` with `c2 = c1`. Each conclusion matches its goal; only
    /// the premise is false. `collect_add` offered for a goal whose second
    /// multiplicand is a different variable is refused as well, within the
    /// same bound.
    #[test]
    fn forged_instances_fail_at_a_closed_premise() {
        let (l, p) = x64();
        let leaf = [("X0", 64)];
        let one = kx::bits(1, 64);
        let r = kx::const_(one.clone());

        // shl_mul for n = 1: c = 4 is refused, c = 2 in the same term is
        // accepted.
        let shl_mul = |c: Expr| {
            let proof = cite(
                names::SHL_MUL,
                [
                    kx::evalf(l.clone()),
                    one.clone(),
                    c.clone(),
                    kx::nat_lit(63),
                    p.clone(),
                    same_len(&c, &l, 64, &p),
                    refl(nat(), val(&c)),
                ],
            );
            let goal = kx::eq_list(
                kx::evalf(kx::shl(l.clone(), r.clone())),
                kx::evalf(kx::mul(l.clone(), kx::const_(c))),
            );
            (proof, goal)
        };
        let (forged, goal) = shl_mul(kx::bits(4, 64));
        assert!(kernel_check_bounded("shl_mul c=4", &leaf, forged, goal).is_err());
        let (honest, goal) = shl_mul(kx::bits(2, 64));
        kernel_check_bounded("shl_mul c=2", &leaf, honest, goal).expect("the control holds");

        // shl_hi_out for n = 1: the UBFIZ shape (two high bits shifted out)
        // is refused; the LSL alias (one high bit) in the same term is
        // accepted.
        let shl_hi_out = |k: u32| {
            let node =
                kx::zext(kx::extract(l.clone(), kx::const_(kx::bits(0, 64 - k))), kx::nat_lit(k));
            let elems = concrete_value(&l).expect("leaf");
            let split = (64 - k) as usize;
            let (lo, hi) = (list_of(&elems[..split]), list_of(&elems[split..]));
            let proof =
                cite(names::SHL_HI_OUT, [lo, hi.clone(), one.clone(), refl(nat(), len(&hi))]);
            let goal = kx::eq_list(
                kx::evalf(kx::shl(node.clone(), r.clone())),
                kx::evalf(kx::shl(l.clone(), r.clone())),
            );
            (node, proof, goal)
        };
        let (ubfiz, forged, goal) = shl_hi_out(2);
        assert!(shl_hi_out_step(&ubfiz, &r).is_none(), "the builder declines");
        assert!(kernel_check_bounded("shl_hi_out hi=2", &leaf, forged, goal).is_err());
        let (lsl, honest, goal) = shl_hi_out(1);
        assert!(shl_hi_out_step(&lsl, &r).is_some(), "the builder accepts");
        kernel_check_bounded("shl_hi_out hi=1", &leaf, honest, goal).expect("the control holds");

        // collect_add for c1 = 2: c2 = c1 is refused, c2 = 3 is accepted.
        let y = kx::const_(kx::bits(7, 64));
        let c1 = kx::bits(2, 64);
        let collect = |x: &Expr, x2: &Expr, c2: &Expr| {
            let proof = cite(
                names::COLLECT_ADD,
                [
                    kx::evalf(x.clone()),
                    kx::evalf(y.clone()),
                    c1.clone(),
                    c2.clone(),
                    kx::nat_lit(63),
                    p.clone(),
                    same_len(&c1, x, 64, &p),
                    same_len(c2, x, 64, &p),
                    refl(nat(), val(c2)),
                ],
            );
            let goal = kx::eq_list(
                kx::evalf(kx::add(
                    kx::add(x.clone(), y.clone()),
                    kx::mul(x2.clone(), kx::const_(c1.clone())),
                )),
                kx::evalf(kx::add(kx::mul(x.clone(), kx::const_(c2.clone())), y.clone())),
            );
            (proof, goal)
        };
        let (forged, goal) = collect(&l, &l, &c1);
        assert!(kernel_check_bounded("collect_add c2=c1", &leaf, forged, goal).is_err());
        let (honest, goal) = collect(&l, &l, &kx::bits(3, 64));
        kernel_check_bounded("collect_add c2=3", &leaf, honest, goal).expect("the control holds");

        // collect_add for a goal whose multiplicand is another variable.
        let other = core(&var("X1", 64));
        assert!(
            add_step(
                &kx::add(l.clone(), y.clone()),
                &kx::mul(other.clone(), kx::const_(c1.clone()))
            )
            .is_none(),
            "the builder declines"
        );
        let (forged, goal) = collect(&l, &other, &kx::bits(3, 64));
        let leaves = [("X0", 64), ("X1", 64)];
        assert!(kernel_check_bounded("collect_add other x", &leaves, forged, goal).is_err());
    }

    /// Each step builder's term is a proof of `bvfEval before = bvfEval core`
    /// on the shapes the rungs produce: a 64-bit shift by 1 (s02), a 32-bit
    /// shift by 3 (s09), the UBFM `lsl #1` (s14, two steps), `collect_add`
    /// with a constant addend (s02) and with the variable as addend (s08),
    /// and `collect_sub` at 32 bits (s09).
    #[test]
    fn steps_are_kernel_checked() {
        let x = var("X0", 64);
        let x32 = low(var("X0", 64), 31);
        let (l, _) = x64();
        let mut checks: Vec<(&str, Step)> = Vec::new();

        let s = shl_steps(&l, &core(&lit(1, 64)));
        assert_eq!(s.len(), 1);
        assert_eq!(s[0].theorem, names::SHL_MUL);
        assert_eq!(s[0].core, core(&mul(x.clone(), lit(2, 64), 64)));
        checks.push(("s02 shl", s[0].clone()));

        let xc = core(&x32);
        let s = shl_mul_step(&xc, &core(&lit(3, 32))).expect("32-bit shift by 3");
        assert_eq!(s.core, core(&mul(x32.clone(), lit(8, 32), 32)));
        checks.push(("s09 shl", s));

        let ubfm = kx::zext(core(&low(x.clone(), 62)), kx::nat_lit(1));
        let s = shl_steps(&ubfm, &core(&lit(1, 64)));
        assert_eq!(
            s.iter().map(|s| s.theorem).collect::<Vec<_>>(),
            [names::SHL_HI_OUT, names::SHL_MUL]
        );
        assert_eq!(s[0].core, kx::shl(l.clone(), core(&lit(1, 64))));
        assert_eq!(s[1].before, s[0].core);
        assert_eq!(s[1].core, core(&mul(x.clone(), lit(2, 64), 64)));
        checks.push(("s14 hi out", s[0].clone()));
        checks.push(("s14 shl", s[1].clone()));

        let s = add_step(
            &core(&add(x.clone(), lit(7, 64), 64)),
            &core(&mul(x.clone(), lit(2, 64), 64)),
        )
        .expect("s02 collect");
        assert_eq!(s.core, core(&add(mul(x.clone(), lit(3, 64), 64), lit(7, 64), 64)));
        checks.push(("s02 collect", s));

        let s =
            add_step(&core(&add(x.clone(), x.clone(), 64)), &core(&mul(x.clone(), lit(2, 64), 64)))
                .expect("s08 collect");
        assert_eq!(s.core, core(&add(mul(x.clone(), lit(3, 64), 64), x.clone(), 64)));
        checks.push(("s08 collect", s));

        let s = sub_step(&core(&add(mul(x32.clone(), lit(8, 32), 32), lit(3, 32), 32)), &xc)
            .expect("s09 collect");
        assert_eq!(s.core, core(&add(mul(x32.clone(), lit(7, 32), 32), lit(3, 32), 32)));
        checks.push(("s09 collect", s));

        for (what, s) in checks {
            let start = Instant::now();
            kernel_check(&[("X0", 64)], s.proof.clone(), step_goal(&s))
                .unwrap_or_else(|e| panic!("{what}: {e}"));
            println!("STEP {what}: {:?}", start.elapsed());
        }
        // The s14 chain end to end: `Shl (ZeroExt …) 1` to `Mul x 2`.
        let s = shl_steps(&ubfm, &core(&lit(1, 64)));
        let before = kx::shl(ubfm.clone(), core(&lit(1, 64)));
        let proof = s
            .iter()
            .fold(kx::eq_refl_list(kx::evalf(before.clone())), |acc, st| st.chain(&before, acc));
        let goal = kx::eq_list(kx::evalf(before), kx::evalf(s[1].core.clone()));
        kernel_check(&[("X0", 64)], proof, goal).expect("s14 chain");
    }

    /// The machine side of s02 (`(x + 7) + (x << 1)`) and of s09's `h`
    /// (`(3 + (x << 3)) - x` at 32 bits), reflected with the steps spliced in
    /// as the route will splice them, reaches the specification's core, and
    /// the kernel accepts the discharge of
    /// `bvfEval (reflect machine) = bvfEval (reflect spec)`. The goal's
    /// machine side is the Formula's own reflection.
    #[test]
    fn s02_and_s09_steps_compose_to_the_specification() {
        let discharge = |bvf: Expr, core_m: Expr, proof_m: Expr, spec: &Formula| {
            let ra = reflect(spec);
            assert_eq!(core_m, ra.core, "the cores meet");
            let goal = kx::eq_list(kx::evalf(bvf.clone()), kx::evalf(ra.bvf.clone()));
            let sym = symm(lb(), kx::evalf(ra.bvf.clone()), kx::evalf(ra.core.clone()), ra.proof);
            let term = kx::eq_trans_list(
                kx::evalf(bvf),
                kx::evalf(core_m),
                kx::evalf(ra.bvf),
                proof_m,
                sym,
            );
            (term, goal)
        };

        // s02.
        let x = var("X0", 64);
        let (rl, rr) =
            (reflect(&add(x.clone(), lit(7, 64), 64)), reflect(&shl(x.clone(), lit(1, 64), 64)));
        let sh = app_of(&rr.core, "Clean.BVC.BvF.Shl", 2)
            .expect("shl")
            .iter()
            .map(|e| (*e).clone())
            .collect::<Vec<_>>();
        let s1 = shl_mul_step(&sh[0], &sh[1]).expect("S1");
        let rr_proof = s1.chain(&rr.bvf, rr.proof);
        let bvf = kx::add(rl.bvf.clone(), rr.bvf.clone());
        let machine = add(add(x.clone(), lit(7, 64), 64), shl(x.clone(), lit(1, 64), 64), 64);
        assert_eq!(bvf, reflect(&machine).bvf);
        let proof0 =
            kx::add_cong(rl.bvf, rl.core.clone(), rr.bvf, s1.core.clone(), rl.proof, rr_proof);
        let s3 = add_step(&rl.core, &s1.core).expect("S3");
        assert_eq!(s3.before, kx::add(rl.core, s1.core.clone()));
        let proof = s3.chain(&bvf, proof0);
        assert_eq!(
            label(&[s1.theorem, s3.theorem], 0),
            format!("{}+{}+{LABEL_TAIL}", names::SHL_MUL, names::COLLECT_ADD)
        );
        let (term, goal) = discharge(
            bvf,
            s3.core.clone(),
            proof,
            &add(mul(x.clone(), lit(3, 64), 64), lit(7, 64), 64),
        );
        kernel_check(&[("X0", 64)], term, goal).expect("s02");

        // s09 h.
        let x32 = low(var("X0", 64), 31);
        let rx = reflect(&x32);
        let r3 = reflect(&lit(3, 32));
        let rs = reflect(&shl(x32.clone(), lit(3, 32), 32));
        let s1 = shl_mul_step(&rx.core, &r3.core.clone()).filter(|_| true);
        let s1 = s1
            .and_then(|_| {
                let sh = app_of(&rs.core, "Clean.BVC.BvF.Shl", 2).expect("shl");
                shl_mul_step(sh[0], sh[1])
            })
            .expect("S1 at 32 bits");
        let rs_proof = s1.chain(&rs.bvf, rs.proof);
        let bvf_a = kx::add(r3.bvf.clone(), rs.bvf.clone());
        let proof_a0 =
            kx::add_cong(r3.bvf, r3.core.clone(), rs.bvf, s1.core.clone(), r3.proof, rs_proof);
        let swap = add_comm::canonical_step(&r3.core, &s1.core).expect("3 + x*8 is reordered");
        let swapped = kx::add(s1.core.clone(), r3.core.clone());
        let proof_a = kx::eq_trans_list(
            kx::evalf(bvf_a.clone()),
            kx::evalf(kx::add(r3.core, s1.core.clone())),
            kx::evalf(swapped.clone()),
            proof_a0,
            swap,
        );
        let bvf = kx::sub(bvf_a.clone(), rx.bvf.clone());
        let machine = sub(add(lit(3, 32), shl(x32.clone(), lit(3, 32), 32), 32), x32.clone(), 32);
        assert_eq!(bvf, reflect(&machine).bvf);
        let proof0 =
            kx::sub_cong(bvf_a, swapped.clone(), rx.bvf, rx.core.clone(), proof_a, rx.proof);
        let s4 = sub_step(&swapped, &rx.core).expect("S4");
        let proof = s4.chain(&bvf, proof0);
        assert_eq!(
            label(&[s1.theorem, s4.theorem], 1),
            format!(
                "{}+{}+{}+{LABEL_TAIL}",
                names::SHL_MUL,
                names::COLLECT_SUB,
                add_comm::names::ADD_REC_M_COMM
            )
        );
        let (term, goal) = discharge(
            bvf,
            s4.core.clone(),
            proof,
            &add(mul(x32.clone(), lit(7, 32), 32), lit(3, 32), 32),
        );
        kernel_check(&[("X0", 64)], term, goal).expect("s09 h");
    }

    /// The guards decline, in Rust, every shape outside the family: a shift
    /// by the width or more, by `2^62`, by a constant wider than 64 bits (129
    /// and 200, which `kx::bits` cannot even render), a shift whose constant
    /// width differs from the operand's, widths other than 32 and 64, a
    /// UBFIZ (`ubfiz x0, x0, #1, #8`: zero-extension by 56, shift by 1), a
    /// zero-extension amount beyond 64, a non-constant shift amount, an
    /// overflowing `collect_add` multiplier, a zero `collect_sub`
    /// multiplier, and a different variable in the two places of the
    /// pattern.
    #[test]
    fn guards_decline_outside_the_family() {
        let x = var("X0", 64);
        let (l, _) = x64();
        let cst = |v: i128, w: u32| core(&lit(v, w));
        assert!(shl_mul_step(&l, &cst(64, 64)).is_none());
        assert!(shl_mul_step(&l, &cst(65, 64)).is_none());
        assert!(shl_mul_step(&l, &cst(1 << 62, 64)).is_none());
        assert!(shl_mul_step(&l, &cst(0, 64)).is_none());
        let mut wide = vec![false; 129];
        wide[0] = true;
        assert!(shl_mul_step(&l, &kx::const_(bl(&wide))).is_none());
        wide.resize(200, false);
        assert!(shl_mul_step(&l, &kx::const_(bl(&wide))).is_none());
        assert!(shl_mul_step(&l, &cst(1, 32)).is_none(), "constant width differs");
        let x16 = core(&low(x.clone(), 15));
        assert!(shl_mul_step(&x16, &cst(1, 16)).is_none(), "16 bits");
        let x8 = core(&var("B0", 8));
        assert!(shl_mul_step(&x8, &cst(1, 8)).is_none(), "8 bits");
        // A shift by a non-constant (a source-level `x << (y & 63)`).
        let amount = core(&Formula::BvAnd(Box::new(var("X1", 64)), Box::new(lit(63, 64)), 64));
        assert!(shl_steps(&l, &amount).is_empty());
        assert!(shl_steps(&l, &core(&var("X1", 64))).is_empty());

        // UBFIZ x0, x0, #1, #8: Shl(ZeroExt(Extract(x, 7, 0), 56), 1).
        let ubfiz = kx::zext(core(&low(x.clone(), 7)), kx::nat_lit(56));
        assert!(shl_hi_out_step(&ubfiz, &cst(1, 64)).is_none());
        // ... but the same node shifted by 56 IS an instance of `shl_hi_out`:
        // `T` is the low 8 = 64 - 56 bits and the shift equals the
        // zero-extension amount 56, so the step is offered.
        assert!(shl_hi_out_step(&ubfiz, &cst(56, 64)).is_some());
        // A zero-extension amount the decoder will not count.
        let huge = kx::zext(core(&low(x.clone(), 62)), kx::nat_lit(100));
        assert!(shl_hi_out_step(&huge, &cst(1, 64)).is_none());
        // ... nor a literal of four million (never unfolded to a succ chain).
        let huge = kx::zext(core(&low(x.clone(), 62)), nlit(4_000_000));
        assert!(shl_hi_out_step(&huge, &cst(1, 64)).is_none());
        // The LSL alias with a mismatched shift constant width.
        let lsl1 = kx::zext(core(&low(x.clone(), 62)), kx::nat_lit(1));
        assert!(shl_hi_out_step(&lsl1, &cst(1, 32)).is_none());
        assert!(shl_hi_out_step(&lsl1, &cst(2, 64)).is_none());
        assert!(shl_hi_out_step(&lsl1, &cst(1, 64)).is_some());

        // collect_add: the multiplier at its maximum cannot be incremented.
        let xy = core(&add(x.clone(), lit(7, 64), 64));
        assert!(add_step(&xy, &core(&mul(x.clone(), lit(-1, 64), 64))).is_none());
        assert!(add_step(&xy, &core(&mul(x.clone(), lit(-2, 64), 64))).is_some());
        assert!(add_step(&xy, &core(&mul(var("X1", 64), lit(2, 64), 64))).is_none());
        assert!(add_step(&xy, &core(&mul(x.clone(), var("X1", 64), 64))).is_none());
        // `x + (x * 2)` with no addend is not this rewrite.
        assert!(add_step(&l, &core(&mul(x.clone(), lit(2, 64), 64))).is_none());
        // collect_sub: a zero multiplier cannot be decremented, and the
        // subtrahend must be the multiplicand.
        let my = |c: i128| core(&add(mul(x.clone(), lit(c, 64), 64), lit(3, 64), 64));
        assert!(sub_step(&my(0), &l).is_none());
        assert!(sub_step(&my(1), &l).is_some());
        assert!(sub_step(&my(8), &core(&var("X1", 64))).is_none());
        // `(x << a) - x` with no addend is not this rewrite.
        assert!(sub_step(&core(&mul(x.clone(), lit(8, 64), 64)), &l).is_none());
    }

    /// The label names exactly the theorems used, once each, in order;
    /// `addRecM_comm` only when an `Add` was reordered.
    #[test]
    fn the_label_lists_the_theorems_used() {
        assert_eq!(
            label(&[names::SHL_HI_OUT, names::SHL_MUL, names::SHL_MUL], 0),
            format!("{}+{}+{LABEL_TAIL}", names::SHL_HI_OUT, names::SHL_MUL)
        );
        assert_eq!(
            label(&[names::COLLECT_ADD], 2),
            format!("{}+{}+{LABEL_TAIL}", names::COLLECT_ADD, add_comm::names::ADD_REC_M_COMM)
        );
        assert!(!label(&[names::SHL_MUL], 0).contains("addRecM_comm"));
    }

    /// Every constant a theorem's statement or proof uses is in [`audited`]
    /// or is not a theorem, and none is an axiom; no statement or proof
    /// applies `Nat.mod`, `Nat.div`, `bvTwoPow`, `natToBvAux`, `bvMul` or
    /// `bvShl` to closed data (on the surface of the term: what one
    /// reduction step exposes is the route test's concern). Every step term
    /// cites only audited theorems, and its only axioms are the leaf bits.
    #[test]
    fn every_citation_is_audited_and_nothing_computes_on_closed_data() {
        fn closed_heavy_app(e: &Expr, found: &mut Vec<String>) {
            if let ExprKind::Const(name, _) = e.get_app_fn().kind() {
                let n = name.to_string();
                let args = e.get_app_args();
                let arity = match n.as_str() {
                    "Nat.mod"
                    | "Nat.div"
                    | "Clean.BVC.natToBvAux"
                    | "Clean.BVC.bvMul"
                    | "Clean.BVC.bvShl" => 2,
                    "Clean.BVC.bvTwoPow" => 1,
                    _ => usize::MAX,
                };
                if args.len() == arity && (0..arity).all(|i| !args[i].has_loose_bvars()) {
                    found.push(format!("{e}"));
                }
            }
            match e.kind() {
                ExprKind::App(f, a) => {
                    closed_heavy_app(f, found);
                    closed_heavy_app(a, found);
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    closed_heavy_app(ty, found);
                    closed_heavy_app(body, found);
                }
                _ => {}
            }
        }
        let x = var("X0", 64);
        let (l, _) = x64();
        let mut steps =
            shl_steps(&kx::zext(core(&low(x.clone(), 62)), kx::nat_lit(1)), &core(&lit(1, 64)));
        steps.extend(add_step(
            &core(&add(x.clone(), lit(7, 64), 64)),
            &core(&mul(x.clone(), lit(2, 64), 64)),
        ));
        steps.extend(sub_step(&core(&add(mul(x.clone(), lit(8, 64), 64), lit(3, 64), 64)), &l));
        assert_eq!(steps.len(), 4);
        assert!(steps.len() <= MAX_REWRITES);
        // The walker sees what it looks for.
        let mut found = Vec::new();
        closed_heavy_app(&nmod(nlit(5), nlit(2)), &mut found);
        closed_heavy_app(&two_pow(nlit(3)), &mut found);
        assert_eq!(found.len(), 2, "{found:?}");

        run_recheck_thread("strength-citations", move || {
            let env = strength_env(&[("X0".to_string(), 64)]).expect("strength env");
            let audited: HashSet<Name> = audited().into_iter().map(Name::from_string).collect();
            let mut terms: Vec<(String, Expr)> = Vec::new();
            for (name, ty, val) in theorems().expect("builders") {
                let mut found = Vec::new();
                closed_heavy_app(&ty, &mut found);
                closed_heavy_app(&val, &mut found);
                assert!(found.is_empty(), "{name} computes on closed data: {found:?}");
                terms.push((name.to_string(), ty));
                terms.push((name.to_string(), val));
            }
            for s in &steps {
                terms.push((format!("step {}", s.theorem), s.proof.clone()));
            }
            for (what, term) in terms {
                let mut used = HashSet::new();
                term.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
                for c in used {
                    let info = env.get_const(&c).unwrap_or_else(|| panic!("{what}: {c} absent"));
                    if c.to_string().starts_with("BVC_LEAFBIT_") {
                        continue;
                    }
                    assert_ne!(info.kind, ConstantKind::Axiom, "{what} cites the axiom {c}");
                    if info.kind == ConstantKind::Theorem {
                        assert!(audited.contains(&c), "{what} cites {c}, which is not audited");
                    }
                }
            }
            // `admit_obligation` refuses an axiom that is not a leaf bit, cited
            // directly or only through a theorem that rests on it, and admits
            // an axiom-free proof.
            let truth = || Expr::const_str("True");
            let mut env = env;
            assert!(env.get_const(&Name::from_string(OBLIGATION)).is_none(), "not in the base");
            env.add_decl(Declaration::Axiom {
                name: Name::from_string("Trust.BVS.test_axiom"),
                level_params: vec![],
                type_: truth(),
            })
            .expect("axiom");
            env.add_decl(Declaration::Theorem {
                name: Name::from_string("Trust.BVS.test_theorem"),
                level_params: vec![],
                type_: truth(),
                value: Expr::const_str("Trust.BVS.test_axiom"),
            })
            .expect("theorem resting on the axiom");
            // A leaf-bit name is not enough: the leaf must be a `Bool`.
            env.add_decl(Declaration::Axiom {
                name: Name::from_string("BVC_LEAFBIT_forged_1_0"),
                level_params: vec![],
                type_: truth(),
            })
            .expect("axiom");
            for (cited, axiom) in [
                ("Trust.BVS.test_axiom", "Trust.BVS.test_axiom"),
                ("Trust.BVS.test_theorem", "Trust.BVS.test_axiom"),
                ("BVC_LEAFBIT_forged_1_0", "BVC_LEAFBIT_forged_1_0"),
            ] {
                let err = admit_obligation(&mut env.clone(), truth(), Expr::const_str(cited))
                    .expect_err(cited);
                assert!(err.contains(axiom), "{cited}: {err}");
            }
            admit_obligation(&mut env.clone(), truth(), Expr::const_str("True.intro"))
                .expect("an axiom-free proof is admitted");
            let err = admit_obligation(&mut env, truth(), Expr::const_str("False"))
                .expect_err("an ill-typed proof");
            assert!(err.starts_with("kernel:"), "{err}");
        })
        .expect("kernel thread");
    }
}
