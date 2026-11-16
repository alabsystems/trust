// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Additive cancellation on the O(1) structured route (DECISION_QUEUE
//! CANCEL-1): the theorem `Trust.BVA.add_sub_cancel`, the audited environment
//! it lives in, and the per-obligation step that splices it into a reflection.
//!
//! # What is missing without this
//!
//! Ladder rung r08 is `let big = u64::MAX - 1000; let y = big + x; y - big + 1`.
//! trust-cg folds it at O2 to `add x0, x0, #1`, which the machine semantics
//! render `x + 1`, while the producer IR keeps `((c + x) - c) + 1` with `c` the
//! SSA value `MAX - 1000`, used twice. The two cores differ by an arithmetic
//! identity: no wrapper strip, operand order (`add_comm`) or strength rewrite
//! (`strength`) joins them, and the 64-bit add/sub chain is far past the
//! bit-blast re-check limit, so the function is graded [VALIDATED].
//!
//! # What this module adds
//!
//! One theorem over the pinned `Clean.BVC` / `Clean.BVI` definitions, a
//! `Declaration::Theorem` whose proof the Clean kernel type-checks when it is
//! added (`V = bvToNat`, `L = bvLen`, `P = bvTwoPow`, `A = addRecM`,
//! `NOT = bvNot`):
//!
//! ```text
//! add_sub_cancel : ∀ c x, L c = L x → A (A c x false) (NOT c) true = x
//! ```
//!
//! That is `(c + x) - c = x`: `bvfEval (Sub a b)` is
//! `addRecM (bvfEval a) (bvNot (bvfEval b)) true` and `bvfEval (Add a b)` is
//! `addRecM (bvfEval a) (bvfEval b) false`. The premise is needed only because
//! the result takes its length from `c`. The proof goes through the values of
//! both sides (`bv_value`): `addRecM_val` twice, `mod_add_mod`, `bvNot_val`
//! (`V (NOT c) + V c + 1 = P (L c)`), `add_mul_mod_self`, a ring rearrangement
//! (`nat_ring`), `toNat_natToBv` and `natToBv_toNat` for `V x % P (L x) = V x`,
//! and finally `Trust.BVV.inj`. No Nat subtraction appears, and no `%`,
//! `bvTwoPow` or `bvMul` is applied to closed data.
//!
//! # The audit
//!
//! [`cancel_base`] is `strength::strength_base` (itself audited) plus the
//! theorem, built once per process. Then the theorem, every name its proof and
//! the step terms cite directly ([`CITED`]) and every theorem the ring
//! normaliser may cite (`nat_ring::CITED`, `nat_ring::names::ALL`) must be a
//! `Theorem` that carries its proof and whose `axiom_deps` and
//! `foundational_axiom_deps` are both empty (`add_comm::audit_theorems`); the
//! closure check also walks every lemma the proof reaches. Otherwise the
//! memoized result is `Err` and the route declines for the life of the
//! process. Each obligation is then admitted only through
//! `strength::admit_obligation`, whose transitive axiom closure may hold only
//! the per-bit `BVC_LEAFBIT_*` `Bool` leaves.
//!
//! # The step and its guards
//!
//! [`sub_cancel_step`] looks at the CORES of a reflected `Sub` node's children:
//! `Add c x` and `c` (the same `c`, structurally), with `add_comm::core_len`
//! proving both `c` and `x` of one width `w ∈ {32, 64}`. The step's proof is
//! the instance `add_sub_cancel (bvfEval c) (bvfEval x) h`, `h` built from the
//! two length proofs as `add_comm::commute` builds its premise. Narrower widths
//! are left to the bit-blast route, which decides them.
//!
//! The small builders strength uses (`cite`, `val`, `len`, `hyp`, `inj`,
//! `app_of`) are private to that frozen file, so this module carries its own
//! copies.
//!
//! # Authority
//!
//! Nothing here decides a grade. A step is a TERM; the caller splices it into
//! the discharge term and the kernel type-checks the whole term against the
//! goal built from the two original Formulas. A wrong match or length proof
//! can only make that check fail.

use std::sync::OnceLock;

use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr, ExprKind, FVarId};

use super::add_comm::{self, audit_theorems, core_len};
use super::bv_value::{btn, names as bvv};
use super::kterm::{
    Fresh, addm, bvlen, congr_arg, eq, lams, lb, nadd, nat, nat_to_bv, nlit, nmod, nmul, pis, symm,
    to_nat, trans, two_pow,
};
use super::kx;
use super::nat_ring::{self, Eqn, ring_eq};
use super::strength::{self, Step};

/// The theorem this module proves. `Trust.BVA.*` (bit-vector arithmetic), apart
/// from the strength family `Trust.BVS.*`.
pub(crate) mod names {
    pub(crate) const ADD_SUB_CANCEL: &str = "Trust.BVA.add_sub_cancel";
    pub(crate) const ALL: [&str; 1] = [ADD_SUB_CANCEL];
}

/// The theorems the proof and the step terms cite directly, other than the ring
/// normaliser's (`nat_ring::CITED` and `nat_ring::names::ALL`, which
/// [`audited`] adds). [`cancel_base`] audits each of them along with
/// [`names::ALL`]; `cited_is_exactly_what_the_proofs_cite` pins the list
/// against the terms.
pub(crate) const CITED: [&str; 12] = [
    bvv::INJ,
    bvv::TO_NAT_NAT_TO_BV,
    bvv::NAT_TO_BV_TO_NAT,
    bvv::ADD_REC_M_VAL,
    bvv::BV_NOT_VAL,
    bvv::MOD_ADD_MOD,
    bvv::ADD_MUL_MOD_SELF,
    bvv::TWO_POW_POS,
    add_comm::names::LEN_ADD_REC_M,
    "congrArg",
    "Eq.trans",
    "Eq.symm",
];

/// The last part of the label of a function proved through this route.
pub(crate) const LABEL_TAIL: &str = "Clean.BVC congruence (O(1) add@N, additive cancellation)";

/// The widths a step is offered at; narrower ones stay with the bit-blast.
const WIDTHS: [u32; 2] = [32, 64];

// ── small builders (copies of strength's private ones) ───────────────────────

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

/// A hypothesis `proof : lhs = rhs` as an equation.
fn hyp(lhs: Expr, rhs: Expr, proof: Expr) -> Eqn {
    Eqn { lhs, rhs, proof }
}

/// `inj xs ys hl hv : xs = ys`.
fn inj(xs: &Expr, ys: &Expr, hl: Eqn, hv: Eqn) -> Expr {
    cite(bvv::INJ, [xs.clone(), ys.clone(), hl.proof, hv.proof])
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

// ── the theorem ──────────────────────────────────────────────────────────────

/// `add_sub_cancel : ∀ c x, L c = L x → A (A c x false) (NOT c) true = x`.
///
/// Lengths: `L lhs = L (A c x false) = L c = L x` (`len_addRecM` twice, the
/// premise). Values, with `Q = P (L c)`: `V lhs` is
/// `((V c + V x + 0) % Q + V (NOT c) + 1) % Q` (`addRecM_val` twice,
/// `len_addRecM` under the modulus), which is `(V c + V x + (V (NOT c) + 1)) % Q`
/// (a ring step, `mod_add_mod`), then `(V x + Q) % Q` (a ring step,
/// `bvNot_val`), then `V x % Q` (`add_mul_mod_self` at `1`), then
/// `V x % P (L x)` (the premise). And `V x % P (L x) = V x` by `toNat_natToBv`
/// reversed and `natToBv_toNat`. Then `inj`.
fn add_sub_cancel() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bc, c) = list_local(&mut fr);
    let (bx, x) = list_local(&mut fr);
    let (h_id, h) = fr.local();
    let (lc, lx) = (len(&c), len(&x));
    let binders = vec![bc, bx, (h_id, eq(nat(), lc.clone(), lx.clone()))];
    let h = hyp(lc.clone(), lx.clone(), h);
    let (f, t) = (kx::bfalse(), kx::btrue());
    let inner = addm(c.clone(), x.clone(), f.clone());
    let nc = kx::bv_not(c.clone());
    let lhs = addm(inner.clone(), nc.clone(), t.clone());
    let ty = pis(binders.clone(), eq(lb(), lhs.clone(), x.clone()));
    let q = two_pow(lc.clone());
    let hq = cite(bvv::TWO_POW_POS, [lc.clone()]);
    let (vc, vx, vnc) = (val(&c), val(&x), val(&nc));
    let one = || nlit(1);

    // Lengths.
    let l_inner = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![c.clone(), x.clone(), f.clone()],
        len(&inner),
        lc.clone(),
    );
    let hl = Eqn::cite(
        add_comm::names::LEN_ADD_REC_M,
        vec![inner.clone(), nc.clone(), t.clone()],
        len(&lhs),
        len(&inner),
    )
    .then(l_inner.clone())
    .then(h.clone());

    // V lhs = V x % P (L x).
    let s0 = nadd(nadd(val(&inner), vnc.clone()), btn(t.clone()));
    let s = nadd(vc.clone(), vx.clone());
    let sf = nadd(s.clone(), btn(f.clone()));
    let sq = nmod(s.clone(), q.clone());
    let not_one = nadd(vnc.clone(), one());
    let r1 = ring_eq(
        &mut fr,
        &nadd(nadd(sq.clone(), vnc.clone()), one()),
        &nadd(sq.clone(), not_one.clone()),
    )?;
    let r2 = ring_eq(
        &mut fr,
        &nadd(s.clone(), not_one.clone()),
        &nadd(vx.clone(), nadd(nadd(vnc.clone(), vc.clone()), one())),
    )?;
    let r3 =
        ring_eq(&mut fr, &nadd(vx.clone(), q.clone()), &nadd(vx.clone(), nmul(q.clone(), one())))?;
    let (s0c, vnc1, t1, q1) = (s0.clone(), vnc.clone(), t.clone(), q.clone());
    let (vnc2, t2, q2) = (vnc.clone(), t.clone(), q.clone());
    let (q3, q4, q5, q6, q7) = (q.clone(), q.clone(), q.clone(), q.clone(), q.clone());
    let (vx1, vx2) = (vx.clone(), vx.clone());
    let left = Eqn::cite(
        bvv::ADD_REC_M_VAL,
        vec![inner.clone(), nc.clone(), t.clone()],
        val(&lhs),
        nmod(s0, two_pow(len(&inner))),
    )
    .then(l_inner.under(&mut fr, |u| nmod(s0c.clone(), two_pow(u))))
    .then(
        Eqn::cite(
            bvv::ADD_REC_M_VAL,
            vec![c.clone(), x.clone(), f.clone()],
            val(&inner),
            nmod(sf.clone(), q.clone()),
        )
        .under(&mut fr, |u| nmod(nadd(nadd(u, vnc1.clone()), btn(t1.clone())), q1.clone())),
    )
    // `btn false` is `0`, and `s + 0` is `s`.
    .then(Eqn::by_defeq(sf, s.clone()).under(&mut fr, |u| {
        nmod(nadd(nadd(nmod(u, q2.clone()), vnc2.clone()), btn(t2.clone())), q2.clone())
    }))
    // `btn true` is `1`.
    .then(
        Eqn::by_defeq(
            nadd(nadd(sq.clone(), vnc.clone()), btn(t.clone())),
            nadd(nadd(sq.clone(), vnc.clone()), one()),
        )
        .under(&mut fr, |u| nmod(u, q3.clone())),
    )
    .then(r1.under(&mut fr, |u| nmod(u, q4.clone())))
    .then(Eqn::cite(
        bvv::MOD_ADD_MOD,
        vec![s.clone(), not_one.clone(), q.clone(), hq.clone()],
        nmod(nadd(sq, not_one.clone()), q.clone()),
        nmod(nadd(s, not_one), q.clone()),
    ))
    .then(r2.under(&mut fr, |u| nmod(u, q5.clone())))
    .then(
        Eqn::cite(bvv::BV_NOT_VAL, vec![c.clone()], nadd(nadd(vnc, vc), one()), q.clone())
            .under(&mut fr, |u| nmod(nadd(vx1.clone(), u), q6.clone())),
    )
    .then(r3.under(&mut fr, |u| nmod(u, q7.clone())))
    .then(Eqn::cite(
        bvv::ADD_MUL_MOD_SELF,
        vec![vx.clone(), q.clone(), one(), hq],
        nmod(nadd(vx.clone(), nmul(q.clone(), one())), q.clone()),
        nmod(vx.clone(), q),
    ))
    .then(h.under(&mut fr, |u| nmod(vx2.clone(), two_pow(u))));

    // V x % P (L x) = V x.
    let nx = nat_to_bv(lx.clone(), vx.clone());
    let right = Eqn::cite(
        bvv::TO_NAT_NAT_TO_BV,
        vec![lx.clone(), vx.clone()],
        val(&nx),
        nmod(vx.clone(), two_pow(lx)),
    )
    .symm()
    .then(Eqn {
        lhs: val(&nx),
        rhs: vx,
        proof: congr_arg(
            lb(),
            nat(),
            nx,
            x.clone(),
            Expr::const_str("Clean.BVC.bvToNat"),
            cite(bvv::NAT_TO_BV_TO_NAT, [x.clone()]),
        ),
    });
    let hv = left.then(right);
    Some((ty, lams(binders, inj(&lhs, &x, hl, hv))))
}

// ── registration and the audited environment ─────────────────────────────────

/// The theorem: `(name, statement, proof)`. `Err` says the normaliser declined
/// a step, which is a bug here, never a reason to admit anything.
pub(crate) fn theorems() -> Result<Vec<(&'static str, Expr, Expr)>, String> {
    let (ty, val) = add_sub_cancel()
        .ok_or_else(|| format!("{}: the normaliser declined a step", names::ADD_SUB_CANCEL))?;
    Ok(vec![(names::ADD_SUB_CANCEL, ty, val)])
}

/// Every name the cancel layer audits on top of the strength base: the
/// theorem, its citations, and every theorem a ring step may cite.
pub(crate) fn audited() -> Vec<&'static str> {
    let mut all: Vec<&'static str> = names::ALL.to_vec();
    all.extend(CITED);
    all.extend(nat_ring::CITED);
    all.extend(nat_ring::names::ALL);
    all
}

/// `base` (which must carry the value theory) plus the theorem, audited. Each
/// is a `Declaration::Theorem`, so `add_decl` type-checks its proof against
/// its statement. Split from [`cancel_base`] so a test can hand it a doctored
/// base.
fn build_base(mut env: Environment) -> Result<Environment, String> {
    for (name, type_, value) in theorems()? {
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
        })
        .map_err(|e| format!("{name}: {e:?}"))?;
    }
    audit_theorems(&env, &audited())?;
    Ok(env)
}

/// The strength base plus `add_sub_cancel`, built and audited once per
/// process. `Err` (the strength base failed, the theorem did not register, or
/// the audit failed) is kept for the life of the process, and the route built
/// on it declines. A panic inside the build is kept as `Err` too. Call it on a
/// kernel re-check thread (the build type-checks deep terms).
pub(crate) fn cancel_base() -> Result<&'static Environment, String> {
    static BASE: OnceLock<Result<Environment, String>> = OnceLock::new();
    BASE.get_or_init(|| {
        std::panic::catch_unwind(|| build_base(strength::strength_base()?.clone()))
            .unwrap_or_else(|_| Err("the cancel base build panicked".to_string()))
    })
    .as_ref()
    .map_err(Clone::clone)
}

/// The environment a cancel discharge is checked in: [`cancel_base`] and one
/// opaque `Bool` per bit of each variable (`add_comm::bit_leaf`).
pub(crate) fn cancel_env(leaves: &[(String, u32)]) -> Result<Environment, String> {
    let mut env = cancel_base()?.clone();
    add_comm::add_leaf_bits(&mut env, leaves);
    Ok(env)
}

/// The label of a function proved through this route: the strength theorems
/// used (first-use order, each once), then `add_sub_cancel`,
/// `Trust.BVC.addRecM_comm` only when an `Add` was reordered, then
/// [`LABEL_TAIL`].
pub(crate) fn label(used: &[&'static str], add_swaps: usize) -> String {
    let mut parts: Vec<&str> = Vec::new();
    for name in used.iter().filter(|n| strength::names::ALL.contains(n)) {
        if !parts.contains(name) {
            parts.push(name);
        }
    }
    for name in used.iter().filter(|n| names::ALL.contains(n)) {
        if !parts.contains(name) {
            parts.push(name);
        }
    }
    debug_assert!(
        used.iter().all(|n| strength::names::ALL.contains(n) || names::ALL.contains(n)),
        "{used:?} names a theorem of neither family"
    );
    if add_swaps > 0 {
        parts.push(add_comm::names::ADD_REC_M_COMM);
    }
    parts.push(LABEL_TAIL);
    parts.join("+")
}

// ── the per-obligation step ──────────────────────────────────────────────────

/// `(p, w)` with `p : bvLen (bvfEval x) = w`, for `w` in [`WIDTHS`].
fn width_of(x: &Expr) -> Option<(Expr, u32)> {
    core_len(x).filter(|(_, w)| WIDTHS.contains(w))
}

/// `add_sub_cancel` at a `Sub` node whose children's cores are `l = Add c x`
/// and `r = c` (structurally), with `c` and `x` of one provable width
/// `w ∈ {32, 64}`: rewritten to `x`.
pub(crate) fn sub_cancel_step(l: &Expr, r: &Expr) -> Option<Step> {
    let cx = app_of(l, "Clean.BVC.BvF.Add", 2)?;
    let (c, x) = (cx[0], cx[1]);
    if c != r {
        return None;
    }
    let (pc, wc) = width_of(c)?;
    let (px, wx) = width_of(x)?;
    if wc != wx {
        return None;
    }
    let (ec, ex) = (kx::evalf(c.clone()), kx::evalf(x.clone()));
    let n = kx::nat_lit(wc);
    let h = trans(nat(), len(&ec), n.clone(), len(&ex), pc, symm(nat(), len(&ex), n, px));
    Some(Step {
        theorem: names::ADD_SUB_CANCEL,
        before: kx::sub(l.clone(), r.clone()),
        core: x.clone(),
        proof: cite(names::ADD_SUB_CANCEL, [ec, ex, h]),
    })
}

#[cfg(test)]
#[path = "cancel/tests.rs"]
mod tests;
