// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The value theory `Trust.BVV.*`: order, division and remainder, and powers
//! of two over `Nat`, the value of a bit, and the values and lengths of the
//! `Clean.BVC` / `Clean.BVI` list operations (adder, multiplier, complement,
//! append, conversion to and from `Nat`), as kernel-checked
//! `Declaration::Theorem`s.
//!
//! # Why
//!
//! The strength-reduction rewrites (shift-to-multiply, collecting a multiply
//! with an add or a subtract) are statements about `Clean.BVC` bit lists, and
//! their proofs go through the lists' values: `bvToNat`, `bvTwoPow`, `% 2^w`.
//! The pinned prelude proves `Nat.div_add_mod` and `Nat.mod_lt` but none of
//! the modular-arithmetic lemmas those proofs need (`Nat.add_mod`,
//! `Nat.mod_add_div`, `Nat.add_mul_mod_self_left`, `Nat.mod_self` and others
//! are absent, measured by `add_comm::tests::prelude_lemma_inventory`), and
//! nothing relates the `Clean.BVC` list operations to their `Nat` values. This
//! module proves both from what is there.
//!
//! # What is proved
//!
//! ```text
//! zero_le          : ∀ n, 0 ≤ n
//! add_le_add_right : ∀ a b c, a ≤ b → a + c ≤ b + c
//! lt_of_lt_of_le   : ∀ a b c, a < b → b ≤ c → a < c
//! lt_le_false      : ∀ a b, a < b → b ≤ a → False
//! pos_of_lt        : ∀ r n, r < n → 0 < n
//! div_mod_cancel   : ∀ n d q m r, m < n → r < n → n*d + m = n*q + r → d = q
//! mod_unique       : ∀ a n q r, r < n → a = r + n*q → a % n = r
//! div_unique       : ∀ a n q r, r < n → a = r + n*q → a / n = q
//! mod_one          : ∀ a, a % 1 = 0
//! add_mul_mod_self : ∀ a n q, 0 < n → (a + n*q) % n = a % n
//! mod_add_mod      : ∀ a b n, 0 < n → (a % n + b) % n = (a + b) % n
//! add_mod_mod      : ∀ a b n, 0 < n → (a + b % n) % n = (a + b) % n
//! bit_split_mod    : ∀ b m p, b < 2 → 0 < p → (b + 2*m) % (2*p) = b + 2*(m % p)
//! two_pow_pos      : ∀ k, 0 < 2^k
//! two_pow_add      : ∀ a b, 2^(a + b) = 2^a * 2^b
//! add_mul_mod_mod  : ∀ a c q n, 0 < n → (a + c * (q % n)) % n = (a + c * q) % n
//!
//! btn_lt_two       : ∀ b, btn b < 2
//! ble_btn          : ∀ b, Nat.ble 1 (btn b) = b
//! btn_ble          : ∀ r, r < 2 → btn (Nat.ble 1 r) = r
//! btn_not          : ∀ b, btn (!b) + btn b = 1
//! full_adder       : ∀ a b c, btn a + btn b + btn c = btn (xor3 a b c) + 2 * btn (maj a b c)
//!
//! toNat_head_tail  : ∀ ys, V ys = btn (bhead ys) + 2 * V (btail ys)
//! addRecM_val      : ∀ xs ys c, V (addRecM xs ys c) = (V xs + V ys + btn c) % 2^(L xs)
//! len_natToBv      : ∀ w v, L (natToBvAux w v) = w
//! toNat_natToBv    : ∀ w v, V (natToBvAux w v) = v % 2^w
//! natToBv_toNat    : ∀ xs, natToBvAux (L xs) (V xs) = xs
//! inj              : ∀ xs ys, L xs = L ys → V xs = V ys → xs = ys
//! toNat_allFalse   : ∀ b, V (bvAllFalse b) = 0
//! bvMul_val        : ∀ a b, V (bvMul a b) = (V a * V b) % 2^(L b)
//! bvNot_val        : ∀ xs, V (bvNot xs) + V xs + 1 = 2^(L xs)
//! toNat_append     : ∀ xs ys, V (xs ++ ys) = V xs + 2^(L xs) * V ys
//! len_append       : ∀ xs ys, L (xs ++ ys) = L xs + L ys
//! toNat_replF      : ∀ k, V (bvReplF k) = 0
//! len_replF        : ∀ k, L (bvReplF k) = k
//! ```
//!
//! Every operator is the raw constant (`Nat.add`, `Nat.mul`, `Nat.mod`,
//! `Nat.div`, `Nat.le`, `Nat.lt`), `2^k` is `Clean.BVC.bvTwoPow k`, and the
//! literals `0`, `1`, `2` are `Expr::nat_lit`, the literals `bvToNat` and
//! `bvTwoPow` are written with. `V` is `Clean.BVC.bvToNat`, `L` is
//! `Clean.BVC.bvLen`, and `btn b` is the one definition this module adds,
//! `Trust.BVV.btn b := Bool.rec (fun _ => Nat) 0 1 b`, the inline bit value of
//! `bvToNat`, so `V (b :: t)` unfolds to `btn b + 2 * V t`.
//!
//! The list lemmas hold over untyped `List Bool` with no length premise
//! except `inj`'s: `addRecM` and `bvMul` take their result length from one
//! operand (`xs`, resp. `b`), and `bhead [] = false`, `btail [] = []`, so the
//! statements are true at every length, `[]` included. `bvMul_val`'s cons
//! case is a `Bool.rec` on the multiplier bit over the whole equation, so the
//! selected addend (`b` or `bvAllFalse b`) is concrete in each branch and its
//! length rewrites to `L b` (`Trust.BVC.len_allFalse`).
//!
//! No trichotomy: `div_mod_cancel` is an induction on the first quotient,
//! generalising the second, with a case split on it. The two mixed cases are
//! absurd because a remainder below `n` would be at least `n`; the successor
//! case cancels one `n` and uses the induction hypothesis. Uniqueness of `%`
//! and `/` follows from it and the prelude's `Nat.div_add_mod` / `Nat.mod_lt`.
//!
//! # Authority
//!
//! Nothing here decides anything. [`register`] adds each statement and proof
//! as a `Declaration::Theorem`, so `add_decl` type-checks the proof against the
//! statement, and then audits every theorem this module proves and every
//! prelude lemma a proof cites ([`audited`]): each must be a `Theorem` that
//! carries its proof and reaches no axiom, domain or foundational
//! (`add_comm::audit_theorems`). The `+`/`*` rearrangements inside the proofs
//! come from the untrusted normaliser `nat_ring`; the kernel checks them as
//! part of each declaration.
//!
//! # Kernel cost
//!
//! Every statement is universally quantified, so the kernel computes on no
//! closed data while checking these proofs: the only reductions are the
//! defeqs `x + 0 ≡ x`, `x * succ y ≡ x * y + x`, `2^(succ k) ≡ 2 * 2^k`,
//! one-step unfoldings of the list recursors at a `cons` (`V (b :: t)`,
//! `addRecM (a :: as) ys c`, `natToBvAux (succ k) v`, …), the Boolean gates
//! and `btn` at ground bits, literal arithmetic on the coefficients `0`, `1`,
//! `2`, and instance unfolding of the prelude's `≤` / `<` notation. Nothing
//! applies `Nat.mod`, `Nat.div`, `bvTwoPow`, `natToBvAux`, `bvMul` or `bvShl`
//! to closed data (test
//! `every_citation_is_audited_and_nothing_computes_on_closed_data`).

use clean_kernel::name::Name;
use clean_kernel::{Declaration, Environment, Expr, FVarId, Level};

use super::add_comm::{self, audit_theorems};
use super::kterm::{
    Fresh, addm, bhead, bool_rec, bool_ty, btail, bv_append, bvlen, bvmul, congr_arg, eq, eq_subst,
    false_elim, l1, lams, lb, le_refl, le_step, list_rec_prop, maj, nadd, nat, nat_rec_prop,
    nat_to_bv, nble, ndiv, nle, nlit, nlt, nmod, nmul, pis, refl, repl_f, succ, symm, to_nat,
    trans, two_pow, xor3, zero,
};
use super::kx;
use super::nat_ring::{self, Eqn, ring_eq, ring_rw};

/// The theorems this module proves (besides `nat_ring`'s helpers).
pub(crate) mod names {
    pub(crate) const ZERO_LE: &str = "Trust.BVV.zero_le";
    pub(crate) const ADD_LE_ADD_RIGHT: &str = "Trust.BVV.add_le_add_right";
    pub(crate) const LT_OF_LT_OF_LE: &str = "Trust.BVV.lt_of_lt_of_le";
    pub(crate) const LT_LE_FALSE: &str = "Trust.BVV.lt_le_false";
    pub(crate) const POS_OF_LT: &str = "Trust.BVV.pos_of_lt";
    pub(crate) const DIV_MOD_CANCEL: &str = "Trust.BVV.div_mod_cancel";
    pub(crate) const MOD_UNIQUE: &str = "Trust.BVV.mod_unique";
    pub(crate) const DIV_UNIQUE: &str = "Trust.BVV.div_unique";
    pub(crate) const MOD_ONE: &str = "Trust.BVV.mod_one";
    pub(crate) const ADD_MUL_MOD_SELF: &str = "Trust.BVV.add_mul_mod_self";
    pub(crate) const MOD_ADD_MOD: &str = "Trust.BVV.mod_add_mod";
    pub(crate) const ADD_MOD_MOD: &str = "Trust.BVV.add_mod_mod";
    pub(crate) const BIT_SPLIT_MOD: &str = "Trust.BVV.bit_split_mod";
    pub(crate) const TWO_POW_POS: &str = "Trust.BVV.two_pow_pos";
    pub(crate) const TWO_POW_ADD: &str = "Trust.BVV.two_pow_add";
    pub(crate) const ADD_MUL_MOD_MOD: &str = "Trust.BVV.add_mul_mod_mod";
    pub(crate) const BTN_LT_TWO: &str = "Trust.BVV.btn_lt_two";
    pub(crate) const BLE_BTN: &str = "Trust.BVV.ble_btn";
    pub(crate) const BTN_BLE: &str = "Trust.BVV.btn_ble";
    pub(crate) const BTN_NOT: &str = "Trust.BVV.btn_not";
    pub(crate) const FULL_ADDER: &str = "Trust.BVV.full_adder";
    pub(crate) const TO_NAT_HEAD_TAIL: &str = "Trust.BVV.toNat_head_tail";
    pub(crate) const ADD_REC_M_VAL: &str = "Trust.BVV.addRecM_val";
    pub(crate) const LEN_NAT_TO_BV: &str = "Trust.BVV.len_natToBv";
    pub(crate) const TO_NAT_NAT_TO_BV: &str = "Trust.BVV.toNat_natToBv";
    pub(crate) const NAT_TO_BV_TO_NAT: &str = "Trust.BVV.natToBv_toNat";
    pub(crate) const INJ: &str = "Trust.BVV.inj";
    pub(crate) const TO_NAT_ALL_FALSE: &str = "Trust.BVV.toNat_allFalse";
    pub(crate) const BV_MUL_VAL: &str = "Trust.BVV.bvMul_val";
    pub(crate) const BV_NOT_VAL: &str = "Trust.BVV.bvNot_val";
    pub(crate) const TO_NAT_APPEND: &str = "Trust.BVV.toNat_append";
    pub(crate) const LEN_APPEND: &str = "Trust.BVV.len_append";
    pub(crate) const TO_NAT_REPL_F: &str = "Trust.BVV.toNat_replF";
    pub(crate) const LEN_REPL_F: &str = "Trust.BVV.len_replF";
    pub(crate) const ALL: [&str; 34] = [
        ZERO_LE,
        ADD_LE_ADD_RIGHT,
        LT_OF_LT_OF_LE,
        LT_LE_FALSE,
        POS_OF_LT,
        DIV_MOD_CANCEL,
        MOD_UNIQUE,
        DIV_UNIQUE,
        MOD_ONE,
        ADD_MUL_MOD_SELF,
        MOD_ADD_MOD,
        ADD_MOD_MOD,
        BIT_SPLIT_MOD,
        TWO_POW_POS,
        TWO_POW_ADD,
        ADD_MUL_MOD_MOD,
        BTN_LT_TWO,
        BLE_BTN,
        BTN_BLE,
        BTN_NOT,
        FULL_ADDER,
        TO_NAT_HEAD_TAIL,
        ADD_REC_M_VAL,
        LEN_NAT_TO_BV,
        TO_NAT_NAT_TO_BV,
        NAT_TO_BV_TO_NAT,
        INJ,
        TO_NAT_ALL_FALSE,
        BV_MUL_VAL,
        BV_NOT_VAL,
        TO_NAT_APPEND,
        LEN_APPEND,
        TO_NAT_REPL_F,
        LEN_REPL_F,
    ];
    /// The one definition this module adds (not a theorem, so not audited as
    /// one): `btn b := Bool.rec (fun _ => Nat) 0 1 b`, the bit's value.
    pub(crate) const BTN: &str = "Trust.BVV.btn";
}

/// The bridge theorems from `add_comm` the proofs here cite.
pub(crate) const BRIDGE_CITED: [&str; 1] = [add_comm::names::LEN_ALL_FALSE];

/// The prelude theorems the proofs here cite directly (the normaliser's own
/// citations are `nat_ring::CITED`). Each is in the pinned inventory
/// (`add_comm::tests::prelude_lemma_inventory`) as a proved `Theorem` with an
/// empty axiom closure, and [`register`] audits it again at run time.
pub(crate) const PRELUDE_CITED: [&str; 12] = [
    "Nat.succ_le_succ",
    "Nat.le_trans",
    "Nat.lt_irrefl",
    "Nat.le_add_right",
    "Nat.add_left_cancel",
    "Nat.mul_le_mul_left",
    "Nat.div_add_mod",
    "Nat.mod_lt",
    "congrArg",
    "Eq.subst",
    "Eq.trans",
    "Eq.symm",
];

/// Every name [`register`] audits: the normaliser's helper theorems and
/// citations, this module's theorems, and its prelude citations.
pub(crate) fn audited() -> Vec<&'static str> {
    let mut all: Vec<&'static str> = nat_ring::names::ALL.to_vec();
    all.extend(nat_ring::CITED);
    all.extend(names::ALL);
    all.extend(PRELUDE_CITED);
    all.extend(BRIDGE_CITED);
    all
}

/// `Trust.BVV.btn b`, the value of a bit (`0` or `1`).
pub(crate) fn btn(b: Expr) -> Expr {
    Expr::app(Expr::const_str(names::BTN), b)
}

/// `btn`'s statement and body: `Bool → Nat`,
/// `fun b => Bool.rec.{1} (fun _ => Nat) 0 1 b`, with the literals
/// `bvToNat` is written with, so `bvToNat (b :: t)` unfolds to
/// `btn b + 2 * bvToNat t` (delta on `btn`, iota on the list).
fn btn_definition() -> (Expr, Expr) {
    let mut fr = Fresh::new();
    let (b_id, b) = fr.local();
    let motive = {
        let (w_id, _) = fr.local();
        lams(vec![(w_id, bool_ty())], nat())
    };
    let body = bool_rec(l1(), motive, nlit(0), nlit(1), b);
    (Expr::arrow(bool_ty(), nat()), lams(vec![(b_id, bool_ty())], body))
}

/// The definitions [`register`] adds before the theorems: `(name, type, value)`.
pub(crate) fn definitions() -> Vec<(&'static str, Expr, Expr)> {
    let (ty, val) = btn_definition();
    vec![(names::BTN, ty, val)]
}

// ── small builders ───────────────────────────────────────────────────────────

fn cite(name: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::apps(Expr::const_str(name), args)
}

/// From `h : a ≤ b`, a proof of `a2 ≤ b2` when `a2 = a` and `b = b2` as
/// polynomials (`nat_ring`), by `Eq.subst` on each side.
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

/// `False`, from `hx : x < n` and `e : x = n + k` (then `n ≤ x`).
fn absurd_below(fr: &mut Fresh, x: &Expr, n: &Expr, k: &Expr, hx: Expr, e: Eqn) -> Expr {
    let base = cite("Nat.le_add_right", [n.clone(), k.clone()]);
    let (t_id, t) = fr.local();
    let motive = lams(vec![(t_id, nat())], nle(n.clone(), t));
    let le_nx =
        eq_subst(nat(), motive, nadd(n.clone(), k.clone()), x.clone(), e.symm().proof, base);
    cite(names::LT_LE_FALSE, [x.clone(), n.clone(), hx, le_nx])
}

/// A fresh `Nat` local: its binder `(id, Nat)` and the variable.
fn nat_local(fr: &mut Fresh) -> ((clean_kernel::FVarId, Expr), Expr) {
    let (id, v) = fr.local();
    ((id, nat()), v)
}

// ── order ────────────────────────────────────────────────────────────────────

/// `zero_le : ∀ n, 0 ≤ n`, by induction: `le.refl 0`, then `le.step`.
fn zero_le() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bn, n) = nat_local(&mut fr);
    let ty = pis(vec![bn.clone()], nle(nlit(0), n.clone()));
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        lams(vec![bt], nle(nlit(0), t))
    };
    let step = {
        let (bk, k) = nat_local(&mut fr);
        let (ih_id, ih) = fr.local();
        lams(vec![bk, (ih_id, nle(nlit(0), k.clone()))], le_step(nlit(0), k, ih))
    };
    let val = lams(vec![bn], nat_rec_prop(motive, le_refl(nlit(0)), step, n));
    Some((ty, val))
}

/// `add_le_add_right : ∀ a b c, a ≤ b → a + c ≤ b + c`, by induction on `c`
/// (`x + succ k ≡ succ (x + k)`, then `Nat.succ_le_succ`).
fn add_le_add_right() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bb, b) = nat_local(&mut fr);
    let (bc, c) = nat_local(&mut fr);
    let (h_id, h) = fr.local();
    let concl = |t: &Expr| nle(nadd(a.clone(), t.clone()), nadd(b.clone(), t.clone()));
    let binders = vec![ba, bb, bc, (h_id, nle(a.clone(), b.clone()))];
    let ty = pis(binders.clone(), concl(&c));
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        lams(vec![bt], concl(&t))
    };
    let step = {
        let (bk, k) = nat_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let body =
            cite("Nat.succ_le_succ", [nadd(a.clone(), k.clone()), nadd(b.clone(), k.clone()), ih]);
        lams(vec![bk, (ih_id, concl(&k))], body)
    };
    let val = lams(binders, nat_rec_prop(motive, h, step, c));
    Some((ty, val))
}

/// `lt_of_lt_of_le : ∀ a b c, a < b → b ≤ c → a < c` over the raw `Nat.lt` /
/// `Nat.le` (the prelude's is stated with the `<` / `≤` instances):
/// `a < b` is `succ a ≤ b`, then `Nat.le_trans`.
fn lt_of_lt_of_le() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bb, b) = nat_local(&mut fr);
    let (bc, c) = nat_local(&mut fr);
    let (h1_id, h1) = fr.local();
    let (h2_id, h2) = fr.local();
    let binders =
        vec![ba, bb, bc, (h1_id, nlt(a.clone(), b.clone())), (h2_id, nle(b.clone(), c.clone()))];
    let ty = pis(binders.clone(), nlt(a.clone(), c.clone()));
    let val = lams(binders, cite("Nat.le_trans", [succ(a), b, c, h1, h2]));
    Some((ty, val))
}

/// `lt_le_false : ∀ a b, a < b → b ≤ a → False`: `succ a ≤ a` contradicts
/// `Nat.lt_irrefl`.
fn lt_le_false() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bb, b) = nat_local(&mut fr);
    let (h1_id, h1) = fr.local();
    let (h2_id, h2) = fr.local();
    let binders =
        vec![ba, bb, (h1_id, nlt(a.clone(), b.clone())), (h2_id, nle(b.clone(), a.clone()))];
    let ty = pis(binders.clone(), Expr::const_str("False"));
    let saa = cite("Nat.le_trans", [succ(a.clone()), b, a.clone(), h1, h2]);
    let val = lams(binders, cite("Nat.lt_irrefl", [a, saa]));
    Some((ty, val))
}

/// `pos_of_lt : ∀ r n, r < n → 0 < n`: `1 ≤ succ r ≤ n`.
fn pos_of_lt() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (br, r) = nat_local(&mut fr);
    let (bn, n) = nat_local(&mut fr);
    let (h_id, h) = fr.local();
    let binders = vec![br, bn, (h_id, nlt(r.clone(), n.clone()))];
    let ty = pis(binders.clone(), nlt(nlit(0), n.clone()));
    let one_le = cite("Nat.succ_le_succ", [nlit(0), r.clone(), cite(names::ZERO_LE, [r.clone()])]);
    let val = lams(binders, cite("Nat.le_trans", [succ(nlit(0)), succ(r), n, one_le, h]));
    Some((ty, val))
}

// ── division and remainder ───────────────────────────────────────────────────

/// `div_mod_cancel : ∀ n d q m r, m < n → r < n → n*d + m = n*q + r → d = q`.
///
/// Induction on `d` generalising `q`, and a case split on `q` (a `Nat.rec`
/// whose hypothesis is unused):
/// - `0, 0`: `Eq.refl`.
/// - `0, succ k`: `m = n + (n*k + r)`, so `n ≤ m`, against `m < n`.
/// - `succ d', 0`: `r = n + (n*d' + m)`, so `n ≤ r`, against `r < n`.
/// - `succ d', succ k`: `n + (n*d' + m) = n + (n*k + r)`; cancel `n`
///   (`Nat.add_left_cancel`), the induction hypothesis gives `d' = k`.
fn div_mod_cancel() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bn, n) = nat_local(&mut fr);
    let (bd, d) = nat_local(&mut fr);
    let (bq, q) = nat_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (br, r) = nat_local(&mut fr);
    let (hm_id, hm) = fr.local();
    let (hr_id, hr) = fr.local();
    let (h_id, h) = fr.local();
    let lhs = |d: &Expr| nadd(nmul(n.clone(), d.clone()), m.clone());
    let rhs = |q: &Expr| nadd(nmul(n.clone(), q.clone()), r.clone());
    let hyp = |d: &Expr, q: &Expr| eq(nat(), lhs(d), rhs(q));
    let concl = |d: &Expr, q: &Expr| eq(nat(), d.clone(), q.clone());
    let binders = vec![
        bn,
        bd,
        bq,
        bm,
        br,
        (hm_id, nlt(m.clone(), n.clone())),
        (hr_id, nlt(r.clone(), n.clone())),
        (h_id, hyp(&d, &q)),
    ];
    let ty = pis(binders.clone(), concl(&d, &q));

    // ∀ q, hyp t q → t = q
    let all_q = |fr: &mut Fresh, t: &Expr| {
        let (bs, s) = nat_local(fr);
        pis(vec![bs], Expr::arrow(hyp(t, &s), concl(t, &s)))
    };
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        let body = all_q(&mut fr, &t);
        lams(vec![bt], body)
    };
    // fun s => hyp dd s → dd = s
    let inner_motive = |fr: &mut Fresh, dd: &Expr| {
        let (bs, s) = nat_local(fr);
        lams(vec![bs], Expr::arrow(hyp(dd, &s), concl(dd, &s)))
    };

    let zero_case = {
        let (bqq, qq) = nat_local(&mut fr);
        let z0 = {
            let (h0_id, _) = fr.local();
            lams(vec![(h0_id, hyp(&zero(), &zero()))], refl(nat(), zero()))
        };
        let zs = {
            let (bk, k) = nat_local(&mut fr);
            let (ih_id, _) = fr.local();
            let (h1_id, h1) = fr.local();
            let sk = succ(k.clone());
            let rest = nadd(nmul(n.clone(), k.clone()), r.clone());
            let e = Eqn { lhs: lhs(&zero()), rhs: rhs(&sk), proof: h1 };
            let e = ring_rw(&mut fr, e, &m, &nadd(n.clone(), rest.clone()))?;
            let contra = absurd_below(&mut fr, &m, &n, &rest, hm.clone(), e);
            lams(
                vec![
                    bk,
                    (ih_id, Expr::arrow(hyp(&zero(), &k), concl(&zero(), &k))),
                    (h1_id, hyp(&zero(), &sk)),
                ],
                false_elim(concl(&zero(), &sk), contra),
            )
        };
        let im = inner_motive(&mut fr, &zero());
        lams(vec![bqq], nat_rec_prop(im, z0, zs, qq))
    };

    let succ_case = {
        let (bdp, dp) = nat_local(&mut fr);
        let ih_ty = all_q(&mut fr, &dp);
        let (ih_id, ih) = fr.local();
        let (bqq, qq) = nat_local(&mut fr);
        let sd = succ(dp.clone());
        let s0 = {
            let (h0_id, h0) = fr.local();
            let rest = nadd(nmul(n.clone(), dp.clone()), m.clone());
            let e = Eqn { lhs: lhs(&sd), rhs: rhs(&zero()), proof: h0 }.symm();
            let e = ring_rw(&mut fr, e, &r, &nadd(n.clone(), rest.clone()))?;
            let contra = absurd_below(&mut fr, &r, &n, &rest, hr.clone(), e);
            lams(vec![(h0_id, hyp(&sd, &zero()))], false_elim(concl(&sd, &zero()), contra))
        };
        let ss = {
            let (bk, k) = nat_local(&mut fr);
            let (ih2_id, _) = fr.local();
            let (h1_id, h1) = fr.local();
            let sk = succ(k.clone());
            let left = nadd(nmul(n.clone(), dp.clone()), m.clone());
            let right = nadd(nmul(n.clone(), k.clone()), r.clone());
            let e = Eqn { lhs: lhs(&sd), rhs: rhs(&sk), proof: h1 };
            let e = ring_rw(
                &mut fr,
                e,
                &nadd(n.clone(), left.clone()),
                &nadd(n.clone(), right.clone()),
            )?;
            let cancel = cite("Nat.add_left_cancel", [n.clone(), left, right, e.proof]);
            let dk = Expr::apps(ih.clone(), [k.clone(), cancel]);
            let body =
                congr_arg(nat(), nat(), dp.clone(), k.clone(), Expr::const_str("Nat.succ"), dk);
            lams(
                vec![
                    bk,
                    (ih2_id, Expr::arrow(hyp(&sd, &k), concl(&sd, &k))),
                    (h1_id, hyp(&sd, &sk)),
                ],
                body,
            )
        };
        let im = inner_motive(&mut fr, &sd);
        lams(vec![bdp, (ih_id, ih_ty), bqq], nat_rec_prop(im, s0, ss, qq))
    };

    let val = lams(binders, Expr::apps(nat_rec_prop(motive, zero_case, succ_case, d), [q, h]));
    Some((ty, val))
}

/// `mod_unique` (`want_mod`) or `div_unique`:
/// `∀ a n q r, r < n → a = r + n*q → a % n = r` (resp. `a / n = q`).
///
/// `(a/n)*n + a%n = a` (`Nat.div_add_mod`) and the premise give
/// `n*(a/n) + a%n = n*q + r`; with `a%n < n` (`Nat.mod_lt`, `0 < n` from
/// `r < n`) `div_mod_cancel` gives `a/n = q`; substituting it and cancelling
/// `n*q` gives `a%n = r`.
fn mod_div_unique(want_mod: bool) -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bn, n) = nat_local(&mut fr);
    let (bq, q) = nat_local(&mut fr);
    let (br, r) = nat_local(&mut fr);
    let (hr_id, hr) = fr.local();
    let (h_id, h) = fr.local();
    let split = nadd(r.clone(), nmul(n.clone(), q.clone()));
    let binders = vec![
        ba,
        bn,
        bq,
        br,
        (hr_id, nlt(r.clone(), n.clone())),
        (h_id, eq(nat(), a.clone(), split.clone())),
    ];
    let (qa, ra) = (ndiv(a.clone(), n.clone()), nmod(a.clone(), n.clone()));
    let concl =
        if want_mod { eq(nat(), ra.clone(), r.clone()) } else { eq(nat(), qa.clone(), q.clone()) };
    let ty = pis(binders.clone(), concl);

    let hpos = cite(names::POS_OF_LT, [r.clone(), n.clone(), hr.clone()]);
    let hlt = cite("Nat.mod_lt", [a.clone(), n.clone(), hpos]);
    let dam = Eqn::cite(
        "Nat.div_add_mod",
        vec![a.clone(), n.clone()],
        nadd(nmul(qa.clone(), n.clone()), ra.clone()),
        a.clone(),
    );
    let whole = dam.then(Eqn { lhs: a.clone(), rhs: split, proof: h });
    let nq_r = nadd(nmul(n.clone(), q.clone()), r.clone());
    let e = ring_rw(&mut fr, whole, &nadd(nmul(n.clone(), qa.clone()), ra.clone()), &nq_r)?;
    let dq = cite(
        names::DIV_MOD_CANCEL,
        [n.clone(), qa.clone(), q.clone(), ra.clone(), r.clone(), hlt, hr, e.proof.clone()],
    );
    let body = if want_mod {
        // n*q + a%n = n*q + r, then cancel n*q.
        let (bt, t) = nat_local(&mut fr);
        let motive = lams(vec![bt], eq(nat(), nadd(nmul(n.clone(), t), ra.clone()), nq_r.clone()));
        let e2 = eq_subst(nat(), motive, qa, q.clone(), dq, e.proof);
        cite("Nat.add_left_cancel", [nmul(n, q), ra, r, e2])
    } else {
        dq
    };
    Some((ty, lams(binders, body)))
}

/// `mod_one : ∀ a, a % 1 = 0`: `mod_unique a 1 a 0`, with `0 < 1` by
/// `Nat.le.refl 1` and `a = 0 + 1*a` by the normaliser.
fn mod_one() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let ty = pis(vec![ba.clone()], eq(nat(), nmod(a.clone(), nlit(1)), nlit(0)));
    let split = ring_eq(&mut fr, &a, &nadd(nlit(0), nmul(nlit(1), a.clone())))?;
    let body =
        cite(names::MOD_UNIQUE, [a.clone(), nlit(1), a, nlit(0), le_refl(nlit(1)), split.proof]);
    Some((ty, lams(vec![ba], body)))
}

/// `(a/n)*n + a%n = a`, reversed and placed under `ctx`:
/// `ctx a = ctx ((a/n)*n + a%n)`.
fn expand_by_div(fr: &mut Fresh, a: &Expr, n: &Expr, ctx: impl Fn(Expr) -> Expr) -> Eqn {
    let (qa, ra) = (ndiv(a.clone(), n.clone()), nmod(a.clone(), n.clone()));
    Eqn::cite(
        "Nat.div_add_mod",
        vec![a.clone(), n.clone()],
        nadd(nmul(qa, n.clone()), ra),
        a.clone(),
    )
    .symm()
    .under(fr, ctx)
}

/// `add_mul_mod_self : ∀ a n q, 0 < n → (a + n*q) % n = a % n`:
/// `a + n*q = a%n + n*(a/n + q)`, then `mod_unique` with `a%n < n`.
fn add_mul_mod_self() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bn, n) = nat_local(&mut fr);
    let (bq, q) = nat_local(&mut fr);
    let (hn_id, hn) = fr.local();
    let binders = vec![ba, bn, bq, (hn_id, nlt(nlit(0), n.clone()))];
    let sum = nadd(a.clone(), nmul(n.clone(), q.clone()));
    let ra = nmod(a.clone(), n.clone());
    let ty = pis(binders.clone(), eq(nat(), nmod(sum.clone(), n.clone()), ra.clone()));
    let quot = nadd(ndiv(a.clone(), n.clone()), q.clone());
    let nq = nmul(n.clone(), q.clone());
    let e = expand_by_div(&mut fr, &a, &n, |t| nadd(t, nq.clone()));
    let e = ring_rw(&mut fr, e, &sum, &nadd(ra.clone(), nmul(n.clone(), quot.clone())))?;
    let hlt = cite("Nat.mod_lt", [a.clone(), n.clone(), hn]);
    let body = cite(names::MOD_UNIQUE, [sum, n, quot, ra, hlt, e.proof]);
    Some((ty, lams(binders, body)))
}

/// `mod_add_mod` (`mod_left`) : `∀ a b n, 0 < n → (a % n + b) % n = (a + b) % n`,
/// or `add_mod_mod` : `∀ a b n, 0 < n → (a + b % n) % n = (a + b) % n`.
/// With `t` the reduced sum, `a + b = t + n*(x/n)` (`x` the reduced operand),
/// so `(a + b) % n = t % n` by `add_mul_mod_self`.
fn mod_add_mod(mod_left: bool) -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bb, b) = nat_local(&mut fr);
    let (bn, n) = nat_local(&mut fr);
    let (hn_id, hn) = fr.local();
    let binders = vec![ba, bb, bn, (hn_id, nlt(nlit(0), n.clone()))];
    let x = if mod_left { a.clone() } else { b.clone() };
    let t = if mod_left {
        nadd(nmod(a.clone(), n.clone()), b.clone())
    } else {
        nadd(a.clone(), nmod(b.clone(), n.clone()))
    };
    let ab = nadd(a.clone(), b.clone());
    let ty =
        pis(binders.clone(), eq(nat(), nmod(t.clone(), n.clone()), nmod(ab.clone(), n.clone())));
    let qx = ndiv(x.clone(), n.clone());
    let e = if mod_left {
        expand_by_div(&mut fr, &a, &n, |s| nadd(s, b.clone()))
    } else {
        expand_by_div(&mut fr, &b, &n, |s| nadd(a.clone(), s))
    };
    let shifted = nadd(t.clone(), nmul(n.clone(), qx.clone()));
    let e = ring_rw(&mut fr, e, &ab, &shifted)?;
    let nn = n.clone();
    let lifted = e.under(&mut fr, |s| nmod(s, nn.clone()));
    let k = Eqn::cite(
        names::ADD_MUL_MOD_SELF,
        vec![t.clone(), n.clone(), qx, hn],
        nmod(shifted, n.clone()),
        nmod(t, n),
    );
    let body = lifted.then(k).symm();
    Some((ty, lams(binders, body.proof)))
}

/// `bit_split_mod : ∀ b m p, b < 2 → 0 < p → (b + 2*m) % (2*p) = b + 2*(m % p)`.
///
/// `b + 2*m = (b + 2*(m%p)) + (2*p)*(m/p)` (`Nat.div_add_mod`), and the
/// remainder candidate is below `2*p`:
/// `succ (b + 2r) = succ b + 2r ≤ 2 + 2r = 2 * succ r ≤ 2 * p`.
fn bit_split_mod() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bb, b) = nat_local(&mut fr);
    let (bm, m) = nat_local(&mut fr);
    let (bp, p) = nat_local(&mut fr);
    let (hb_id, hb) = fr.local();
    let (hp_id, hp) = fr.local();
    let two = || nlit(2);
    let binders =
        vec![bb, bm, bp, (hb_id, nlt(b.clone(), two())), (hp_id, nlt(nlit(0), p.clone()))];
    let rm = nmod(m.clone(), p.clone());
    let cand = nadd(b.clone(), nmul(two(), rm.clone()));
    let total = nadd(b.clone(), nmul(two(), m.clone()));
    let tp = nmul(two(), p.clone());
    let ty = pis(binders.clone(), eq(nat(), nmod(total.clone(), tp.clone()), cand.clone()));

    // The bound `cand < 2*p`.
    let hr = cite("Nat.mod_lt", [m.clone(), p.clone(), hp]);
    let two_rm = nmul(two(), rm.clone());
    let s1 = cite(names::ADD_LE_ADD_RIGHT, [succ(b.clone()), two(), two_rm.clone(), hb]);
    let s1 = le_rw(
        &mut fr,
        s1,
        &nadd(succ(b.clone()), two_rm.clone()),
        &nadd(two(), two_rm),
        &succ(cand.clone()),
        &nmul(two(), succ(rm.clone())),
    )?;
    let s2 = cite("Nat.mul_le_mul_left", [succ(rm.clone()), p.clone(), two(), hr]);
    let bound =
        cite("Nat.le_trans", [succ(cand.clone()), nmul(two(), succ(rm)), tp.clone(), s1, s2]);

    let qm = ndiv(m.clone(), p.clone());
    let bb2 = b.clone();
    let e = expand_by_div(&mut fr, &m, &p, |s| nadd(bb2.clone(), nmul(nlit(2), s)));
    let e = ring_rw(&mut fr, e, &total, &nadd(cand.clone(), nmul(tp.clone(), qm.clone())))?;
    let body = cite(names::MOD_UNIQUE, [total, tp, qm, cand, bound, e.proof]);
    Some((ty, lams(binders, body)))
}

// ── powers of two ────────────────────────────────────────────────────────────

/// `two_pow_pos : ∀ k, 0 < 2^k`. `2^0 ≡ 1` and `0 < 1` is `Nat.le.refl 1`;
/// from `1 ≤ 2^k ≤ 2^k + 2^k = 2 * 2^k ≡ 2^(succ k)`.
fn two_pow_pos() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bk, k) = nat_local(&mut fr);
    let concl = |t: &Expr| nlt(nlit(0), two_pow(t.clone()));
    let ty = pis(vec![bk.clone()], concl(&k));
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        lams(vec![bt], concl(&t))
    };
    let step = {
        let (bj, j) = nat_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let pj = two_pow(j.clone());
        let doubled = nadd(pj.clone(), pj.clone());
        let s = cite(
            "Nat.le_trans",
            [
                nlit(1),
                pj.clone(),
                doubled.clone(),
                ih,
                cite("Nat.le_add_right", [pj.clone(), pj.clone()]),
            ],
        );
        let s = le_rw(&mut fr, s, &nlit(1), &doubled, &nlit(1), &nmul(nlit(2), pj))?;
        lams(vec![bj, (ih_id, concl(&j))], s)
    };
    let val = lams(vec![bk], nat_rec_prop(motive, le_refl(nlit(1)), step, k));
    Some((ty, val))
}

/// `two_pow_add : ∀ a b, 2^(a + b) = 2^a * 2^b`, by induction on `b`:
/// `2^(a+0) ≡ 2^a = 2^a * 1 ≡ 2^a * 2^0`, and
/// `2^(a + succ b) ≡ 2 * 2^(a+b) = 2 * (2^a * 2^b) = 2^a * (2 * 2^b) ≡ 2^a * 2^(succ b)`.
fn two_pow_add() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bb, b) = nat_local(&mut fr);
    let pa = two_pow(a.clone());
    let concl = |t: &Expr| {
        eq(nat(), two_pow(nadd(a.clone(), t.clone())), nmul(pa.clone(), two_pow(t.clone())))
    };
    let ty = pis(vec![ba.clone(), bb.clone()], concl(&b));
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        lams(vec![bt], concl(&t))
    };
    let base = ring_eq(&mut fr, &pa, &nmul(pa.clone(), nlit(1)))?.proof;
    let step = {
        let (bj, j) = nat_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let pj = two_pow(j.clone());
        let prod = nmul(pa.clone(), pj.clone());
        let lifted = Eqn { lhs: two_pow(nadd(a.clone(), j.clone())), rhs: prod.clone(), proof: ih }
            .under(&mut fr, |t| nmul(nlit(2), t));
        let rearranged =
            ring_eq(&mut fr, &nmul(nlit(2), prod), &nmul(pa.clone(), nmul(nlit(2), pj)))?;
        lams(vec![bj, (ih_id, concl(&j))], lifted.then(rearranged).proof)
    };
    let val = lams(vec![ba, bb], nat_rec_prop(motive, base, step, b));
    Some((ty, val))
}

/// `add_mul_mod_mod : ∀ a c q n, 0 < n → (a + c * (q % n)) % n = (a + c * q) % n`:
/// `a + c*q = (a + c*(q%n)) + n*(c*(q/n))` (`Nat.div_add_mod`), then
/// `add_mul_mod_self`.
fn add_mul_mod_mod() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = nat_local(&mut fr);
    let (bc, c) = nat_local(&mut fr);
    let (bq, q) = nat_local(&mut fr);
    let (bn, n) = nat_local(&mut fr);
    let (hn_id, hn) = fr.local();
    let binders = vec![ba, bc, bq, bn, (hn_id, nlt(nlit(0), n.clone()))];
    let reduced = nadd(a.clone(), nmul(c.clone(), nmod(q.clone(), n.clone())));
    let full = nadd(a.clone(), nmul(c.clone(), q.clone()));
    let ty = pis(
        binders.clone(),
        eq(nat(), nmod(reduced.clone(), n.clone()), nmod(full.clone(), n.clone())),
    );
    let qd = nmul(c.clone(), ndiv(q.clone(), n.clone()));
    let (a2, c2) = (a.clone(), c.clone());
    let e = expand_by_div(&mut fr, &q, &n, |s| nadd(a2.clone(), nmul(c2.clone(), s)));
    let shifted = nadd(reduced.clone(), nmul(n.clone(), qd.clone()));
    let e = ring_rw(&mut fr, e, &full, &shifted)?;
    let nn = n.clone();
    let lifted = e.under(&mut fr, |s| nmod(s, nn.clone()));
    let k = Eqn::cite(
        names::ADD_MUL_MOD_SELF,
        vec![reduced.clone(), n.clone(), qd, hn],
        nmod(shifted, n.clone()),
        nmod(reduced, n),
    );
    Some((ty, lams(binders, lifted.then(k).symm().proof)))
}

// ── bits ─────────────────────────────────────────────────────────────────────

/// A fresh `Bool` local: its binder and the variable.
fn bit_local(fr: &mut Fresh) -> ((FVarId, Expr), Expr) {
    let (id, v) = fr.local();
    ((id, bool_ty()), v)
}

/// A fresh `List Bool` local: its binder and the variable.
fn list_local(fr: &mut Fresh) -> ((FVarId, Expr), Expr) {
    let (id, v) = fr.local();
    ((id, lb()), v)
}

/// `∀ b, stmt b` by `Bool.rec` into `Prop`, with the two cases given.
fn by_bool_cases(
    fr: &mut Fresh,
    stmt: impl Fn(&Expr) -> Expr,
    on_false: Expr,
    on_true: Expr,
) -> (Expr, Expr) {
    let (bb, b) = bit_local(fr);
    let ty = pis(vec![bb.clone()], stmt(&b));
    let motive = {
        let (bx, x) = bit_local(fr);
        lams(vec![bx], stmt(&x))
    };
    (ty, lams(vec![bb], bool_rec(Level::zero(), motive, on_false, on_true, b)))
}

/// `btn_lt_two : ∀ b, btn b < 2`: `1 ≤ 2` and `2 ≤ 2`.
fn btn_lt_two() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    Some(by_bool_cases(
        &mut fr,
        |x| nlt(btn(x.clone()), nlit(2)),
        le_step(nlit(1), nlit(1), le_refl(nlit(1))),
        le_refl(nlit(2)),
    ))
}

/// `ble_btn : ∀ b, Nat.ble 1 (btn b) = b`, both cases by computation.
fn ble_btn() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    Some(by_bool_cases(
        &mut fr,
        |x| eq(bool_ty(), nble(nlit(1), btn(x.clone())), x.clone()),
        refl(bool_ty(), kx::bfalse()),
        refl(bool_ty(), kx::btrue()),
    ))
}

/// `btn_not : ∀ b, btn (!b) + btn b = 1`, both cases by computation.
fn btn_not() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    Some(by_bool_cases(
        &mut fr,
        |x| eq(nat(), nadd(btn(kx::bnot(x.clone())), btn(x.clone())), nlit(1)),
        refl(nat(), nlit(1)),
        refl(nat(), nlit(1)),
    ))
}

/// `btn_ble : ∀ r, r < 2 → btn (Nat.ble 1 r) = r`. Cases `0` and `1` compute;
/// `succ (succ j) < 2` contradicts `2 ≤ succ (succ j)` (`lt_le_false`).
fn btn_ble() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let concl = |r: &Expr| eq(nat(), btn(nble(nlit(1), r.clone())), r.clone());
    let hyp = |r: &Expr| nlt(r.clone(), nlit(2));
    let stmt = |r: &Expr| Expr::arrow(hyp(r), concl(r));
    let (br, r) = nat_local(&mut fr);
    let ty = pis(vec![br.clone()], stmt(&r));
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        lams(vec![bt], stmt(&t))
    };
    let zero_case = {
        let (h_id, _) = fr.local();
        lams(vec![(h_id, hyp(&zero()))], refl(nat(), zero()))
    };
    let succ_case = {
        let (bk, k) = nat_local(&mut fr);
        let (ih_id, _) = fr.local();
        let inner_motive = {
            let (bt, t) = nat_local(&mut fr);
            lams(vec![bt], stmt(&succ(t)))
        };
        let one = {
            let (h_id, _) = fr.local();
            lams(vec![(h_id, hyp(&succ(zero())))], refl(nat(), succ(zero())))
        };
        let two_up = {
            let (bj, j) = nat_local(&mut fr);
            let (ih2_id, _) = fr.local();
            let (h_id, h) = fr.local();
            let ssj = succ(succ(j.clone()));
            let le1 =
                cite("Nat.succ_le_succ", [nlit(0), j.clone(), cite(names::ZERO_LE, [j.clone()])]);
            let le2 = cite("Nat.succ_le_succ", [succ(nlit(0)), succ(j.clone()), le1]);
            let contra = cite(names::LT_LE_FALSE, [ssj.clone(), nlit(2), h, le2]);
            lams(
                vec![bj, (ih2_id, stmt(&succ(j))), (h_id, hyp(&ssj))],
                false_elim(concl(&ssj), contra),
            )
        };
        lams(vec![bk, (ih_id, stmt(&k))], nat_rec_prop(inner_motive, one, two_up, k))
    };
    Some((ty, lams(vec![br], nat_rec_prop(motive, zero_case, succ_case, r))))
}

/// `full_adder : ∀ a b c, btn a + btn b + btn c = btn (xor3 a b c) + 2 * btn (maj a b c)`,
/// by an exhaustive eight-leaf `Bool.rec`, each leaf `Eq.refl` of a ground
/// value the kernel computes.
fn full_adder() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let lhs =
        |a: &Expr, b: &Expr, c: &Expr| nadd(nadd(btn(a.clone()), btn(b.clone())), btn(c.clone()));
    let stmt = |a: &Expr, b: &Expr, c: &Expr| {
        eq(
            nat(),
            lhs(a, b, c),
            nadd(
                btn(xor3(a.clone(), b.clone(), c.clone())),
                nmul(nlit(2), btn(maj(a.clone(), b.clone(), c.clone()))),
            ),
        )
    };
    let (ba, a) = bit_local(&mut fr);
    let (bb, b) = bit_local(&mut fr);
    let (bc, c) = bit_local(&mut fr);
    let binders = vec![ba, bb, bc];
    let ty = pis(binders.clone(), stmt(&a, &b, &c));
    let split = |fr: &mut Fresh, major: &Expr, with: &dyn Fn(&Expr) -> Expr, cases: [Expr; 2]| {
        let (bx, x) = bit_local(fr);
        let motive = lams(vec![bx], with(&x));
        let [f, t] = cases;
        bool_rec(Level::zero(), motive, f, t, major.clone())
    };
    let (f, t) = (kx::bfalse(), kx::btrue());
    let mut on_a = Vec::new();
    for ag in [&f, &t] {
        let mut on_b = Vec::new();
        for bg in [&f, &t] {
            let leaves = [refl(nat(), lhs(ag, bg, &f)), refl(nat(), lhs(ag, bg, &t))];
            on_b.push(split(&mut fr, &c, &|z| stmt(ag, bg, z), leaves));
        }
        let [bf, bt]: [Expr; 2] = on_b.try_into().ok()?;
        on_a.push(split(&mut fr, &b, &|y| stmt(ag, y, &c), [bf, bt]));
    }
    let [af, at]: [Expr; 2] = on_a.try_into().ok()?;
    let body = split(&mut fr, &a, &|x| stmt(x, &b, &c), [af, at]);
    Some((ty, lams(binders, body)))
}

// ── lists ────────────────────────────────────────────────────────────────────

/// `bvToNat` and `bvLen`, short.
fn val(xs: Expr) -> Expr {
    to_nat(xs)
}

/// `Eq.trans` over `List Bool`.
fn ltrans(a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    trans(lb(), a, b, c, h1, h2)
}

/// `toNat_head_tail : ∀ ys, V ys = btn (bhead ys) + 2 * V (btail ys)`. Both
/// cases compute (`bhead [] = false`, `btail [] = []`).
fn to_nat_head_tail() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let stmt = |ys: &Expr| {
        eq(
            nat(),
            val(ys.clone()),
            nadd(btn(bhead(ys.clone())), nmul(nlit(2), val(btail(ys.clone())))),
        )
    };
    let (bys, ys) = list_local(&mut fr);
    let ty = pis(vec![bys.clone()], stmt(&ys));
    let motive = {
        let (bw, w) = list_local(&mut fr);
        lams(vec![bw], stmt(&w))
    };
    let cons_case = {
        let (bh, h) = bit_local(&mut fr);
        let (bt, t) = list_local(&mut fr);
        let (ih_id, _) = fr.local();
        let whole = kx::cons(h, t.clone());
        lams(vec![bh, bt, (ih_id, stmt(&t))], refl(nat(), val(whole)))
    };
    let body = list_rec_prop(motive, refl(nat(), nlit(0)), cons_case, ys);
    Some((ty, lams(vec![bys], body)))
}

/// `addRecM_val : ∀ xs ys c, V (addRecM xs ys c) = (V xs + V ys + btn c) % 2^(L xs)`.
///
/// Induction on `xs`, generalising `ys` and `c` (the `len_addRecM` motive).
/// `[]`: both sides are `0` (`mod_one`). `a :: as`, with `h = bhead ys`,
/// `t = btail ys`, `s = xor3 a h c`, `k = maj a h c`:
/// ```text
/// V (addRecM (a::as) ys c) ≡ btn s + 2 * V (addRecM as t k)
///   = btn s + 2 * ((V as + V t + btn k) % P)              (IH)
///   = (btn s + 2 * (V as + V t + btn k)) % (2 * P)        (bit_split_mod)
///   = (btn a + 2 * V as + V ys + btn c) % (2 * P)         (full_adder, toNat_head_tail)
///   ≡ (V (a::as) + V ys + btn c) % 2^(L (a::as))
/// ```
fn add_rec_m_val() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let sum = |xs: &Expr, ys: &Expr, c: &Expr| {
        nadd(nadd(val(xs.clone()), val(ys.clone())), btn(c.clone()))
    };
    let stmt = |xs: &Expr, ys: &Expr, c: &Expr| {
        eq(
            nat(),
            val(addm(xs.clone(), ys.clone(), c.clone())),
            nmod(sum(xs, ys, c), two_pow(bvlen(xs.clone()))),
        )
    };
    let all = |fr: &mut Fresh, xs: &Expr| {
        let (bys, ys) = list_local(fr);
        let (bc, c) = bit_local(fr);
        pis(vec![bys, bc], stmt(xs, &ys, &c))
    };
    let (bxs, xs) = list_local(&mut fr);
    let ty = {
        let body = all(&mut fr, &xs);
        pis(vec![bxs.clone()], body)
    };
    let motive = {
        let (bw, w) = list_local(&mut fr);
        let body = all(&mut fr, &w);
        lams(vec![bw], body)
    };
    let nil_case = {
        let (bys, ys) = list_local(&mut fr);
        let (bc, c) = bit_local(&mut fr);
        let x = sum(&kx::nil(), &ys, &c);
        let body = symm(nat(), nmod(x.clone(), nlit(1)), nlit(0), cite(names::MOD_ONE, [x]));
        lams(vec![bys, bc], body)
    };
    let cons_case = {
        let (ba, a) = bit_local(&mut fr);
        let (bas, as_) = list_local(&mut fr);
        let ih_ty = all(&mut fr, &as_);
        let (ih_id, ih) = fr.local();
        let (bys, ys) = list_local(&mut fr);
        let (bc, c) = bit_local(&mut fr);
        let (h, t) = (bhead(ys.clone()), btail(ys.clone()));
        let s = xor3(a.clone(), h.clone(), c.clone());
        let k = maj(a.clone(), h.clone(), c.clone());
        let two = || nlit(2);
        let (vas, vt) = (val(as_.clone()), val(t.clone()));
        let m = nadd(nadd(vas.clone(), vt.clone()), btn(k.clone()));
        let p = two_pow(bvlen(as_.clone()));
        let rest = addm(as_.clone(), t.clone(), k.clone());
        let bs = btn(s.clone());

        let e0 = Eqn::by_defeq(
            val(addm(kx::cons(a.clone(), as_.clone()), ys.clone(), c.clone())),
            nadd(bs.clone(), nmul(two(), val(rest.clone()))),
        );
        let bs1 = bs.clone();
        let e1 = Eqn {
            lhs: val(rest),
            rhs: nmod(m.clone(), p.clone()),
            proof: Expr::apps(ih, [t.clone(), k.clone()]),
        }
        .under(&mut fr, |x| nadd(bs1.clone(), nmul(nlit(2), x)));
        let e2 = Eqn::cite(
            names::BIT_SPLIT_MOD,
            vec![
                bs.clone(),
                m.clone(),
                p.clone(),
                cite(names::BTN_LT_TWO, [s.clone()]),
                cite(names::TWO_POW_POS, [bvlen(as_.clone())]),
            ],
            nmod(nadd(bs.clone(), nmul(two(), m.clone())), nmul(two(), p.clone())),
            nadd(bs.clone(), nmul(two(), nmod(m.clone(), p.clone()))),
        )
        .symm();

        // btn s + 2*(V as + V t + btn k) = btn a + 2*V as + V ys + btn c
        let (ba_, bh, bc_) = (btn(a.clone()), btn(h.clone()), btn(c.clone()));
        let twos = nadd(nmul(two(), vas.clone()), nmul(two(), vt.clone()));
        let fa_lhs = nadd(nadd(ba_.clone(), bh.clone()), bc_.clone());
        let fa_rhs = nadd(bs.clone(), nmul(two(), btn(k.clone())));
        let r1 = ring_eq(
            &mut fr,
            &nadd(bs.clone(), nmul(two(), m.clone())),
            &nadd(fa_rhs.clone(), twos.clone()),
        )?;
        let tw = twos.clone();
        let fa = Eqn::cite(
            names::FULL_ADDER,
            vec![a.clone(), h.clone(), c.clone()],
            fa_lhs.clone(),
            fa_rhs,
        )
        .symm()
        .under(&mut fr, |x| nadd(x, tw.clone()));
        let a2v = nadd(ba_.clone(), nmul(two(), vas.clone()));
        let ht_rhs = nadd(bh.clone(), nmul(two(), vt.clone()));
        let r2 = ring_eq(
            &mut fr,
            &nadd(fa_lhs, twos),
            &nadd(nadd(a2v.clone(), ht_rhs.clone()), bc_.clone()),
        )?;
        let (a2v1, bc1) = (a2v.clone(), bc_.clone());
        let ht = Eqn::cite(names::TO_NAT_HEAD_TAIL, vec![ys.clone()], val(ys.clone()), ht_rhs)
            .symm()
            .under(&mut fr, |x| nadd(nadd(a2v1.clone(), x), bc1.clone()));
        let tp = nmul(two(), p);
        let e3 = r1.then(fa).then(r2).then(ht).under(&mut fr, |x| nmod(x, tp.clone()));
        let body = e0.then(e1).then(e2).then(e3);
        lams(vec![ba, bas, (ih_id, ih_ty), bys, bc], body.proof)
    };
    let body = list_rec_prop(motive, nil_case, cons_case, xs);
    Some((ty, lams(vec![bxs], body)))
}

/// `len_natToBv : ∀ w v, L (natToBvAux w v) = w`, by induction on `w`
/// generalising `v`.
fn len_nat_to_bv() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let stmt = |w: &Expr, v: &Expr| eq(nat(), bvlen(nat_to_bv(w.clone(), v.clone())), w.clone());
    let all = |fr: &mut Fresh, w: &Expr| {
        let (bv, v) = nat_local(fr);
        pis(vec![bv], stmt(w, &v))
    };
    let (bw, w) = nat_local(&mut fr);
    let ty = {
        let body = all(&mut fr, &w);
        pis(vec![bw.clone()], body)
    };
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        let body = all(&mut fr, &t);
        lams(vec![bt], body)
    };
    let zero_case = {
        let (bv, _) = nat_local(&mut fr);
        lams(vec![bv], refl(nat(), zero()))
    };
    let succ_case = {
        let (bk, k) = nat_local(&mut fr);
        let ih_ty = all(&mut fr, &k);
        let (ih_id, ih) = fr.local();
        let (bv, v) = nat_local(&mut fr);
        let half = ndiv(v, nlit(2));
        let body = congr_arg(
            nat(),
            nat(),
            bvlen(nat_to_bv(k.clone(), half.clone())),
            k.clone(),
            Expr::const_str("Nat.succ"),
            Expr::app(ih, half),
        );
        lams(vec![bk, (ih_id, ih_ty), bv], body)
    };
    Some((ty, lams(vec![bw], nat_rec_prop(motive, zero_case, succ_case, w))))
}

/// `0 < 2`, as `Nat.le 1 2`.
fn zero_lt_two() -> Expr {
    le_step(nlit(1), nlit(1), le_refl(nlit(1)))
}

/// `toNat_natToBv : ∀ w v, V (natToBvAux w v) = v % 2^w`, by induction on `w`
/// generalising `v`:
/// ```text
/// V (natToBvAux (succ k) v) ≡ btn (ble 1 (v%2)) + 2 * V (natToBvAux k (v/2))
///   = v%2 + 2 * ((v/2) % 2^k)          (btn_ble, IH)
///   = (v%2 + 2 * (v/2)) % (2 * 2^k)     (bit_split_mod)
///   = v % 2^(succ k)                    (Nat.div_add_mod)
/// ```
fn to_nat_nat_to_bv() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let stmt = |w: &Expr, v: &Expr| {
        eq(nat(), val(nat_to_bv(w.clone(), v.clone())), nmod(v.clone(), two_pow(w.clone())))
    };
    let all = |fr: &mut Fresh, w: &Expr| {
        let (bv, v) = nat_local(fr);
        pis(vec![bv], stmt(w, &v))
    };
    let (bw, w) = nat_local(&mut fr);
    let ty = {
        let body = all(&mut fr, &w);
        pis(vec![bw.clone()], body)
    };
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        let body = all(&mut fr, &t);
        lams(vec![bt], body)
    };
    let zero_case = {
        let (bv, v) = nat_local(&mut fr);
        let body = symm(nat(), nmod(v.clone(), nlit(1)), nlit(0), cite(names::MOD_ONE, [v]));
        lams(vec![bv], body)
    };
    let succ_case = {
        let (bk, k) = nat_local(&mut fr);
        let ih_ty = all(&mut fr, &k);
        let (ih_id, ih) = fr.local();
        let (bv, v) = nat_local(&mut fr);
        let two = || nlit(2);
        let (r, q) = (nmod(v.clone(), two()), ndiv(v.clone(), two()));
        let pk = two_pow(k.clone());
        let hr = cite("Nat.mod_lt", [v.clone(), two(), zero_lt_two()]);
        let low = nat_to_bv(k.clone(), q.clone());
        let bit = btn(nble(nlit(1), r.clone()));
        let e0 = Eqn::by_defeq(
            val(nat_to_bv(succ(k.clone()), v.clone())),
            nadd(bit.clone(), nmul(two(), val(low.clone()))),
        );
        let low1 = low.clone();
        let e1 = Eqn::cite(names::BTN_BLE, vec![r.clone(), hr.clone()], bit, r.clone())
            .under(&mut fr, |x| nadd(x, nmul(nlit(2), val(low1.clone()))));
        let r1 = r.clone();
        let e2 = Eqn {
            lhs: val(low),
            rhs: nmod(q.clone(), pk.clone()),
            proof: Expr::app(ih, q.clone()),
        }
        .under(&mut fr, |x| nadd(r1.clone(), nmul(nlit(2), x)));
        let e3 = Eqn::cite(
            names::BIT_SPLIT_MOD,
            vec![r.clone(), q.clone(), pk.clone(), hr, cite(names::TWO_POW_POS, [k.clone()])],
            nmod(nadd(r.clone(), nmul(two(), q.clone())), nmul(two(), pk.clone())),
            nadd(r.clone(), nmul(two(), nmod(q.clone(), pk.clone()))),
        )
        .symm();
        let dam = Eqn::cite(
            "Nat.div_add_mod",
            vec![v.clone(), two()],
            nadd(nmul(q.clone(), two()), r.clone()),
            v.clone(),
        );
        let tp = nmul(two(), pk);
        let e4 = ring_rw(&mut fr, dam, &nadd(r, nmul(two(), q)), &v)?
            .under(&mut fr, |x| nmod(x, tp.clone()));
        let body = e0.then(e1).then(e2).then(e3).then(e4);
        lams(vec![bk, (ih_id, ih_ty), bv], body.proof)
    };
    Some((ty, lams(vec![bw], nat_rec_prop(motive, zero_case, succ_case, w))))
}

/// `natToBv_toNat : ∀ xs, natToBvAux (L xs) (V xs) = xs`, by induction on
/// `xs`. For `b :: t`, with `x = V (b :: t) ≡ btn b + 2 * V t`:
/// `x % 2 = btn b` (`mod_unique`), `x / 2 = V t` (`div_unique`), so the head
/// is `ble 1 (btn b) = b` (`ble_btn`) and the tail is the IH.
fn nat_to_bv_to_nat() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let stmt = |xs: &Expr| eq(lb(), nat_to_bv(bvlen(xs.clone()), val(xs.clone())), xs.clone());
    let (bxs, xs) = list_local(&mut fr);
    let ty = pis(vec![bxs.clone()], stmt(&xs));
    let motive = {
        let (bw, w) = list_local(&mut fr);
        lams(vec![bw], stmt(&w))
    };
    let cons_case = {
        let (bb, b) = bit_local(&mut fr);
        let (bt, t) = list_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let two = || nlit(2);
        let x = val(kx::cons(b.clone(), t.clone()));
        let vt = val(t.clone());
        let hb = cite(names::BTN_LT_TWO, [b.clone()]);
        let hsplit = refl(nat(), x.clone());
        let unique = |name: &str| {
            cite(name, [x.clone(), two(), vt.clone(), btn(b.clone()), hb.clone(), hsplit.clone()])
        };
        let (hm, hd) = (unique(names::MOD_UNIQUE), unique(names::DIV_UNIQUE));
        let (xm, xd) = (nmod(x.clone(), two()), ndiv(x.clone(), two()));
        let head_fn = {
            let (bn, n) = nat_local(&mut fr);
            lams(vec![bn], nble(nlit(1), n))
        };
        let c1 = congr_arg(nat(), bool_ty(), xm.clone(), btn(b.clone()), head_fn, hm);
        let hd_val = nble(nlit(1), xm);
        let head = trans(
            bool_ty(),
            hd_val.clone(),
            nble(nlit(1), btn(b.clone())),
            b.clone(),
            c1,
            cite(names::BLE_BTN, [b.clone()]),
        );
        let lt = bvlen(t.clone());
        let tail_fn = {
            let (bn, n) = nat_local(&mut fr);
            lams(vec![bn], nat_to_bv(lt.clone(), n))
        };
        let tl_val = nat_to_bv(lt.clone(), xd.clone());
        let c2 = congr_arg(nat(), lb(), xd, vt.clone(), tail_fn, hd);
        let tail = ltrans(tl_val.clone(), nat_to_bv(lt, vt), t.clone(), c2, ih);
        let s1 = {
            let (bs, s) = bit_local(&mut fr);
            let f = lams(vec![bs], kx::cons(s, tl_val.clone()));
            congr_arg(bool_ty(), lb(), hd_val.clone(), b.clone(), f, head)
        };
        let s2 = {
            let (bl, l) = list_local(&mut fr);
            let f = lams(vec![bl], kx::cons(b.clone(), l));
            congr_arg(lb(), lb(), tl_val.clone(), t.clone(), f, tail)
        };
        let body = ltrans(
            kx::cons(hd_val, tl_val.clone()),
            kx::cons(b.clone(), tl_val),
            kx::cons(b, t.clone()),
            s1,
            s2,
        );
        lams(vec![bb, bt, (ih_id, stmt(&t))], body)
    };
    let body = list_rec_prop(motive, refl(lb(), kx::nil()), cons_case, xs);
    Some((ty, lams(vec![bxs], body)))
}

/// `inj : ∀ xs ys, L xs = L ys → V xs = V ys → xs = ys`: both are
/// `natToBvAux (L _) (V _)` of themselves (`natToBv_toNat`).
fn inj() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bxs, xs) = list_local(&mut fr);
    let (bys, ys) = list_local(&mut fr);
    let (hl_id, hl) = fr.local();
    let (hv_id, hv) = fr.local();
    let (lx, ly, vx, vy) = (bvlen(xs.clone()), bvlen(ys.clone()), val(xs.clone()), val(ys.clone()));
    let binders = vec![
        bxs,
        bys,
        (hl_id, eq(nat(), lx.clone(), ly.clone())),
        (hv_id, eq(nat(), vx.clone(), vy.clone())),
    ];
    let ty = pis(binders.clone(), eq(lb(), xs.clone(), ys.clone()));
    let n_xx = nat_to_bv(lx.clone(), vx.clone());
    let n_yx = nat_to_bv(ly.clone(), vx.clone());
    let n_yy = nat_to_bv(ly.clone(), vy.clone());
    let e1 = symm(lb(), n_xx.clone(), xs.clone(), cite(names::NAT_TO_BV_TO_NAT, [xs.clone()]));
    let f1 = {
        let (bn, n) = nat_local(&mut fr);
        lams(vec![bn], nat_to_bv(n, vx.clone()))
    };
    let e2 = congr_arg(nat(), lb(), lx, ly.clone(), f1, hl);
    let f2 = {
        let (bn, n) = nat_local(&mut fr);
        lams(vec![bn], nat_to_bv(ly.clone(), n))
    };
    let e3 = congr_arg(nat(), lb(), vx, vy, f2, hv);
    let e4 = cite(names::NAT_TO_BV_TO_NAT, [ys.clone()]);
    let e123 =
        ltrans(xs.clone(), n_yx.clone(), n_yy.clone(), ltrans(xs.clone(), n_xx, n_yx, e1, e2), e3);
    let body = ltrans(xs, n_yy, ys, e123, e4);
    Some((ty, lams(binders, body)))
}

/// `V xs = 0` for a list that unfolds to `false :: rest`, by induction:
/// `V (false :: rest) ≡ 0 + 2 * V rest = 0 + 2 * 0 ≡ 0`. `zero_list` is
/// `bvAllFalse` (over a list) or `bvReplF` (over a `Nat`).
fn to_nat_zeros(over_list: bool) -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let mk = |e: &Expr| if over_list { kx::all_false(e.clone()) } else { repl_f(e.clone()) };
    let stmt = |e: &Expr| eq(nat(), val(mk(e)), nlit(0));
    let local = |fr: &mut Fresh| if over_list { list_local(fr) } else { nat_local(fr) };
    let (bx, x) = local(&mut fr);
    let ty = pis(vec![bx.clone()], stmt(&x));
    let motive = {
        let (bw, w) = local(&mut fr);
        lams(vec![bw], stmt(&w))
    };
    let step = |fr: &mut Fresh, prev: &Expr, ih: Expr| {
        Eqn { lhs: val(mk(prev)), rhs: nlit(0), proof: ih }
            .under(fr, |e| nadd(nlit(0), nmul(nlit(2), e)))
            .proof
    };
    let body = if over_list {
        let cons_case = {
            let (bh, _) = bit_local(&mut fr);
            let (bt, t) = list_local(&mut fr);
            let (ih_id, ih) = fr.local();
            let p = step(&mut fr, &t, ih);
            lams(vec![bh, bt, (ih_id, stmt(&t))], p)
        };
        list_rec_prop(motive, refl(nat(), nlit(0)), cons_case, x)
    } else {
        let succ_case = {
            let (bk, k) = nat_local(&mut fr);
            let (ih_id, ih) = fr.local();
            let p = step(&mut fr, &k, ih);
            lams(vec![bk, (ih_id, stmt(&k))], p)
        };
        nat_rec_prop(motive, refl(nat(), nlit(0)), succ_case, x)
    };
    Some((ty, lams(vec![bx], body)))
}

/// `len_replF : ∀ k, L (bvReplF k) = k`, by induction on `k`.
fn len_repl_f() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let stmt = |k: &Expr| eq(nat(), bvlen(repl_f(k.clone())), k.clone());
    let (bk, k) = nat_local(&mut fr);
    let ty = pis(vec![bk.clone()], stmt(&k));
    let motive = {
        let (bt, t) = nat_local(&mut fr);
        lams(vec![bt], stmt(&t))
    };
    let succ_case = {
        let (bj, j) = nat_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let body = congr_arg(
            nat(),
            nat(),
            bvlen(repl_f(j.clone())),
            j.clone(),
            Expr::const_str("Nat.succ"),
            ih,
        );
        lams(vec![bj, (ih_id, stmt(&j))], body)
    };
    Some((ty, lams(vec![bk], nat_rec_prop(motive, refl(nat(), zero()), succ_case, k))))
}

/// `len_append : ∀ xs ys, L (xs ++ ys) = L xs + L ys`, by induction on `xs`.
fn len_append() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bxs, xs) = list_local(&mut fr);
    let (bys, ys) = list_local(&mut fr);
    let ly = bvlen(ys.clone());
    let stmt = |w: &Expr| {
        eq(nat(), bvlen(bv_append(w.clone(), ys.clone())), nadd(bvlen(w.clone()), ly.clone()))
    };
    let ty = pis(vec![bxs.clone(), bys.clone()], stmt(&xs));
    let motive = {
        let (bw, w) = list_local(&mut fr);
        lams(vec![bw], stmt(&w))
    };
    let nil_case = ring_eq(&mut fr, &ly, &nadd(zero(), ly.clone()))?.proof;
    let cons_case = {
        let (bh, h) = bit_local(&mut fr);
        let (bt, t) = list_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let lt = bvlen(t.clone());
        let tail = bvlen(bv_append(t.clone(), ys.clone()));
        let e0 =
            Eqn::by_defeq(bvlen(bv_append(kx::cons(h, t.clone()), ys.clone())), succ(tail.clone()));
        let e1 =
            Eqn { lhs: tail, rhs: nadd(lt.clone(), ly.clone()), proof: ih }.under(&mut fr, succ);
        let e2 = ring_eq(&mut fr, &e1.rhs, &nadd(succ(lt), ly.clone()))?;
        lams(vec![bh, bt, (ih_id, stmt(&t))], e0.then(e1).then(e2).proof)
    };
    let body = list_rec_prop(motive, nil_case, cons_case, xs);
    Some((ty, lams(vec![bxs, bys], body)))
}

/// `toNat_append : ∀ xs ys, V (xs ++ ys) = V xs + 2^(L xs) * V ys`, by
/// induction on `xs`.
fn to_nat_append() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (bxs, xs) = list_local(&mut fr);
    let (bys, ys) = list_local(&mut fr);
    let vy = val(ys.clone());
    let stmt = |w: &Expr| {
        eq(
            nat(),
            val(bv_append(w.clone(), ys.clone())),
            nadd(val(w.clone()), nmul(two_pow(bvlen(w.clone())), vy.clone())),
        )
    };
    let ty = pis(vec![bxs.clone(), bys.clone()], stmt(&xs));
    let motive = {
        let (bw, w) = list_local(&mut fr);
        lams(vec![bw], stmt(&w))
    };
    let nil_case = ring_eq(&mut fr, &vy, &nadd(nlit(0), nmul(nlit(1), vy.clone())))?.proof;
    let cons_case = {
        let (bh, h) = bit_local(&mut fr);
        let (bt, t) = list_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let tail = val(bv_append(t.clone(), ys.clone()));
        let bh_ = btn(h.clone());
        let e0 = Eqn::by_defeq(
            val(bv_append(kx::cons(h, t.clone()), ys.clone())),
            nadd(bh_.clone(), nmul(nlit(2), tail.clone())),
        );
        let pt = two_pow(bvlen(t.clone()));
        let bh1 = bh_.clone();
        let e1 =
            Eqn { lhs: tail, rhs: nadd(val(t.clone()), nmul(pt.clone(), vy.clone())), proof: ih }
                .under(&mut fr, |x| nadd(bh1.clone(), nmul(nlit(2), x)));
        let target =
            nadd(nadd(bh_, nmul(nlit(2), val(t.clone()))), nmul(nmul(nlit(2), pt), vy.clone()));
        let e2 = ring_eq(&mut fr, &e1.rhs, &target)?;
        lams(vec![bh, bt, (ih_id, stmt(&t))], e0.then(e1).then(e2).proof)
    };
    let body = list_rec_prop(motive, nil_case, cons_case, xs);
    Some((ty, lams(vec![bxs, bys], body)))
}

/// `bvNot_val : ∀ xs, V (bvNot xs) + V xs + 1 = 2^(L xs)`, by induction:
/// `(btn (!h) + 2 V (¬t)) + (btn h + 2 V t) + 1 = 1 + 2 (V (¬t) + V t) + 1
/// = 2 (V (¬t) + V t + 1) = 2 * 2^(L t)` (`btn_not`, IH).
fn bv_not_val() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let stmt = |w: &Expr| {
        eq(
            nat(),
            nadd(nadd(val(kx::bv_not(w.clone())), val(w.clone())), nlit(1)),
            two_pow(bvlen(w.clone())),
        )
    };
    let (bxs, xs) = list_local(&mut fr);
    let ty = pis(vec![bxs.clone()], stmt(&xs));
    let motive = {
        let (bw, w) = list_local(&mut fr);
        lams(vec![bw], stmt(&w))
    };
    let cons_case = {
        let (bh, h) = bit_local(&mut fr);
        let (bt, t) = list_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let two = || nlit(2);
        let (vn, vt) = (val(kx::bv_not(t.clone())), val(t.clone()));
        let (bnh, bh_) = (btn(kx::bnot(h.clone())), btn(h.clone()));
        let whole = kx::cons(h.clone(), t.clone());
        let lhs0 = nadd(
            nadd(
                nadd(bnh.clone(), nmul(two(), vn.clone())),
                nadd(bh_.clone(), nmul(two(), vt.clone())),
            ),
            nlit(1),
        );
        let e0 = Eqn::by_defeq(
            nadd(nadd(val(kx::bv_not(whole.clone())), val(whole)), nlit(1)),
            lhs0.clone(),
        );
        let rest = nadd(nmul(two(), vn.clone()), nadd(nmul(two(), vt.clone()), nlit(1)));
        let pair = nadd(bnh, bh_);
        let r1 = ring_eq(&mut fr, &lhs0, &nadd(pair.clone(), rest.clone()))?;
        let rest1 = rest.clone();
        let bn = Eqn::cite(names::BTN_NOT, vec![h], pair, nlit(1))
            .under(&mut fr, |x| nadd(x, rest1.clone()));
        let inner = nadd(nadd(vn, vt), nlit(1));
        let r2 = ring_eq(&mut fr, &nadd(nlit(1), rest), &nmul(two(), inner.clone()))?;
        let e_ih = Eqn { lhs: inner, rhs: two_pow(bvlen(t.clone())), proof: ih }
            .under(&mut fr, |x| nmul(nlit(2), x));
        let body = e0.then(r1).then(bn).then(r2).then(e_ih);
        lams(vec![bh, bt, (ih_id, stmt(&t))], body.proof)
    };
    let body = list_rec_prop(motive, refl(nat(), nlit(1)), cons_case, xs);
    Some((ty, lams(vec![bxs], body)))
}

/// `bvMul_val : ∀ a b, V (bvMul a b) = (V a * V b) % 2^(L b)`.
///
/// Induction on `a`. `[]`: `0 = (0 * V b) % n` (`mod_unique`). `a0 :: t`: a
/// case split on `a0` over the whole equation (`Bool.rec`), so the selected
/// addend `sel` is concrete: `bvAllFalse b` (value `0`, length `L b` by
/// `len_allFalse`) or `b`. Then, with `n = 2^(L b)` and `q = V t * V b`:
/// ```text
/// V (bvMul (a0::t) b) ≡ V (addRecM sel (false :: bvMul t b) false)
///   = (V sel + V (false :: bvMul t b) + 0) % 2^(L sel)   (addRecM_val)
///   = (s + 2 * (q % n)) % n                              (len_allFalse, toNat_allFalse, IH)
///   = (s + 2 * q) % n                                    (add_mul_mod_mod)
///   = ((btn a0 + 2 * V t) * V b) % n ≡ (V (a0::t) * V b) % n
/// ```
fn bv_mul_val() -> Option<(Expr, Expr)> {
    let mut fr = Fresh::new();
    let (ba, a) = list_local(&mut fr);
    let (bb, b) = list_local(&mut fr);
    let vb = val(b.clone());
    let n = two_pow(bvlen(b.clone()));
    let stmt = |w: &Expr| {
        eq(
            nat(),
            val(bvmul(w.clone(), b.clone())),
            nmod(nmul(val(w.clone()), vb.clone()), n.clone()),
        )
    };
    let ty = pis(vec![ba.clone(), bb.clone()], stmt(&a));
    let motive = {
        let (bw, w) = list_local(&mut fr);
        lams(vec![bw], stmt(&w))
    };
    let hn = cite(names::TWO_POW_POS, [bvlen(b.clone())]);
    let nil_case = {
        let zb = nmul(nlit(0), vb.clone());
        let split = ring_eq(&mut fr, &zb, &nadd(nlit(0), nmul(n.clone(), nlit(0))))?;
        let mu = cite(
            names::MOD_UNIQUE,
            [zb.clone(), n.clone(), nlit(0), nlit(0), hn.clone(), split.proof],
        );
        symm(nat(), nmod(zb, n.clone()), nlit(0), mu)
    };
    let cons_case = {
        let (ba0, a0) = bit_local(&mut fr);
        let (bt, t) = list_local(&mut fr);
        let (ih_id, ih) = fr.local();
        let two = || nlit(2);
        let q = nmul(val(t.clone()), vb.clone());
        let mtb = bvmul(t.clone(), b.clone());
        let shifted = kx::cons(kx::bfalse(), mtb.clone());
        // One branch: the bit `bit` (value `bit_val`), its addend `sel` with
        // value `sel_val`, and the equations `V sel = sel_val`, `L sel = L b`
        // where they are not definitional.
        let branch = |fr: &mut Fresh,
                      bit: Expr,
                      bit_val: u64,
                      sel: Expr,
                      sel_val: Expr,
                      val_eq: Option<Eqn>,
                      len_eq: Option<Eqn>|
         -> Option<Expr> {
            let s0 = nadd(nadd(val(sel.clone()), val(shifted.clone())), btn(kx::bfalse()));
            let e0 = Eqn::by_defeq(
                val(bvmul(kx::cons(bit.clone(), t.clone()), b.clone())),
                val(addm(sel.clone(), shifted.clone(), kx::bfalse())),
            )
            .then(Eqn::cite(
                names::ADD_REC_M_VAL,
                vec![sel.clone(), shifted.clone(), kx::bfalse()],
                val(addm(sel.clone(), shifted.clone(), kx::bfalse())),
                nmod(s0.clone(), two_pow(bvlen(sel.clone()))),
            ));
            let e0 = match len_eq {
                Some(le) => {
                    let s0c = s0.clone();
                    e0.then(le.under(fr, |x| nmod(s0c.clone(), two_pow(x))))
                }
                None => e0,
            };
            let doubled = |x: Expr| nadd(nlit(0), nmul(nlit(2), x));
            let s1 = nadd(nadd(val(sel.clone()), doubled(val(mtb.clone()))), nlit(0));
            let mut inner = Eqn::by_defeq(s0, s1);
            if let Some(ve) = val_eq {
                let m1 = mtb.clone();
                inner =
                    inner.then(ve.under(fr, |x| nadd(nadd(x, doubled(val(m1.clone()))), nlit(0))));
            }
            let sv = sel_val.clone();
            inner = inner.then(
                Eqn { lhs: val(mtb.clone()), rhs: nmod(q.clone(), n.clone()), proof: ih.clone() }
                    .under(fr, |x| nadd(nadd(sv.clone(), doubled(x)), nlit(0))),
            );
            let reduced = nadd(sel_val.clone(), nmul(two(), nmod(q.clone(), n.clone())));
            let tidy = ring_eq(fr, &inner.rhs, &reduced)?;
            inner = inner.then(tidy);
            let nn = n.clone();
            let e1 = inner.under(fr, |x| nmod(x, nn.clone()));
            let full = nadd(sel_val.clone(), nmul(two(), q.clone()));
            let e2 = Eqn::cite(
                names::ADD_MUL_MOD_MOD,
                vec![sel_val, two(), q.clone(), n.clone(), hn.clone()],
                nmod(reduced, n.clone()),
                nmod(full.clone(), n.clone()),
            );
            let target = nmul(nadd(nlit(bit_val), nmul(two(), val(t.clone()))), vb.clone());
            let nn = n.clone();
            let e3 = ring_eq(fr, &full, &target)?.under(fr, |x| nmod(x, nn.clone()));
            Some(e0.then(e1).then(e2).then(e3).proof)
        };
        let on_false = branch(
            &mut fr,
            kx::bfalse(),
            0,
            kx::all_false(b.clone()),
            nlit(0),
            Some(Eqn::cite(
                names::TO_NAT_ALL_FALSE,
                vec![b.clone()],
                val(kx::all_false(b.clone())),
                nlit(0),
            )),
            Some(Eqn::cite(
                add_comm::names::LEN_ALL_FALSE,
                vec![b.clone()],
                bvlen(kx::all_false(b.clone())),
                bvlen(b.clone()),
            )),
        )?;
        let on_true = branch(&mut fr, kx::btrue(), 1, b.clone(), vb.clone(), None, None)?;
        let bit_motive = {
            let (bx, x) = bit_local(&mut fr);
            lams(vec![bx], stmt(&kx::cons(x, t.clone())))
        };
        let body = bool_rec(Level::zero(), bit_motive, on_false, on_true, a0);
        lams(vec![ba0, bt, (ih_id, stmt(&t))], body)
    };
    let body = list_rec_prop(motive, nil_case, cons_case, a);
    Some((ty, lams(vec![ba, bb], body)))
}

// ── registration ─────────────────────────────────────────────────────────────

/// Every theorem in dependency order (`nat_ring`'s helpers first):
/// `(name, statement, proof)`. `Err` names a builder whose normaliser step
/// declined, which is a bug in this module, never a reason to admit anything.
pub(crate) fn theorems() -> Result<Vec<(&'static str, Expr, Expr)>, String> {
    let mut out = nat_ring::theorems();
    let builders: [(&'static str, fn() -> Option<(Expr, Expr)>); 34] = [
        (names::ZERO_LE, zero_le),
        (names::ADD_LE_ADD_RIGHT, add_le_add_right),
        (names::LT_OF_LT_OF_LE, lt_of_lt_of_le),
        (names::LT_LE_FALSE, lt_le_false),
        (names::POS_OF_LT, pos_of_lt),
        (names::DIV_MOD_CANCEL, div_mod_cancel),
        (names::MOD_UNIQUE, || mod_div_unique(true)),
        (names::DIV_UNIQUE, || mod_div_unique(false)),
        (names::MOD_ONE, mod_one),
        (names::ADD_MUL_MOD_SELF, add_mul_mod_self),
        (names::MOD_ADD_MOD, || mod_add_mod(true)),
        (names::ADD_MOD_MOD, || mod_add_mod(false)),
        (names::BIT_SPLIT_MOD, bit_split_mod),
        (names::TWO_POW_POS, two_pow_pos),
        (names::TWO_POW_ADD, two_pow_add),
        (names::ADD_MUL_MOD_MOD, add_mul_mod_mod),
        (names::BTN_LT_TWO, btn_lt_two),
        (names::BLE_BTN, ble_btn),
        (names::BTN_BLE, btn_ble),
        (names::BTN_NOT, btn_not),
        (names::FULL_ADDER, full_adder),
        (names::TO_NAT_HEAD_TAIL, to_nat_head_tail),
        (names::ADD_REC_M_VAL, add_rec_m_val),
        (names::LEN_NAT_TO_BV, len_nat_to_bv),
        (names::TO_NAT_NAT_TO_BV, to_nat_nat_to_bv),
        (names::NAT_TO_BV_TO_NAT, nat_to_bv_to_nat),
        (names::INJ, inj),
        (names::TO_NAT_ALL_FALSE, || to_nat_zeros(true)),
        (names::BV_MUL_VAL, bv_mul_val),
        (names::BV_NOT_VAL, bv_not_val),
        (names::TO_NAT_APPEND, to_nat_append),
        (names::LEN_APPEND, len_append),
        (names::TO_NAT_REPL_F, || to_nat_zeros(false)),
        (names::LEN_REPL_F, len_repl_f),
    ];
    for (name, build) in builders {
        let (ty, val) = build().ok_or_else(|| format!("{name}: the normaliser declined a step"))?;
        out.push((name, ty, val));
    }
    Ok(out)
}

/// Add [`definitions`] to `env`. A name already present is refused by
/// `add_decl`, so a different `btn` from elsewhere can never stand in for it.
pub(crate) fn add_definitions(env: &mut Environment) -> Result<(), String> {
    for (name, type_, value) in definitions() {
        env.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
            is_reducible: true,
        })
        .map_err(|e| format!("{name}: {e:?}"))?;
    }
    Ok(())
}

/// Add every theorem to `env` (which must carry the `Clean.BVC` layer and the
/// prelude), each a `Declaration::Theorem` that `add_decl` type-checks, then
/// audit [`audited`]. `Err` on the first refusal: the caller declines.
pub(crate) fn register(env: &mut Environment) -> Result<(), String> {
    add_definitions(env)?;
    for (name, type_, value) in theorems()? {
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value,
        })
        .map_err(|e| format!("{name}: {e:?}"))?;
    }
    audit_theorems(env, &audited())
}

#[cfg(test)]
mod tests {
    use clean_kernel::{ConstantKind, TypeChecker};

    use super::super::{add_comm, run_recheck_thread};
    use super::*;

    /// `add_comm`'s audited base plus this module's theorems.
    fn value_env() -> Result<Environment, String> {
        let mut env = add_comm::commuting_base()?.clone();
        register(&mut env)?;
        Ok(env)
    }

    /// T-U1. Every theorem registers, is a `Theorem` carrying its proof, and
    /// reaches no axiom (domain or foundational); every prelude lemma a proof
    /// cites passes the same audit; and, independently of `add_decl`, every
    /// proof re-checks against its statement in the environment of the ones
    /// before it.
    #[test]
    fn value_theory_is_kernel_checked_and_audited() {
        run_recheck_thread("bv-value-theorems", || {
            let env = value_env().expect("the value theory registers and passes its audit");
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
            let mut env = add_comm::commuting_base().expect("base").clone();
            add_definitions(&mut env).expect("btn");
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

    /// The statements are pinned as text, so a change to what a theorem says
    /// is a visible diff here and not only in the proof builders.
    #[test]
    fn statements_are_pinned() {
        let expected = [
            (names::ZERO_LE, "(n : Nat) -> Nat.le 0 n"),
            (
                names::DIV_MOD_CANCEL,
                "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> (n3 : Nat) -> (n4 : Nat) -> Nat.lt n3 n -> Nat.lt n4 n -> Nat.add (Nat.mul n n1) n3 = Nat.add (Nat.mul n n2) n4 -> n1 = n2",
            ),
            (
                names::MOD_UNIQUE,
                "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> (n3 : Nat) -> Nat.lt n3 n1 -> n = Nat.add n3 (Nat.mul n1 n2) -> Nat.mod n n1 = n3",
            ),
            (
                names::BIT_SPLIT_MOD,
                "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> Nat.lt n 2 -> Nat.lt 0 n2 -> Nat.mod (Nat.add n (Nat.mul 2 n1)) (Nat.mul 2 n2) = Nat.add n (Nat.mul 2 (Nat.mod n1 n2))",
            ),
            (
                names::TWO_POW_ADD,
                "(n : Nat) -> (n1 : Nat) -> Clean.BVC.bvTwoPow (Nat.add n n1) = Nat.mul (Clean.BVC.bvTwoPow n) (Clean.BVC.bvTwoPow n1)",
            ),
            (
                names::ADD_MUL_MOD_MOD,
                "(n : Nat) -> (n1 : Nat) -> (n2 : Nat) -> (n3 : Nat) -> Nat.lt 0 n3 -> Nat.mod (Nat.add n (Nat.mul n1 (Nat.mod n2 n3))) n3 = Nat.mod (Nat.add n (Nat.mul n1 n2)) n3",
            ),
            (names::BTN_BLE, "(n : Nat) -> Nat.lt n 2 -> Trust.BVV.btn (Nat.ble 1 n) = n"),
            (
                names::FULL_ADDER,
                "(b : Bool) -> (b1 : Bool) -> (b2 : Bool) -> Nat.add (Nat.add (Trust.BVV.btn b) (Trust.BVV.btn b1)) (Trust.BVV.btn b2) = Nat.add (Trust.BVV.btn (Clean.BVI.xor3 b b1 b2)) (Nat.mul 2 (Trust.BVV.btn (Clean.BVI.maj b b1 b2)))",
            ),
            (
                names::ADD_REC_M_VAL,
                "(x : List Bool) -> (x1 : List Bool) -> (b : Bool) -> Clean.BVC.bvToNat (Clean.BVI.addRecM x x1 b) = Nat.mod (Nat.add (Nat.add (Clean.BVC.bvToNat x) (Clean.BVC.bvToNat x1)) (Trust.BVV.btn b)) (Clean.BVC.bvTwoPow (Clean.BVC.bvLen x))",
            ),
            (
                names::TO_NAT_NAT_TO_BV,
                "(n : Nat) -> (n1 : Nat) -> Clean.BVC.bvToNat (Clean.BVC.natToBvAux n n1) = Nat.mod n1 (Clean.BVC.bvTwoPow n)",
            ),
            (
                names::INJ,
                "(x : List Bool) -> (x1 : List Bool) -> Clean.BVC.bvLen x = Clean.BVC.bvLen x1 -> Clean.BVC.bvToNat x = Clean.BVC.bvToNat x1 -> x = x1",
            ),
            (
                names::BV_MUL_VAL,
                "(x : List Bool) -> (x1 : List Bool) -> Clean.BVC.bvToNat (Clean.BVC.bvMul x x1) = Nat.mod (Nat.mul (Clean.BVC.bvToNat x) (Clean.BVC.bvToNat x1)) (Clean.BVC.bvTwoPow (Clean.BVC.bvLen x1))",
            ),
            (
                names::BV_NOT_VAL,
                "(x : List Bool) -> Nat.add (Nat.add (Clean.BVC.bvToNat (Clean.BVC.bvNot x)) (Clean.BVC.bvToNat x)) 1 = Clean.BVC.bvTwoPow (Clean.BVC.bvLen x)",
            ),
            (
                names::TO_NAT_APPEND,
                "(x : List Bool) -> (x1 : List Bool) -> Clean.BVC.bvToNat (Clean.BVC.bvAppend x x1) = Nat.add (Clean.BVC.bvToNat x) (Nat.mul (Clean.BVC.bvTwoPow (Clean.BVC.bvLen x)) (Clean.BVC.bvToNat x1))",
            ),
        ];
        let all = theorems().expect("builders");
        for (name, text) in expected {
            let (_, ty, _) = all.iter().find(|(n, _, _)| *n == name).expect("listed");
            assert_eq!(ty.to_string(), text, "{name}");
        }
    }

    /// The kernel's verdict on `val : ty` in the value environment.
    fn kernel_check(val: Expr, ty: Expr) -> Result<(), String> {
        run_recheck_thread("bv-value-check", move || {
            let env = value_env()?;
            let tc = TypeChecker::with_mode(&env, env.mode());
            tc.check_type(&val, &ty).map_err(|e| format!("{e:?}"))
        })
        .map_err(|e| e.to_string())?
    }

    /// `r < n` at literals, by `succ r` steps from `Nat.le.refl (succ r)`.
    fn lt_lit(r: u64, n: u64) -> Expr {
        assert!(r < n);
        let mut h = le_refl(nlit(r + 1));
        for k in (r + 1)..n {
            h = le_step(nlit(r + 1), nlit(k), h);
        }
        h
    }

    /// T-U3. Each premise is needed: at a witness where every OTHER premise
    /// holds (each checked by the kernel at literals), the conclusion is false,
    /// and the kernel refuses `Eq.refl` for it. The witnesses are small, so the
    /// kernel's `%` computes in a few steps.
    #[test]
    fn premises_are_needed_kernel_counterexamples() {
        let n = |v: u64| nlit(v);
        let holds = |val: Expr, ty: Expr, what: &str| {
            kernel_check(val, ty).unwrap_or_else(|e| panic!("{what} should hold: {e}"));
        };
        let refuted = |lhs: Expr, rhs: Expr, what: &str| {
            assert!(
                kernel_check(refl(nat(), lhs.clone()), eq(nat(), lhs, rhs)).is_err(),
                "{what}: the conclusion was accepted"
            );
        };

        // div_mod_cancel without `m < n`: n=2 d=0 q=1 m=2 r=0.
        holds(lt_lit(0, 2), nlt(n(0), n(2)), "r < n");
        let e = |d: u64, m: u64, q: u64, r: u64| {
            eq(nat(), nadd(nmul(n(2), n(d)), n(m)), nadd(nmul(n(2), n(q)), n(r)))
        };
        holds(refl(nat(), n(2)), e(0, 2, 1, 0), "2*0 + 2 = 2*1 + 0");
        refuted(n(0), n(1), "div_mod_cancel without m < n");
        // div_mod_cancel without `r < n`: n=2 d=1 q=0 m=0 r=2.
        holds(lt_lit(0, 2), nlt(n(0), n(2)), "m < n");
        holds(refl(nat(), n(2)), e(1, 0, 0, 2), "2*1 + 0 = 2*0 + 2");
        refuted(n(1), n(0), "div_mod_cancel without r < n");

        // mod_unique / div_unique without `r < n`: a=5 n=2 q=1 r=3.
        holds(refl(nat(), n(5)), eq(nat(), n(5), nadd(n(3), nmul(n(2), n(1)))), "5 = 3 + 2*1");
        refuted(nmod(n(5), n(2)), n(3), "mod_unique without r < n");
        refuted(ndiv(n(5), n(2)), n(1), "div_unique without r < n");

        // bit_split_mod without `b < 2`: b=2 m=0 p=1.
        holds(lt_lit(0, 1), nlt(n(0), n(1)), "0 < p");
        refuted(
            nmod(nadd(n(2), nmul(n(2), n(0))), nmul(n(2), n(1))),
            nadd(n(2), nmul(n(2), nmod(n(0), n(1)))),
            "bit_split_mod without b < 2",
        );

        // And the theorems themselves, instantiated at a true witness, are
        // accepted: `mod_unique 5 2 2 1 (1 < 2) (5 = 1 + 2*2) : 5 % 2 = 1`.
        let inst =
            cite(names::MOD_UNIQUE, [n(5), n(2), n(2), n(1), lt_lit(1, 2), refl(nat(), n(5))]);
        holds(inst, eq(nat(), nmod(n(5), n(2)), n(1)), "mod_unique at 5, 2");
    }

    /// A concrete bit list, least significant bit first.
    fn bl(bits: &[bool]) -> Expr {
        bits.iter()
            .rev()
            .fold(kx::nil(), |acc, &b| kx::cons(if b { kx::btrue() } else { kx::bfalse() }, acc))
    }

    /// T-U3 for the bit and list lemmas. At small concrete lists where every
    /// OTHER premise holds (checked by the kernel), the conclusion without the
    /// premise or term under test is false, and the kernel refuses `Eq.refl`
    /// for it; the theorem itself, instantiated there, is accepted.
    #[test]
    fn list_premises_are_needed_kernel_counterexamples() {
        let n = |v: u64| nlit(v);
        let holds = |val: Expr, ty: Expr, what: &str| {
            kernel_check(val, ty).unwrap_or_else(|e| panic!("{what} should hold: {e}"));
        };
        let refuted = |ty: Expr, lhs: Expr, rhs: Expr, what: &str| {
            assert!(
                kernel_check(refl(ty.clone(), lhs.clone()), eq(ty, lhs, rhs)).is_err(),
                "{what}: the conclusion was accepted"
            );
        };
        let (t, f) = (true, false);

        // bvMul_val without `% 2^(L b)`: 3 * 3 = 9, but the 2-bit product is 1.
        let (a, b) = (bl(&[t, t]), bl(&[t, t]));
        let prod = val(bvmul(a.clone(), b.clone()));
        holds(refl(nat(), prod.clone()), eq(nat(), prod.clone(), n(1)), "V (bvMul 3 3) = 1");
        refuted(nat(), prod.clone(), nmul(val(a.clone()), val(b.clone())), "bvMul_val without %");
        holds(
            cite(names::BV_MUL_VAL, [a.clone(), b.clone()]),
            eq(nat(), prod, nmod(nmul(val(a.clone()), val(b.clone())), two_pow(bvlen(b.clone())))),
            "bvMul_val at 3, 3",
        );

        // addRecM_val without the carry: [f] + [f] + carry 1 is [t] (value 1).
        let (xs, ys) = (bl(&[f]), bl(&[f]));
        let sum = val(addm(xs.clone(), ys.clone(), kx::btrue()));
        holds(refl(nat(), sum.clone()), eq(nat(), sum.clone(), n(1)), "0 + 0 + 1 = 1");
        refuted(
            nat(),
            sum.clone(),
            nmod(nadd(val(xs.clone()), val(ys.clone())), two_pow(bvlen(xs.clone()))),
            "addRecM_val without the carry",
        );
        holds(
            cite(names::ADD_REC_M_VAL, [xs.clone(), ys.clone(), kx::btrue()]),
            eq(
                nat(),
                sum,
                nmod(
                    nadd(nadd(val(xs.clone()), val(ys.clone())), btn(kx::btrue())),
                    two_pow(bvlen(xs.clone())),
                ),
            ),
            "addRecM_val at [f], [f], true",
        );

        // inj without `L xs = L ys`: [f] and [] both have value 0.
        let (xs, ys) = (bl(&[f]), bl(&[]));
        holds(refl(nat(), n(0)), eq(nat(), val(xs.clone()), val(ys.clone())), "V [f] = V []");
        refuted(lb(), xs, ys, "inj without the length premise");
        // inj without `V xs = V ys`: [f] and [t] have length 1.
        let (xs, ys) = (bl(&[f]), bl(&[t]));
        holds(refl(nat(), n(1)), eq(nat(), bvlen(xs.clone()), bvlen(ys.clone())), "L [f] = L [t]");
        refuted(lb(), xs, ys, "inj without the value premise");

        // bvNot_val without the `+ 1`: at [], 0 + 0 is not 2^0.
        let e = bl(&[]);
        let nv = nadd(val(kx::bv_not(e.clone())), val(e.clone()));
        holds(
            refl(nat(), n(1)),
            eq(nat(), nadd(nv.clone(), n(1)), two_pow(bvlen(e.clone()))),
            "V (bvNot []) + V [] + 1 = 2^0",
        );
        refuted(nat(), nv, two_pow(bvlen(e)), "bvNot_val without + 1");

        // toNat_append without the `2^(L xs)` factor: [f] ++ [t] is 2, not 0 + 1.
        let (xs, ys) = (bl(&[f]), bl(&[t]));
        let app = val(bv_append(xs.clone(), ys.clone()));
        holds(refl(nat(), n(2)), eq(nat(), app.clone(), n(2)), "V ([f] ++ [t]) = 2");
        refuted(nat(), app, nadd(val(xs), val(ys)), "toNat_append without the place value");

        // btn_ble without `r < 2`: btn (ble 1 2) is 1.
        holds(refl(nat(), n(1)), eq(nat(), btn(nble(n(1), n(2))), n(1)), "btn (ble 1 2) = 1");
        refuted(nat(), btn(nble(n(1), n(2))), n(2), "btn_ble without r < 2");

        // toNat_natToBv without `% 2^w`: the 3 low bits of 13 are 5.
        let low = val(nat_to_bv(n(3), n(13)));
        holds(refl(nat(), n(5)), eq(nat(), low.clone(), n(5)), "V (natToBvAux 3 13) = 5");
        refuted(nat(), low, n(13), "toNat_natToBv without %");

        // natToBv_toNat and toNat_head_tail at a concrete list.
        let xs = bl(&[t, f, t]);
        holds(
            cite(names::NAT_TO_BV_TO_NAT, [xs.clone()]),
            eq(lb(), nat_to_bv(n(3), n(5)), xs.clone()),
            "natToBvAux 3 5 = [t, f, t]",
        );
        holds(
            cite(names::TO_NAT_HEAD_TAIL, [kx::nil()]),
            eq(nat(), n(0), nadd(n(0), nmul(n(2), n(0)))),
            "toNat_head_tail at []",
        );
    }

    /// Every constant a statement or proof uses is either in [`audited`] or not
    /// a theorem at all (a definition, an inductive, a constructor or a
    /// recursor), and none is an axiom: a new citation cannot bypass the
    /// run-time audit. And no statement or proof applies `Nat.mod`, `Nat.div`,
    /// `bvTwoPow`, `natToBvAux`, `bvMul` or `bvShl` to closed data, so checking
    /// them computes no remainder, quotient, power, conversion or product.
    #[test]
    fn every_citation_is_audited_and_nothing_computes_on_closed_data() {
        use std::collections::HashSet;

        use clean_kernel::ExprKind;
        use clean_kernel::expr::UsedConstants;

        fn closed_heavy_app(e: &Expr, found: &mut Vec<String>) {
            let head = e.get_app_fn();
            if let ExprKind::Const(name, _) = head.kind() {
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
                // A full application (a partial one is the head of the
                // enclosing spine, which is checked there) to closed data.
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

        // The walker sees a closed remainder, and not an open one.
        let mut found = Vec::new();
        closed_heavy_app(&nadd(nlit(1), nmod(nlit(5), nlit(2))), &mut found);
        assert_eq!(found.len(), 1);
        let mut fr = Fresh::new();
        let (x_id, x) = fr.local();
        closed_heavy_app(&lams(vec![(x_id, nat())], nmod(x, nlit(2))), &mut found);
        assert_eq!(found.len(), 1);

        run_recheck_thread("bv-value-citations", || {
            let env = value_env().expect("value theory");
            let audited: HashSet<Name> = audited().into_iter().map(Name::from_string).collect();
            for (name, ty, val) in theorems().expect("builders") {
                let mut used = HashSet::new();
                ty.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
                val.used_constants_dag(UsedConstants::ConstantsOnly, &mut used);
                for c in used {
                    let info = env.get_const(&c).unwrap_or_else(|| panic!("{name}: {c} absent"));
                    assert_ne!(info.kind, ConstantKind::Axiom, "{name} cites the axiom {c}");
                    if info.kind == ConstantKind::Theorem {
                        assert!(audited.contains(&c), "{name} cites {c}, which is not audited");
                    }
                }
                let mut found = Vec::new();
                closed_heavy_app(&ty, &mut found);
                closed_heavy_app(&val, &mut found);
                assert!(found.is_empty(), "{name} computes on closed data: {found:?}");
            }
        })
        .expect("kernel thread");
    }

    /// The statements are not provable by a wrong proof: `div_mod_cancel`'s
    /// term is refused as a proof of the statement without `m < n`, and
    /// `mod_unique`'s as a proof of the statement without `r < n`.
    #[test]
    fn proofs_are_refused_against_weakened_statements() {
        let all = theorems().expect("builders");
        let get = |name: &str| all.iter().find(|(n, _, _)| *n == name).expect("listed").clone();
        // ∀ n d q m r, r < n → n*d + m = n*q + r → d = q
        let (_, _, dmc_val) = get(names::DIV_MOD_CANCEL);
        let weakened = {
            let mut fr = Fresh::new();
            let (bn, nv) = nat_local(&mut fr);
            let (bd, d) = nat_local(&mut fr);
            let (bq, q) = nat_local(&mut fr);
            let (bm, m) = nat_local(&mut fr);
            let (br, r) = nat_local(&mut fr);
            let (hr_id, _) = fr.local();
            let (h_id, _) = fr.local();
            pis(
                vec![
                    bn,
                    bd,
                    bq,
                    bm,
                    br,
                    (hr_id, nlt(r.clone(), nv.clone())),
                    (
                        h_id,
                        eq(
                            nat(),
                            nadd(nmul(nv.clone(), d.clone()), m),
                            nadd(nmul(nv, q.clone()), r),
                        ),
                    ),
                ],
                eq(nat(), d, q),
            )
        };
        assert!(kernel_check(dmc_val, weakened).is_err());
        let (_, _, mu_val) = get(names::MOD_UNIQUE);
        let weakened = {
            let mut fr = Fresh::new();
            let (ba, a) = nat_local(&mut fr);
            let (bn, nv) = nat_local(&mut fr);
            let (bq, q) = nat_local(&mut fr);
            let (br, r) = nat_local(&mut fr);
            let (h_id, _) = fr.local();
            pis(
                vec![
                    ba,
                    bn,
                    bq,
                    br,
                    (h_id, eq(nat(), a.clone(), nadd(r.clone(), nmul(nv.clone(), q)))),
                ],
                eq(nat(), nmod(a, nv), r),
            )
        };
        assert!(kernel_check(mu_val, weakened).is_err());
        // addRecM_val's term is not a proof of the statement without the carry.
        let (_, _, arm_val) = get(names::ADD_REC_M_VAL);
        let weakened = {
            let mut fr = Fresh::new();
            let (bxs, xs) = list_local(&mut fr);
            let (bys, ys) = list_local(&mut fr);
            let (bc, c) = bit_local(&mut fr);
            pis(
                vec![bxs, bys, bc],
                eq(
                    nat(),
                    val(addm(xs.clone(), ys.clone(), c)),
                    nmod(nadd(val(xs.clone()), val(ys)), two_pow(bvlen(xs))),
                ),
            )
        };
        assert!(kernel_check(arm_val, weakened).is_err());
        // bvMul_val's term is not a proof of the statement without the `%`.
        let (_, _, bmv_val) = get(names::BV_MUL_VAL);
        let weakened = {
            let mut fr = Fresh::new();
            let (ba, a) = list_local(&mut fr);
            let (bb, b) = list_local(&mut fr);
            pis(vec![ba, bb], eq(nat(), val(bvmul(a.clone(), b.clone())), nmul(val(a), val(b))))
        };
        assert!(kernel_check(bmv_val, weakened).is_err());
    }
}
