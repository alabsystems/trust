// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Kernel term builders for bridge-side theorems over `Clean.BVC` / `Clean.BVI`.
//!
//! The helpers the add-commutation theorems (`add_comm`) were written with,
//! moved here unchanged so later bridge-side value theories build their proof
//! terms the same way. Nothing here carries authority: each function returns
//! an `Expr`, and only the Clean kernel's type check of a finished declaration
//! or discharge term against its statement decides anything.
//!
//! Every builder that moved produces exactly the term `add_comm` produced
//! before the move (`add_comm::tests::statements_proofs_steps_and_label_are_byte_pinned`).
//! The raw `Nat` builders (`nlit`, `nadd`, `nmul`, `nmod`, `ndiv`, `nle`,
//! `nlt`, `two_pow`, `le_refl`, `le_step`) were added for the value theory
//! (`nat_ring`, `bv_value`), and `bv_shl` / `zero_ext` for the
//! strength-reduction theorems (`strength`).

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, FVarId, Level};

use super::kx;

/// Universe level 1 (`Sort 1 = Type`).
pub(crate) fn l1() -> Level {
    Level::succ(Level::zero())
}
pub(crate) fn bool_ty() -> Expr {
    kx::bool_ty()
}
/// `List Bool`.
pub(crate) fn lb() -> Expr {
    kx::list_bool()
}
pub(crate) fn nat() -> Expr {
    Expr::const_str("Nat")
}
/// The constructor `Nat.zero` (not the literal `0`).
pub(crate) fn zero() -> Expr {
    Expr::const_str("Nat.zero")
}
/// The constructor application `Nat.succ n`.
pub(crate) fn succ(n: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.succ"), n)
}
pub(crate) fn prop() -> Expr {
    Expr::sort(Level::zero())
}
/// `@Eq.{1} ty a b`.
pub(crate) fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![l1()]), [ty, a, b])
}
/// `@Eq.refl.{1} ty a : a = a`.
pub(crate) fn refl(ty: Expr, a: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.refl"), vec![l1()]), [ty, a])
}
/// `@Eq.trans.{1} ty a b c h1 h2 : a = c`.
pub(crate) fn trans(ty: Expr, a: Expr, b: Expr, c: Expr, h1: Expr, h2: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.trans"), vec![l1()]), [ty, a, b, c, h1, h2])
}
/// `@Eq.symm.{1} ty a b h : b = a`.
pub(crate) fn symm(ty: Expr, a: Expr, b: Expr, h: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.symm"), vec![l1()]), [ty, a, b, h])
}
/// `@congrArg.{1,1} A B a1 a2 f h : f a1 = f a2`.
pub(crate) fn congr_arg(a_ty: Expr, b_ty: Expr, a1: Expr, a2: Expr, f: Expr, h: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("congrArg"), vec![l1(), l1()]),
        [a_ty, b_ty, a1, a2, f, h],
    )
}
/// `@Eq.subst.{1} A motive a b h base : motive b`.
pub(crate) fn eq_subst(ty: Expr, motive: Expr, a: Expr, b: Expr, h: Expr, base: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq.subst"), vec![l1()]), [ty, motive, a, b, h, base])
}
/// `@False.elim.{0} concl contra`.
pub(crate) fn false_elim(concl: Expr, contra: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]), [concl, contra])
}
/// `@List.rec.{0,0} Bool motive nil cons major`, motive into `Prop`.
pub(crate) fn list_rec_prop(motive: Expr, nil_case: Expr, cons_case: Expr, major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.rec"), vec![Level::zero(), Level::zero()]),
        [bool_ty(), motive, nil_case, cons_case, major],
    )
}
/// `@Bool.rec.{u} motive false_case true_case major`.
pub(crate) fn bool_rec(level: Level, motive: Expr, f: Expr, t: Expr, major: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Bool.rec"), vec![level]), [motive, f, t, major])
}
/// `@Nat.rec.{1} motive z s major`, motive into `Type`.
pub(crate) fn nat_rec1(motive: Expr, z: Expr, s: Expr, major: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Nat.rec"), vec![l1()]), [motive, z, s, major])
}
/// `@Nat.rec.{0} motive z s major`, motive into `Prop`: induction on `Nat`.
pub(crate) fn nat_rec_prop(motive: Expr, z: Expr, s: Expr, major: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]),
        [motive, z, s, major],
    )
}
/// The literal `n` (`Expr::nat_lit`, the form `Clean.BVC.bvToNat` and
/// `bvTwoPow` are written with), not a `Nat.succ` chain.
pub(crate) fn nlit(n: u64) -> Expr {
    Expr::nat_lit(n)
}
/// `Nat.add a b` (raw, not `HAdd.hAdd`).
pub(crate) fn nadd(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [a, b])
}
/// `Nat.mul a b`.
pub(crate) fn nmul(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.mul"), [a, b])
}
/// `Nat.mod a n`.
pub(crate) fn nmod(a: Expr, n: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.mod"), [a, n])
}
/// `Nat.div a n`.
pub(crate) fn ndiv(a: Expr, n: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.div"), [a, n])
}
/// `Nat.le a b` (the inductive, not `LE.le`).
pub(crate) fn nle(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.le"), [a, b])
}
/// `Nat.lt a b`, which unfolds to `Nat.le (Nat.succ a) b`.
pub(crate) fn nlt(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.lt"), [a, b])
}
/// `Clean.BVC.bvTwoPow k` (`2^k`, `Nat.rec 1 (fun _ ih => Nat.mul 2 ih)`).
pub(crate) fn two_pow(k: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.BVC.bvTwoPow"), k)
}
/// `@Nat.le.refl n : Nat.le n n`.
pub(crate) fn le_refl(n: Expr) -> Expr {
    Expr::app(Expr::const_str("Nat.le.refl"), n)
}
/// `@Nat.le.step n m h : Nat.le n (Nat.succ m)`, given `h : Nat.le n m`.
pub(crate) fn le_step(n: Expr, m: Expr, h: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.le.step"), [n, m, h])
}
/// `Clean.BVC.bvLen xs`.
pub(crate) fn bvlen(xs: Expr) -> Expr {
    kx::bv_len(xs)
}
/// `Clean.BVI.addRecM xs ys c`.
pub(crate) fn addm(xs: Expr, ys: Expr, c: Expr) -> Expr {
    kx::add_rec_m(xs, ys, c)
}
/// A three-input gate `name a b c`.
pub(crate) fn gate(name: &str, a: Expr, b: Expr, c: Expr) -> Expr {
    Expr::apps(Expr::const_str(name), [a, b, c])
}
/// `Clean.BVI.xor3 a b c` (the full adder's sum bit).
pub(crate) fn xor3(a: Expr, b: Expr, c: Expr) -> Expr {
    gate("Clean.BVI.xor3", a, b, c)
}
/// `Clean.BVI.maj a b c` (the full adder's carry bit).
pub(crate) fn maj(a: Expr, b: Expr, c: Expr) -> Expr {
    gate("Clean.BVI.maj", a, b, c)
}
pub(crate) fn bhead(v: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.BVI.bhead"), v)
}
pub(crate) fn btail(v: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.BVI.btail"), v)
}
/// `Clean.BVC.bvMul a b`.
pub(crate) fn bvmul(a: Expr, b: Expr) -> Expr {
    kx::bv_mul(a, b)
}
/// `Nat.ble a b : Bool`.
pub(crate) fn nble(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.ble"), [a, b])
}
/// `Clean.BVC.bvToNat xs` (the LSB-first value of a bit list).
pub(crate) fn to_nat(xs: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.BVC.bvToNat"), xs)
}
/// `Clean.BVC.natToBvAux w v` (the `w` low bits of `v`, LSB first).
pub(crate) fn nat_to_bv(w: Expr, v: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.natToBvAux"), [w, v])
}
/// `Clean.BVC.bvAppend xs ys` (`xs ++ ys`).
pub(crate) fn bv_append(xs: Expr, ys: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.bvAppend"), [xs, ys])
}
/// `Clean.BVC.bvReplF k` (`k` copies of `false`).
pub(crate) fn repl_f(k: Expr) -> Expr {
    Expr::app(Expr::const_str("Clean.BVC.bvReplF"), k)
}
/// `Clean.BVC.bvShl a n`, which unfolds to
/// `natToBvAux (bvLen a) (bvToNat a * bvTwoPow (bvToNat n))`.
pub(crate) fn bv_shl(a: Expr, n: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.bvShl"), [a, n])
}
/// `Clean.BVC.bvZeroExt e k`, which unfolds to `bvAppend e (bvReplF k)`.
pub(crate) fn zero_ext(e: Expr, k: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.bvZeroExt"), [e, k])
}

/// Fresh free variables for building binders. A term is closed by [`lams`] /
/// [`pis`] before the kernel sees it, so the ids only have to be distinct
/// within one declaration.
pub(crate) struct Fresh(u64);

impl Fresh {
    pub(crate) fn new() -> Self {
        Self(0x8000_0000_0000_0000)
    }
    pub(crate) fn local(&mut self) -> (FVarId, Expr) {
        let id = FVarId::new(self.0);
        self.0 += 1;
        (id, Expr::fvar(id))
    }
}

/// `fun (x1 : T1) … (xn : Tn) => body`, binders outermost first.
pub(crate) fn lams(binders: Vec<(FVarId, Expr)>, body: Expr) -> Expr {
    binders
        .into_iter()
        .rev()
        .fold(body, |acc, (id, ty)| Expr::lam(BinderInfo::Default, ty, acc.abstract_fvar(id)))
}

/// `∀ (x1 : T1) … (xn : Tn), body`, binders outermost first.
pub(crate) fn pis(binders: Vec<(FVarId, Expr)>, body: Expr) -> Expr {
    binders
        .into_iter()
        .rev()
        .fold(body, |acc, (id, ty)| Expr::pi(BinderInfo::Default, ty, acc.abstract_fvar(id)))
}

/// `fun n => Nat.rec (fun _ => Prop) True (fun _ _ => False) n`: `True` at
/// zero, `False` at a successor.
pub(crate) fn nat_disc(fr: &mut Fresh) -> Expr {
    let (n_id, n) = fr.local();
    let motive = {
        let (w_id, _) = fr.local();
        lams(vec![(w_id, nat())], prop())
    };
    let succ_case = {
        let (m_id, _) = fr.local();
        let (ih_id, _) = fr.local();
        lams(vec![(m_id, nat()), (ih_id, prop())], Expr::const_str("False"))
    };
    lams(vec![(n_id, nat())], nat_rec1(motive, Expr::const_str("True"), succ_case, n))
}

/// From `h : zero = succ k`, a proof of `concl`.
pub(crate) fn absurd_zero_eq_succ(fr: &mut Fresh, k: Expr, h: Expr, concl: Expr) -> Expr {
    let contra = eq_subst(nat(), nat_disc(fr), zero(), succ(k), h, Expr::const_str("True.intro"));
    false_elim(concl, contra)
}

/// `fun z => Nat.rec (fun _ => Nat) zero (fun p _ => p) z`.
pub(crate) fn nat_pred(fr: &mut Fresh) -> Expr {
    let (z_id, z) = fr.local();
    let motive = {
        let (w_id, _) = fr.local();
        lams(vec![(w_id, nat())], nat())
    };
    let succ_case = {
        let (p_id, p) = fr.local();
        let (ih_id, _) = fr.local();
        lams(vec![(p_id, nat()), (ih_id, nat())], p)
    };
    lams(vec![(z_id, nat())], nat_rec1(motive, zero(), succ_case, z))
}

#[cfg(test)]
mod tests {
    use clean_kernel::TypeChecker;

    use super::super::{discharge_env, run_recheck_thread};
    use super::*;

    /// `nat_rec_prop` is induction into `Prop`: `∀ n, n = n` by `Nat.rec`
    /// (refl at zero, `congrArg succ` of the hypothesis at a successor) is
    /// accepted, and the same recursor with a wrong successor case
    /// (`Eq.refl` of `zero` offered for `succ k = succ k`) is rejected.
    #[test]
    fn nat_rec_prop_is_kernel_checked_induction() {
        run_recheck_thread("kterm-nat-rec-prop", || {
            let env = discharge_env(&[], &[]).expect("base");
            let tc = TypeChecker::with_mode(&env, env.mode());
            let mut fr = Fresh::new();
            let stmt = |n: &Expr| eq(nat(), n.clone(), n.clone());
            let ty = {
                let (n_id, n) = fr.local();
                pis(vec![(n_id, nat())], stmt(&n))
            };
            let build = |fr: &mut Fresh, wrong: bool| {
                let (n_id, n) = fr.local();
                let motive = {
                    let (w_id, w) = fr.local();
                    lams(vec![(w_id, nat())], stmt(&w))
                };
                let (k_id, k) = fr.local();
                let (ih_id, ih) = fr.local();
                let step = if wrong {
                    refl(nat(), zero())
                } else {
                    congr_arg(nat(), nat(), k.clone(), k.clone(), Expr::const_str("Nat.succ"), ih)
                };
                let s = lams(vec![(k_id, nat()), (ih_id, stmt(&k))], step);
                lams(vec![(n_id, nat())], nat_rec_prop(motive, refl(nat(), zero()), s, n))
            };
            let good = build(&mut fr, false);
            let bad = build(&mut fr, true);
            assert!(tc.check_type(&good, &ty).is_ok(), "induction rejected");
            assert!(tc.check_type(&bad, &ty).is_err(), "a wrong successor case was accepted");
        })
        .expect("kernel thread");
    }
}
