//! Closed universal byte-word reconstruction, retaining the ORIGINAL Nat shift.
use super::*;
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]), [ty, a, b])
}
fn rfl(ty: Expr, a: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
        [ty, a],
    )
}
fn trans(a: Expr, b: Expr, c: Expr, p: Expr, q: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq.trans"), vec![Level::succ(Level::zero())]),
        [list_ty(), a, b, c, p, q],
    )
}
fn cong(input: Expr, out: Expr, a: Expr, b: Expr, f: Expr, p: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        ),
        [input, out, a, b, f, p],
    )
}
fn zip(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str("Clean.BVC.bvZipOr"), [a, b])
}
fn piece(bits: &[Expr; 64], k: usize, pad: bool) -> Expr {
    let byte: [Expr; 8] = bits[k * 8..k * 8 + 8].to_vec().try_into().unwrap();
    if k == 0 {
        return Expr::apps(Expr::const_str("Clean.BVC.bvZeroExt"), [list(&byte), nat(56)]);
    }
    if pad { padded(&byte, (k * 8) as u32).unwrap() } else { original(&byte, (k * 8) as u32) }
}
pub fn word(bits: &[Expr; 64], pad: bool) -> Expr {
    let mut out = piece(bits, 0, pad);
    for k in 1..8 {
        out = zip(out, piece(bits, k, pad));
    }
    out
}
fn fold_bit(value: Expr, position: usize) -> Expr {
    let at = |i| {
        if i == position { value.clone() } else { lit(false) }
    };
    let mut out = at(0);
    for k in 1..8 {
        out = Expr::apps(Expr::const_str("Bool.or"), [out, at(k)]);
    }
    out
}
fn bit_proof(value: Expr, position: usize) -> Expr {
    let motive = Expr::lam(
        BinderInfo::Default,
        boolean(),
        eq(boolean(), fold_bit(Expr::bvar(0), position), Expr::bvar(0)),
    );
    Expr::apps(
        Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]),
        [motive, rfl(boolean(), lit(false)), rfl(boolean(), lit(true)), value],
    )
}
fn cons_congruence() -> Expr {
    let a = Expr::bvar(5);
    let b = Expr::bvar(4);
    let ta = Expr::bvar(3);
    let tb = Expr::bvar(2);
    let before = cons(a.clone(), ta.clone());
    let middle = cons(b.clone(), ta.clone());
    let after = cons(b.clone(), tb.clone());
    let hp = cong(
        boolean(),
        list_ty(),
        a,
        b,
        Expr::lam(BinderInfo::Default, boolean(), cons(Expr::bvar(0), Expr::bvar(4))),
        Expr::bvar(1),
    );
    let tp = cong(
        list_ty(),
        list_ty(),
        ta,
        tb,
        Expr::lam(BinderInfo::Default, list_ty(), cons(Expr::bvar(5), Expr::bvar(0))),
        Expr::bvar(0),
    );
    let body = trans(before, middle, after, hp, tp);
    let body = Expr::lam(BinderInfo::Default, eq(list_ty(), Expr::bvar(2), Expr::bvar(1)), body);
    let body = Expr::lam(BinderInfo::Default, eq(boolean(), Expr::bvar(3), Expr::bvar(2)), body);
    Expr::lam(
        BinderInfo::Default,
        boolean(),
        Expr::lam(
            BinderInfo::Default,
            boolean(),
            Expr::lam(
                BinderInfo::Default,
                list_ty(),
                Expr::lam(BinderInfo::Default, list_ty(), body),
            ),
        ),
    )
}
pub fn expected_type() -> Expr {
    let bits = std::array::from_fn(|i| Expr::bvar(63 - i as u32));
    let mut goal = equality(word(&bits, false), list(&bits));
    for _ in 0..64 {
        goal = Expr::pi(BinderInfo::Default, boolean(), goal);
    }
    goal
}
pub fn proof_pair() -> (Expr, Expr) {
    #[cfg(feature = "test-hooks")]
    assert!(
        !FORBID_PRODUCTION.load(std::sync::atomic::Ordering::SeqCst),
        "word reassembly proof producer forbidden during replay"
    );
    let ids: [FVarId; 64] = std::array::from_fn(|i| FVarId::new(0x6a00_0000 + i as u64));
    let bits = ids.map(Expr::fvar);
    let mut raw = piece(&bits, 0, false);
    let mut normalized = piece(&bits, 0, true);
    let mut normalize = refl(raw.clone());
    for k in 1..8 {
        let a = piece(&bits, k, false);
        let ap = piece(&bits, k, true);
        let proof = Expr::apps(
            Expr::const_str(&format!("Clean.FrameByteShiftV1.shl{}", k * 8)),
            bits[k * 8..k * 8 + 8].iter().cloned(),
        );
        let leaf = |x| Expr::app(Expr::const_str("Clean.BVC.BvF.Leaf"), x);
        normalize = Expr::apps(
            Expr::const_str("Clean.BVC.bvf_or_cong"),
            [
                leaf(raw.clone()),
                leaf(normalized.clone()),
                leaf(a.clone()),
                leaf(ap.clone()),
                normalize,
                proof,
            ],
        );
        raw = zip(raw, a);
        normalized = zip(normalized, ap);
    }
    let mut ta = nil();
    let mut tb = nil();
    let mut list_proof = refl(nil());
    let comb = cons_congruence();
    for i in (0..64).rev() {
        let a = fold_bit(bits[i].clone(), i / 8);
        let b = bits[i].clone();
        let hp = bit_proof(b.clone(), i / 8);
        list_proof = Expr::apps(
            comb.clone(),
            [a.clone(), b.clone(), ta.clone(), tb.clone(), hp, list_proof],
        );
        ta = cons(a, ta);
        tb = cons(b, tb);
    }
    let mut goal = equality(raw.clone(), list(&bits));
    let mut proof = trans(raw, normalized, list(&bits), normalize, list_proof);
    for id in ids.into_iter().rev() {
        goal = Expr::pi(BinderInfo::Default, boolean(), goal.abstract_fvar(id));
        proof = Expr::lam(BinderInfo::Default, boolean(), proof.abstract_fvar(id));
    }
    assert_eq!(goal, expected_type());
    assert!(!proof.has_fvar_quick() && !proof.has_loose_bvars());
    (goal, proof)
}
