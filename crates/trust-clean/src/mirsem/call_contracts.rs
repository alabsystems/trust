// Call contracts in the object language: a callee's postcondition holding at
// its return, and the mutual-recursion form where two contracts are discharged
// together under a decreasing rank.

use super::*;

/// Register the inter-procedural CALL inductive `Call : Type` (one constructor
/// `Call.mk : Nat → Operand → Int → Call`). Idempotent. See [`MIRSEM_CALL`].
pub(super) fn register_call_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CALL);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // Call.mk : Nat → Operand → Int → Call
    let mk_ctor = Constructor {
        name: Name::from_string(MIRSEM_CALL_MK),
        type_: Expr::pi(
            bd(),
            cst("Nat"),
            Expr::pi(bd(), operand_ty(), Expr::pi(bd(), int_ty(), cst(MIRSEM_CALL))),
        ),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![mk_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(Call): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.call_result : Call → Int` (idempotent) — the call site's
/// DENOTATION via the `Call` recursor: `Call.rec (λ_.Int) (λ callee arg ret. ret)`.
/// A genuine recursor projection of the (separately-verified) callee return.
pub(super) fn register_call_result(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CALL_RESULT);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // @Call.rec.{1} : motive lands in Int : Type ⇒ Sort 1.
    let call_rec =
        Expr::const_(Name::from_string(MIRSEM_CALL_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst(MIRSEM_CALL), int_ty());
    // minor : λ (callee:Nat)(arg:Operand)(ret:Int). ret   (ret=0)
    let minor = Expr::lam(
        bd(),
        cst("Nat"),
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), Expr::bvar(0))),
    );
    // λ (c : Call). Call.rec (λ_.Int) minor c
    let body = Expr::apps(call_rec, [motive, minor, Expr::bvar(0)]);
    let val = Expr::lam(bd(), cst(MIRSEM_CALL), body);
    let ty = Expr::pi(bd(), cst(MIRSEM_CALL), int_ty());
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(call_result): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.call_callee : Call → Nat` (idempotent) — the callee-ID
/// projection via the `Call` recursor: `Call.rec (λ callee arg ret. callee)`. See
/// [`MIRSEM_CALL_CALLEE`].
pub(super) fn register_call_callee(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CALL_CALLEE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // @Call.rec.{1} : motive lands in Nat : Type ⇒ Sort 1.
    let call_rec =
        Expr::const_(Name::from_string(MIRSEM_CALL_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst(MIRSEM_CALL), cst("Nat"));
    // minor : λ (callee:Nat)(arg:Operand)(ret:Int). callee   (callee=2)
    let minor = Expr::lam(
        bd(),
        cst("Nat"),
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), Expr::bvar(2))),
    );
    let body = Expr::apps(call_rec, [motive, minor, Expr::bvar(0)]);
    let val = Expr::lam(bd(), cst(MIRSEM_CALL), body);
    let ty = Expr::pi(bd(), cst(MIRSEM_CALL), cst("Nat"));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(call_callee): {e:?}"))?;
    Ok(())
}

/// `call_callee c : Nat`.
pub(super) fn call_callee_app(c: Expr) -> Expr {
    Expr::app(cst(MIRSEM_CALL_CALLEE), c)
}

/// `call_result c : Int`.
pub(super) fn call_result_app(c: Expr) -> Expr {
    Expr::app(cst(MIRSEM_CALL_RESULT), c)
}

/// `Post (call_callee c) (call_result c) : Prop` — callee `call_callee c`'s
/// contract holds at this call's result. `post_ref`/`c_ref` denote `Post`/`c` at
/// the current depth.
pub(super) fn post_holds(post_ref: Expr, c_ref: Expr) -> Expr {
    Expr::apps(post_ref, [call_callee_app(c_ref.clone()), call_result_app(c_ref)])
}

/// The MUTUAL-STEP inner hypothesis as a kernel `Prop`:
/// `∀ (c' : Call), Nat.lt (rank c') (rank c) → Post (call_callee c') (call_result c')`
/// — every STRICTLY-SMALLER-rank call already satisfies its callee's contract.
/// `post_ref`/`rank_ref`/`c_ref` denote `Post`/`rank`/`c` at the depth this is
/// BUILT (before the inner `∀ c'`); lifted internally.
pub(super) fn mutual_inner_hyp(post_ref: &Expr, rank_ref: &Expr, c_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    // ∀ (c':Call), Nat.lt (rank c') (rank c) → Post (call_callee c') (call_result c')
    //   dom (under ∀ c'): c'=0, refs +1.
    let rank_c2 = Expr::app(lift(rank_ref, 1), Expr::bvar(0));
    let rank_c = Expr::app(lift(rank_ref, 1), lift(c_ref, 1));
    let dom = nat_lt(rank_c2, rank_c);
    //   cod (under ∀ c' + 1 arrow): c'=1, refs +2.
    let cod = post_holds(lift(post_ref, 2), Expr::bvar(1));
    Expr::pi(bd(), cst(MIRSEM_CALL), Expr::pi(bd(), dom, cod))
}

/// The MUTUAL-STEP hypothesis as a kernel `Prop`:
/// `∀ (c : Call), (inner_hyp c) → Post (call_callee c) (call_result c)`.
/// `post_ref`/`rank_ref` denote `Post`/`rank` at the depth this is BUILT (before
/// the `∀ c`); lifted internally.
pub(super) fn mutual_step_hyp(post_ref: &Expr, rank_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    // ∀ (c:Call), (inner_hyp c) → Post (call_callee c) (call_result c)
    //   under ∀ c: c=0, refs +1.
    let inner = mutual_inner_hyp(&lift(post_ref, 1), &lift(rank_ref, 1), &Expr::bvar(0));
    //   cod (under ∀ c + inner arrow): c=1, refs +2.
    let cod = post_holds(lift(post_ref, 2), Expr::bvar(1));
    Expr::pi(bd(), cst(MIRSEM_CALL), Expr::pi(bd(), inner, cod))
}

/// The DEPTH-BOUNDED mutual-contract lemma TYPE. See [`MIRSEM_BOUNDED_SAT`].
pub(super) fn bounded_sat_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let post_ty = Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), int_ty(), Expr::prop()));
    let rank_ty = Expr::pi(bd(), cst(MIRSEM_CALL), cst("Nat"));
    // inside `∀ Post ∀ rank`: rank=0, Post=1.
    let step = mutual_step_hyp(&Expr::bvar(1), &Expr::bvar(0));
    // conclusion: ∀ k c, Nat.le (rank c) k → Post (call_callee c) (call_result c)
    //   inside `∀ Post ∀ rank (step→) ∀ k ∀ c`: c=0,k=1,step=2,rank=3,Post=4.
    let rank_c = Expr::app(Expr::bvar(3), Expr::bvar(0));
    let le_hyp = nat_le(rank_c, Expr::bvar(1));
    // post_holds (under one more arrow): c=1,k=2,step=3,rank=4,Post=5.
    let cod = post_holds(Expr::bvar(5), Expr::bvar(1));
    let arrow = Expr::pi(bd(), le_hyp, cod);
    let body_c = Expr::pi(bd(), cst(MIRSEM_CALL), arrow);
    let body_k = Expr::pi(bd(), cst("Nat"), body_c);
    let after_step = Expr::pi(bd(), step, body_k);
    Expr::pi(bd(), post_ty, Expr::pi(bd(), rank_ty, after_step))
}

/// The DEPTH-BOUNDED mutual-contract lemma PROOF — well-founded descent by
/// `Nat.rec` on the rank budget `k`. See [`MIRSEM_BOUNDED_SAT`].
pub(super) fn bounded_sat_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let post_ty = Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), int_ty(), Expr::prop()));
    let rank_ty = Expr::pi(bd(), cst(MIRSEM_CALL), cst("Nat"));

    // depth inside `λ Post λ rank λ step`: step=0,rank=1,Post=2.

    // motive Q : Nat → Prop = λ k. ∀ c, Nat.le (rank c) k → post_holds Post c
    //   under `λ Post λ rank λ step λ k`: k=0,step=1,rank=2,Post=3; then `∀ c`: c=0,k=1,step=2,rank=3,Post=4.
    let motive = {
        let rank_c = Expr::app(Expr::bvar(3), Expr::bvar(0));
        let le_hyp = nat_le(rank_c, Expr::bvar(1));
        // post_holds (under one more arrow): c=1,k=2,step=3,rank=4,Post=5.
        let cod = post_holds(Expr::bvar(5), Expr::bvar(1));
        let arrow = Expr::pi(bd(), le_hyp, cod);
        Expr::lam(bd(), cst("Nat"), Expr::pi(bd(), cst(MIRSEM_CALL), arrow))
    };

    // zero_case : ∀ c, Nat.le (rank c) 0 → post_holds Post c
    //   = λ c (hk : Nat.le (rank c) 0). step c innerH
    //     where innerH : ∀ c', Nat.lt (rank c') (rank c) → post_holds Post c'
    //         = λ c' (hlt : Nat.lt (rank c') (rank c)).
    //             False.elim (post_holds Post c')
    //               (Nat.not_succ_le_zero (rank c')
    //                  (nat_le_trans (succ (rank c')) (rank c) 0 hlt hk))
    //   under `λ Post λ rank λ step λ c λ hk`: hk=0,c=1,step=2,rank=3,Post=4.
    let zero_case = {
        // innerH : ∀ c' (hlt). False.elim …
        //   under `..λ c λ hk λ c' λ hlt`: hlt=0,c'=1,hk=2,c=3,step=4,rank=5,Post=6.
        let inner = {
            // domain hlt : Nat.lt (rank c') (rank c)  (under λ c': c'=0,hk=1,c=2,step=3,rank=4,Post=5)
            let rank_c2_dom = Expr::app(Expr::bvar(4), Expr::bvar(0));
            let rank_c_dom = Expr::app(Expr::bvar(4), Expr::bvar(2));
            let hlt_ty = nat_lt(rank_c2_dom, rank_c_dom);
            // body under `λ hlt`: hlt=0,c'=1,hk=2,c=3,step=4,rank=5,Post=6.
            let rank_c2 = Expr::app(Expr::bvar(5), Expr::bvar(1)); // rank c'
            let rank_c = Expr::app(Expr::bvar(5), Expr::bvar(3)); // rank c
            // nat_le_trans (succ (rank c')) (rank c) 0 hlt hk : Nat.le (succ (rank c')) 0
            let trans = Expr::apps(
                cst(MIRSEM_NAT_LE_TRANS),
                [
                    nat_succ(rank_c2.clone()),
                    rank_c,
                    Expr::nat_lit(0),
                    Expr::bvar(0), // hlt : Nat.lt (rank c')(rank c) ≡ Nat.le (succ (rank c')) (rank c)
                    Expr::bvar(2), // hk : Nat.le (rank c) 0
                ],
            );
            let false_pf = Expr::apps(
                Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
                [rank_c2, trans],
            );
            // @False.elim.{0} (post_holds Post c') false_pf
            let goal = post_holds(Expr::bvar(6), Expr::bvar(1)); // Post (callee c')(result c')
            let elim = Expr::apps(
                Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                [goal, false_pf],
            );
            // λ c' (hlt). elim
            Expr::lam(bd(), cst(MIRSEM_CALL), Expr::lam(bd(), hlt_ty, elim))
        };
        // step c innerH  (under λ c λ hk: c=1,hk=0,step=2,rank=3,Post=4)
        let body = Expr::apps(Expr::bvar(2), [Expr::bvar(1), inner]);
        // hk : Nat.le (rank c) 0  (under λ c: c=0,step=1,rank=2,Post=3)
        let hk_ty = nat_le(Expr::app(Expr::bvar(2), Expr::bvar(0)), Expr::nat_lit(0));
        Expr::lam(bd(), cst(MIRSEM_CALL), Expr::lam(bd(), hk_ty, body))
    };

    // succ_case : λ (k':Nat)(ih : Q k')(c : Call)(hk : Nat.le (rank c) (succ k')).
    //   step c innerH where innerH : ∀ c' (hlt : Nat.lt (rank c') (rank c)).
    //       ih c' (Nat.le_of_succ_le_succ (rank c') k'
    //               (nat_le_trans (succ (rank c')) (rank c) (succ k') hlt hk))
    //   under `..λ k' λ ih λ c λ hk`: hk=0,c=1,ih=2,k'=3,step=4,rank=5,Post=6.
    let succ_case = {
        // ih : Q k'  (after λ k', before λ ih): under `..λ step λ k'`: k'=0,step=1,rank=2,Post=3.
        let ih_ty = {
            // ∀ c, Nat.le (rank c) k' → post_holds Post c
            // under `∀ c`: c=0,k'=1,step=2,rank=3,Post=4
            let le_hyp = nat_le(Expr::app(Expr::bvar(3), Expr::bvar(0)), Expr::bvar(1));
            // post_holds (under arrow): c=1,k'=2,step=3,rank=4,Post=5
            let cod = post_holds(Expr::bvar(5), Expr::bvar(1));
            Expr::pi(bd(), cst(MIRSEM_CALL), Expr::pi(bd(), le_hyp, cod))
        };
        // innerH : ∀ c' (hlt). ih c' bound
        //   under `..λ c λ hk λ c' λ hlt`: hlt=0,c'=1,hk=2,c=3,ih=4,k'=5,step=6,rank=7,Post=8.
        let inner = {
            // domain hlt : Nat.lt (rank c') (rank c)  (under λ c': c'=0,hk=1,c=2,ih=3,k'=4,step=5,rank=6,Post=7)
            let rank_c2_dom = Expr::app(Expr::bvar(6), Expr::bvar(0));
            let rank_c_dom = Expr::app(Expr::bvar(6), Expr::bvar(2));
            let hlt_ty = nat_lt(rank_c2_dom, rank_c_dom);
            // body under `λ hlt`: hlt=0,c'=1,hk=2,c=3,ih=4,k'=5,step=6,rank=7,Post=8.
            let rank_c2 = Expr::app(Expr::bvar(7), Expr::bvar(1)); // rank c'
            let rank_c = Expr::app(Expr::bvar(7), Expr::bvar(3)); // rank c
            // nat_le_trans (succ (rank c')) (rank c) (succ k') hlt hk
            let trans = Expr::apps(
                cst(MIRSEM_NAT_LE_TRANS),
                [
                    nat_succ(rank_c2.clone()),
                    rank_c,
                    nat_succ(Expr::bvar(5)), // succ k'
                    Expr::bvar(0),           // hlt
                    Expr::bvar(2),           // hk
                ],
            );
            // Nat.le_of_succ_le_succ (rank c') k' trans : Nat.le (rank c') k'
            let bound = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
                [rank_c2, Expr::bvar(5), trans],
            );
            // ih c' bound
            let ih_app = Expr::apps(Expr::bvar(4), [Expr::bvar(1), bound]);
            Expr::lam(bd(), cst(MIRSEM_CALL), Expr::lam(bd(), hlt_ty, ih_app))
        };
        // step c innerH  (under λ k' λ ih λ c λ hk: hk=0,c=1,ih=2,k'=3,step=4,rank=5,Post=6)
        let body = Expr::apps(Expr::bvar(4), [Expr::bvar(1), inner]);
        // hk : Nat.le (rank c) (succ k')  (under λ k' λ ih λ c: c=0,ih=1,k'=2,step=3,rank=4,Post=5)
        let hk_ty = nat_le(Expr::app(Expr::bvar(4), Expr::bvar(0)), nat_succ(Expr::bvar(2)));
        Expr::lam(
            bd(),
            cst("Nat"), // k'
            Expr::lam(
                bd(),
                ih_ty,                                                           // ih
                Expr::lam(bd(), cst(MIRSEM_CALL), Expr::lam(bd(), hk_ty, body)), // c, hk
            ),
        )
    };

    // λ Post rank step k. @Nat.rec.{0} motive zero_case succ_case k
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        post_ty,
        Expr::lam(
            bd(),
            rank_ty,
            Expr::lam(
                bd(),
                mutual_step_hyp(&Expr::bvar(1), &Expr::bvar(0)),
                Expr::lam(bd(), cst("Nat"), rec_applied),
            ),
        ),
    )
}

/// The MUTUAL-RECURSION CONTRACT rule TYPE. `claimed_concl_post = Some(p)`
/// overrides ONLY the conclusion's contract family (fail-closed hook: a WRONG
/// contract — a different `Post` from the one the step hypothesis establishes —
/// must NOT prove). See [`MIRSEM_MUTUAL_CALL_CONTRACTS`].
pub(super) fn mutual_call_contracts_type(claimed_concl_post: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let post_ty = Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), int_ty(), Expr::prop()));
    let rank_ty = Expr::pi(bd(), cst(MIRSEM_CALL), cst("Nat"));
    // inside `∀ Post ∀ rank`: rank=0, Post=1.
    let step = mutual_step_hyp(&Expr::bvar(1), &Expr::bvar(0));
    // conclusion: ∀ c, Post (call_callee c) (call_result c)
    //   inside `∀ Post ∀ rank (step→) ∀ c`: c=0,step=1,rank=2,Post=3.
    let post_pred = claimed_concl_post
        .cloned()
        .map(|p| p.lift(4)) // claimed Post supplied at OUTSIDE depth; lift past Post,rank,step,c
        .unwrap_or_else(|| Expr::bvar(3));
    let cod = post_holds(post_pred, Expr::bvar(0));
    let body_c = Expr::pi(bd(), cst(MIRSEM_CALL), cod);
    let after_step = Expr::pi(bd(), step, body_c);
    Expr::pi(bd(), post_ty, Expr::pi(bd(), rank_ty, after_step))
}

/// The MUTUAL-RECURSION CONTRACT rule PROOF: instantiate `boundedSat`'s rank budget
/// at the call's rank. `λ Post rank step c. boundedSat Post rank step (rank c) c
/// (Nat.le.refl (rank c))`.
pub(super) fn mutual_call_contracts_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let post_ty = Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), int_ty(), Expr::prop()));
    let rank_ty = Expr::pi(bd(), cst(MIRSEM_CALL), cst("Nat"));
    // under `λ Post λ rank λ step λ c`: c=0,step=1,rank=2,Post=3.
    let rank_c = Expr::app(Expr::bvar(2), Expr::bvar(0)); // rank c
    let le_refl =
        Expr::apps(Expr::const_(Name::from_string("Nat.le.refl"), vec![]), [rank_c.clone()]);
    let bs = Expr::apps(
        cst(MIRSEM_BOUNDED_SAT),
        [
            Expr::bvar(3), // Post
            Expr::bvar(2), // rank
            Expr::bvar(1), // step
            rank_c,        // k := rank c
            Expr::bvar(0), // c
            le_refl,       // Nat.le (rank c) (rank c)
        ],
    );
    Expr::lam(
        bd(),
        post_ty,
        Expr::lam(
            bd(),
            rank_ty,
            Expr::lam(
                bd(),
                mutual_step_hyp(&Expr::bvar(1), &Expr::bvar(0)),
                Expr::lam(bd(), cst(MIRSEM_CALL), bs),
            ),
        ),
    )
}

/// Register `call_callee`, `boundedSat`, then `mutualCallContracts` into `env`.
/// Requires the `Call` inductive + `call_result` + `nat_le_trans` registered.
pub(super) fn register_mutual_call_contracts(env: &mut Environment) -> Result<(), String> {
    register_call_callee(env)?;
    // boundedSat
    let bs_name = Name::from_string(MIRSEM_BOUNDED_SAT);
    if env.get_const(&bs_name).is_none() {
        let bs_ty = bounded_sat_type();
        let bs_proof = bounded_sat_proof();
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&bs_proof, &bs_ty)
                .map_err(|e| format!("boundedSat check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem {
            name: bs_name,
            level_params: vec![],
            type_: bs_ty,
            value: bs_proof,
        })
        .map_err(|e| format!("add_decl(boundedSat): {e:?}"))?;
    }
    // mutualCallContracts
    let mc_name = Name::from_string(MIRSEM_MUTUAL_CALL_CONTRACTS);
    if env.get_const(&mc_name).is_none() {
        let mc_ty = mutual_call_contracts_type(None);
        let mc_proof = mutual_call_contracts_proof();
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&mc_proof, &mc_ty)
                .map_err(|e| format!("mutualCallContracts check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem {
            name: mc_name,
            level_params: vec![],
            type_: mc_ty,
            value: mc_proof,
        })
        .map_err(|e| format!("add_decl(mutualCallContracts): {e:?}"))?;
    }
    Ok(())
}

/// The CONTRACT-CALL rule TYPE: `∀ (post : Int → Prop)(c : Call),
/// post (call_result c) → post (call_result c)`. `claimed_concl_pred = Some(p)`
/// overrides the CONCLUSION's predicate (fail-closed hook: a wrong postcondition
/// — a different predicate from the assumed one — must NOT prove).
pub(super) fn call_contract_type(claimed_concl_pred: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    // inside `∀ post ∀ c`: c=0, post=1.
    // HYPOTHESIS: post (call_result c)
    let res_c = Expr::app(cst(MIRSEM_CALL_RESULT), Expr::bvar(0));
    let hyp = Expr::app(Expr::bvar(1), res_c);
    // CONCLUSION: <pred> (call_result c)  — under the `hyp →` arrow everything +1.
    let res_c2 = Expr::app(cst(MIRSEM_CALL_RESULT), Expr::bvar(1));
    // Inside `concl` (codomain of `hyp →`): hyp=0, c=1, post=2.
    let concl_pred = claimed_concl_pred
        .cloned()
        // A claimed predicate is supplied relative to the OUTSIDE (closed, or refs to
        // pre-`post` binders); lift it past `post`, `c`, `hyp` so it is valid here.
        .map(|p| p.lift(3))
        .unwrap_or_else(|| Expr::bvar(2)); // the assumed `post` itself
    let concl = Expr::app(concl_pred, res_c2);
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), cst(MIRSEM_CALL), arrow))
}

/// The CONTRACT-CALL TRANSPORT lemma PROOF: `λ (post)(c)(h : post (call_result c)). h`
/// — the IDENTITY (A-implies-A). It TRANSPORTS the ASSUMED callee contract to the call
/// site; the caller inherits EXACTLY the callee's postcondition. HONEST: the identity
/// proves nothing about dispatch and discharges no callee body — the guarantee `h` is
/// established elsewhere (modular, separate verification), not by this transport.
pub(super) fn call_contract_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    // inside `λ post λ c`: c=0, post=1.  hyp : post (call_result c).
    let res_c = Expr::app(cst(MIRSEM_CALL_RESULT), Expr::bvar(0));
    let hyp_ty = Expr::app(Expr::bvar(1), res_c);
    Expr::lam(
        bd(),
        int_to_prop,
        Expr::lam(bd(), cst(MIRSEM_CALL), Expr::lam(bd(), hyp_ty, Expr::bvar(0))),
    )
}

// ---------------------------------------------------------------------------
// Trust: call-spine increment — the PER-CALL-SITE instance of the transport
// lemma. `callRefinesContract` is ∀-quantified over EVERY `Call`; the instance
// pins it at THIS call site's concrete `Call.mk <callee-id> <arg>` (quantified
// only over the callee-supplied return value `ret` and the contract `post`).
// The proof APPLIES the registered proven theorem — no new axiom, no new
// inductive; the axiom closure is audited empty (modulo 3) per instance.
// ---------------------------------------------------------------------------
/// The per-call instance TYPE: `∀ (post : Int → Prop)(ret : Int),
/// post (call_result (Call.mk <id> <arg> ret)) → <pred> (call_result (Call.mk
/// <id> <arg> ret))` where `<pred>` defaults to the assumed `post` itself.
/// `claimed_concl_pred = Some(p)` overrides the conclusion's predicate — the
/// fail-closed hook (a WRONG postcondition must NOT prove).
pub(super) fn call_return_instance_type(
    callee_id: u64,
    arg: &SemOperand,
    claimed_concl_pred: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    // `arg.to_operand_expr()` is CLOSED (constructor literals only) — no lifting.
    let call_at = |ret: Expr| {
        Expr::apps(cst(MIRSEM_CALL_MK), [Expr::nat_lit(callee_id), arg.to_operand_expr(), ret])
    };
    // inside `∀ post ∀ ret`: ret=0, post=1. HYPOTHESIS: post (call_result C[ret]).
    let hyp = Expr::app(Expr::bvar(1), Expr::app(cst(MIRSEM_CALL_RESULT), call_at(Expr::bvar(0))));
    // CONCLUSION (under the `hyp →` arrow, everything +1): <pred> (call_result C[ret]).
    let concl_pred = claimed_concl_pred
        .cloned()
        // A claimed predicate is supplied CLOSED (or relative to pre-`post`
        // binders); lift it past `post`, `ret`, `hyp`.
        .map(|p| p.lift(3))
        .unwrap_or_else(|| Expr::bvar(2)); // the assumed `post` itself
    let concl = Expr::app(concl_pred, Expr::app(cst(MIRSEM_CALL_RESULT), call_at(Expr::bvar(1))));
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), int_ty(), arrow))
}

/// The per-call instance PROOF: `λ (post)(ret)(h). callRefinesContract post
/// (Call.mk <id> <arg> ret) h` — a plain APPLICATION of the registered proven
/// transport lemma at the concrete call value. Inherits the lemma's honesty: it
/// transports the ASSUMED callee guarantee to the call site and discharges no
/// callee body (the callee is separately verified — the registry's job).
pub(super) fn call_return_instance_proof(callee_id: u64, arg: &SemOperand) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(cst(MIRSEM_CALL_MK), [Expr::nat_lit(callee_id), arg.to_operand_expr(), ret])
    };
    // hyp type inside `λ post λ ret`: ret=0, post=1.
    let hyp_ty =
        Expr::app(Expr::bvar(1), Expr::app(cst(MIRSEM_CALL_RESULT), call_at(Expr::bvar(0))));
    // body inside `λ post λ ret λ h`: h=0, ret=1, post=2.
    let body = Expr::apps(
        cst(MIRSEM_CALL_REFINES_CONTRACT),
        [Expr::bvar(2), call_at(Expr::bvar(1)), Expr::bvar(0)],
    );
    Expr::lam(bd(), int_to_prop, Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, body)))
}
