// Higher-order and open-world calls, the assembled whole-program environment,
// and the checked verdicts over it. An open-world call cannot be resolved to a
// body, so its conclusion may only rest on the declared contract.

use super::*;

// ===========================================================================
// Step 6H — THE HIGHER-ORDER (INDIRECT) CALL RULE (finite candidate set).
// ===========================================================================
/// `ho_target c : Nat` — the resolved candidate index.
pub(super) fn ho_target_app(c: Expr) -> Expr {
    Expr::app(cst(MIRSEM_HO_TARGET), c)
}

/// `ho_result c : Int` — the indirect call's denotation.
pub(super) fn ho_result_app(c: Expr) -> Expr {
    Expr::app(cst(MIRSEM_HO_RESULT), c)
}

/// `@Eq Nat a b` — equality of `Nat` (`Nat : Type` ⇒ `Eq.{1}`).
pub(super) fn eq_nat_expr(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [cst("Nat"), a, b],
    )
}

/// `Or a b : Prop`.
pub(super) fn or_expr(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Or"), vec![]), [a, b])
}

/// Register `Trust.MirSem.HoCall : Type` (one ctor `HoCall.mk : Nat → Operand → Int
/// → HoCall`). Idempotent. See [`MIRSEM_HO_CALL`].
pub(super) fn register_ho_call_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_HO_CALL);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let mk_ctor = Constructor {
        name: Name::from_string(MIRSEM_HO_CALL_MK),
        type_: Expr::pi(
            bd(),
            cst("Nat"),
            Expr::pi(bd(), operand_ty(), Expr::pi(bd(), int_ty(), cst(MIRSEM_HO_CALL))),
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
    env.add_inductive(decl).map_err(|e| format!("add_inductive(HoCall): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.ho_target : HoCall → Nat` (idempotent) — the resolved
/// candidate-index projection via the `HoCall` recursor.
pub(super) fn register_ho_target(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_HO_TARGET);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let rec = Expr::const_(Name::from_string(MIRSEM_HO_CALL_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst(MIRSEM_HO_CALL), cst("Nat"));
    // minor : λ (target:Nat)(arg:Operand)(ret:Int). target   (target=2)
    let minor = Expr::lam(
        bd(),
        cst("Nat"),
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), Expr::bvar(2))),
    );
    let body = Expr::apps(rec, [motive, minor, Expr::bvar(0)]);
    let val = Expr::lam(bd(), cst(MIRSEM_HO_CALL), body);
    let ty = Expr::pi(bd(), cst(MIRSEM_HO_CALL), cst("Nat"));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(ho_target): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.ho_result : HoCall → Int` (idempotent) — the indirect-call
/// result projection via the `HoCall` recursor.
pub(super) fn register_ho_result(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_HO_RESULT);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let rec = Expr::const_(Name::from_string(MIRSEM_HO_CALL_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst(MIRSEM_HO_CALL), int_ty());
    // minor : λ (target:Nat)(arg:Operand)(ret:Int). ret   (ret=0)
    let minor = Expr::lam(
        bd(),
        cst("Nat"),
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), Expr::bvar(0))),
    );
    let body = Expr::apps(rec, [motive, minor, Expr::bvar(0)]);
    let val = Expr::lam(bd(), cst(MIRSEM_HO_CALL), body);
    let ty = Expr::pi(bd(), cst(MIRSEM_HO_CALL), int_ty());
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(ho_result): {e:?}"))?;
    Ok(())
}

/// The HIGHER-ORDER CALL rule TYPE (resolve over a finite candidate family):
/// `∀ (Post : Nat → Int → Prop)(c : HoCall),
///   (∀ (i : Nat), Post i (ho_result c)) → Post (ho_target c) (ho_result c)`.
/// `claimed_concl_post = Some(p)` overrides the conclusion's contract family
/// (fail-closed hook). Inside `∀ Post ∀ c`: c=0, Post=1.
pub(super) fn higher_order_call_type(claimed_concl_post: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let post_ty = Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), int_ty(), Expr::prop()));
    // hypothesis: ∀ (i : Nat), Post i (ho_result c)
    //   inside `∀ Post ∀ c ∀ i`: i=0, c=1, Post=2.
    let hyp = {
        let res_c = ho_result_app(Expr::bvar(1));
        let post_i = Expr::apps(Expr::bvar(2), [Expr::bvar(0), res_c]);
        Expr::pi(bd(), cst("Nat"), post_i)
    };
    // conclusion: <Post> (ho_target c) (ho_result c)
    //   under one more arrow (the hyp →): hyp=0, c=1, Post=2.
    let concl_post = claimed_concl_post
        .cloned()
        .map(|p| p.lift(3)) // supplied at OUTSIDE depth; lift past Post,c,hyp
        .unwrap_or_else(|| Expr::bvar(2));
    let tgt = ho_target_app(Expr::bvar(1));
    let res = ho_result_app(Expr::bvar(1));
    let concl = Expr::apps(concl_post, [tgt, res]);
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), post_ty, Expr::pi(bd(), cst(MIRSEM_HO_CALL), arrow))
}

/// The HIGHER-ORDER CALL rule PROOF: instantiate the per-candidate hypothesis at the
/// RESOLVED target index. `λ (Post)(c)(h : ∀ i, Post i (ho_result c)). h (ho_target c)`.
/// The `h (ho_target c)` application IS the candidate case-split: it resolves the
/// universally-quantified candidate contract to the actual devirtualized target.
pub(super) fn higher_order_call_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let post_ty = Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), int_ty(), Expr::prop()));
    // hyp type : ∀ (i : Nat), Post i (ho_result c)   (under `λ Post λ c`: c=0, Post=1; then ∀ i: i=0,c=1,Post=2)
    let hyp_ty = {
        let res_c = ho_result_app(Expr::bvar(1));
        let post_i = Expr::apps(Expr::bvar(2), [Expr::bvar(0), res_c]);
        Expr::pi(bd(), cst("Nat"), post_i)
    };
    // body : h (ho_target c)   (under `λ Post λ c λ h`: h=0, c=1, Post=2)
    let tgt = ho_target_app(Expr::bvar(1));
    let body = Expr::app(Expr::bvar(0), tgt);
    Expr::lam(bd(), post_ty, Expr::lam(bd(), cst(MIRSEM_HO_CALL), Expr::lam(bd(), hyp_ty, body)))
}

/// The TWO-CANDIDATE DISJUNCTION higher-order rule TYPE:
/// `∀ (P0 P1 : Int → Prop)(c : HoCall),
///   Or (Eq Nat (ho_target c) 0) (Eq Nat (ho_target c) 1)
///   → P0 (ho_result c) → P1 (ho_result c)
///   → Or (P0 (ho_result c)) (P1 (ho_result c))`.
/// `claimed_membership = Some(m)` overrides the membership hypothesis (fail-closed
/// hook: a candidate set the proof's case-split cannot consume must NOT prove).
/// Inside `∀ P0 ∀ P1 ∀ c`: c=0, P1=1, P0=2.
pub(super) fn higher_order_disj_type(claimed_membership: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    // membership hyp: Or (ho_target c = 0) (ho_target c = 1)   (c=0,P1=1,P0=2)
    let membership = claimed_membership.cloned().map(|m| m.lift(3)).unwrap_or_else(|| {
        let tgt = ho_target_app(Expr::bvar(0));
        or_expr(eq_nat_expr(tgt.clone(), Expr::nat_lit(0)), eq_nat_expr(tgt, Expr::nat_lit(1)))
    });
    // h0 : P0 (ho_result c)   (under membership →: mem=0, c=1, P1=2, P0=3)
    let h0 = Expr::app(Expr::bvar(3), ho_result_app(Expr::bvar(1)));
    // h1 : P1 (ho_result c)   (under mem→ h0→: h0=0, mem=1, c=2, P1=3, P0=4)
    let h1 = Expr::app(Expr::bvar(3), ho_result_app(Expr::bvar(2)));
    // concl : Or (P0 (ho_result c)) (P1 (ho_result c))
    //   (under mem→ h0→ h1→: h1=0, h0=1, mem=2, c=3, P1=4, P0=5)
    let concl = {
        let res = ho_result_app(Expr::bvar(3));
        or_expr(Expr::app(Expr::bvar(5), res.clone()), Expr::app(Expr::bvar(4), res))
    };
    let arrows = Expr::pi(bd(), membership, Expr::pi(bd(), h0, Expr::pi(bd(), h1, concl)));
    Expr::pi(
        bd(),
        int_to_prop.clone(),
        Expr::pi(bd(), int_to_prop, Expr::pi(bd(), cst(MIRSEM_HO_CALL), arrows)),
    )
}

/// The TWO-CANDIDATE DISJUNCTION higher-order rule PROOF — a genuine `Or.rec`
/// CASE-SPLIT on the membership witness `(target=0) ∨ (target=1)`:
/// `λ P0 P1 c hmem h0 h1.
///    @Or.rec (target=0) (target=1) (λ_. Or (P0 res)(P1 res))
///      (λ _:target=0. Or.inl … h0)     -- candidate 0 resolved ⇒ left injection
///      (λ _:target=1. Or.inr … h1)     -- candidate 1 resolved ⇒ right injection
///      hmem`.
/// The `Or.rec` is the candidate case analysis (sum recursor): each arm supplies the
/// resolved candidate's postcondition under the matching disjunct injection.
pub(super) fn higher_order_disj_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    // Build inside `λ P0 λ P1 λ c λ hmem λ h0 λ h1`: h1=0, h0=1, hmem=2, c=3, P1=4, P0=5.
    let tgt_c = || ho_target_app(Expr::bvar(3));
    let mem0 = || eq_nat_expr(tgt_c(), Expr::nat_lit(0)); // target = 0
    let mem1 = || eq_nat_expr(tgt_c(), Expr::nat_lit(1)); // target = 1
    let p0_res = || Expr::app(Expr::bvar(5), ho_result_app(Expr::bvar(3)));
    let p1_res = || Expr::app(Expr::bvar(4), ho_result_app(Expr::bvar(3)));
    // motive of Or.rec : λ (_ : Or mem0 mem1). Prop-target = Or (P0 res)(P1 res).
    //   Or.rec's motive binds the Or proof; the goal Or (P0 res)(P1 res) does NOT
    //   reference it, so we lift the body past the motive binder.
    let or_goal = or_expr(p0_res(), p1_res());
    let motive = Expr::lam(bd(), or_expr(mem0(), mem1()), or_goal.clone().lift(1));
    // left minor : λ (_ : target=0). Or.inl (P0 res)(P1 res) h0
    //   under the extra λ binder: refs +1 ⇒ h1=1, h0=2, hmem=3, c=4, P1=5, P0=6.
    let left = {
        let inl = Expr::const_(Name::from_string("Or.inl"), vec![]);
        let p0 = Expr::app(Expr::bvar(6), ho_result_app(Expr::bvar(4)));
        let p1 = Expr::app(Expr::bvar(5), ho_result_app(Expr::bvar(4)));
        let inj = Expr::apps(inl, [p0, p1, Expr::bvar(2)]); // h0 (now bvar 2)
        Expr::lam(bd(), mem0(), inj)
    };
    // right minor : λ (_ : target=1). Or.inr (P0 res)(P1 res) h1
    let right = {
        let inr = Expr::const_(Name::from_string("Or.inr"), vec![]);
        let p0 = Expr::app(Expr::bvar(6), ho_result_app(Expr::bvar(4)));
        let p1 = Expr::app(Expr::bvar(5), ho_result_app(Expr::bvar(4)));
        let inj = Expr::apps(inr, [p0, p1, Expr::bvar(1)]); // h1 (now bvar 1)
        Expr::lam(bd(), mem1(), inj)
    };
    // @Or.rec mem0 mem1 motive left right hmem
    //   `Or : Prop → Prop → Prop` is a Prop inductive eliminating ONLY into Prop, so
    //   its recursor carries NO universe parameter (`vec![]`), matching the kernel's
    //   own `Or.rec` usage in `logic_or.rs` / the algebra proofs.
    let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
    let body = Expr::apps(or_rec, [mem0(), mem1(), motive, left, right, Expr::bvar(2)]);
    // h0 type : P0 (ho_result c)   (under `λ P0 λ P1 λ c λ hmem`: hmem=0,c=1,P1=2,P0=3)
    let h0_ty = Expr::app(Expr::bvar(3), ho_result_app(Expr::bvar(1)));
    // h1 type : P1 (ho_result c)   (under `… λ h0`: h0=0,hmem=1,c=2,P1=3,P0=4)
    let h1_ty = Expr::app(Expr::bvar(3), ho_result_app(Expr::bvar(2)));
    // membership type : Or (target=0) (target=1)  (under `λ P0 λ P1 λ c`: c=0,P1=1,P0=2)
    let mem_ty = {
        let tgt = ho_target_app(Expr::bvar(0));
        or_expr(eq_nat_expr(tgt.clone(), Expr::nat_lit(0)), eq_nat_expr(tgt, Expr::nat_lit(1)))
    };
    Expr::lam(
        bd(),
        int_to_prop.clone(), // P0
        Expr::lam(
            bd(),
            int_to_prop, // P1
            Expr::lam(
                bd(),
                cst(MIRSEM_HO_CALL), // c
                Expr::lam(
                    bd(),
                    mem_ty,                                               // hmem
                    Expr::lam(bd(), h0_ty, Expr::lam(bd(), h1_ty, body)), // h0, h1
                ),
            ),
        ),
    )
}

/// The ASSUME-THE-TRAIT-CONTRACT TRANSPORT lemma TYPE (NOT a Liskov dispatch theorem):
/// `∀ (TPost : Int → Prop)(c : HoCall),
///   (∀ (impl : Nat), TPost (ho_result c)) → TPost (ho_result c)`.
/// Honest: `ho_result c` is independent of `impl`, so the `∀ impl` hypothesis ranges
/// over an index the conclusion ignores; the lemma transports the assumed `TPost`.
/// `claimed_concl_post = Some(p)` overrides the conclusion's trait contract
/// (fail-closed hook: a `TPost` the hypothesis does NOT establish must NOT prove).
/// Inside `∀ TPost ∀ c`: c=0, TPost=1.
pub(super) fn open_world_call_type(claimed_concl_post: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let tpost_ty = Expr::pi(bd(), int_ty(), Expr::prop());
    // hypothesis: ∀ (impl : Nat), TPost (ho_result c)  — ASSUME the trait contract `TPost`
    //   (a real `∀ impl` Π, but `ho_result c` is INDEPENDENT of `impl`, so it ranges over
    //   an index the body ignores — NOT a genuine over-all-implementors statement).
    //   inside `∀ TPost ∀ c ∀ impl`: impl=0, c=1, TPost=2.
    let hyp = {
        let res_c = ho_result_app(Expr::bvar(1));
        let tpost_res = Expr::app(Expr::bvar(2), res_c);
        Expr::pi(bd(), cst("Nat"), tpost_res)
    };
    // conclusion: <TPost> (ho_result c)  — transport the assumed `TPost` to the call site.
    //   under one more arrow (the hyp →): hyp=0, c=1, TPost=2.
    let concl_post = claimed_concl_post
        .cloned()
        .map(|p| p.lift(3)) // supplied at OUTSIDE depth; lift past TPost,c,hyp
        .unwrap_or_else(|| Expr::bvar(2));
    let res = ho_result_app(Expr::bvar(1));
    let concl = Expr::app(concl_post, res);
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), tpost_ty, Expr::pi(bd(), cst(MIRSEM_HO_CALL), arrow))
}

/// The ASSUME-THE-TRAIT-CONTRACT TRANSPORT lemma PROOF: a plain ∀-elimination of the
/// assumed trait-contract hypothesis. `λ (TPost)(c)(h : ∀ impl, TPost (ho_result c)).
/// h (ho_target c)`. HONEST: `ho_result c` does NOT depend on the index, so the
/// conclusion is INDEPENDENT of the implementor — instantiating `h` at `ho_target c`
/// (or at ANY index) yields the SAME `TPost (ho_result c)`. This is NOT a genuine
/// case-split or behavioral-subtyping dispatch proof; it merely transports the assumed
/// `TPost` to the call site. We instantiate at the resolved `ho_target c` only to record
/// that a target was named — the proof does not (and cannot, given this `HoCall` model)
/// depend on which implementor it was.
pub(super) fn open_world_call_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let tpost_ty = Expr::pi(bd(), int_ty(), Expr::prop());
    // hyp type : ∀ (impl : Nat), TPost (ho_result c)  (under `λ TPost λ c`: c=0,TPost=1; then ∀ impl: impl=0,c=1,TPost=2)
    let hyp_ty = {
        let res_c = ho_result_app(Expr::bvar(1));
        let tpost_res = Expr::app(Expr::bvar(2), res_c);
        Expr::pi(bd(), cst("Nat"), tpost_res)
    };
    // body : h (ho_target c)   (under `λ TPost λ c λ h`: h=0, c=1, TPost=2)
    let tgt = ho_target_app(Expr::bvar(1));
    let body = Expr::app(Expr::bvar(0), tgt);
    Expr::lam(bd(), tpost_ty, Expr::lam(bd(), cst(MIRSEM_HO_CALL), Expr::lam(bd(), hyp_ty, body)))
}

/// Register the full HIGHER-ORDER-CALL chain into `env`: the `HoCall` inductive, its
/// two projections, the candidate-resolving rule, and the two-candidate disjunction
/// rule — all kernel-checked, modulo 3. Idempotent.
pub(super) fn register_higher_order_call(env: &mut Environment) -> Result<(), String> {
    register_ho_call_inductive(env)?;
    register_ho_target(env)?;
    register_ho_result(env)?;
    // higherOrderCallRefines
    let hc_name = Name::from_string(MIRSEM_HIGHER_ORDER_CALL);
    if env.get_const(&hc_name).is_none() {
        let hc_ty = higher_order_call_type(None);
        let hc_proof = higher_order_call_proof();
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&hc_proof, &hc_ty)
                .map_err(|e| format!("higherOrderCallRefines check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem {
            name: hc_name,
            level_params: vec![],
            type_: hc_ty,
            value: hc_proof,
        })
        .map_err(|e| format!("add_decl(higherOrderCallRefines): {e:?}"))?;
    }
    // higherOrderCallDisjunction
    let hd_name = Name::from_string(MIRSEM_HIGHER_ORDER_CALL_DISJ);
    if env.get_const(&hd_name).is_none() {
        let hd_ty = higher_order_disj_type(None);
        let hd_proof = higher_order_disj_proof();
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&hd_proof, &hd_ty)
                .map_err(|e| format!("higherOrderCallDisjunction check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem {
            name: hd_name,
            level_params: vec![],
            type_: hd_ty,
            value: hd_proof,
        })
        .map_err(|e| format!("add_decl(higherOrderCallDisjunction): {e:?}"))?;
    }
    Ok(())
}

/// Build the full WHILE-rule + CONTRACT-CALL environment: `stepLoop`/`exec_loop`
/// (the iterate function, reused from the loop refinement), the invariant
/// preservation lemma, the Hoare while-rule, the `Call` inductive, `call_result`,
/// and the contract-call rule — all registered and kernel-checked, modulo 3.
pub fn mirsem_whole_program_env() -> Result<Environment, String> {
    let mut env = mirsem_env()?;
    register_step_loop(&mut env)?;
    register_exec_loop(&mut env)?;
    register_step_preserves_inv(&mut env)?;

    // The Hoare while-rule (partial correctness), proven by Nat.rec on n.
    let rule_ty = loop_invariant_rule_type(None);
    let rule_proof = loop_invariant_rule_proof();
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(&rule_proof, &rule_ty)
            .map_err(|e| format!("loopInvariantRule check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_LOOP_INVARIANT_RULE),
        level_params: vec![],
        type_: rule_ty,
        value: rule_proof,
    })
    .map_err(|e| format!("add_decl(loopInvariantRule): {e:?}"))?;

    // TOTAL correctness: the termination (well-founded RANKING) while-rule.
    // Raw Nat.le transitivity + guard-false stability + the bounded-halt descent
    // by Nat.rec on the fuel bound, then instantiate the bound at the rank itself.
    register_nat_le_trans(&mut env)?;
    register_guard_false_stable(&mut env)?;
    register_loop_rank_terminates(&mut env)?;

    // TOTAL correctness AS A SINGLE THEOREM: `loopTotalCorrect` — the `And` (via
    // `And.intro`) of `loopInvariantRule` at fuel `R e` (partial: invariant at the
    // halting state) and `loopRankTerminates` at `e` (termination within `R e` steps).
    // Total correctness = partial + termination as ONE kernel-checked conjunction.
    register_loop_total_correct(&mut env)?;

    // The inter-procedural contract-call rule (assume-the-callee).
    register_call_inductive(&mut env)?;
    register_call_result(&mut env)?;
    // The MUTUAL-RECURSION contract rule (assume-the-callees, well-founded over a
    // call ranking): boundedSat by Nat.rec on the rank budget, then instantiate at
    // the call's own rank. Composes per-callee contracts over the call graph.
    register_mutual_call_contracts(&mut env)?;
    let call_ty = call_contract_type(None);
    let call_proof = call_contract_proof();
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(&call_proof, &call_ty)
            .map_err(|e| format!("callRefinesContract check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_CALL_REFINES_CONTRACT),
        level_params: vec![],
        type_: call_ty,
        value: call_proof,
    })
    .map_err(|e| format!("add_decl(callRefinesContract): {e:?}"))?;

    // The UNSTRUCTURED / IRREDUCIBLE CFG refinement (bounded, fuel-indexed): the
    // CfgState transition system, exec_cfg/step_cfg, the inductive unroll law, and
    // the CFG refinement theorem — the general transition-system version of the
    // structured-loop refinement, covering arbitrary terminator edges.
    register_cfg_refinement(&mut env)?;

    // The UNBOUNDED IRREDUCIBLE-CFG TERMINATION rule via a CFG-state RANKING: the
    // exit-stability lemma, the CFG bounded-halt descent (Nat.rec on the fuel bound),
    // and the termination rule (instantiate the bound at the rank itself). Upgrades
    // the bounded CFG refinement to TOTAL correctness for an unbounded irreducible CFG
    // that carries a ranking. `nat_le_trans` is already registered above.
    register_cfg_rank_terminates(&mut env)?;

    // The HIGHER-ORDER (indirect) call rule over a FINITE candidate set: the HoCall
    // inductive, the candidate-resolving rule (instantiate the per-candidate
    // contract at the resolved target), and the two-candidate disjunction rule
    // (Or.rec case-split on which candidate the target resolved to).
    register_higher_order_call(&mut env)?;

    // The ASSUME-THE-TRAIT-CONTRACT TRANSPORT lemma for a `dyn Trait` call (NOT a
    // Liskov dispatch theorem): given the assumed trait postcondition `TPost`
    // (`∀ impl, TPost (ho_result c)`, over an index `ho_result` ignores), transport
    // it to the call site. The conclusion is independent of the dispatched
    // implementor — the proof is a plain ∀-elimination. Reuses the HoCall inductive.
    let ow_ty = open_world_call_type(None);
    let ow_proof = open_world_call_proof();
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(&ow_proof, &ow_ty)
            .map_err(|e| format!("openWorldCallRefines check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_OPEN_WORLD_CALL),
        level_params: vec![],
        type_: ow_ty,
        value: ow_proof,
    })
    .map_err(|e| format!("add_decl(openWorldCallRefines): {e:?}"))?;
    Ok(env)
}

/// Pin the WHILE-rule + CONTRACT-CALL anchor and audit its axiom closure: confirm
/// the preservation lemma, the Hoare while-rule, `call_result`, the contract-call
/// rule, AND the new UNSTRUCTURED-CFG-refinement + HIGHER-ORDER-call rules each rest
/// on ONLY the 3 foundational axioms (modulo 3, no 4th axiom).
#[must_use]
pub fn pin_mirsem_whole_program_anchor() -> AnchorVerdict {
    let env = match mirsem_whole_program_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for n in [
        MIRSEM_STEP_PRESERVES_INV,
        MIRSEM_LOOP_INVARIANT_RULE,
        MIRSEM_NAT_LE_TRANS,
        MIRSEM_GUARD_FALSE_STABLE,
        MIRSEM_BOUNDED_HALT,
        MIRSEM_LOOP_RANK_TERMINATES,
        // Step 6TC — the COMPOSED total-correctness theorem (partial ∧ termination).
        MIRSEM_LOOP_TOTAL_CORRECT,
        MIRSEM_CALL_RESULT,
        MIRSEM_CALL_CALLEE,
        MIRSEM_BOUNDED_SAT,
        MIRSEM_MUTUAL_CALL_CONTRACTS,
        MIRSEM_CALL_REFINES_CONTRACT,
        // Step 6U — the unstructured/irreducible CFG refinement chain.
        MIRSEM_CFG_PC,
        MIRSEM_CFG_ENV,
        MIRSEM_STEP_CFG,
        MIRSEM_EXEC_CFG,
        MIRSEM_CFG_THREADED,
        MIRSEM_CFG_SUBST,
        MIRSEM_EXEC_CFG_UNROLL_LAW,
        MIRSEM_CFG_REFINEMENT,
        // Step 6X — the unbounded irreducible-CFG termination (ranking) chain.
        MIRSEM_CFG_EXIT_STABLE,
        MIRSEM_CFG_BOUNDED_HALT,
        MIRSEM_CFG_RANK_TERMINATES,
        // Step 6H — the higher-order (indirect) call rules.
        MIRSEM_HO_TARGET,
        MIRSEM_HO_RESULT,
        MIRSEM_HIGHER_ORDER_CALL,
        MIRSEM_HIGHER_ORDER_CALL_DISJ,
        // Step 6O — the assume-the-trait-contract transport lemma (NOT a dispatch theorem).
        MIRSEM_OPEN_WORLD_CALL,
    ] {
        match env.axiom_deps(&Name::from_string(n)) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                names.sort();
                return AnchorVerdict::Residue(names);
            }
            None => return AnchorVerdict::KernelRejected(format!("decl not found: {n}")),
        }
    }
    AnchorVerdict::Modulo3
}

/// Check the GENERAL UNSTRUCTURED-CFG refinement theorem against the real
/// clean-kernel (build the env up to the theorem, kernel-check the proof inhabits
/// the statement, audit ⊆ 3). With `claimed_rhs = Some`, the RHS is overridden
/// (fail-closed hook: a wrong CFG denotation — one NOT following the real terminator
/// edges — must NOT type-check).
#[must_use]
pub fn check_cfg_refinement() -> RefinementVerdict {
    check_cfg_refinement_inner(None)
}

pub(super) fn check_cfg_refinement_inner(claimed_rhs: Option<&Expr>) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    // Build the CFG chain up to (but not including) the refinement theorem.
    if let Err(e) = register_cfg_state(&mut env)
        .and_then(|()| register_cfg_pc(&mut env))
        .and_then(|()| register_cfg_env(&mut env))
        .and_then(|()| register_step_cfg(&mut env))
        .and_then(|()| register_exec_cfg(&mut env))
        .and_then(|()| register_cfg_threaded(&mut env))
        .and_then(|()| register_cfg_substituted(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    // The inductive unroll law.
    let law_ty = exec_cfg_unroll_law_type();
    let law_proof = exec_cfg_unroll_law_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&law_proof, &law_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "execCfgUnrollLaw check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_EXEC_CFG_UNROLL_LAW),
        level_params: vec![],
        type_: law_ty,
        value: law_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add execCfgUnrollLaw: {e:?}"));
    }
    // The refinement theorem (possibly with a wrong RHS).
    let ref_ty = cfg_refinement_type(claimed_rhs);
    let ref_proof = cfg_refinement_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&ref_proof, &ref_ty) {
            return RefinementVerdict::KernelRejected(format!("cfgRefinement check_type: {e:?}"));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_CFG_REFINEMENT),
        level_params: vec![],
        type_: ref_ty,
        value: ref_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add cfgRefinement: {e:?}"));
    }
    match env.axiom_deps(&Name::from_string(MIRSEM_CFG_REFINEMENT)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!("cfgRefinement axiom residue: {names:?}"))
        }
        None => RefinementVerdict::KernelRejected("cfgRefinement decl not found".to_string()),
    }
}

/// Check the UNBOUNDED IRREDUCIBLE-CFG TERMINATION rule against the real clean-kernel.
/// The rule quantifies over a CFG-state ranking `R : CfgState → Nat`; GIVEN the rank
/// strictly DROPS on every terminator step until an exit/stable state, the unbounded
/// run reaches an exit within `R s` steps. `claimed_concl_rank = Some(p)` overrides
/// ONLY the conclusion's fuel rank (fail-closed hook: a non-decreasing / wrong measure
/// — a DIFFERENT rank from the `R` the decrease hypothesis constrains — must NOT prove,
/// since `cfgBoundedHalt` is instantiated at the real `R`).
#[must_use]
pub fn check_cfg_rank_terminates() -> RefinementVerdict {
    check_cfg_rank_terminates_inner(None)
}

pub(super) fn check_cfg_rank_terminates_inner(claimed_concl_rank: Option<&Expr>) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    // Build the CFG transition system + nat_le_trans, then the termination chain.
    if let Err(e) = register_cfg_state(&mut env)
        .and_then(|()| register_cfg_pc(&mut env))
        .and_then(|()| register_cfg_env(&mut env))
        .and_then(|()| register_step_cfg(&mut env))
        .and_then(|()| register_exec_cfg(&mut env))
        .and_then(|()| register_nat_le_trans(&mut env))
        .and_then(|()| register_cfg_rank_terminates(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    // Re-check against a possibly-overridden conclusion rank: the proof term is the
    // honest `cfgRankTerminates` proof; if the claimed conclusion rank does not match
    // the `R` the proof was built for, the kernel rejects (fail-closed).
    let rule_ty = cfg_rank_terminates_type(claimed_concl_rank);
    let rule_proof = cfg_rank_terminates_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&rule_proof, &rule_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "cfgRankTerminates check_type: {e:?}"
            ));
        }
    }
    match env.axiom_deps(&Name::from_string(MIRSEM_CFG_RANK_TERMINATES)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!("cfgRankTerminates axiom residue: {names:?}"))
        }
        None => RefinementVerdict::KernelRejected("cfgRankTerminates decl not found".to_string()),
    }
}

/// Check the HIGHER-ORDER (indirect) call rule against the real clean-kernel. The rule
/// quantifies over the per-candidate contract family `Post : Nat → Int → Prop`;
/// GIVEN every candidate satisfies its contract, the indirect call resolves to the
/// ACTUAL target's contract. `claimed_concl_post = Some(p)` overrides the conclusion's
/// contract family (fail-closed hook: a contract for a DIFFERENT family than the
/// hypothesis establishes must NOT prove).
#[must_use]
pub fn check_higher_order_call() -> RefinementVerdict {
    check_higher_order_call_inner(None)
}

pub(super) fn check_higher_order_call_inner(claimed_concl_post: Option<&Expr>) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_ho_call_inductive(&mut env)
        .and_then(|()| register_ho_target(&mut env))
        .and_then(|()| register_ho_result(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    let rule_ty = higher_order_call_type(claimed_concl_post);
    let rule_proof = higher_order_call_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&rule_proof, &rule_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "higherOrderCallRefines check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_HIGHER_ORDER_CALL),
        level_params: vec![],
        type_: rule_ty,
        value: rule_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add higherOrderCallRefines: {e:?}"));
    }
    match env.axiom_deps(&Name::from_string(MIRSEM_HIGHER_ORDER_CALL)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "higherOrderCallRefines axiom residue: {names:?}"
            ))
        }
        None => {
            RefinementVerdict::KernelRejected("higherOrderCallRefines decl not found".to_string())
        }
    }
}

/// Check the TWO-CANDIDATE DISJUNCTION higher-order rule against the real
/// clean-kernel. GIVEN the target is one of `{0,1}` AND each candidate satisfies its
/// contract, the call refines to the disjunction of the two postconditions — proven
/// by `Or.rec` case-split. `claimed_membership = Some(m)` overrides the membership
/// hypothesis (fail-closed hook: a candidate set the case-split cannot consume — e.g.
/// a target outside `{0,1}` — must NOT prove).
#[must_use]
pub fn check_higher_order_disjunction() -> RefinementVerdict {
    check_higher_order_disjunction_inner(None)
}

pub(super) fn check_higher_order_disjunction_inner(claimed_membership: Option<&Expr>) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_ho_call_inductive(&mut env)
        .and_then(|()| register_ho_target(&mut env))
        .and_then(|()| register_ho_result(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    let rule_ty = higher_order_disj_type(claimed_membership);
    let rule_proof = higher_order_disj_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&rule_proof, &rule_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "higherOrderCallDisjunction check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_HIGHER_ORDER_CALL_DISJ),
        level_params: vec![],
        type_: rule_ty,
        value: rule_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add higherOrderCallDisjunction: {e:?}"));
    }
    match env.axiom_deps(&Name::from_string(MIRSEM_HIGHER_ORDER_CALL_DISJ)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "higherOrderCallDisjunction axiom residue: {names:?}"
            ))
        }
        None => RefinementVerdict::KernelRejected(
            "higherOrderCallDisjunction decl not found".to_string(),
        ),
    }
}

/// Check the ASSUME-THE-TRAIT-CONTRACT TRANSPORT lemma against the real clean-kernel
/// (NOT a Liskov dispatch theorem). The lemma quantifies over the trait contract
/// `TPost : Int → Prop`; GIVEN the assumed `∀ impl, TPost (ho_result c)` it transports
/// `TPost` to the call site. HONEST: `ho_result c` is independent of `impl`, so the
/// conclusion does not depend on the dispatched implementor. `claimed_concl_post =
/// Some(p)` overrides the conclusion's contract (fail-closed hook: a `TPost` the
/// hypothesis does NOT establish must NOT prove).
#[must_use]
pub fn check_open_world_call() -> RefinementVerdict {
    check_open_world_call_inner(None)
}

pub(super) fn check_open_world_call_inner(claimed_concl_post: Option<&Expr>) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_ho_call_inductive(&mut env)
        .and_then(|()| register_ho_target(&mut env))
        .and_then(|()| register_ho_result(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    let rule_ty = open_world_call_type(claimed_concl_post);
    let rule_proof = open_world_call_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&rule_proof, &rule_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "openWorldCallRefines check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_OPEN_WORLD_CALL),
        level_params: vec![],
        type_: rule_ty,
        value: rule_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add openWorldCallRefines: {e:?}"));
    }
    match env.axiom_deps(&Name::from_string(MIRSEM_OPEN_WORLD_CALL)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "openWorldCallRefines axiom residue: {names:?}"
            ))
        }
        None => {
            RefinementVerdict::KernelRejected("openWorldCallRefines decl not found".to_string())
        }
    }
}

/// Check the GENERAL Hoare while-rule (loop invariant rule) against the real
/// clean-kernel. `claimed_concl_pred = Some` overrides the conclusion's invariant
/// predicate (fail-closed hook: a NON-preserved invariant must NOT prove).
#[must_use]
pub fn check_loop_invariant_rule() -> RefinementVerdict {
    check_loop_invariant_rule_inner(None)
}

pub(super) fn check_loop_invariant_rule_inner(claimed_concl_pred: Option<&Expr>) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_step_loop(&mut env)
        .and_then(|()| register_exec_loop(&mut env))
        .and_then(|()| register_step_preserves_inv(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    let rule_ty = loop_invariant_rule_type(claimed_concl_pred);
    let rule_proof = loop_invariant_rule_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&rule_proof, &rule_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "loopInvariantRule check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_LOOP_INVARIANT_RULE),
        level_params: vec![],
        type_: rule_ty,
        value: rule_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add loopInvariantRule: {e:?}"));
    }
    match env.axiom_deps(&Name::from_string(MIRSEM_LOOP_INVARIANT_RULE)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!("loopInvariantRule axiom residue: {names:?}"))
        }
        None => RefinementVerdict::KernelRejected("loopInvariantRule decl not found".to_string()),
    }
}

/// Check the TOTAL-CORRECTNESS termination (well-founded RANKING) while-rule
/// against the real clean-kernel. The rule quantifies over `R : Env → Nat`; GIVEN
/// the rank strictly decreases on every guarded iteration the loop halts within
/// `R e` steps. `claimed_concl_rank = Some(p)` overrides ONLY the conclusion's
/// fuel rank (fail-closed hook: a rank `p` that is NOT the one the decrease
/// hypothesis constrains — i.e. a DIFFERENT measure from the `R` in the
/// hypothesis — must NOT prove, since `boundedHalt` is instantiated at the real
/// `R` and the conclusion would then mention a non-matching fuel).
#[must_use]
pub fn check_loop_rank_terminates() -> RefinementVerdict {
    check_loop_rank_terminates_inner(None)
}

pub(super) fn check_loop_rank_terminates_inner(claimed_concl_rank: Option<&Expr>) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_step_loop(&mut env)
        .and_then(|()| register_exec_loop(&mut env))
        .and_then(|()| register_nat_le_trans(&mut env))
        .and_then(|()| register_guard_false_stable(&mut env))
        .and_then(|()| register_loop_rank_terminates(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    // Re-check against a possibly-overridden conclusion rank: the proof term is the
    // honest `loopRankTerminates` proof; if the claimed conclusion rank does not
    // match the `R` the proof was built for, the kernel rejects (fail-closed).
    let rule_ty = loop_rank_terminates_type(claimed_concl_rank);
    let rule_proof = loop_rank_terminates_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&rule_proof, &rule_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "loopRankTerminates check_type: {e:?}"
            ));
        }
    }
    match env.axiom_deps(&Name::from_string(MIRSEM_LOOP_RANK_TERMINATES)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "loopRankTerminates axiom residue: {names:?}"
            ))
        }
        None => RefinementVerdict::KernelRejected("loopRankTerminates decl not found".to_string()),
    }
}

/// Build the env with everything `loopTotalCorrect` needs (`loopInvariantRule`,
/// `loopRankTerminates`, and their dependencies), but WITHOUT adding `loopTotalCorrect`
/// itself. Shared by the composed-theorem check and its fail-closed variants.
pub(super) fn loop_total_correct_env() -> Result<Environment, String> {
    let mut env = mirsem_env()?;
    register_step_loop(&mut env)?;
    register_exec_loop(&mut env)?;
    register_step_preserves_inv(&mut env)?;
    // loopInvariantRule (partial correctness)
    let rule_ty = loop_invariant_rule_type(None);
    let rule_proof = loop_invariant_rule_proof();
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(&rule_proof, &rule_ty)
            .map_err(|e| format!("loopInvariantRule check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_LOOP_INVARIANT_RULE),
        level_params: vec![],
        type_: rule_ty,
        value: rule_proof,
    })
    .map_err(|e| format!("add_decl(loopInvariantRule): {e:?}"))?;
    // loopRankTerminates (termination) + its dependencies.
    register_nat_le_trans(&mut env)?;
    register_guard_false_stable(&mut env)?;
    register_loop_rank_terminates(&mut env)?;
    Ok(env)
}

/// Check the COMPOSED TOTAL-CORRECTNESS theorem `loopTotalCorrect` against the real
/// clean-kernel: build the env up to (but excluding) the theorem, kernel-check the
/// `And.intro` proof inhabits the `And`-of-two-conclusions statement, register it, and
/// audit ⊆ 3. The statement is the CONJUNCTION of (a) the invariant holding at the
/// halting state and (b) the loop terminating within `R e` steps — TOTAL correctness as
/// ONE kernel-checked theorem, not two lemmas.
#[must_use]
pub fn check_loop_total_correct() -> RefinementVerdict {
    let mut env = match loop_total_correct_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let ty = loop_total_correct_type(None);
    let proof = loop_total_correct_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &ty) {
            return RefinementVerdict::KernelRejected(format!(
                "loopTotalCorrect check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_LOOP_TOTAL_CORRECT),
        level_params: vec![],
        type_: ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add loopTotalCorrect: {e:?}"));
    }
    match env.axiom_deps(&Name::from_string(MIRSEM_LOOP_TOTAL_CORRECT)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!("loopTotalCorrect axiom residue: {names:?}"))
        }
        None => RefinementVerdict::KernelRejected("loopTotalCorrect decl not found".to_string()),
    }
}

/// FAIL-CLOSED hook for the composed total-correctness theorem: kernel-check the HONEST
/// `loopTotalCorrect` proof against a STATEMENT that DROPS one conjunct-hypothesis
/// (`"pres"` drops the preservation hypothesis the partial-correctness conjunct needs;
/// `"decrease"` drops the rank-decrease hypothesis the termination conjunct needs).
/// The honest proof feeds that dropped hypothesis into its `And.intro` argument, so
/// against a type missing it the kernel rejects — DROPPING EITHER CONJUNCT-HYPOTHESIS
/// FAILS CLOSED. Returns `KernelRejected` on success of the fail-closed property.
#[cfg(test)]
#[must_use]
pub(super) fn check_loop_total_correct_drop_hyp(which: &str) -> RefinementVerdict {
    let env = match loop_total_correct_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let ty = match loop_total_correct_type_drop_hyp(which) {
        Some(t) => t,
        None => return RefinementVerdict::KernelRejected(format!("unknown drop_hyp: {which}")),
    };
    let proof = loop_total_correct_proof();
    let tc = TypeChecker::new(&env);
    match tc.check_type(&proof, &ty) {
        Ok(()) => RefinementVerdict::ProvenModulo3, // NOT the wanted outcome for the fail-closed test
        Err(e) => RefinementVerdict::KernelRejected(format!("loopTotalCorrect check_type: {e:?}")),
    }
}

/// Build a `loopTotalCorrect` STATEMENT that omits one conjunct-hypothesis. `"pres"`:
/// the preservation hypothesis is dropped (so the binders are `∀ I R cond body,
/// decrease → ∀ e, I e → And A B`). `"decrease"`: the rank-decrease hypothesis is
/// dropped (binders `∀ I R cond body, pres → ∀ e, I e → And A B`). The conjuncts `A`/`B`
/// are unchanged (still reference fuel `R e`). The honest 8-binder proof cannot inhabit
/// either 7-binder statement (a genuine type mismatch), so this is the fail-closed witness.
#[cfg(test)]
pub(super) fn loop_total_correct_type_drop_hyp(which: &str) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_nat = Expr::pi(bd(), env_ty(), cst("Nat"));
    // inside `∀ I ∀ R ∀ cond ∀ body`: body=0, cond=1, R=2, I=3.
    // The retained single hypothesis (only ONE arrow, so the conclusion sits one binder
    // SHALLOWER than the real two-hypothesis theorem — the de-Bruijn shift the honest
    // proof's `And.intro` arguments will NOT match).
    let single_hyp = match which {
        "pres" => preservation_hyp_type(&Expr::bvar(3), &Expr::bvar(1), &Expr::bvar(0)),
        "decrease" => decrease_hyp_type(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
        _ => return None,
    };
    // conclusion after ONE `hyp →`, then `∀ e`, then `I e →`: hI=0, e=1, hyp=2, body=3,
    //   cond=4, R=5, I=6. Build conjuncts at THIS (shallower-by-one) depth.
    let r_e = Expr::app(Expr::bvar(5), Expr::bvar(1)); // R e
    let looped = exec_loop_app(Expr::bvar(1), Expr::bvar(4), Expr::bvar(3), r_e.clone());
    let a = Expr::app(Expr::bvar(6), looped);
    let b = loop_halts_prop(Expr::bvar(1), Expr::bvar(4), Expr::bvar(3), r_e);
    let concl = Expr::apps(cst("And"), [a, b]);
    // hI : I e   (e=0 inside `∀ e`, I=5 there)
    let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
    let after_hi = Expr::pi(bd(), i_e, concl);
    let body_e = Expr::pi(bd(), env_ty(), after_hi);
    let after_hyp = Expr::pi(bd(), single_hyp, body_e);
    Some(Expr::pi(
        bd(),
        env_pred_ty(),
        Expr::pi(
            bd(),
            env_to_nat,
            Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_stmt, after_hyp)),
        ),
    ))
}

/// Check the GENERAL contract-call rule against the real clean-kernel.
/// `claimed_concl_pred = Some` overrides the conclusion's postcondition predicate
/// (fail-closed hook: a wrong postcondition must NOT prove).
#[must_use]
pub fn check_call_refines_contract() -> RefinementVerdict {
    check_call_refines_contract_inner(None)
}

pub(super) fn check_call_refines_contract_inner(claimed_concl_pred: Option<&Expr>) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_call_inductive(&mut env).and_then(|()| register_call_result(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    let call_ty = call_contract_type(claimed_concl_pred);
    let call_proof = call_contract_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&call_proof, &call_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "callRefinesContract check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_CALL_REFINES_CONTRACT),
        level_params: vec![],
        type_: call_ty,
        value: call_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callRefinesContract: {e:?}"));
    }
    match env.axiom_deps(&Name::from_string(MIRSEM_CALL_REFINES_CONTRACT)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "callRefinesContract axiom residue: {names:?}"
            ))
        }
        None => RefinementVerdict::KernelRejected("callRefinesContract decl not found".to_string()),
    }
}
