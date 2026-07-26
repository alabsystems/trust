// Loop postcondition instances, assert discharge inside loops, counter overflow
// discharge, and the slice-index and iterator partial witnesses. The partial
// tier havocs the returned value: it claims the loop is safe, not what it
// computed.

use super::*;

/// Kernel-check that the SYNTHESIZED loop invariant `lf.synth_inv` DISCHARGES the source
/// postcondition `post` at the loop's halting state, modulo 3. The theorem proved is
///
///   `∀ (e : Env), I e → <postcondition-conjunct>(exec_loop e cond body (R e))`
///
/// i.e. starting from the loop entry invariant `I e`, the relevant interval conjunct (the
/// upper bound `i ≤ n` for `RetLeBound`, the lower bound `c ≤ i` for `ConstLeRet`) holds
/// AT THE HALTING STATE `exec_loop e cond body (R e)` — which is exactly the source
/// postcondition once the return reads the counter (`ret = halt i_idx`). The proof
/// COMPOSES the kernel-checked per-function `loopTotalCorrect` instance (`And.left` gives
/// `I (haltState)`, kernel-proven modulo 3) with `And.left`/`And.right` to project the
/// conjunct out of the synthesized range invariant `I := λ e. (c ≤ i) ∧ (i ≤ n)`. No new
/// induction — it reuses the synthesized total-correctness proof. Fail-closed: only the
/// `CounterInRange` synthesized form (which carries BOTH conjuncts) discharges these
/// postconditions; a `post` whose bound/const does not match the synthesized invariant's
/// conjunct is ill-typed ⇒ `KernelRejected`.
pub(super) fn check_loop_postcondition_instance(
    lf: &SemLoopFunction,
    post: LoopPostcondition,
) -> RefinementVerdict {
    // RELATIONAL ACCUMULATOR (PART 1): `I := λ e. (s == i) ∧ (i ≤ n)` discharges the STRONGER
    // postcondition `ret ≤ n` (the return reads `s`): at the halting state, project `s == i`
    // and `i ≤ n` out of `I halt`, then `Eq.subst` along `i = s` to rewrite `i ≤ n` into the
    // GOAL `s ≤ n`. This is dispatched separately from the interval `(i_idx, c, upper)` path
    // because its conjuncts are RELATIONAL (`s == i`), not a `c ≤ i ∧ i ≤ n` interval.
    if let Some(SynthInvariant::AccumEqCounter { s_idx, i_idx, n_idx }) = lf.synth_inv {
        return check_accum_eq_postcondition_instance(lf, post, s_idx, i_idx, n_idx);
    }
    // GENERAL RELATIONAL ACCUMULATOR (PART 1, >2 vars): `I := λ e. (⋀ₖ aₖ == i) ∧ (i ≤ n)`
    // discharges `ret ≤ n` for the RETURNED accumulator `a_{ret}` (ANY `aₖ`, not just `a₀`): project
    // `a_{ret} == i` (the conjunct at position `ret`'s index in `accum_idxs`) and `i ≤ n` out of
    // `I halt`, then `Eq.subst` along `i = a_{ret}` to rewrite `i ≤ n` into the GOAL `a_{ret} ≤ n`.
    if let Some(SynthInvariant::AccumEqCounterSet { accum_idxs, i_idx, n_idx, ret_idx }) =
        &lf.synth_inv
    {
        return check_accum_eq_set_postcondition_instance(
            lf, post, accum_idxs, *i_idx, *n_idx, *ret_idx,
        );
    }
    // CONDITIONALLY-UPDATED ACCUMULATOR (Step 6CU): `I := λ e. (c ≤ m) ∧ (0 ≤ i)` discharges
    // `c ≤ ret` (the return reads `m`): project `And.left (I halt) : c ≤ halt m`. Dispatched
    // separately because the invariant's conjuncts are `(c ≤ m) ∧ (0 ≤ i)` (an interval lower
    // bound on the conditionally-updated `m` plus the counter lower bound), NOT the `c ≤ i ∧ i ≤ n`
    // range the default path projects.
    if let Some(SynthInvariant::CondUpdateGeConst { m_idx, c, i_idx, .. }) = lf.synth_inv {
        return check_cond_update_postcondition_instance(lf, post, m_idx, c, i_idx);
    }
    // The synthesized-invariant SHAPE at the halting state: `(i_idx, c, upper)` where
    // `upper` is `None` for a BARE lower bound (`c ≤ i`, countdown/stride) or
    // `Some((bound_idx, succ))` for a CONJOINED range whose upper conjunct is `i ≤ n`
    // (`succ = false`) or `i ≤ n+1` (`succ = true`).
    let (i_idx, c, upper): (u64, i128, Option<(u64, bool)>) = match lf.synth_inv {
        Some(SynthInvariant::CounterInRange { i_idx, c, bound_idx }) => {
            (i_idx, c, Some((bound_idx, false)))
        }
        Some(SynthInvariant::CounterInRangeSucc { i_idx, c, bound_idx }) => {
            (i_idx, c, Some((bound_idx, true)))
        }
        Some(SynthInvariant::CountdownGeConst { i_idx, c })
        | Some(SynthInvariant::StrideGeConst { i_idx, c, .. }) => (i_idx, c, None),
        // ACCUMULATOR: the bare lower bound `c ≤ s` discharges `c ≤ ret` at the index of the
        // ACCUMULATOR `s_idx` (the return reads `s`, not the guard counter `i`).
        Some(SynthInvariant::AccumGeConst { s_idx, c, .. }) => (s_idx, c, None),
        // CONDITIONAL-INCREMENT accumulator (Increment B): the bare lower bound `c ≤
        // count` discharges `c ≤ ret` at the accumulator `count_idx` — structurally
        // IDENTICAL to `AccumGeConst`'s dispatch (the invariant is a BARE fact, no
        // upper conjunct); only the preservation proof differs.
        Some(SynthInvariant::CondIncrGeConst { count_idx, c, .. }) => (count_idx, c, None),
        _ => {
            return RefinementVerdict::KernelRejected(
                "postcondition discharge requires a synthesized lower/range invariant".to_string(),
            );
        }
    };
    let Some((ranking, decrease)) = synthesize_counter_ranking(lf) else {
        return RefinementVerdict::KernelRejected(
            "postcondition discharge requires a synthesized (terminating) ranking".to_string(),
        );
    };
    let mut env = match loop_total_correct_instance_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };

    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    let body_expr = lf.body_list_expr();

    // The per-function total-correctness PROOF term `loopTotalCorrect I R cond body pres dec`
    // : ∀ e, I e → And (I (exec_loop e cond body (R e))) (eval_cond (...) cond = false).
    let total_proof = loop_total_instance_proof(lf, &ranking, &decrease);

    // Build, under `λ (e:Env) λ (hI : I e)`, the halting state and the invariant `I halt`.
    //   under `λ e λ hI`: hI=0, e=1.
    let e_ref = || Expr::bvar(1);
    let r_e = Expr::app(ranking.clone().lift(2), e_ref()); // R e
    let halt = exec_loop_app(e_ref(), cond_expr.clone().lift(2), body_expr.clone().lift(2), r_e);
    let halt_i = Expr::app(halt.clone(), Expr::nat_lit(i_idx));
    let conj_lo = Expr::apps(cst("Int.le"), [int_lit(c), halt_i.clone()]); // c ≤ halt i
    // The upper conjunct (when present) and the full `I halt` proposition.
    let (conj_hi_opt, i_halt) = match upper {
        Some((bound_idx, succ)) => {
            let halt_b = Expr::app(halt.clone(), Expr::nat_lit(bound_idx));
            let rhs = if succ { Expr::apps(cst("Int.add"), [halt_b, int_one()]) } else { halt_b };
            let conj_hi = Expr::apps(cst("Int.le"), [halt_i.clone(), rhs]); // halt i ≤ (n[+1])
            let i_halt = Expr::apps(cst("And"), [conj_lo.clone(), conj_hi.clone()]);
            (Some(conj_hi), i_halt)
        }
        None => (None, conj_lo.clone()), // bare lower bound: `I halt ≡ c ≤ halt i`.
    };
    // `total_proof e hI : And (I halt) (eval_cond halt cond = false)`.
    let tc_app = Expr::apps(total_proof.clone().lift(2), [e_ref(), Expr::bvar(0)]);
    // halt_false_prop : eval_cond halt cond = false (the And's right component type).
    let halt_false = eq_bool_false(eval_cond_app(halt.clone(), cond_expr.clone().lift(2)));
    // And.left (I halt) (halt-false) tc_app : I halt.
    let i_halt_proof = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [i_halt.clone(), halt_false, tc_app],
    );
    // Project the conjunct the postcondition needs.
    let and_proj = |left: bool, lo: &Expr, hi: &Expr, h: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string(if left { "And.left" } else { "And.right" }), vec![]),
            [lo.clone(), hi.clone(), h],
        )
    };
    let (concl_prop, proof_body) = match (post, &conj_hi_opt) {
        // `ret ≤ n` from the `i ≤ n` upper conjunct (Lt-guard range).
        (LoopPostcondition::RetLeBound { bound_idx: pb }, Some(conj_hi)) => {
            if upper != Some((pb, false)) {
                return RefinementVerdict::KernelRejected(
                    "postcondition `ret ≤ n` requires an `i ≤ n` upper conjunct at that bound"
                        .to_string(),
                );
            }
            (conj_hi.clone(), and_proj(false, &conj_lo, conj_hi, i_halt_proof))
        }
        // `ret ≤ n+1` from the `i ≤ n+1` upper conjunct (Le-guard range).
        (LoopPostcondition::RetLeBoundSucc { bound_idx: pb }, Some(conj_hi)) => {
            if upper != Some((pb, true)) {
                return RefinementVerdict::KernelRejected(
                    "postcondition `ret ≤ n+1` requires an `i ≤ n+1` upper conjunct at that bound"
                        .to_string(),
                );
            }
            (conj_hi.clone(), and_proj(false, &conj_lo, conj_hi, i_halt_proof))
        }
        // `c ≤ ret` from the lower conjunct/bound.
        (LoopPostcondition::ConstLeRet { c: pc }, conj_hi_opt) => {
            if pc != c {
                return RefinementVerdict::KernelRejected(
                    "postcondition constant does not match the synthesized invariant".to_string(),
                );
            }
            match conj_hi_opt {
                // conjoined range: project the lower conjunct.
                Some(conj_hi) => (conj_lo.clone(), and_proj(true, &conj_lo, conj_hi, i_halt_proof)),
                // bare lower bound: `I halt` IS `c ≤ halt i`, no projection.
                None => (conj_lo.clone(), i_halt_proof),
            }
        }
        // Upper-bound postcondition against a BARE lower bound (no upper conjunct) fails closed.
        (LoopPostcondition::RetLeBound { .. } | LoopPostcondition::RetLeBoundSucc { .. }, None) => {
            return RefinementVerdict::KernelRejected(
                "an upper-bound postcondition requires a conjoined-range synthesized invariant"
                    .to_string(),
            );
        }
    };

    // Conclusion TYPE: ∀ (e:Env), I e → <conjunct>(halt).
    //   under `∀ e`: e=0. `I e`: I lifted +1.
    let i_e = Expr::app(i_expr.lift(1), Expr::bvar(0));
    let concl_ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, concl_prop));
    // PROOF: λ (e:Env) λ (hI : I e). proof_body.
    let i_e_dom = {
        let i_expr2 = lf.invariant_expr(None);
        Expr::app(i_expr2.lift(1), Expr::bvar(0))
    };
    let proof = Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_dom, proof_body));

    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "loop postcondition check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.MirSem.loopInstance.postcondition");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add loop postcondition: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "loop postcondition axiom residue: {names:?}"
            ))
        }
        None => RefinementVerdict::KernelRejected("loop postcondition decl not found".to_string()),
    }
}

/// Kernel-check (modulo 3) that the RELATIONAL accumulator invariant `I := λ e. (s == i) ∧
/// (i ≤ n)` discharges the source postcondition `ret ≤ n` at the halting state (PART 1). The
/// proved theorem is `∀ (e:Env), I e → Int.le (halt s_idx) (halt n_idx)` (`s ≤ n` at halt,
/// which is `ret ≤ n` once the return reads `s`):
///   1. `I halt` (= `And (halt s == halt i) (halt i ≤ halt n)`) is the kernel-checked
///      `And.left (loopTotalCorrect … e hI)`.
///   2. `h_eq := And.left … (I halt) : halt s == halt i`, `h_le := And.right … : halt i ≤ halt n`.
///   3. `Eq.subst (λ t. Int.le t (halt n)) (halt i) (halt s) (Eq.symm h_eq) h_le : Int.le
///      (halt s) (halt n)` — rewrite `i ≤ n` along `i = s` to the goal `s ≤ n`.
/// This GENUINELY USES the RELATIONAL conjunct (the `Eq.subst` is impossible without `s == i`);
/// `ret ≤ n` is STRICTLY stronger than the `ret ≥ 0` the bare lower bound gives. Fail-closed:
/// only `RetLeBound { bound_idx = n_idx }` is accepted; a different bound, or any non-`RetLeBound`
/// postcondition, is `KernelRejected`.
pub(super) fn check_accum_eq_postcondition_instance(
    lf: &SemLoopFunction,
    post: LoopPostcondition,
    s_idx: u64,
    i_idx: u64,
    n_idx: u64,
) -> RefinementVerdict {
    // Only `ret ≤ n` (at the guard bound `n_idx`) is discharged by the relational invariant.
    let LoopPostcondition::RetLeBound { bound_idx } = post else {
        return RefinementVerdict::KernelRejected(
            "the relational accumulator invariant discharges only `ret ≤ n`".to_string(),
        );
    };
    if bound_idx != n_idx {
        return RefinementVerdict::KernelRejected(
            "postcondition `ret ≤ n` bound must be the guard bound the relational invariant uses"
                .to_string(),
        );
    }
    let Some((ranking, decrease)) = synthesize_counter_ranking(lf) else {
        return RefinementVerdict::KernelRejected(
            "postcondition discharge requires a synthesized (terminating) ranking".to_string(),
        );
    };
    let mut env = match loop_total_correct_instance_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };

    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    let body_expr = lf.body_list_expr();
    let l1 = || Level::succ(Level::zero());
    let total_proof = loop_total_instance_proof(lf, &ranking, &decrease);

    // under `λ e λ hI`: hI=0, e=1.
    let e_ref = || Expr::bvar(1);
    let r_e = Expr::app(ranking.clone().lift(2), e_ref()); // R e
    let halt = exec_loop_app(e_ref(), cond_expr.clone().lift(2), body_expr.clone().lift(2), r_e);
    let halt_s = Expr::app(halt.clone(), Expr::nat_lit(s_idx)); // halt s
    let halt_i = Expr::app(halt.clone(), Expr::nat_lit(i_idx)); // halt i
    let halt_n = Expr::app(halt.clone(), Expr::nat_lit(n_idx)); // halt n
    let eq_of = |a: Expr, b: Expr| {
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![l1()]), [int_ty(), a, b])
    };
    let conj_eq = eq_of(halt_s.clone(), halt_i.clone()); // halt s == halt i
    let conj_le = Expr::apps(cst("Int.le"), [halt_i.clone(), halt_n.clone()]); // halt i ≤ halt n
    let i_halt = Expr::apps(cst("And"), [conj_eq.clone(), conj_le.clone()]);

    // `total_proof e hI : And (I halt) (eval_cond halt cond = false)`.
    let tc_app = Expr::apps(total_proof.clone().lift(2), [e_ref(), Expr::bvar(0)]);
    let halt_false = eq_bool_false(eval_cond_app(halt.clone(), cond_expr.clone().lift(2)));
    let i_halt_proof = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [i_halt.clone(), halt_false, tc_app],
    ); // : I halt
    let and_proj = |left: bool, lo: &Expr, hi: &Expr, h: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string(if left { "And.left" } else { "And.right" }), vec![]),
            [lo.clone(), hi.clone(), h],
        )
    };
    let h_eq = and_proj(true, &conj_eq, &conj_le, i_halt_proof.clone()); // halt s == halt i
    let h_le = and_proj(false, &conj_eq, &conj_le, i_halt_proof); // halt i ≤ halt n
    // Eq.symm (halt s == halt i) : halt i == halt s.
    let h_eq_sym = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![l1()]),
        [int_ty(), halt_s.clone(), halt_i.clone(), h_eq],
    );
    // motive := λ (t : Int). Int.le t (halt n).  Eq.subst motive (halt i)(halt s) h_eq_sym h_le
    //   : Int.le (halt s) (halt n).
    let motive = Expr::lam(
        bd(),
        int_ty(),
        Expr::apps(cst("Int.le"), [Expr::bvar(0), halt_n.clone().lift(1)]),
    );
    let proof_body = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![l1()]),
        [int_ty(), motive, halt_i, halt_s.clone(), h_eq_sym, h_le],
    );
    let concl_prop = Expr::apps(cst("Int.le"), [halt_s, halt_n]); // halt s ≤ halt n  (`ret ≤ n`)

    // Conclusion TYPE: ∀ (e:Env), I e → (halt s ≤ halt n).
    let i_e = Expr::app(i_expr.lift(1), Expr::bvar(0));
    let concl_ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, concl_prop));
    let i_e_dom = {
        let i_expr2 = lf.invariant_expr(None);
        Expr::app(i_expr2.lift(1), Expr::bvar(0))
    };
    let proof = Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_dom, proof_body));

    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "relational postcondition check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.MirSem.loopInstance.postcondition.relational");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add relational postcondition: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "relational postcondition axiom residue: {names:?}"
            ))
        }
        None => {
            RefinementVerdict::KernelRejected("relational postcondition decl not found".to_string())
        }
    }
}

/// Kernel-check (modulo 3) that the CONDITIONALLY-UPDATED accumulator invariant
/// `I := λ e. (c ≤ m) ∧ (0 ≤ i)` discharges the source postcondition `c ≤ ret` at the halting
/// state (Step 6CU). The proved theorem is `∀ (e:Env), I e → Int.le c (halt m_idx)` (`c ≤ m` at
/// halt, which is `c ≤ ret` once the return reads `m`):
///   1. `I halt` (= `And (c ≤ halt m) (0 ≤ halt i)`) is the kernel-checked
///      `And.left (loopTotalCorrect … e hI)`.
///   2. `And.left (c ≤ halt m) (0 ≤ halt i) (I halt) : Int.le c (halt m)` — project the LEFT
///      conjunct (the conditionally-updated `m`'s lower bound). The `m` lower bound was proved
///      preserved by the `Bool.rec` case-split over the update condition (see
///      [`cond_update_ge_const_preservation_proof`]); here we read it off at the halting state.
/// Fail-closed: only `ConstLeRet { c }` (matching the synthesized `c`) is accepted; a different
/// constant, or any non-`ConstLeRet` postcondition, is `KernelRejected`.
pub(super) fn check_cond_update_postcondition_instance(
    lf: &SemLoopFunction,
    post: LoopPostcondition,
    m_idx: u64,
    c: i128,
    i_idx: u64,
) -> RefinementVerdict {
    // Only `c ≤ ret` (the synthesized lower-bound constant) is discharged.
    let LoopPostcondition::ConstLeRet { c: pc } = post else {
        return RefinementVerdict::KernelRejected(
            "the conditionally-updated accumulator invariant discharges only `c ≤ ret`".to_string(),
        );
    };
    if pc != c {
        return RefinementVerdict::KernelRejected(
            "postcondition constant does not match the synthesized invariant".to_string(),
        );
    }
    let Some((ranking, decrease)) = synthesize_counter_ranking(lf) else {
        return RefinementVerdict::KernelRejected(
            "postcondition discharge requires a synthesized (terminating) ranking".to_string(),
        );
    };
    let mut env = match loop_total_correct_instance_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };

    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    let body_expr = lf.body_list_expr();
    let total_proof = loop_total_instance_proof(lf, &ranking, &decrease);

    // under `λ e λ hI`: hI=0, e=1.
    let e_ref = || Expr::bvar(1);
    let r_e = Expr::app(ranking.clone().lift(2), e_ref()); // R e
    let halt = exec_loop_app(e_ref(), cond_expr.clone().lift(2), body_expr.clone().lift(2), r_e);
    let halt_m = Expr::app(halt.clone(), Expr::nat_lit(m_idx)); // halt m
    let halt_i = Expr::app(halt.clone(), Expr::nat_lit(i_idx)); // halt i
    let conj_lo_m = Expr::apps(cst("Int.le"), [int_lit(c), halt_m.clone()]); // c ≤ halt m
    let conj_lo_i = Expr::apps(cst("Int.le"), [int_lit(0), halt_i]); // 0 ≤ halt i
    let i_halt = Expr::apps(cst("And"), [conj_lo_m.clone(), conj_lo_i.clone()]);

    // `total_proof e hI : And (I halt) (eval_cond halt cond = false)`.
    let tc_app = Expr::apps(total_proof.clone().lift(2), [e_ref(), Expr::bvar(0)]);
    let halt_false = eq_bool_false(eval_cond_app(halt.clone(), cond_expr.clone().lift(2)));
    let i_halt_proof = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [i_halt.clone(), halt_false, tc_app],
    ); // : I halt
    // And.left (c ≤ halt m) (0 ≤ halt i) (I halt) : Int.le c (halt m).
    let proof_body = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [conj_lo_m.clone(), conj_lo_i, i_halt_proof],
    );
    let concl_prop = conj_lo_m; // c ≤ halt m  (`c ≤ ret`)

    // Conclusion TYPE: ∀ (e:Env), I e → (c ≤ halt m).
    let i_e = Expr::app(i_expr.lift(1), Expr::bvar(0));
    let concl_ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, concl_prop));
    let i_e_dom = {
        let i_expr2 = lf.invariant_expr(None);
        Expr::app(i_expr2.lift(1), Expr::bvar(0))
    };
    let proof = Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_dom, proof_body));

    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "cond-update postcondition check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.MirSem.loopInstance.postcondition.condUpdate");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add cond-update postcondition: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "cond-update postcondition axiom residue: {names:?}"
            ))
        }
        None => RefinementVerdict::KernelRejected(
            "cond-update postcondition decl not found".to_string(),
        ),
    }
}

/// Kernel-check (modulo 3) that the GENERAL RELATIONAL invariant `I := λ e. (a₀ == i) ∧ … ∧
/// (aₘ == i) ∧ (i ≤ n)` discharges the source postcondition `ret ≤ n` at the halting state
/// (PART 1: >2 vars). The proved theorem is `∀ (e:Env), I e → Int.le (halt a₀_idx) (halt n_idx)`
/// (`a₀ ≤ n` at halt, which is `ret ≤ n` once the return reads `a₀`):
///   1. `I halt` is `And.left (loopTotalCorrect … e hI)` (kernel-checked).
///   2. `h_eq0 := And.left … (I halt) : halt a₀ == halt i` (the OUTERMOST left conjunct).
///   3. `h_le := i ≤ n` projected by `m+1` `And.right`s + the final `And.left`-free cap.
///   4. `Eq.subst (λ t. Int.le t (halt n)) (halt i)(halt a₀) (Eq.symm h_eq0) h_le : a₀ ≤ n`.
/// GENUINELY USES the RELATIONAL conjunct `a₀ == i` (the `Eq.subst` is impossible without it).
/// Fail-closed: only `RetLeBound { bound_idx = n_idx }` is accepted.
pub(super) fn check_accum_eq_set_postcondition_instance(
    lf: &SemLoopFunction,
    post: LoopPostcondition,
    accum_idxs: &[u64],
    i_idx: u64,
    n_idx: u64,
    ret_idx: u64,
) -> RefinementVerdict {
    let LoopPostcondition::RetLeBound { bound_idx } = post else {
        return RefinementVerdict::KernelRejected(
            "the general relational accumulator invariant discharges only `ret ≤ n`".to_string(),
        );
    };
    if bound_idx != n_idx {
        return RefinementVerdict::KernelRejected(
            "postcondition `ret ≤ n` bound must be the guard bound the relational invariant uses"
                .to_string(),
        );
    }
    // The RETURNED accumulator `a_{ret}` must be one of the lockstep accumulators the relational
    // invariant pins (`a_{ret} == i`). `ret_pos` is its position in the nested `And` — we project
    // its conjunct by walking `ret_pos` `And.right`s then one `And.left` (`ret_pos = 0` is the
    // FIRST accumulator `a₀`, recovering the original `three`/`four` discharge; `ret_pos = 1` is
    // `three_ret_b`'s SECOND accumulator). Fail-closed: a `ret_idx` not in `accum_idxs` is rejected.
    let Some(ret_pos) = accum_idxs.iter().position(|&a| a == ret_idx) else {
        return RefinementVerdict::KernelRejected(
            "the returned accumulator must be one of the relational invariant's accumulators"
                .to_string(),
        );
    };
    let a_ret_idx = ret_idx;
    let Some((ranking, decrease)) = synthesize_counter_ranking(lf) else {
        return RefinementVerdict::KernelRejected(
            "postcondition discharge requires a synthesized (terminating) ranking".to_string(),
        );
    };
    let mut env = match loop_total_correct_instance_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };

    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = lf.invariant_expr(None);
    let cond_expr = lf.cond.to_cond_expr();
    let body_expr = lf.body_list_expr();
    let l1 = || Level::succ(Level::zero());
    let total_proof = loop_total_instance_proof(lf, &ranking, &decrease);

    // under `λ e λ hI`: hI=0, e=1.
    let e_ref = || Expr::bvar(1);
    let r_e = Expr::app(ranking.clone().lift(2), e_ref());
    let halt = exec_loop_app(e_ref(), cond_expr.clone().lift(2), body_expr.clone().lift(2), r_e);
    let halt_at = |idx: u64| Expr::app(halt.clone(), Expr::nat_lit(idx));
    let halt_a_ret = halt_at(a_ret_idx);
    let halt_i = halt_at(i_idx);
    let halt_n = halt_at(n_idx);
    let eq_of = |a: Expr, b: Expr| {
        Expr::apps(Expr::const_(Name::from_string("Eq"), vec![l1()]), [int_ty(), a, b])
    };
    // Reconstruct the nested `And` PROP `I halt = (a₀==i) ∧ ((a₁==i) ∧ (… ∧ (i≤n)))` exactly as
    // `invariant_expr` builds it, so the `And.left`/`And.right` projectors are fully applied.
    let cap_le = Expr::apps(cst("Int.le"), [halt_i.clone(), halt_n.clone()]); // i ≤ n
    let n = accum_idxs.len();
    let mut suffix_prop = vec![cap_le.clone(); n + 1];
    suffix_prop[n] = cap_le.clone();
    for k in (0..n).rev() {
        let eqk = eq_of(halt_at(accum_idxs[k]), halt_i.clone());
        suffix_prop[k] = Expr::apps(cst("And"), [eqk, suffix_prop[k + 1].clone()]);
    }
    // `total_proof e hI : And (I halt) (eval_cond halt cond = false)`.
    let tc_app = Expr::apps(total_proof.clone().lift(2), [e_ref(), Expr::bvar(0)]);
    let halt_false = eq_bool_false(eval_cond_app(halt.clone(), cond_expr.clone().lift(2)));
    let h_base = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [suffix_prop[0].clone(), halt_false, tc_app],
    ); // : I halt = suffix_prop[0]
    // h_eq_ret : halt a_{ret} == halt i — walk `And.right` `ret_pos` times to reach
    // `suffix_prop[ret_pos]`, then `And.left` projects the returned accumulator's equality.
    // (`ret_pos = 0` reproduces the original `a₀ == i` discharge; `ret_pos = 1` is `three_ret_b`.)
    let mut h_walk = h_base.clone();
    for k in 0..ret_pos {
        let eqk_prop = eq_of(halt_at(accum_idxs[k]), halt_i.clone());
        h_walk = Expr::apps(
            Expr::const_(Name::from_string("And.right"), vec![]),
            [eqk_prop, suffix_prop[k + 1].clone(), h_walk],
        );
    } // h_walk : suffix_prop[ret_pos]
    let eq_ret_prop = eq_of(halt_a_ret.clone(), halt_i.clone());
    let h_eq_ret = Expr::apps(
        Expr::const_(Name::from_string("And.left"), vec![]),
        [eq_ret_prop.clone(), suffix_prop[ret_pos + 1].clone(), h_walk],
    );
    // h_le : Int.le (halt i)(halt n) — walk `And.right` all `n` times from the SAME base to the cap.
    let mut h_rest = h_base;
    for k in 0..n {
        let eqk_prop = eq_of(halt_at(accum_idxs[k]), halt_i.clone());
        h_rest = Expr::apps(
            Expr::const_(Name::from_string("And.right"), vec![]),
            [eqk_prop, suffix_prop[k + 1].clone(), h_rest],
        );
    }
    let h_le = h_rest; // : Int.le (halt i)(halt n)
    // Eq.symm (halt a_{ret} == halt i) : halt i == halt a_{ret}.
    let h_eq_sym = Expr::apps(
        Expr::const_(Name::from_string("Eq.symm"), vec![l1()]),
        [int_ty(), halt_a_ret.clone(), halt_i.clone(), h_eq_ret],
    );
    // motive := λ (t : Int). Int.le t (halt n). Eq.subst motive (halt i)(halt a_{ret}) h_eq_sym h_le.
    let motive = Expr::lam(
        bd(),
        int_ty(),
        Expr::apps(cst("Int.le"), [Expr::bvar(0), halt_n.clone().lift(1)]),
    );
    let proof_body = Expr::apps(
        Expr::const_(Name::from_string("Eq.subst"), vec![l1()]),
        [int_ty(), motive, halt_i, halt_a_ret.clone(), h_eq_sym, h_le],
    );
    let concl_prop = Expr::apps(cst("Int.le"), [halt_a_ret, halt_n]); // a_{ret} ≤ n  (`ret ≤ n`)

    let i_e = Expr::app(i_expr.lift(1), Expr::bvar(0));
    let concl_ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, concl_prop));
    let i_e_dom = {
        let i_expr2 = lf.invariant_expr(None);
        Expr::app(i_expr2.lift(1), Expr::bvar(0))
    };
    let proof = Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_dom, proof_body));

    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "general relational postcondition check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.MirSem.loopInstance.postcondition.relational.general");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!(
            "add general relational postcondition: {e:?}"
        ));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "general relational postcondition axiom residue: {names:?}"
            ))
        }
        None => RefinementVerdict::KernelRejected(
            "general relational postcondition decl not found".to_string(),
        ),
    }
}

/// Mint a [`LoopPostconditionCertificate`] for `lf` discharging `post` IF the synthesized
/// invariant kernel-proves the postcondition at the halting state modulo 3. Fail-closed:
/// `None` for a non-`CounterInRange` invariant, a non-counter shape, or a kernel rejection.
#[must_use]
pub fn loop_postcondition_witness(
    lf: &SemLoopFunction,
    post: LoopPostcondition,
) -> Option<LoopPostconditionCertificate> {
    match check_loop_postcondition_instance(lf, post) {
        RefinementVerdict::ProvenModulo3 => Some(LoopPostconditionCertificate {
            function: lf.clone(),
            post,
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// The unsigned `2^w − 1` overflow threshold as an `i128` (fits for `w ≤ 127`).
pub(super) fn unsigned_max_i128(width: u32) -> i128 {
    if width >= 128 { i128::MAX } else { (1i128 << width) - 1 }
}

/// Kernel-check the PER-ASSERT DISCHARGE IMPLICATION `∀ (e:Env), I e → eval_cond e guard =
/// true → eval_cond e assert = true` for the projected loop's invariant `I`, modulo 3.
///
/// The proof is `λ (e:Env)(_hI : I e)(hg : eval_cond e guard = true). hg` — it type-checks
/// iff `eval_cond e assert` is def-eq to `eval_cond e guard`, i.e. `assert ≡ guard` as
/// reflected `Cond`s. The `BoundsCheck` assert of the recognized fragment reads
/// `Lt(counter, PtrMetadata(slice))`; after len-pinning normalization its operands are the
/// SAME `(i, n)` as the guard, so it discharges. FAIL-CLOSED: a hidden-second-index assert
/// (`Lt(j, n)`, j ≠ i) or an off-by-one guard (`Le` vs the `Lt` assert) makes `hg`'s type
/// NOT def-eq to the goal ⇒ `check_type` rejects ⇒ [`RefinementVerdict::KernelRejected`].
#[must_use]
pub fn check_assert_discharge_instance(
    projected: &SemLoopFunction,
    guard: &SemCond,
    assert_cond: &SemCond,
) -> RefinementVerdict {
    let mut env = match loop_instance_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = projected.invariant_expr(None);
    let guard_expr = guard.to_cond_expr();
    let assert_expr = assert_cond.to_cond_expr();

    // Conclusion TYPE: ∀ (e:Env), I e → (eval_cond e guard = true) → (eval_cond e assert = true).
    //   under `∀ e`: e = bvar(0); `I e` for the invariant hypothesis.
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    //   under `∀ e, ∀ hI`: e = bvar(1); the guard hypothesis prop.
    let guard_prop = eq_bool_true(eval_cond_app(Expr::bvar(1), guard_expr.clone().lift(2)));
    //   under `∀ e, ∀ hI, ∀ hg`: e = bvar(2); the assert GOAL prop.
    let assert_prop = eq_bool_true(eval_cond_app(Expr::bvar(2), assert_expr.lift(3)));
    let concl_ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(bd(), i_e, Expr::pi(bd(), guard_prop, assert_prop)),
    );

    // PROOF: λ (e:Env) λ (_hI : I e) λ (hg : guard=true). hg.
    let i_e_dom = Expr::app(i_expr.lift(1), Expr::bvar(0));
    let guard_dom = eq_bool_true(eval_cond_app(Expr::bvar(1), guard_expr.lift(2)));
    let proof = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(bd(), i_e_dom, Expr::lam(bd(), guard_dom, Expr::bvar(0))),
    );

    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!("assert discharge check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.sliceIndexLoop.assertDischarge");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add assert discharge: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!("assert discharge axiom residue: {names:?}"))
        }
        None => RefinementVerdict::KernelRejected("assert discharge decl not found".to_string()),
    }
}

/// Kernel-check the COUNTER-INCREMENT OVERFLOW DISCHARGE `∀ (e:Env), I e → eval_cond e
/// guard = true → Int.le (e n) (2^len_width−1) → Int.le (Int.add (e i) 1)
/// (2^counter_width−1)`, modulo 3.
///
/// This is the `no-overflow` obligation for the counter's `CheckedAdd(i, 1)` assert, made
/// discharge-able by the usize TYPE-BOUND on the slice length `n` (the explicit `n ≤
/// 2^len_width−1` hypothesis — sound because `n = PtrMetadata(s)` is a `usize`, a
/// recognizer-trust fact stated in the report). The proof chains the guard and the bound:
///   `Int.le_trans (i+1) (e n) MAX_counter
///        (of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt …) hg)   -- i+1 ≤ n from i<n
///        hbound`.                                                    -- n ≤ MAX_counter
/// `of_decide_eq_true … hg : Int.lt (e i)(e n)`, DEF-EQ `Int.le ((e i)+1)(e n)` (the same
/// `Int.lt`-unfold `counter_le_bound_preservation_proof` relies on).
///
/// FAIL-CLOSED — the two side conditions are LOAD-BEARING: (a) an off-by-one guard (`Le`
/// not `Lt`) makes `eval_cond` not reduce to `decide (Int.lt …)`, so `of_decide_eq_true`
/// does not apply ⇒ rejected; (b) a NARROW counter (`counter_width < len_width`, e.g. `u8`
/// counter vs `u64` len, where `i+1` genuinely CAN overflow while `i < n`) makes `hbound :
/// Int.le (e n) MAX_len` NOT match `Int.le_trans`'s required `Int.le (e n) MAX_counter` ⇒
/// rejected — proving the type-bound side condition is not a tautology of the encoding.
#[must_use]
pub fn check_counter_overflow_discharge_instance(
    projected: &SemLoopFunction,
    guard: &SemCond,
    i_idx: u64,
    n_idx: u64,
    counter_width: u32,
    len_width: u32,
) -> RefinementVerdict {
    let mut env = match loop_instance_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let bd = || BinderData::from(BinderInfo::Default);
    let i_expr = projected.invariant_expr(None);
    let guard_expr = guard.to_cond_expr();
    let counter_max = int_lit(unsigned_max_i128(counter_width));
    let len_max = int_lit(unsigned_max_i128(len_width));

    // Conclusion TYPE: ∀ (e:Env), I e → guard=true → (Int.le (e n) MAX_len) → (Int.le
    //   (Int.add (e i) 1) MAX_counter).
    //   under `∀ e`: e = bvar(0).
    let i_e = Expr::app(i_expr.clone().lift(1), Expr::bvar(0));
    //   under `∀ e, ∀ hI`: e = bvar(1).
    let guard_prop = eq_bool_true(eval_cond_app(Expr::bvar(1), guard_expr.clone().lift(2)));
    //   under `∀ e, ∀ hI, ∀ hg`: e = bvar(2); the type-bound hypothesis `n ≤ MAX_len`.
    let e_n_ty = Expr::app(Expr::bvar(2), Expr::nat_lit(n_idx));
    let bound_prop = Expr::apps(cst("Int.le"), [e_n_ty, len_max.clone()]);
    //   under `∀ e, ∀ hI, ∀ hg, ∀ hbound`: e = bvar(3); the overflow GOAL `i+1 ≤ MAX_counter`.
    let e_i_ty = Expr::app(Expr::bvar(3), Expr::nat_lit(i_idx));
    let i_plus_one_ty = Expr::apps(cst("Int.add"), [e_i_ty, int_lit(1)]);
    let goal_prop = Expr::apps(cst("Int.le"), [i_plus_one_ty, counter_max.clone()]);
    let concl_ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            i_e,
            Expr::pi(bd(), guard_prop, Expr::pi(bd(), bound_prop, goal_prop)),
        ),
    );

    // PROOF: λ e λ _hI λ hg λ hbound. Int.le_trans (i+1) (e n) MAX_counter <i+1≤n> hbound.
    //   under 4 lambdas: e = bvar(3), _hI = bvar(2), hg = bvar(1), hbound = bvar(0).
    let i_e_dom = Expr::app(i_expr.lift(1), Expr::bvar(0));
    let guard_dom = eq_bool_true(eval_cond_app(Expr::bvar(1), guard_expr.lift(2)));
    let e_n_dom = Expr::app(Expr::bvar(2), Expr::nat_lit(n_idx)); // under `λ e λ _hI λ hg`
    let bound_dom = Expr::apps(cst("Int.le"), [e_n_dom, len_max.clone()]);
    let e_i = Expr::app(Expr::bvar(3), Expr::nat_lit(i_idx));
    let e_n = Expr::app(Expr::bvar(3), Expr::nat_lit(n_idx));
    let i_plus_one = Expr::apps(cst("Int.add"), [e_i.clone(), int_lit(1)]);
    // <i+1 ≤ n> := of_decide_eq_true (Int.lt (e i)(e n)) (Int.decLt (e i)(e n)) hg.
    let p = Expr::apps(cst("Int.lt"), [e_i.clone(), e_n.clone()]);
    let inst = Expr::apps(cst("Int.decLt"), [e_i, e_n.clone()]);
    let lt_proof = Expr::apps(of_decide_eq_true_term(), [p, inst, Expr::bvar(1)]);
    // Int.le_trans (i+1) (e n) MAX_counter <i+1≤n> hbound : Int.le (i+1) MAX_counter.
    let proof_body =
        Expr::apps(cst("Int.le_trans"), [i_plus_one, e_n, counter_max, lt_proof, Expr::bvar(0)]);
    let proof = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            i_e_dom,
            Expr::lam(bd(), guard_dom, Expr::lam(bd(), bound_dom, proof_body)),
        ),
    );

    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &concl_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "counter overflow discharge check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string("Trust.MirSem.sliceIndexLoop.counterOverflowDischarge");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: concl_ty,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add counter overflow discharge: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "counter overflow discharge axiom residue: {names:?}"
            ))
        }
        None => {
            RefinementVerdict::KernelRejected("counter overflow discharge decl not found".to_string())
        }
    }
}

/// Mint a [`SliceIndexPartialCertificate`] for the recognized slice-index loop `silf`:
/// kernel-check the invariant (via the existing [`loop_refinement_witness`] on the
/// counter-projected loop), the BoundsCheck-assert discharge, and the counter-increment
/// overflow discharge, all modulo 3. `total_available` MUST be `function_safety_vcs_all_
/// discharged(func)` (the mandatory termination gate, threaded from the prove.rs entry):
/// when `true` the termination half (loopTotalCorrect) is ALSO minted; when `false` the
/// PARTIAL tier is certified with NO reach-Return claim. Fail-closed: `None` if the
/// invariant obligation does not kernel-check (a wrong invariant is KernelRejected).
#[must_use]
pub fn slice_index_partial_witness(
    silf: &SliceIndexLoopFunction,
    total_available: bool,
) -> Option<SliceIndexPartialCertificate> {
    // (I) the genuinely inductive invariant — reuse the EXISTING kernel machinery verbatim.
    let invariant = match loop_refinement_witness(&silf.projected) {
        Some(cert) => cert.verdict,
        None => return None, // a wrong/unpreserved invariant fails closed here.
    };
    // (II) the BoundsCheck assert discharge implication.
    let bounds_discharge =
        check_assert_discharge_instance(&silf.projected, &silf.guard, &silf.bounds_cond);
    // (III) the counter-increment overflow discharge (under the usize len type-bound).
    let counter_overflow_discharge = check_counter_overflow_discharge_instance(
        &silf.projected,
        &silf.guard,
        silf.i_idx,
        silf.n_idx,
        silf.counter_width,
        silf.len_width,
    );
    // TERMINATION — the mandatory gate. Only when the caller certifies (via
    // `function_safety_vcs_all_discharged`) that NO undischarged panic exit remains.
    let termination = if total_available {
        Some(match loop_total_correct_witness(&silf.projected) {
            Some(cert) => cert.verdict,
            None => RefinementVerdict::KernelRejected(
                "termination requested but loopTotalCorrect did not kernel-check".to_string(),
            ),
        })
    } else {
        None
    };
    Some(SliceIndexPartialCertificate {
        function: silf.clone(),
        invariant,
        bounds_discharge,
        counter_overflow_discharge,
        termination,
    })
}

/// Trust: P-ITER-COUNT WITNESS — the GHOST-MODEL EXIT-COUNT lemma FORMULA (the VIOLATION
/// whose refutation modulo 3 witnesses `(0≤i ∧ i≤n ∧ ¬(i<n)) ⇒ i=n`). Built over two fresh
/// ghost Int `Var`s named `i_name`/`n_name`; it is exposed so the fence pin can structurally
/// scan it (it names ONLY the two ghost vars + integer literals — no fenced symbol). The
/// refutation is discharged by the EXISTING `vc_refute` Int-order-totality machinery (the
/// #21 disequality widening `i != n ⟹ i<n ∨ i>n`, both branches closed under the guards):
/// NO new axiom / opaque / named kernel rule, proven modulo the same 3 foundational axioms.
#[must_use]
pub fn ghost_exit_count_lemma_formula(i_name: &str, n_name: &str) -> trust_types::Formula {
    use trust_types::{Formula as F, Sort};
    let i = || F::Var(i_name.to_string(), Sort::Int);
    let n = || F::Var(n_name.to_string(), Sort::Int);
    // The VIOLATION of the exit lemma: 0≤i ∧ i≤n ∧ ¬(i<n) ∧ ¬(i=n). UNSAT modulo 3.
    F::And(vec![
        F::Ge(Box::new(i()), Box::new(F::Int(0))),
        F::Le(Box::new(i()), Box::new(n())),
        F::Not(Box::new(F::Lt(Box::new(i()), Box::new(n())))),
        F::Not(Box::new(F::Eq(Box::new(i()), Box::new(n())))),
    ])
}

/// Trust: P-ITER-COUNT WITNESS — whether the ghost-model exit-count lemma refutes modulo 3
/// via the existing `vc_refute` Int-totality machinery. Fence-free (two fresh ghost vars).
#[must_use]
pub fn ghost_exit_count_refuted_modulo_3() -> bool {
    let violation = ghost_exit_count_lemma_formula("i_ghost", "n_ghost");
    matches!(
        crate::vc_refute::check_refute_vc(&violation),
        Some(crate::RefuteOutcome::RefutedModulo3)
    )
}

/// Mint an [`IterLoopPartialCertificate`] for the recognized iterator-for-loop `ilf`:
/// kernel-check the ghost-counter invariant (via the EXISTING [`loop_refinement_witness`]
/// on the projected loop) — obligation (I) ONLY. `total_available` MUST be
/// `function_safety_vcs_all_discharged(func)` (the mandatory termination gate, threaded
/// from the prove.rs entry): when `true` the termination half is ALSO minted; when `false`
/// the PARTIAL tier is certified with NO reach-Return claim. Fail-closed: `None` if the
/// invariant obligation does not kernel-check (a wrong/tampered projected model is
/// KernelRejected). No bounds/counter-overflow discharge is minted (they do not exist for
/// the for-desugar caller — see the type doc + module comment).
#[must_use]
pub fn iter_loop_partial_witness(
    ilf: &IterLoopFunction,
    total_available: bool,
) -> Option<IterLoopPartialCertificate> {
    // Trust: HONEST FLOOR inc-2 (2026-07-23) — GATE-ITER-GEN-KEY-DISCIPLINE clause-(i) decline
    // half, WIRED at this consumer chokepoint (defense-in-depth on `ilf.projected`, redundant
    // with the guard inside `loop_refinement_witness`). The ghost projection names ONLY
    // {i_ghost, n_ghost}, so this is VACUOUSLY FALSE / byte-green; it declines fail-closed if a
    // future increment ever routes the two-key handle into the projected loop.
    if sem_loop_function_carries_entry_iter_handle(&ilf.projected) {
        return None;
    }
    // (I) the genuinely inductive ghost-counter invariant — reuse the INC1 kernel
    // machinery VERBATIM. A tampered projected model (wrong constant / stride / guard) is
    // ill-typed ⇒ KernelRejected ⇒ `None` here.
    let invariant = match loop_refinement_witness(&ilf.projected) {
        Some(cert) => cert.verdict,
        None => return None,
    };
    // TERMINATION — the mandatory gate. Only when the caller certifies (via
    // `function_safety_vcs_all_discharged`) that NO undischarged panic exit remains. Never
    // reached for sum_loop/count_pos (their accumulator-overflow VCs are open).
    let termination = if total_available {
        Some(match loop_total_correct_witness(&ilf.projected) {
            Some(cert) => cert.verdict,
            None => RefinementVerdict::KernelRejected(
                "termination requested but loopTotalCorrect did not kernel-check".to_string(),
            ),
        })
    } else {
        None
    };
    // The per-link witness is ATTACHED separately (it needs the sibling dumps + the caller
    // CFG), by the with-bodies funnel `crate::prove::iter_loop_partial_faithful_with_bodies`.
    // The bare witness mints `None` here — class-neutrality preserved by construction.
    Some(IterLoopPartialCertificate {
        function: ilf.clone(),
        invariant,
        termination,
        premise_witness: None,
    })
}
