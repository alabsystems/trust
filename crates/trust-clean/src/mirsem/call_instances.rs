// Per-instance verdicts and witnesses for the call shapes: plain return,
// call-then-pure-op, call-op-call, two-call chains and call-then-project. Each
// builds the instance type from the recognised shape and checks the proof term
// against it, so an unrecognised shape yields no witness.

use super::*;

/// Trust: call-spine increment — mint the CALL-RETURN adequacy certificate for a
/// recognized call-return shape: build the kernel env, register the `Call`
/// inductive + `call_result` projection, type-check + register the PROVEN
/// `callRefinesContract` transport lemma, then type-check + register the
/// PER-CALL INSTANCE at this call site's concrete `(callee-id, first-arg)`
/// `Call.mk` value and audit its axiom closure. `Some` ONLY when the instance is
/// `ProvenModulo3` (fail-closed on any kernel rejection or axiom residue) —
/// never a false certificate.
#[must_use]
pub fn call_return_adequacy_witness(call: &SemCallReturn) -> Option<CallReturnAdequacyCertificate> {
    match call_return_instance_verdict(call, None) {
        RefinementVerdict::ProvenModulo3 => Some(CallReturnAdequacyCertificate {
            call: call.clone(),
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// Check the per-call `callRefinesContract` INSTANCE against the real
/// clean-kernel. `claimed_concl_pred = Some(p)` overrides the instance
/// conclusion's postcondition predicate (fail-closed hook: a WRONG postcondition
/// — a different predicate from the assumed one — must NOT prove).
pub(super) fn call_return_instance_verdict(
    call: &SemCallReturn,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_call_inductive(&mut env).and_then(|()| register_call_result(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    // Register the GENERAL proven transport lemma (same discipline as
    // `check_call_refines_contract`: type-check the proof, add as a Theorem).
    let lemma_ty = call_contract_type(None);
    let lemma_proof = call_contract_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&lemma_proof, &lemma_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "callRefinesContract check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_CALL_REFINES_CONTRACT),
        level_params: vec![],
        type_: lemma_ty,
        value: lemma_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callRefinesContract: {e:?}"));
    }
    // The PER-CALL INSTANCE at the concrete (callee-id, first-arg) call value.
    // The recognizer guarantees a non-empty modeled arg list (fail-closed).
    let Some(arg) = call.args.first() else {
        return RefinementVerdict::KernelRejected(
            "call-return shape has no modeled argument".to_string(),
        );
    };
    let inst_ty = call_return_instance_type(call.callee_id, arg, claimed_concl_pred);
    let inst_proof = call_return_instance_proof(call.callee_id, arg);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "callReturnInstance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string(MIRSEM_CALL_RETURN_INSTANCE);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callReturnInstance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("callReturnInstance decl not found".to_string()),
    }
}

// ---------------------------------------------------------------------------
// Trust: CALL-THEN-PUREOP — the kernel certificate. Reuses the SAME PROVEN
// `callRefinesContract` transport lemma [`call_return_instance_type`]/
// [`call_return_instance_proof`] apply (structure, not content — NO new axiom):
// `callRefinesContract : ∀ (post:Int→Prop)(c:Call), post(call_result c) →
// post(call_result c)` is universally quantified over ANY `post`, so instantiating
// it at `post' := λ x. post(wrap x)` for a chosen WRAP function gives, after beta
// reduction, EXACTLY `post(wrap(call_result c)) → post(wrap(call_result c))` — the
// bare-passthrough instance generalized to "the call's opaque result, wrapped by
// the pure op the caller applies to it." `wrap` embeds the pure op via the
// ALREADY-MODELED pieces: `int_binop_expr` (Lemma 1B's own arithmetic grounding,
// reused verbatim) for [`CallThenOp::Bin`], or `cmp_bool_expr` + `bool_as_int` (the
// SAME closed-form comparison term `eval_cond` reduces to, plus the existing
// Bool-as-0/1-on-Int convention) for [`CallThenOp::Cmp`].
// ---------------------------------------------------------------------------
/// The per-call CALL-THEN-PUREOP instance TYPE — mirrors [`call_return_instance_type`]
/// EXACTLY, with `call_result C[ret]` WRAPPED by the pure op (`wrap`) in BOTH the
/// hypothesis and conclusion (the SAME binder structure: inside `∀ post ∀ ret`,
/// `ret=0, post=1`; under the `hyp →` arrow, `hyp=0, ret=1, post=2` — byte-identical
/// depths, `wrap` never opens a binder of its own). `claimed_concl_pred = Some(p)`
/// overrides the conclusion's predicate (the SAME fail-closed hook).
pub(super) fn call_then_pureop_instance_type(
    callee_id: u64,
    call_arg: &SemOperand,
    wrap: &dyn Fn(Expr) -> Expr,
    claimed_concl_pred: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(cst(MIRSEM_CALL_MK), [Expr::nat_lit(callee_id), call_arg.to_operand_expr(), ret])
    };
    // inside `∀ post ∀ ret`: ret=0, post=1. HYPOTHESIS: post (wrap (call_result C[ret])).
    let hyp =
        Expr::app(Expr::bvar(1), wrap(Expr::app(cst(MIRSEM_CALL_RESULT), call_at(Expr::bvar(0)))));
    // CONCLUSION (under the `hyp →` arrow, everything +1): <pred> (wrap (call_result C[ret])).
    let concl_pred =
        claimed_concl_pred.cloned().map(|p| p.lift(3)).unwrap_or_else(|| Expr::bvar(2)); // the assumed `post` itself
    let concl =
        Expr::app(concl_pred, wrap(Expr::app(cst(MIRSEM_CALL_RESULT), call_at(Expr::bvar(1)))));
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), int_ty(), arrow))
}

/// The per-call CALL-THEN-PUREOP instance PROOF: `λ (post)(ret)(h). callRefinesContract
/// (λ x. post (wrap x)) (Call.mk <id> <arg> ret) h` — a plain APPLICATION of the
/// registered PROVEN [`MIRSEM_CALL_REFINES_CONTRACT`] transport lemma at the WRAPPED
/// predicate (structure, not content — no new axiom; mirrors
/// [`call_return_instance_proof`], generalized only by the extra `wrap` composed
/// into the instantiated `post'`). Beta-reduces the hypothesis/goal to EXACTLY the
/// wrapped statement [`call_then_pureop_instance_type`] states.
pub(super) fn call_then_pureop_instance_proof(
    callee_id: u64,
    call_arg: &SemOperand,
    wrap: &dyn Fn(Expr) -> Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(cst(MIRSEM_CALL_MK), [Expr::nat_lit(callee_id), call_arg.to_operand_expr(), ret])
    };
    // hyp type inside `λ post λ ret`: ret=0, post=1.
    let hyp_ty =
        Expr::app(Expr::bvar(1), wrap(Expr::app(cst(MIRSEM_CALL_RESULT), call_at(Expr::bvar(0)))));
    // body inside `λ post λ ret λ h`: h=0, ret=1, post=2.
    // `λ x. post (wrap x)` — entering this NEW binder shifts `post` (was bvar(2))
    // to bvar(3); `x` is this binder's own bvar(0).
    let wrapped_post = Expr::lam(bd(), int_ty(), Expr::app(Expr::bvar(3), wrap(Expr::bvar(0))));
    let body = Expr::apps(
        cst(MIRSEM_CALL_REFINES_CONTRACT),
        [wrapped_post, call_at(Expr::bvar(1)), Expr::bvar(0)],
    );
    Expr::lam(bd(), int_to_prop, Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, body)))
}

/// Trust: PARAM-OPERAND generalization — the per-call CALL-THEN-PUREOP instance
/// TYPE when the shape's non-call operand is a function PARAMETER, not a closed
/// constant (`has_len`/`at_least`'s `len() == n` / `len() >= n`, e.g.). Mirrors
/// [`call_then_pureop_instance_type`] EXACTLY, with ONE extra ∀-bound `Int` binder
/// (`paramVal`, standing for "whatever value the parameter operand denotes")
/// inserted BETWEEN `post` and `ret`, threaded into `wrap` in place of the closed
/// literal [`call_then_pureop_instance_type`] splices in. The transport lemma
/// this instantiates is already universally quantified over `post`; adding
/// `paramVal` as ANOTHER ∀-bound variable is the SAME discipline, not a new axiom
/// — `paramVal` is never asserted to equal the actual parameter's value here (that
/// connection is the separately kernel-checked operand-adequacy certificate for
/// `call_then_op.other`, [`operand_adequacy_witness`]; this instance only needs
/// the TRANSPORT shape to type-check for an arbitrary such value).
///
/// Binder order `∀ post ∀ paramVal ∀ ret`: inside the hypothesis, `ret=0,
/// paramVal=1, post=2`; under the `hyp →` arrow (everything +1), `hyp=0, ret=1,
/// paramVal=2, post=3`. `claimed_concl_pred = Some(p)` overrides the conclusion's
/// predicate (the SAME fail-closed hook, lifted one level deeper than
/// [`call_then_pureop_instance_type`]'s own `lift(3)` to clear the extra binder).
pub(super) fn call_then_pureop_instance_type_param(
    callee_id: u64,
    call_arg: &SemOperand,
    wrap: &dyn Fn(Expr, Expr) -> Expr,
    claimed_concl_pred: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(cst(MIRSEM_CALL_MK), [Expr::nat_lit(callee_id), call_arg.to_operand_expr(), ret])
    };
    // inside `∀ post ∀ paramVal ∀ ret`: ret=0, paramVal=1, post=2.
    // HYPOTHESIS: post (wrap paramVal (call_result C[ret])).
    let hyp = Expr::app(
        Expr::bvar(2),
        wrap(Expr::bvar(1), Expr::app(cst(MIRSEM_CALL_RESULT), call_at(Expr::bvar(0)))),
    );
    // CONCLUSION (under the `hyp →` arrow, everything +1): ret=1, paramVal=2, post=3.
    let concl_pred =
        claimed_concl_pred.cloned().map(|p| p.lift(4)).unwrap_or_else(|| Expr::bvar(3)); // the assumed `post` itself
    let concl = Expr::app(
        concl_pred,
        wrap(Expr::bvar(2), Expr::app(cst(MIRSEM_CALL_RESULT), call_at(Expr::bvar(1)))),
    );
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), arrow)))
}

/// Trust: PARAM-OPERAND generalization — the per-call CALL-THEN-PUREOP instance
/// PROOF for the PARAM-operand path: `λ (post)(paramVal)(ret)(h). callRefinesContract
/// (λ x. post (wrap paramVal x)) (Call.mk <id> <arg> ret) h` — a plain APPLICATION
/// of the registered PROVEN [`MIRSEM_CALL_REFINES_CONTRACT`] transport lemma at the
/// WRAPPED predicate, exactly as [`call_then_pureop_instance_proof`] does, with the
/// SAME extra `paramVal` binder [`call_then_pureop_instance_type_param`] adds.
/// Beta-reduces the hypothesis/goal to EXACTLY the wrapped statement that function
/// states.
pub(super) fn call_then_pureop_instance_proof_param(
    callee_id: u64,
    call_arg: &SemOperand,
    wrap: &dyn Fn(Expr, Expr) -> Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(cst(MIRSEM_CALL_MK), [Expr::nat_lit(callee_id), call_arg.to_operand_expr(), ret])
    };
    // hyp type inside `λ post λ paramVal λ ret`: ret=0, paramVal=1, post=2.
    let hyp_ty = Expr::app(
        Expr::bvar(2),
        wrap(Expr::bvar(1), Expr::app(cst(MIRSEM_CALL_RESULT), call_at(Expr::bvar(0)))),
    );
    // body inside `λ post λ paramVal λ ret λ h`: h=0, ret=1, paramVal=2, post=3.
    // `λ x. post (wrap paramVal x)` — entering this NEW binder shifts `post` (was
    // bvar(3)) to bvar(4) and `paramVal` (was bvar(2)) to bvar(3); `x` is this
    // binder's own bvar(0).
    let wrapped_post =
        Expr::lam(bd(), int_ty(), Expr::app(Expr::bvar(4), wrap(Expr::bvar(3), Expr::bvar(0))));
    let body = Expr::apps(
        cst(MIRSEM_CALL_REFINES_CONTRACT),
        [wrapped_post, call_at(Expr::bvar(1)), Expr::bvar(0)],
    );
    Expr::lam(
        bd(),
        int_to_prop,
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, body))),
    )
}

/// Check the per-call CALL-THEN-PUREOP instance against the real clean-kernel.
/// SCOPE (Trust: PARAM-OPERAND generalization): the shape's `other` operand must
/// be a CLOSED CONSTANT (`SemOperand::Const` — the ORIGINAL, byte-identical path)
/// OR a function PARAMETER (`SemOperand::Var`, optionally `Move`-wrapped — the
/// NEW path, [`call_then_pureop_instance_type_param`]/[`call_then_pureop_instance_proof_param`]:
/// the param is threaded as an extra ∀-bound instance variable, never a fresh
/// axiom). Anything else (a second call result, a field-read, or any other
/// unmodeled operand — Call-OP-Call's two-call-result shape, e.g.) is STILL a
/// NAMED RESIDUE and fails closed (`KernelRejected`, never silently absorbed) —
/// this generalization only widens WHICH operand kinds are admitted, it does not
/// touch the fail-closed default.
pub(super) fn call_then_pureop_instance_verdict(
    call_then_op: &SemCallThenPureOp,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_call_inductive(&mut env).and_then(|()| register_call_result(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    // Register the GENERAL proven transport lemma (same discipline as
    // `call_return_instance_verdict`: type-check the proof, add as a Theorem).
    let lemma_ty = call_contract_type(None);
    let lemma_proof = call_contract_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&lemma_proof, &lemma_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "callRefinesContract check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_CALL_REFINES_CONTRACT),
        level_params: vec![],
        type_: lemma_ty,
        value: lemma_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callRefinesContract: {e:?}"));
    }

    let Some(call_arg) = call_then_op.call.args.first() else {
        return RefinementVerdict::KernelRejected(
            "call-then-pureop shape has no modeled argument".to_string(),
        );
    };
    let call_is_lhs = call_then_op.call_is_lhs;

    // Trust: PARAM-OPERAND generalization — is the non-call operand a bare
    // parameter (`Var`), or the move-out form of one (`Move (Var _)` —
    // `sem_operand_of_mir`'s modeling of `Operand::Move` of a parameter place)?
    // Either way it is "a function parameter" for this instance's purposes: the
    // kernel side never inspects WHICH param index, only that the value is bound
    // as an arbitrary ∀-quantified `Int` (see `call_then_pureop_instance_type_param`'s
    // doc) — the concrete index is what `operand_adequacy_witness` separately
    // certifies.
    let is_param_other = matches!(&call_then_op.other, SemOperand::Var(_))
        || matches!(
            &call_then_op.other,
            SemOperand::Move(inner) if matches!(inner.as_ref(), SemOperand::Var(_))
        );

    // SCOPE gate: the non-call operand must be a closed constant (BYTE-IDENTICAL
    // original path) or a function parameter (NEW path). Anything else — a second
    // call result, a field-read, … — is still a named residue: fail closed.
    let (inst_ty, inst_proof) = if let SemOperand::Const(other_const) = call_then_op.other {
        let wrap: Box<dyn Fn(Expr) -> Expr> = match call_then_op.op {
            CallThenOp::Bin(op) => Box::new(move |x: Expr| {
                let lit = int_lit(other_const);
                if call_is_lhs { int_binop_expr(&op, x, lit) } else { int_binop_expr(&op, lit, x) }
            }),
            CallThenOp::Cmp(op) => Box::new(move |x: Expr| {
                let lit = int_lit(other_const);
                let (a, b) = if call_is_lhs { (x, lit) } else { (lit, x) };
                bool_as_int(cmp_bool_expr(op, a, b))
            }),
            CallThenOp::Cast(destination_width, destination_signed) => Box::new(move |x: Expr| {
                let _ = other_const;
                Expr::apps(
                    cst(MIRSEM_IDX_ELEM),
                    [x, int_lit(mirsem_cast_tag_key(destination_width, destination_signed))],
                )
            }),
        };
        (
            call_then_pureop_instance_type(
                call_then_op.call.callee_id,
                call_arg,
                &wrap,
                claimed_concl_pred,
            ),
            call_then_pureop_instance_proof(call_then_op.call.callee_id, call_arg, &wrap),
        )
    } else if is_param_other {
        let wrap: Box<dyn Fn(Expr, Expr) -> Expr> = match call_then_op.op {
            CallThenOp::Bin(op) => Box::new(move |p: Expr, x: Expr| {
                if call_is_lhs { int_binop_expr(&op, x, p) } else { int_binop_expr(&op, p, x) }
            }),
            CallThenOp::Cmp(op) => Box::new(move |p: Expr, x: Expr| {
                let (a, b) = if call_is_lhs { (x, p) } else { (p, x) };
                bool_as_int(cmp_bool_expr(op, a, b))
            }),
            // The recognizer always supplies a closed dummy for a unary Cast,
            // but retain a total exhaustive arm that ignores the param.
            CallThenOp::Cast(destination_width, destination_signed) => {
                Box::new(move |_p: Expr, x: Expr| {
                    Expr::apps(
                        cst(MIRSEM_IDX_ELEM),
                        [x, int_lit(mirsem_cast_tag_key(destination_width, destination_signed))],
                    )
                })
            }
        };
        (
            call_then_pureop_instance_type_param(
                call_then_op.call.callee_id,
                call_arg,
                &wrap,
                claimed_concl_pred,
            ),
            call_then_pureop_instance_proof_param(call_then_op.call.callee_id, call_arg, &wrap),
        )
    } else {
        return RefinementVerdict::KernelRejected(
            "call-then-pureop: the non-call operand must be a constant or a \
             function parameter (a second call result, field-read, or other \
             unmodeled operand is a named residue, not yet closed)"
                .to_string(),
        );
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "callThenPureOpInstance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string(MIRSEM_CALL_THEN_PUREOP_INSTANCE);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callThenPureOpInstance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => {
            RefinementVerdict::KernelRejected("callThenPureOpInstance decl not found".to_string())
        }
    }
}

/// Trust: CALL-THEN-PUREOP — mint the adequacy certificate for a recognized
/// call-then-pureop shape: build the kernel env, register the `Call` inductive +
/// `call_result` projection, type-check + register the PROVEN
/// `callRefinesContract` transport lemma, then type-check + register the PER-CALL
/// WRAPPED INSTANCE at this call site's concrete `(callee-id, first-arg)`
/// `Call.mk` value and audit its axiom closure. `Some` ONLY when the instance is
/// `ProvenModulo3` (fail-closed on any kernel rejection, axiom residue, or
/// out-of-scope `other` operand — see [`call_then_pureop_instance_verdict`]'s
/// scope note) — never a false certificate.
#[must_use]
pub fn call_then_pureop_adequacy_witness(
    call_then_op: &SemCallThenPureOp,
) -> Option<CallThenPureOpAdequacyCertificate> {
    match call_then_pureop_instance_verdict(call_then_op, None) {
        RefinementVerdict::ProvenModulo3 => Some(CallThenPureOpAdequacyCertificate {
            call_then_op: call_then_op.clone(),
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Trust: CALL-RESULT-AWARE COMPOSITION — the kernel certificate. REUSES
// [`call_then_pureop_instance_type`]/[`call_then_pureop_instance_proof`] (the
// CONST-other path) and [`call_then_pureop_instance_type_param`]/[`call_then_
// pureop_instance_proof_param`] (the PARAM-other path) VERBATIM — zero new
// Expr-building code. Those four functions already generalize the proven
// `callRefinesContract` transport lemma to an ARBITRARY `wrap` closure over
// the call's opaque result (and, in the PARAM path, an extra ∀-bound operand
// value); this section's ONLY new content is a BIGGER `wrap` that ALSO
// composes the inner checked-arith Mul on top (via the SAME `int_binop_expr`
// every unchecked/checked-arith VALUE in this file already grounds through —
// see [`resolve_checked_field_rvalue`]'s doc: field 0 of a checked op grounds
// IDENTICALLY to the unchecked op, so no separate "checked" Expr content is
// needed). The bool -> int CAST hop needs NO Expr-level content at all: see
// [`sem_call_chain_pureop_of_mir`]'s module doc for why `wrap` never builds a
// separate Cast node.
// ---------------------------------------------------------------------------
/// Check the per-call CALL-RESULT-AWARE COMPOSITION instance against the real
/// clean-kernel. SCOPE (mirrors [`call_then_pureop_instance_verdict`]
/// exactly): the shape's `other` operand must be a CLOSED CONSTANT
/// (`SemOperand::Const`) or a function PARAMETER (`SemOperand::Var`,
/// optionally `Move`-wrapped) — anything else (a second call result, a
/// field-read, or any other unmodeled operand) is a named residue and fails
/// closed (`KernelRejected`), never silently absorbed.
pub(super) fn call_chain_pureop_instance_verdict(
    chain: &SemCallChainPureOp,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_call_inductive(&mut env).and_then(|()| register_call_result(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    // Register the GENERAL proven transport lemma (same discipline as every
    // other per-call instance verdict in this file).
    let lemma_ty = call_contract_type(None);
    let lemma_proof = call_contract_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&lemma_proof, &lemma_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "callRefinesContract check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_CALL_REFINES_CONTRACT),
        level_params: vec![],
        type_: lemma_ty,
        value: lemma_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callRefinesContract: {e:?}"));
    }

    let Some(call_arg) = chain.call.args.first() else {
        return RefinementVerdict::KernelRejected(
            "call-chain-pureop shape has no modeled argument".to_string(),
        );
    };

    let inner_op = chain.inner_op;
    let inner_const = chain.inner_const;
    let inner_call_is_lhs = chain.inner_call_is_lhs;
    let outer_op = chain.outer_op;
    let outer_mul_is_lhs = chain.outer_mul_is_lhs;
    // The inner checked-arith Mul, applied to the (bool-identity-cast) call
    // result `x`.
    let mul_expr = move |x: Expr| -> Expr {
        let lit = int_lit(inner_const);
        if inner_call_is_lhs {
            int_binop_expr(&inner_op, x, lit)
        } else {
            int_binop_expr(&inner_op, lit, x)
        }
    };

    let is_param_other = matches!(&chain.other, SemOperand::Var(_))
        || matches!(&chain.other, SemOperand::Move(inner) if matches!(inner.as_ref(), SemOperand::Var(_)));

    let (inst_ty, inst_proof) = if let SemOperand::Const(other_const) = chain.other {
        let wrap: Box<dyn Fn(Expr) -> Expr> = Box::new(move |x: Expr| {
            let m = mul_expr(x);
            let lit = int_lit(other_const);
            if outer_mul_is_lhs {
                int_binop_expr(&outer_op, m, lit)
            } else {
                int_binop_expr(&outer_op, lit, m)
            }
        });
        (
            call_then_pureop_instance_type(
                chain.call.callee_id,
                call_arg,
                &wrap,
                claimed_concl_pred,
            ),
            call_then_pureop_instance_proof(chain.call.callee_id, call_arg, &wrap),
        )
    } else if is_param_other {
        let wrap: Box<dyn Fn(Expr, Expr) -> Expr> = Box::new(move |p: Expr, x: Expr| {
            let m = mul_expr(x);
            if outer_mul_is_lhs {
                int_binop_expr(&outer_op, m, p)
            } else {
                int_binop_expr(&outer_op, p, m)
            }
        });
        (
            call_then_pureop_instance_type_param(
                chain.call.callee_id,
                call_arg,
                &wrap,
                claimed_concl_pred,
            ),
            call_then_pureop_instance_proof_param(chain.call.callee_id, call_arg, &wrap),
        )
    } else {
        return RefinementVerdict::KernelRejected(
            "call-chain-pureop: the non-call operand must be a constant or a \
             function parameter (a second call result, field-read, or other \
             unmodeled operand is a named residue, not yet closed)"
                .to_string(),
        );
    };

    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "callChainPureOpInstance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string(MIRSEM_CALL_CHAIN_PUREOP_INSTANCE);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callChainPureOpInstance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => {
            RefinementVerdict::KernelRejected("callChainPureOpInstance decl not found".to_string())
        }
    }
}

/// Trust: CALL-RESULT-AWARE COMPOSITION — mint the adequacy certificate for a
/// recognized call-chain-pureop shape: build the kernel env, register the
/// `Call` inductive + `call_result` projection, type-check + register the
/// PROVEN `callRefinesContract` transport lemma, then type-check + register
/// the PER-CALL WRAPPED INSTANCE at this call site's concrete
/// `(callee-id, first-arg)` `Call.mk` value and audit its axiom closure.
/// `Some` ONLY when the instance is `ProvenModulo3` (fail-closed on any
/// kernel rejection, axiom residue, or out-of-scope `other` operand — see
/// [`call_chain_pureop_instance_verdict`]'s scope note) — never a false
/// certificate.
#[must_use]
pub fn call_chain_pureop_adequacy_witness(
    chain: &SemCallChainPureOp,
) -> Option<CallChainPureOpAdequacyCertificate> {
    match call_chain_pureop_instance_verdict(chain, None) {
        RefinementVerdict::ProvenModulo3 => Some(CallChainPureOpAdequacyCertificate {
            chain: chain.clone(),
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Trust: CALL-OP-CALL — the kernel certificate. Reuses the SAME PROVEN
// `callRefinesContract` transport lemma TWICE (once per call), nested: the
// INNER application transports call_b's result at the predicate `λ b. post
// (wrap (call_result CallA[retA]) b)` (closing over `retA`, still symbolic);
// the OUTER application transports call_a's result at `λ a. post (wrap a
// (call_result CallB[retB]))` (closing over `retB`), applied to the inner
// application's proof. Both are STRUCTURAL applications of the ONE registered
// theorem — NO new axiom, exactly the same posture as the PARAM-OPERAND
// widening's single extra ∀-bound binder, just TWO of them (`retA`, `retB`
// each ∀-bound, threaded into the SAME `wrap`).
// ---------------------------------------------------------------------------
/// The per-call-pair CALL-OP-CALL instance TYPE: `∀ post ∀ retA ∀ retB, post
/// (wrap (call_result CallA[retA]) (call_result CallB[retB])) → <pred> (wrap
/// (call_result CallA[retA]) (call_result CallB[retB]))` where `<pred>`
/// defaults to the assumed `post` itself. Binder order `∀ post ∀ retA ∀ retB`:
/// inside the hypothesis, `retB=0, retA=1, post=2`; under the `hyp →` arrow
/// (everything +1), `retB=1, retA=2, post=3`. `claimed_concl_pred = Some(p)`
/// overrides the conclusion's predicate — the SAME fail-closed hook, lifted
/// past all 3 foralls + the arrow (4 binders, matching the PARAM-OPERAND
/// instance's own `lift(4)`).
pub(super) fn call_op_call_instance_type(
    callee_id_a: u64,
    call_arg_a: &SemOperand,
    callee_id_b: u64,
    call_arg_b: &SemOperand,
    wrap: &dyn Fn(Expr, Expr) -> Expr,
    claimed_concl_pred: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at_a = |ret: Expr| {
        Expr::apps(
            cst(MIRSEM_CALL_MK),
            [Expr::nat_lit(callee_id_a), call_arg_a.to_operand_expr(), ret],
        )
    };
    let call_at_b = |ret: Expr| {
        Expr::apps(
            cst(MIRSEM_CALL_MK),
            [Expr::nat_lit(callee_id_b), call_arg_b.to_operand_expr(), ret],
        )
    };
    let cr_a = |ret: Expr| Expr::app(cst(MIRSEM_CALL_RESULT), call_at_a(ret));
    let cr_b = |ret: Expr| Expr::app(cst(MIRSEM_CALL_RESULT), call_at_b(ret));
    // inside `∀ post ∀ retA ∀ retB`: retB=0, retA=1, post=2.
    let hyp = Expr::app(Expr::bvar(2), wrap(cr_a(Expr::bvar(1)), cr_b(Expr::bvar(0))));
    // CONCLUSION (under the `hyp →` arrow, everything +1): retB=1, retA=2, post=3.
    let concl_pred =
        claimed_concl_pred.cloned().map(|p| p.lift(4)).unwrap_or_else(|| Expr::bvar(3)); // the assumed `post` itself
    let concl = Expr::app(concl_pred, wrap(cr_a(Expr::bvar(2)), cr_b(Expr::bvar(1))));
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), arrow)))
}

/// The per-call-pair CALL-OP-CALL instance PROOF: TWO NESTED applications of
/// the registered proven [`MIRSEM_CALL_REFINES_CONTRACT`] — `λ post retA retB
/// h. callRefinesContract postA (Call.mk <idA> <argA> retA) (callRefinesContract
/// postB (Call.mk <idB> <argB> retB) h)` where `postB := λ b. post (wrap
/// (call_result CallA[retA]) b)` and `postA := λ a. post (wrap a (call_result
/// CallB[retB]))`. Both `callRefinesContract` applications are structural (the
/// SAME registered theorem, instantiated at two DIFFERENT wrapped predicates) —
/// never a new axiom. Beta-reduces to EXACTLY the statement
/// [`call_op_call_instance_type`] states (both nested transports are the
/// identity `x → x` on their own wrapped predicate, so composing them changes
/// nothing about the TERM, only makes explicit that BOTH calls' results are
/// individually transported).
pub(super) fn call_op_call_instance_proof(
    callee_id_a: u64,
    call_arg_a: &SemOperand,
    callee_id_b: u64,
    call_arg_b: &SemOperand,
    wrap: &dyn Fn(Expr, Expr) -> Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at_a = |ret: Expr| {
        Expr::apps(
            cst(MIRSEM_CALL_MK),
            [Expr::nat_lit(callee_id_a), call_arg_a.to_operand_expr(), ret],
        )
    };
    let call_at_b = |ret: Expr| {
        Expr::apps(
            cst(MIRSEM_CALL_MK),
            [Expr::nat_lit(callee_id_b), call_arg_b.to_operand_expr(), ret],
        )
    };
    let cr_a = |ret: Expr| Expr::app(cst(MIRSEM_CALL_RESULT), call_at_a(ret));
    let cr_b = |ret: Expr| Expr::app(cst(MIRSEM_CALL_RESULT), call_at_b(ret));

    // hyp type inside `λ post λ retA λ retB`: retB=0, retA=1, post=2.
    let hyp_ty = Expr::app(Expr::bvar(2), wrap(cr_a(Expr::bvar(1)), cr_b(Expr::bvar(0))));

    // Body inside `λ post λ retA λ retB λ h`: h=0, retB=1, retA=2, post=3.
    //
    // postB := λ b. post (wrap (call_result CallA[retA]) b) — entering this NEW
    // binder shifts `retA` (was bvar(2)) to bvar(3) and `post` (was bvar(3)) to
    // bvar(4); `b` is this binder's own bvar(0).
    let post_b = Expr::lam(
        bd(),
        int_ty(),
        Expr::app(Expr::bvar(4), wrap(cr_a(Expr::bvar(3)), Expr::bvar(0))),
    );
    // innerApp := callRefinesContract postB (Call.mk <idB> <argB> retB) h — a
    // plain application at the OUTER (h=0,retB=1,retA=2,post=3) depth.
    let inner_app = Expr::apps(
        cst(MIRSEM_CALL_REFINES_CONTRACT),
        [post_b, call_at_b(Expr::bvar(1)), Expr::bvar(0)],
    );
    // postA := λ a. post (wrap a (call_result CallB[retB])) — entering this NEW
    // binder shifts `retB` (was bvar(1)) to bvar(2) and `post` (was bvar(3)) to
    // bvar(4); `a` is this binder's own bvar(0).
    let post_a = Expr::lam(
        bd(),
        int_ty(),
        Expr::app(Expr::bvar(4), wrap(Expr::bvar(0), cr_b(Expr::bvar(2)))),
    );
    // result := callRefinesContract postA (Call.mk <idA> <argA> retA) innerApp.
    let body = Expr::apps(
        cst(MIRSEM_CALL_REFINES_CONTRACT),
        [post_a, call_at_a(Expr::bvar(2)), inner_app],
    );

    Expr::lam(
        bd(),
        int_to_prop,
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, body))),
    )
}

/// Check the per-call-pair CALL-OP-CALL instance against the real clean-kernel.
/// Builds `wrap(a, b) = op(a, b)` (or, for a comparison, `bool_as_int(cmp(a,
/// b))`) from the recognized [`CallThenOp`] — REUSING the SAME
/// `int_binop_expr`/`cmp_bool_expr`/`bool_as_int` fragments the single-call
/// CALL-THEN-PUREOP instance already uses. No scope gate is needed here (unlike
/// [`call_then_pureop_instance_verdict`]'s param-vs-const split): BOTH operands
/// are ALWAYS call results by construction (`sem_call_op_call_of_mir` only ever
/// produces this shape when both are), so there is no "other operand kind" to
/// admit or reject.
pub(super) fn call_op_call_instance_verdict(
    call_op_call: &SemCallOpCall,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_call_inductive(&mut env).and_then(|()| register_call_result(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    // Register the GENERAL proven transport lemma (same discipline as
    // `call_then_pureop_instance_verdict`: type-check the proof, add as a Theorem).
    let lemma_ty = call_contract_type(None);
    let lemma_proof = call_contract_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&lemma_proof, &lemma_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "callRefinesContract check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_CALL_REFINES_CONTRACT),
        level_params: vec![],
        type_: lemma_ty,
        value: lemma_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callRefinesContract: {e:?}"));
    }

    let Some(arg_a) = call_op_call.call_a.args.first() else {
        return RefinementVerdict::KernelRejected(
            "call-op-call shape has no modeled argument for call_a".to_string(),
        );
    };
    let Some(arg_b) = call_op_call.call_b.args.first() else {
        return RefinementVerdict::KernelRejected(
            "call-op-call shape has no modeled argument for call_b".to_string(),
        );
    };

    let wrap: Box<dyn Fn(Expr, Expr) -> Expr> = match call_op_call.op {
        CallThenOp::Bin(op) => Box::new(move |a: Expr, b: Expr| int_binop_expr(&op, a, b)),
        CallThenOp::Cmp(op) => {
            Box::new(move |a: Expr, b: Expr| bool_as_int(cmp_bool_expr(op, a, b)))
        }
        CallThenOp::Cast(..) => {
            return RefinementVerdict::KernelRejected(
                "call-op-call cannot contain a unary result cast".to_string(),
            );
        }
    };
    let inst_ty = call_op_call_instance_type(
        call_op_call.call_a.callee_id,
        arg_a,
        call_op_call.call_b.callee_id,
        arg_b,
        &wrap,
        claimed_concl_pred,
    );
    let inst_proof = call_op_call_instance_proof(
        call_op_call.call_a.callee_id,
        arg_a,
        call_op_call.call_b.callee_id,
        arg_b,
        &wrap,
    );
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "callOpCallInstance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string(MIRSEM_CALL_OP_CALL_INSTANCE);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callOpCallInstance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("callOpCallInstance decl not found".to_string()),
    }
}

/// Trust: CALL-OP-CALL — mint the adequacy certificate for a recognized
/// call-op-call shape: build the kernel env, register the `Call` inductive +
/// `call_result` projection, type-check + register the PROVEN
/// `callRefinesContract` transport lemma, then type-check + register the
/// PER-CALL-PAIR instance (TWO nested transports, one per call, at this call
/// pair's concrete `(callee-id, first-arg)` values) and audit its axiom
/// closure. `Some` ONLY when the instance is `ProvenModulo3` (fail-closed on
/// any kernel rejection or axiom residue) — never a false certificate.
#[must_use]
pub fn call_op_call_adequacy_witness(
    call_op_call: &SemCallOpCall,
) -> Option<CallOpCallAdequacyCertificate> {
    match call_op_call_instance_verdict(call_op_call, None) {
        RefinementVerdict::ProvenModulo3 => Some(CallOpCallAdequacyCertificate {
            call_op_call: call_op_call.clone(),
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// The `(lo, hi)` inclusive value range of an integer type, or `None` for a
/// width outside `Formula::Int`'s representable range (fail-closed at the
/// 128-bit boundary, the SAME guard the requires-establishment lane applies to
/// a parameter's declared integer type).
pub(super) fn int_ty_bound(width: u32, signed: bool) -> Option<(i128, i128)> {
    if width == 0 || width > 127 {
        return None;
    }
    Some(if signed {
        (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
    } else {
        (0, (1i128 << width) - 1)
    })
}

/// Trust: TWO-CALL CHAIN — the whole-body USE scan for the intermediate temp
/// `t`. Returns `(bare_uses, bad_uses)` where `bare_uses` counts occurrences of
/// `t` as a BARE (unprojected) `Copy`/`Move` operand and `bad_uses` counts EVERY
/// other syntactic occurrence: a PROJECTED read (`_t.0`), an `Index`-projection
/// operand (`arr[_t]`), or an aliasing/opaque place mention (`&_t`, `&raw _t`,
/// `Discriminant(_t)`, `Len(_t)`, `CopyForDeref(_t)`). The inner call's DEST
/// write of `t` is a terminator dest (never an operand) and is not counted.
///
/// The recognizer requires `bad_uses == 0 && bare_uses == 1` so `_t` is
/// consumed EXACTLY ONCE, as a plain value, with no aliasing — the fail-closed
/// single-use / no-alias discipline the composed certificate rests on.
pub(super) fn two_call_chain_intermediate_uses(body: &trust_types::VerifiableBody, t: usize) -> (usize, usize) {
    use trust_types::{Statement, Terminator};
    let mut bare = 0usize;
    let mut bad = 0usize;
    for block in &body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    tcc_scan_place_projs(place, t, &mut bad); // a `_t`-indexed LHS place is a use.
                    tcc_scan_rvalue(rvalue, t, &mut bare, &mut bad);
                }
                Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place }
                | Statement::Retag { place }
                | Statement::PlaceMention(place) => tcc_scan_place_projs(place, t, &mut bad),
                Statement::Intrinsic { args, .. } => {
                    for op in args {
                        tcc_scan_operand(op, t, &mut bare, &mut bad);
                    }
                }
                // StorageLive/Dead (liveness only), Unsupported (declines the shape
                // upstream), and any other #[non_exhaustive] variant mention nothing
                // that reads `_t`'s value.
                _ => {}
            }
        }
        match &block.terminator {
            Terminator::SwitchInt { discr, .. } => tcc_scan_operand(discr, t, &mut bare, &mut bad),
            Terminator::Call { args, .. } => {
                for op in args {
                    tcc_scan_operand(op, t, &mut bare, &mut bad);
                }
            }
            Terminator::Assert { cond, .. } => tcc_scan_operand(cond, t, &mut bare, &mut bad),
            _ => {}
        }
    }
    (bare, bad)
}

/// Count an `Index`-projection operand `arr[_t]` as a (bad) use of `t` — the
/// index local of ANY place's projection list reads `t`'s value.
pub(super) fn tcc_scan_place_projs(p: &trust_types::Place, t: usize, bad: &mut usize) {
    for proj in &p.projections {
        if let trust_types::Projection::Index(idx) = proj {
            if *idx == t {
                *bad += 1;
            }
        }
    }
}

/// Scan one operand for uses of `t`: a BARE (unprojected) `Copy`/`Move` of `_t`
/// is a plain value read (`bare`); a PROJECTED `Copy`/`Move` of `_t` (`_t.0`) or
/// an `Index`-projection referencing `t` is out of fragment (`bad`).
pub(super) fn tcc_scan_operand(op: &trust_types::Operand, t: usize, bare: &mut usize, bad: &mut usize) {
    if let trust_types::Operand::Copy(p) | trust_types::Operand::Move(p) = op {
        if p.local == t {
            if p.projections.is_empty() {
                *bare += 1;
            } else {
                *bad += 1; // a PROJECTED read of `_t` (e.g. `_t.0`) — out of fragment.
            }
        }
        tcc_scan_place_projs(p, t, bad);
    }
}

/// Scan one rvalue for uses of `t`: operand reads via [`tcc_scan_operand`], and
/// any aliasing/opaque place mention (`&_t`, `&raw _t`, `Discriminant(_t)`,
/// `Len(_t)`, `CopyForDeref(_t)`) as a (bad) use.
pub(super) fn tcc_scan_rvalue(rv: &trust_types::Rvalue, t: usize, bare: &mut usize, bad: &mut usize) {
    use trust_types::Rvalue;
    match rv {
        Rvalue::Use(op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) | Rvalue::UnaryOp(_, op) => {
            tcc_scan_operand(op, t, bare, bad);
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            tcc_scan_operand(a, t, bare, bad);
            tcc_scan_operand(b, t, bare, bad);
        }
        Rvalue::Aggregate(_, ops) | Rvalue::Unsupported { operands: ops, .. } => {
            for op in ops {
                tcc_scan_operand(op, t, bare, bad);
            }
        }
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => {
            if place.local == t {
                *bad += 1; // an aliasing / opaque place read of `_t` — out of fragment.
            }
            tcc_scan_place_projs(place, t, bad);
        }
        _ => {} // trust_types::Rvalue is #[non_exhaustive] — any future variant reads nothing here.
    }
}

/// Recognize the TWO-CALL CHAIN shape — see the section doc above for the exact
/// two-call spine and why the four landed call recognizers decline. Mirrors
/// [`sem_call_op_call_of_mir`]'s entry-to-return linear walk and sole-writer
/// discipline, specialized to the SEQUENTIAL (result-feeds-argument), not
/// PARALLEL (both-feed-one-op), composition.
///
/// The admitted shape (fail-closed on everything else, `None`):
///   * no `Unsupported` statement anywhere; every terminator is Call/Goto/
///     Return (no Assert — the caller emits no safety guard in this fragment);
///     EXACTLY TWO `Call` terminators, reached in program order by the linear
///     entry-to-`Return` walk.
///   * INNER call: direct/non-foreign/non-atomic, live target, dest a BARE,
///     non-`_0`, non-parameter temp `_t` of `Ty::Int` (the Int-intermediate
///     scope; Bool/ADT intermediates are residue), resolves in the certified
///     registry (not self-recursive), arity matches, EVERY actual argument a
///     modeled scalar operand (at least one).
///   * `_t` is SOLE-WRITTEN by the inner call (no statement writes it), used
///     EXACTLY ONCE as a bare value, with NO aliasing (the
///     [`two_call_chain_intermediate_uses`] `bare == 1 && bad == 0` gate), and
///     that one use is an argument of the OUTER call.
///   * OUTER call: direct/non-foreign/non-atomic, live target, dest EXACTLY the
///     return place `_0` (bare, `Ty::Int`/`Ty::Bool`), resolves in the certified
///     registry (not self-recursive), arity matches; its actuals are the
///     intermediate `_t` (EXACTLY ONCE) plus MODELED scalar operands (at least
///     one), and `_0` is written ONLY by this call.
///   * the outer call's continuation reaches the UNIQUE `Return` block through
///     Gotos only.
pub(crate) fn sem_two_call_chain_of_mir(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemTwoCallChain> {
    use trust_types::{BlockId, Operand, Terminator, Ty};
    if callees.is_empty() {
        return None; // no certified callee ⇒ the shape can never be admitted.
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let local_is_int_or_bool = |local: usize| -> bool {
        matches!(body.locals.get(local).map(|l| &l.ty), Some(Ty::Int { .. }) | Some(Ty::Bool))
    };

    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, trust_types::Statement::Unsupported { .. }))
    {
        return None;
    }

    // EXACTLY TWO Call terminators; every other terminator is Goto/Return.
    let mut call_count = 0usize;
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Call { .. } => call_count += 1,
            Terminator::Goto(_) | Terminator::Return => {}
            _ => return None,
        }
    }
    if call_count != 2 {
        return None;
    }

    // The UNIQUE Return block.
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block = rets.next()?;
    if rets.next().is_some() {
        return None;
    }

    // Walk the (necessarily linear) control flow from the entry block, collecting
    // the two Calls in PROGRAM ORDER (mirrors `sem_call_op_call_of_mir`).
    let mut cur = BlockId(0);
    let mut walked: Vec<(BlockId, &String, &Vec<Operand>, &trust_types::Place, Option<BlockId>)> =
        Vec::new();
    let mut steps = 0usize;
    loop {
        let blk = body.blocks.iter().find(|b| b.id == cur)?;
        match &blk.terminator {
            Terminator::Return => break,
            Terminator::Goto(g) => cur = *g,
            Terminator::Call { func: callee, args, dest, target, atomic, is_foreign, .. } => {
                if *is_foreign || atomic.is_some() {
                    return None;
                }
                walked.push((blk.id, callee, args, dest, *target));
                cur = (*target)?;
            }
            _ => return None,
        }
        steps += 1;
        if steps > body.blocks.len() {
            return None; // cycle — not a linear spine.
        }
    }
    if walked.len() != 2 {
        return None; // not exactly two calls ON the entry-to-return path.
    }
    let (call_block_in, callee_in, args_in, dest_in, _target_in) = walked[0];
    let (call_block_out, callee_out, args_out, dest_out, target_out) = walked[1];

    // INNER dest `_t`: bare, non-`_0`, non-parameter, Int-typed (Int-intermediate
    // scope). Its integer type supplies the requires-establishment bound.
    if !dest_in.projections.is_empty() {
        return None;
    }
    let t = dest_in.local;
    if t == 0 || param_index(t).is_some() {
        return None;
    }
    let (width, signed) = match body.locals.get(t).map(|l| &l.ty) {
        Some(Ty::Int { width, signed }) => (*width, *signed),
        // a Bool/ADT intermediate is out of this increment's fragment.
        _ => return None,
    };
    let intermediate_bound = int_ty_bound(width, signed)?;

    // OUTER dest: EXACTLY the return place `_0` (bare, Int/Bool).
    if !dest_out.projections.is_empty() || dest_out.local != 0 || !local_is_int_or_bool(0) {
        return None;
    }
    // The outer call's continuation reaches the Return block through Gotos only.
    {
        let mut c = target_out?;
        let mut n = 0usize;
        while c != ret_block.id {
            let blk = body.blocks.iter().find(|b| b.id == c)?;
            match &blk.terminator {
                Terminator::Goto(g) => c = *g,
                _ => return None,
            }
            n += 1;
            if n > body.blocks.len() {
                return None;
            }
        }
    }

    // Resolve both callees; self-recursion (either) declines.
    let (resolved_in, fact_in, callee_id_in) = resolve_certified_callee(callees, callee_in)?;
    let (resolved_out, fact_out, callee_id_out) = resolve_certified_callee(callees, callee_out)?;
    if resolved_in == func.def_path
        || *callee_in == func.def_path
        || resolved_out == func.def_path
        || *callee_out == func.def_path
    {
        return None;
    }
    if fact_in.arg_count != args_in.len() || fact_out.arg_count != args_out.len() {
        return None;
    }
    if args_in.is_empty() || args_out.is_empty() {
        return None;
    }

    // SOLE-WRITER discipline: `_t` and `_0` are each written by NO statement (the
    // inner/outer call terminators are their only writers).
    let writes_to = |local: usize| -> usize {
        body.blocks.iter().flat_map(|b| &b.stmts).filter(|s| stmt_writes_local(s, local)).count()
    };
    if writes_to(t) != 0 || writes_to(0) != 0 {
        return None;
    }

    // `_t` used EXACTLY ONCE, as a bare value, with no aliasing anywhere.
    let (bare_uses, bad_uses) = two_call_chain_intermediate_uses(body, t);
    if bare_uses != 1 || bad_uses != 0 {
        return None;
    }

    // INNER args: all modeled scalar operands.
    let mut inner_args = Vec::with_capacity(args_in.len());
    for a in args_in {
        inner_args.push(sem_call_arg_operand(body, a, call_block_in, &param_index)?);
    }

    // OUTER args: the single bare-`_t` slot is the intermediate; every other
    // actual must be a modeled scalar operand; at least one modeled (naming arg).
    let is_bare_t = |op: &Operand| -> bool {
        matches!(op, Operand::Copy(p) | Operand::Move(p) if p.local == t && p.projections.is_empty())
    };
    let mut outer_args = Vec::with_capacity(args_out.len());
    let mut intermediate_count = 0usize;
    let mut modeled_count = 0usize;
    for a in args_out {
        if is_bare_t(a) {
            intermediate_count += 1;
            outer_args.push(ChainArg::Intermediate);
        } else {
            outer_args.push(ChainArg::Modeled(sem_call_arg_operand(
                body,
                a,
                call_block_out,
                &param_index,
            )?));
            modeled_count += 1;
        }
    }
    if intermediate_count != 1 || modeled_count == 0 {
        return None; // exactly one intermediate slot; at least one naming arg.
    }

    Some(SemTwoCallChain {
        inner: SemCallReturn {
            callee: resolved_in.to_string(),
            callee_id: callee_id_in,
            args: inner_args,
        },
        outer_callee: resolved_out.to_string(),
        outer_callee_id: callee_id_out,
        outer_args,
        intermediate_bound,
    })
}

/// Trust: TWO-CALL CHAIN — mint the adequacy certificate for a recognized
/// two-call-chain shape: kernel-check the INNER call's `callReturnInstance`
/// transport (`_t = call_result(CallF)`) AND the OUTER call's
/// `callReturnInstance` transport (`_0 = call_result(CallG)`), the OUTER named
/// by its first MODELED (non-intermediate) actual argument. `Some` ONLY when
/// BOTH are `ProvenModulo3` (fail-closed on any kernel rejection or axiom
/// residue) — never a false certificate.
#[must_use]
pub fn two_call_chain_adequacy_witness(
    chain: &SemTwoCallChain,
) -> Option<TwoCallChainAdequacyCertificate> {
    // The OUTER call, named by its modeled args (the intermediate is not a
    // first-class operand; the single-call model already keys a call by its
    // first modeled arg alone — the naming is cosmetic, the transport universal).
    let outer_modeled = chain.outer_modeled_args();
    if outer_modeled.is_empty() {
        return None; // no naming arg — fail closed (the recognizer already ensures ≥1).
    }
    let outer_call = SemCallReturn {
        callee: chain.outer_callee.clone(),
        callee_id: chain.outer_callee_id,
        args: outer_modeled,
    };
    let inner_verdict = call_return_instance_verdict(&chain.inner, None);
    if !matches!(inner_verdict, RefinementVerdict::ProvenModulo3) {
        return None;
    }
    let outer_verdict = call_return_instance_verdict(&outer_call, None);
    if !matches!(outer_verdict, RefinementVerdict::ProvenModulo3) {
        return None;
    }
    Some(TwoCallChainAdequacyCertificate {
        chain: chain.clone(),
        inner_verdict,
        outer_verdict,
    })
}

/// Recognize the CALL-THEN-PROJECT shape — see the section doc above. Mirrors
/// [`sem_call_return_of_mir`] clause-for-clause, with the dest widened to a
/// TUPLE temp and the return widened to its single field projection.
///
/// The admitted shape (fail-closed on everything else, `None`):
///   * no `Unsupported` statement anywhere; EXACTLY ONE `Call` terminator; every
///     other terminator is Goto/Return.
///   * the call is direct/non-foreign/non-atomic with a live target; its dest is
///     a BARE, non-`_0`, non-parameter temp `_t` of `Ty::Tuple` type, SOLE-
///     WRITTEN by the call.
///   * the callee resolves in the certified registry (not self-recursive), arity
///     matches, and EVERY actual argument is a modeled scalar operand (≥1).
///   * `_t` is used EXACTLY ONCE (the [`two_call_chain_intermediate_uses`] scan,
///     reused: `bare == 0` — no bare read of a tuple temp — and the SINGLE
///     projected use `_t.Field(i)` is the return write, verified below), with no
///     aliasing.
///   * `_0` (bare, `Ty::Int`/`Ty::Bool` — the field's type) is written EXACTLY
///     ONCE, by `_0 := Use(Copy/Move _t.Field(i))`, in the linear-Goto return
///     spine's `Return` block.
pub(crate) fn sem_call_then_project_of_mir(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemCallThenProject> {
    use trust_types::{Operand, Projection, Rvalue, Statement, Terminator, Ty};
    if callees.is_empty() {
        return None;
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let local_is_int_or_bool = |local: usize| -> bool {
        matches!(body.locals.get(local).map(|l| &l.ty), Some(Ty::Int { .. }) | Some(Ty::Bool))
    };

    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. })) {
        return None;
    }

    // EXACTLY ONE Call terminator; every other terminator is Goto/Return.
    let mut call = None;
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Call { func: callee, args, dest, target, atomic, is_foreign, .. } => {
                if call.is_some() {
                    return None;
                }
                call = Some((block.id, callee, args, dest, *target, atomic, *is_foreign));
            }
            Terminator::Goto(_) | Terminator::Return => {}
            _ => return None,
        }
    }
    let (call_block_id, callee_str, args, dest, target, atomic, is_foreign) = call?;
    if is_foreign || atomic.is_some() {
        return None;
    }
    let target = target?;

    // Dest `_t`: a BARE, non-`_0`, non-parameter TUPLE temp.
    if !dest.projections.is_empty() {
        return None;
    }
    let t = dest.local;
    if t == 0 || param_index(t).is_some() {
        return None;
    }
    if !matches!(body.locals.get(t).map(|l| &l.ty), Some(Ty::Tuple(_))) {
        return None; // only a Tuple-returning call reaches this shape.
    }

    // Resolve the callee (self-recursion declines), arity, modeled args.
    let (resolved, fact, callee_id) = resolve_certified_callee(callees, callee_str)?;
    if resolved == func.def_path || *callee_str == func.def_path {
        return None;
    }
    if fact.arg_count != args.len() || args.is_empty() {
        return None;
    }
    let mut sem_args = Vec::with_capacity(args.len());
    for a in args {
        sem_args.push(sem_call_arg_operand(body, a, call_block_id, &param_index)?);
    }

    // The UNIQUE Return block, reached from the call's target through Gotos only.
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block = rets.next()?;
    if rets.next().is_some() {
        return None;
    }
    let mut cur = target;
    let mut steps = 0usize;
    while cur != ret_block.id {
        let blk = body.blocks.iter().find(|b| b.id == cur)?;
        match &blk.terminator {
            Terminator::Goto(t) => cur = *t,
            _ => return None,
        }
        steps += 1;
        if steps > body.blocks.len() {
            return None;
        }
    }

    // SOLE-WRITER: `_t` (the tuple temp) written by NO statement — the call is
    // its only writer. (`_0` IS written once, by the projection statement below;
    // that single write is enforced by `writes_0_total == 1`.)
    let writes_to = |local: usize| -> usize {
        body.blocks.iter().flat_map(|b| &b.stmts).filter(|s| stmt_writes_local(s, local)).count()
    };
    if writes_to(t) != 0 {
        return None;
    }
    if param_index(0).is_some() {
        return None; // defensive: `_0` is never a parameter.
    }

    // `_0`'s SOLE write: `_0 := Use(Copy/Move _t.Field(i))`.
    let last_to_0 = ret_block.stmts.iter().rev().find_map(|s| match s {
        Statement::Assign { place, rvalue, .. }
            if place.local == 0 && place.projections.is_empty() =>
        {
            Some(rvalue)
        }
        _ => None,
    })?;
    // Count ALL writes to `_0` across the whole body (not just the Return block).
    let writes_0_total = body
        .blocks
        .iter()
        .flat_map(|b| &b.stmts)
        .filter(|s| stmt_writes_local(s, 0))
        .count();
    if writes_0_total != 1 {
        return None;
    }
    let field = match last_to_0 {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if p.local == t && matches!(p.projections.as_slice(), [Projection::Field(_)]) =>
        {
            match p.projections.as_slice() {
                [Projection::Field(i)] => u64::try_from(*i).ok()?,
                _ => return None,
            }
        }
        _ => return None,
    };
    // The projected `_0` must be an Int/Bool scalar (the field's type).
    if !local_is_int_or_bool(0) {
        return None;
    }

    // `_t` is used EXACTLY ONCE — and it is the PROJECTED field read above, never
    // a bare read or an alias. Reuse the intermediate use-scan: a Tuple temp has
    // NO bare read (`bare == 0`), and its ONLY projected/aliased mention (`bad ==
    // 1`) is the `_t.Field(i)` return read just matched.
    let (bare_uses, bad_uses) = two_call_chain_intermediate_uses(body, t);
    if bare_uses != 0 || bad_uses != 1 {
        return None;
    }

    Some(SemCallThenProject { call: SemCallReturn { callee: resolved.to_string(), callee_id, args: sem_args }, field })
}

/// Check the per-call CALL-THEN-PROJECT instance against the real clean-kernel.
/// Reuses [`call_then_pureop_instance_type`]/[`call_then_pureop_instance_proof`]
/// VERBATIM with `wrap(x) = idx_elem(x, field)` — the field-`i` projection of
/// the callee's opaque tuple result. `claimed_concl_pred = Some(p)` overrides
/// the instance conclusion's postcondition predicate (fail-closed hook: a WRONG
/// projected field builds a DIFFERENT `idx_elem` key, which must not prove).
pub(super) fn call_then_project_instance_verdict(
    proj: &SemCallThenProject,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_call_inductive(&mut env).and_then(|()| register_call_result(&mut env)) {
        return RefinementVerdict::KernelRejected(e);
    }
    let lemma_ty = call_contract_type(None);
    let lemma_proof = call_contract_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&lemma_proof, &lemma_ty) {
            return RefinementVerdict::KernelRejected(format!("callRefinesContract check_type: {e:?}"));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_CALL_REFINES_CONTRACT),
        level_params: vec![],
        type_: lemma_ty,
        value: lemma_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callRefinesContract: {e:?}"));
    }
    let Some(call_arg) = proj.call.args.first() else {
        return RefinementVerdict::KernelRejected("call-then-project shape has no modeled argument".to_string());
    };
    let field_key = int_lit(i128::from(proj.field));
    let wrap: Box<dyn Fn(Expr) -> Expr> =
        Box::new(move |x: Expr| Expr::apps(cst(MIRSEM_IDX_ELEM), [x, field_key.clone()]));
    let inst_ty =
        call_then_pureop_instance_type(proj.call.callee_id, call_arg, &wrap, claimed_concl_pred);
    let inst_proof = call_then_pureop_instance_proof(proj.call.callee_id, call_arg, &wrap);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!("callThenProjectInstance check_type: {e:?}"));
        }
    }
    let name = Name::from_string(MIRSEM_CALL_THEN_PROJECT_INSTANCE);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add callThenProjectInstance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("callThenProjectInstance decl not found".to_string()),
    }
}

/// Trust: CALL-THEN-PROJECT — mint the adequacy certificate for a recognized
/// call-then-project shape. `Some` ONLY when the per-call
/// `callThenProjectInstance` is `ProvenModulo3` (fail-closed on any kernel
/// rejection or axiom residue) — never a false certificate.
#[must_use]
pub fn call_then_project_adequacy_witness(
    proj: &SemCallThenProject,
) -> Option<CallThenProjectAdequacyCertificate> {
    match call_then_project_instance_verdict(proj, None) {
        RefinementVerdict::ProvenModulo3 => {
            Some(CallThenProjectAdequacyCertificate { proj: proj.clone(), verdict: RefinementVerdict::ProvenModulo3 })
        }
        _ => None,
    }
}

/// Check the MUTUAL-RECURSION contract rule against the real clean-kernel. The rule
/// quantifies over the per-callee contract family `Post : Nat → Int → Prop`, a call
/// ranking `rank : Call → Nat`, and the mutual STEP (assume-the-callees, only for
/// strictly-smaller-rank calls); GIVEN the step it composes the contracts over the
/// whole call graph. `claimed_concl_post = Some(p)` overrides ONLY the conclusion's
/// contract family (fail-closed hook: a WRONG contract — a different `Post` from the
/// one the step establishes — must NOT prove, since the proof composes the real
/// `Post` and a non-matching conclusion contract fails to inhabit).
#[must_use]
pub fn check_mutual_call_contracts() -> RefinementVerdict {
    check_mutual_call_contracts_inner(None)
}

pub(super) fn check_mutual_call_contracts_inner(claimed_concl_post: Option<&Expr>) -> RefinementVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_call_inductive(&mut env)
        .and_then(|()| register_call_result(&mut env))
        .and_then(|()| register_nat_le_trans(&mut env))
        .and_then(|()| register_mutual_call_contracts(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    let rule_ty = mutual_call_contracts_type(claimed_concl_post);
    let rule_proof = mutual_call_contracts_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&rule_proof, &rule_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "mutualCallContracts check_type: {e:?}"
            ));
        }
    }
    match env.axiom_deps(&Name::from_string(MIRSEM_MUTUAL_CALL_CONTRACTS)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!(
                "mutualCallContracts axiom residue: {names:?}"
            ))
        }
        None => RefinementVerdict::KernelRejected("mutualCallContracts decl not found".to_string()),
    }
}
