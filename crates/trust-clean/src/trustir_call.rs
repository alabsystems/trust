// trust-clean/trustir_call.rs — the trust-ir CALL denotation (the call-spine
// increment's NAMED RESIDUE #1, closed): the inter-procedural `Call` theory ported
// onto the trust-ir-keyed Clean denotation, so the call-spine CALLER certifies VIA
// TRUST-IR instead of as a MirSem strangler fallback.
//
// WHY THIS EXISTS.
// The call-spine increment (reports/call-spine-increment-2026-07-03.md) landed the
// FOURTH return shape — a caller whose return value is written by a sole
// `Terminator::Call` to an already-certified same-crate callee — with its adequacy
// witness on the MirSem `Call`/`call_result` machinery (`mirsem.rs`:
// `register_call_inductive` / `callRefinesContract` / `callReturnInstance`). Under
// the flipped gate that caller counted as `fully_faithful_mirsem_fallback` (> 0 on
// the call-spine corpus, BY DESIGN — the residue was named, not hidden). This module
// is the closure: the SAME theory, byte-for-byte with names swapped (the
// `trustir_termination.rs` LoopLayer-port discipline), registered under
// `Trust.TrustIr.*` names ONLY in the trust-ir env — returning the measured
// MirSem-fallback population to 0 everywhere and un-pausing the MirSem-deletion soak.
//
// WHAT IS REGISTERED (all kernel-checked; every theorem's axiom residue EMPTY — the
// axiom closure ⊆ {propext, Quot.sound, Classical.choice}, modulo exactly 3):
//
//   * `Trust.TrustIr.Call : Type` — one constructor
//     `Call.mk : Nat → Operand → Int → Call`, where `Operand` is the trust-ir
//     `Trust.TrustIr.Operand` (NOT the MirSem one — the zero-MirSem separation is
//     load-bearing; the census + the separation probe below assert it). `callee`
//     names the resolved certified callee (its registry index as a `Nat`), `arg`
//     the first actual argument, `ret` the value the callee returns. Port of
//     `Trust.MirSem.Call`.
//   * `Trust.TrustIr.callResult : Call → Int` — the call site's DENOTATION via the
//     `Call` recursor (`Call.rec (λ_.Int) (λ callee arg ret. ret)`): a genuine
//     recursor projection of the (separately-verified) callee return. Port of
//     `Trust.MirSem.call_result`.
//   * `Trust.TrustIr.callCallee : Call → Nat` — the callee-ID projection. Port of
//     `Trust.MirSem.call_callee`.
//   * `Trust.TrustIr.callRefinesContract` — the PROVEN contract-transport lemma
//     `∀ (post : Int → Prop)(c : Call), post (callResult c) → post (callResult c)`,
//     proof `λ post c h. h`. HONEST (same reading as the MirSem original): the
//     identity TRANSPORTS the ASSUMED callee guarantee to the call site and
//     discharges no callee body — the hypothesis is established by the callee's own
//     separate certification (the callees-first registry's job). Registered as a
//     `Declaration::Theorem` through the audited helper (check_type + add_decl +
//     EMPTY-residue assert) — NO new axiom, NO new free constant.
//
// PER-CALL-SITE INSTANTIATION (the wired increment):
//   * `check_call_return_instance(callee_id, arg)` — the PER-CALL instance
//     `Trust.TrustIr.callReturnInstance : ∀ (post : Int → Prop)(ret : Int),
//     post (callResult (Call.mk <id> <arg> ret)) → post (callResult (Call.mk <id>
//     <arg> ret))`, whose proof is a plain APPLICATION `λ post ret h.
//     callRefinesContract post (Call.mk <id> <arg> ret) h` of the registered proven
//     lemma at the concrete callee-id `Nat` literal and the concrete trust-ir
//     `Operand` constructor value. check_type → register → `axiom_deps` audit;
//     `ProvenModulo3` IFF the residue is empty. The fail-closed hook mirrors the
//     MirSem one: a WRONG conclusion predicate (`claimed_concl_pred`) must NOT
//     prove — kernel-tested below.
//
// AXIS HONESTY (unchanged from the MirSem call witness — this is a RELOCATION, not
// a strengthening): the instance is on the DENOTATIONAL-ADEQUACY axis. The call's
// return denotes the opaque `callResult` recursor projection — "the value the
// SEPARATELY-VERIFIED callee returns". `post` stays a ∀-bound parameter; no
// postcondition-VC rebinding moves onto this axis. The call-site `#[requires]`
// establishment (the call-spine increment's NAMED residue #2) is CLOSED as a
// SEPARATE clause of the via-path predicate — clause (d) of
// `prove::call_return_fully_faithful_via_trustir`: every callee requires-conjunct,
// with the actuals substituted for the formals, has its negation refuted modulo 3
// by the consumed `vc_refute` lane under the caller's own preconditions + type
// bounds (`prove::call_site_requires_established`). It is deliberately NOT part
// of this kernel instance (correct altitude: establishment is a caller-side
// proof obligation, not a property of the call's denotation). The one-arg
// `Call.mk` model (residue #3) still carries over: the instance pins the FIRST
// actual arg; all args are still operand-certified on the Rust side (prove.rs's
// via-path clause) and arity is checked by the recognizer.
//
// SOUNDNESS DISCIPLINE (house rules, non-negotiable):
//   * modulo exactly 3 — the general lemma's registration re-audits `env.axiom_deps`
//     and FAILS on any non-empty residue; the per-call instance verdict is
//     `ProvenModulo3` IFF its own residue is empty;
//   * fail-closed — a wrong postcondition is KernelRejected; the recognizer side
//     (mirsem::sem_call_return_of_mir, SHAPE-ONLY reuse) fails closed everywhere;
//   * ADDITIVE — no existing `trustir_anchor` / `mirsem` registration is altered
//     (the only sibling edits are `pub(crate)` visibility); `vc_refute.rs` untouched;
//   * zero MirSem names — no decl registered here references any `Trust.MirSem.*`
//     constant (the separation probe test asserts it, and `axiom_census` covers
//     `trustir_call_env`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use clean_kernel::{
    BinderData, BinderInfo, Constructor, Declaration, Environment, Expr, InductiveDecl,
    InductiveType, Level, LevelVec, Name, TypeChecker,
};

use crate::trustir_anchor::{
    IrCfg, IrOperand, IrTerm, RefinementVerdict, TRUSTIR_EVAL_CFG, TRUSTIR_EVAL_COND,
    TRUSTIR_EVAL_OPERAND, TRUSTIR_OPERAND, refinement_env,
};

// ---------------------------------------------------------------------------
// Canonical Clean names — Trust.TrustIr.* ONLY (never Trust.MirSem.*)
// ---------------------------------------------------------------------------

/// The inter-procedural CALL inductive on the trust-ir side:
/// `Call.mk (callee : Nat)(arg : Operand)(ret : Int) : Call` over the trust-ir
/// `Trust.TrustIr.Operand`. Port of `Trust.MirSem.Call`.
pub const TRUSTIR_CALL: &str = "Trust.TrustIr.Call";
/// `Call.mk : Nat → Operand → Int → Call`.
pub const TRUSTIR_CALL_MK: &str = "Trust.TrustIr.Call.mk";
/// The `Call` recursor (auto-generated by the inductive registration).
pub const TRUSTIR_CALL_REC: &str = "Trust.TrustIr.Call.rec";
/// `callResult : Call → Int` = `Call.rec (λ_.Int) (λ callee arg ret. ret)` — the
/// call site's denotation (the value the separately-verified callee returns).
/// Port of `Trust.MirSem.call_result`.
pub const TRUSTIR_CALL_RESULT: &str = "Trust.TrustIr.callResult";
/// `callCallee : Call → Nat` = `Call.rec (λ_.Nat) (λ callee arg ret. callee)` —
/// the callee-ID projection. Port of `Trust.MirSem.call_callee`.
pub const TRUSTIR_CALL_CALLEE: &str = "Trust.TrustIr.callCallee";
/// The PROVEN contract-transport lemma
/// `∀ (post : Int → Prop)(c : Call), post (callResult c) → post (callResult c)`.
/// READ PRECISELY (same honesty note as the MirSem original): the HYPOTHESIS
/// `post (callResult c)` is the GUARANTEE — the assumption that the callee
/// satisfies its contract, established by SEPARATE verification (the callees-first
/// registry); the conclusion re-states that guarantee AT the call site's
/// denotation. Port of `Trust.MirSem.callRefinesContract`.
pub const TRUSTIR_CALL_REFINES_CONTRACT: &str = "Trust.TrustIr.callRefinesContract";
/// The PER-CALL-SITE instance of [`TRUSTIR_CALL_REFINES_CONTRACT`]: the general
/// transport lemma APPLIED at the concrete `Call.mk <callee-id> <arg> ret` value of
/// a recognized call-return shape. A `Theorem` whose value applies the proven
/// lemma — never a new axiom. Port of `Trust.MirSem.callReturnInstance`.
pub const TRUSTIR_CALL_RETURN_INSTANCE: &str = "Trust.TrustIr.callReturnInstance";

// ---------------------------------------------------------------------------
// Small kernel-term builders (shared de-Bruijn convention with trustir_anchor.rs)
// ---------------------------------------------------------------------------

fn cst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), LevelVec::new())
}

fn int_ty() -> Expr {
    cst("Int")
}

fn operand_ty() -> Expr {
    cst(TRUSTIR_OPERAND)
}

// ---------------------------------------------------------------------------
// Registration — the Call inductive + projections + the proven transport lemma.
// Byte-for-byte ports of `mirsem::register_call_inductive` /
// `register_call_result` / `register_call_callee` / the `callRefinesContract`
// type/proof builders, with `Trust.MirSem.*` ↦ `Trust.TrustIr.*` and the operand
// type swapped to the trust-ir `Operand`.
// ---------------------------------------------------------------------------

/// Register the CALL inductive `Trust.TrustIr.Call : Type` (one constructor
/// `Call.mk : Nat → Operand → Int → Call`). Idempotent. See [`TRUSTIR_CALL`].
fn register_call_inductive_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_CALL);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // Call.mk : Nat → Operand → Int → Call
    let mk_ctor = Constructor {
        name: Name::from_string(TRUSTIR_CALL_MK),
        type_: Expr::pi(
            bd(),
            cst("Nat"),
            Expr::pi(bd(), operand_ty(), Expr::pi(bd(), int_ty(), cst(TRUSTIR_CALL))),
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
    env.add_inductive(decl).map_err(|e| format!("add_inductive(TrustIr.Call): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.callResult : Call → Int` (idempotent) — the call site's
/// DENOTATION via the `Call` recursor: `Call.rec (λ_.Int) (λ callee arg ret. ret)`.
/// A genuine recursor projection of the (separately-verified) callee return.
fn register_call_result_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_CALL_RESULT);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // @Call.rec.{1} : motive lands in Int : Type ⇒ Sort 1.
    let call_rec =
        Expr::const_(Name::from_string(TRUSTIR_CALL_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst(TRUSTIR_CALL), int_ty());
    // minor : λ (callee:Nat)(arg:Operand)(ret:Int). ret   (ret=0)
    let minor = Expr::lam(
        bd(),
        cst("Nat"),
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), Expr::bvar(0))),
    );
    // λ (c : Call). Call.rec (λ_.Int) minor c
    let body = Expr::apps(call_rec, [motive, minor, Expr::bvar(0)]);
    let val = Expr::lam(bd(), cst(TRUSTIR_CALL), body);
    let ty = Expr::pi(bd(), cst(TRUSTIR_CALL), int_ty());
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(callResult): {e:?}"))?;
    Ok(())
}

/// Register `Trust.TrustIr.callCallee : Call → Nat` (idempotent) — the callee-ID
/// projection via the `Call` recursor: `Call.rec (λ_.Nat) (λ callee arg ret. callee)`.
fn register_call_callee_ir(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(TRUSTIR_CALL_CALLEE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // @Call.rec.{1} : motive lands in Nat : Type ⇒ Sort 1.
    let call_rec =
        Expr::const_(Name::from_string(TRUSTIR_CALL_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst(TRUSTIR_CALL), cst("Nat"));
    // minor : λ (callee:Nat)(arg:Operand)(ret:Int). callee   (callee=2)
    let minor = Expr::lam(
        bd(),
        cst("Nat"),
        Expr::lam(bd(), operand_ty(), Expr::lam(bd(), int_ty(), Expr::bvar(2))),
    );
    let body = Expr::apps(call_rec, [motive, minor, Expr::bvar(0)]);
    let val = Expr::lam(bd(), cst(TRUSTIR_CALL), body);
    let ty = Expr::pi(bd(), cst(TRUSTIR_CALL), cst("Nat"));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(callCallee): {e:?}"))?;
    Ok(())
}

/// The CONTRACT-TRANSPORT lemma TYPE: `∀ (post : Int → Prop)(c : Call),
/// post (callResult c) → post (callResult c)`. `claimed_concl_pred = Some(p)`
/// overrides the CONCLUSION's predicate (fail-closed hook: a wrong postcondition —
/// a different predicate from the assumed one — must NOT prove). Byte-identical to
/// `mirsem::call_contract_type` modulo the constant names.
fn call_contract_type_ir(claimed_concl_pred: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    // inside `∀ post ∀ c`: c=0, post=1.
    // HYPOTHESIS: post (callResult c)
    let res_c = Expr::app(cst(TRUSTIR_CALL_RESULT), Expr::bvar(0));
    let hyp = Expr::app(Expr::bvar(1), res_c);
    // CONCLUSION: <pred> (callResult c)  — under the `hyp →` arrow everything +1.
    let res_c2 = Expr::app(cst(TRUSTIR_CALL_RESULT), Expr::bvar(1));
    // Inside `concl` (codomain of `hyp →`): hyp=0, c=1, post=2.
    let concl_pred = claimed_concl_pred
        .cloned()
        // A claimed predicate is supplied relative to the OUTSIDE (closed, or refs to
        // pre-`post` binders); lift it past `post`, `c`, `hyp` so it is valid here.
        .map(|p| p.lift(3))
        .unwrap_or_else(|| Expr::bvar(2)); // the assumed `post` itself
    let concl = Expr::app(concl_pred, res_c2);
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), cst(TRUSTIR_CALL), arrow))
}

/// The CONTRACT-TRANSPORT lemma PROOF: `λ (post)(c)(h : post (callResult c)). h`
/// — the IDENTITY (A-implies-A). It TRANSPORTS the ASSUMED callee contract to the
/// call site; the caller inherits EXACTLY the callee's postcondition. HONEST: the
/// identity proves nothing about dispatch and discharges no callee body — the
/// guarantee `h` is established elsewhere (modular, separate verification), not by
/// this transport. Byte-identical to `mirsem::call_contract_proof` modulo names.
fn call_contract_proof_ir() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    // inside `λ post λ c`: c=0, post=1.  hyp : post (callResult c).
    let res_c = Expr::app(cst(TRUSTIR_CALL_RESULT), Expr::bvar(0));
    let hyp_ty = Expr::app(Expr::bvar(1), res_c);
    Expr::lam(
        bd(),
        int_to_prop,
        Expr::lam(bd(), cst(TRUSTIR_CALL), Expr::lam(bd(), hyp_ty, Expr::bvar(0))),
    )
}

/// `check_type` a `(type, proof)`, register it as a `Declaration::Theorem`
/// (idempotent on `name`), and AUDIT the axiom residue: registration FAILS unless
/// the decl's axiom closure is ⊆ the 3 foundational axioms (empty residue). The
/// same audited-registration pattern as `trustir_termination.rs`'s
/// `register_checked_theorem_t` (mirrors `mirsem::register_checked_theorem` + the
/// house per-decl `axiom_deps` gate).
fn register_checked_theorem_c(
    env: &mut Environment,
    name_str: &str,
    ty: Expr,
    proof: Expr,
) -> Result<(), String> {
    let name = Name::from_string(name_str);
    if env.get_const(&name).is_none() {
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&proof, &ty).map_err(|e| format!("{name_str} check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: ty,
            value: proof,
        })
        .map_err(|e| format!("add_decl({name_str}): {e:?}"))?;
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => Ok(()),
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            Err(format!("{name_str} axiom residue: {names:?}"))
        }
        None => Err(format!("{name_str} decl not found after registration")),
    }
}

/// Register the whole trust-ir CALL theory: the `Call` inductive, the
/// `callResult`/`callCallee` recursor projections, and the PROVEN
/// `callRefinesContract` transport lemma (audited: EMPTY residue asserted).
fn register_trustir_call(env: &mut Environment) -> Result<(), String> {
    register_call_inductive_ir(env)?;
    register_call_result_ir(env)?;
    register_call_callee_ir(env)?;
    register_checked_theorem_c(
        env,
        TRUSTIR_CALL_REFINES_CONTRACT,
        call_contract_type_ir(None),
        call_contract_proof_ir(),
    )?;
    Ok(())
}

/// Build the env the per-call-site instances live in:
/// `trustir_anchor::trustir_env()` (the whole trust-ir denotation, zero MirSem
/// constants) EXTENDED with this module's CALL theory.
pub fn trustir_call_env() -> Result<Environment, String> {
    let mut env = crate::trustir_anchor::trustir_env()?;
    register_trustir_call(&mut env)?;
    Ok(env)
}

// ---------------------------------------------------------------------------
// The PER-CALL-SITE instance — `callRefinesContract` pinned at the concrete
// `Call.mk <callee-id> <arg>` (quantified only over the callee-supplied return
// value `ret` and the contract `post`). Byte-for-byte port of
// `mirsem::call_return_instance_type/proof` with the trust-ir names and the
// trust-ir `IrOperand` constructor value.
// ---------------------------------------------------------------------------

/// The per-call instance TYPE: `∀ (post : Int → Prop)(ret : Int),
/// post (callResult (Call.mk <id> <arg> ret)) → <pred> (callResult (Call.mk <id>
/// <arg> ret))` where `<pred>` defaults to the assumed `post` itself.
/// `claimed_concl_pred = Some(p)` overrides the conclusion's predicate — the
/// fail-closed hook (a WRONG postcondition must NOT prove).
fn call_return_instance_type_ir(
    callee_id: u64,
    arg: &IrOperand,
    claimed_concl_pred: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    // `arg.to_operand_expr()` is CLOSED (constructor literals only) — no lifting.
    let call_at = |ret: Expr| {
        Expr::apps(cst(TRUSTIR_CALL_MK), [Expr::nat_lit(callee_id), arg.to_operand_expr(), ret])
    };
    // inside `∀ post ∀ ret`: ret=0, post=1. HYPOTHESIS: post (callResult C[ret]).
    let hyp = Expr::app(Expr::bvar(1), Expr::app(cst(TRUSTIR_CALL_RESULT), call_at(Expr::bvar(0))));
    // CONCLUSION (under the `hyp →` arrow, everything +1): <pred> (callResult C[ret]).
    let concl_pred = claimed_concl_pred
        .cloned()
        // A claimed predicate is supplied CLOSED (or relative to pre-`post`
        // binders); lift it past `post`, `ret`, `hyp`.
        .map(|p| p.lift(3))
        .unwrap_or_else(|| Expr::bvar(2)); // the assumed `post` itself
    let concl = Expr::app(concl_pred, Expr::app(cst(TRUSTIR_CALL_RESULT), call_at(Expr::bvar(1))));
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), int_ty(), arrow))
}

/// The per-call instance PROOF: `λ (post)(ret)(h). callRefinesContract post
/// (Call.mk <id> <arg> ret) h` — a plain APPLICATION of the registered proven
/// transport lemma at the concrete call value. Inherits the lemma's honesty: it
/// transports the ASSUMED callee guarantee to the call site and discharges no
/// callee body (the callee is separately verified — the registry's job).
fn call_return_instance_proof_ir(callee_id: u64, arg: &IrOperand) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(cst(TRUSTIR_CALL_MK), [Expr::nat_lit(callee_id), arg.to_operand_expr(), ret])
    };
    // hyp type inside `λ post λ ret`: ret=0, post=1.
    let hyp_ty =
        Expr::app(Expr::bvar(1), Expr::app(cst(TRUSTIR_CALL_RESULT), call_at(Expr::bvar(0))));
    // body inside `λ post λ ret λ h`: h=0, ret=1, post=2.
    let body = Expr::apps(
        cst(TRUSTIR_CALL_REFINES_CONTRACT),
        [Expr::bvar(2), call_at(Expr::bvar(1)), Expr::bvar(0)],
    );
    Expr::lam(bd(), int_to_prop, Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, body)))
}

/// Check the per-call `callRefinesContract` INSTANCE against the real clean-kernel
/// on the TRUST-IR env: instantiate at the concrete `Call.mk <callee-id> <arg>`,
/// `check_type` the applied proof, register `Trust.TrustIr.callReturnInstance`,
/// and audit its axiom closure — `ProvenModulo3` IFF the residue is EMPTY.
/// Fail-closed on every kernel rejection.
#[must_use]
pub fn check_call_return_instance(callee_id: u64, arg: &IrOperand) -> RefinementVerdict {
    check_call_return_instance_inner(callee_id, arg, None)
}

/// Inner check with the fail-closed hook: `claimed_concl_pred = Some(p)` overrides
/// the instance conclusion's postcondition predicate (a WRONG postcondition — a
/// different predicate from the assumed one — must NOT prove).
fn check_call_return_instance_inner(
    callee_id: u64,
    arg: &IrOperand,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match trustir_call_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let inst_ty = call_return_instance_type_ir(callee_id, arg, claimed_concl_pred);
    let inst_proof = call_return_instance_proof_ir(callee_id, arg);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "TrustIr.callReturnInstance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string(TRUSTIR_CALL_RETURN_INSTANCE);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add TrustIr.callReturnInstance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected(
            "TrustIr.callReturnInstance decl not found".to_string(),
        ),
    }
}

// ---------------------------------------------------------------------------
// Trust: CALL-THEN-PUREOP — the trust-ir PORT of `mirsem::call_then_pureop_
// instance_type`/`_proof`/`_verdict` + its small helpers (byte-for-byte,
// `Trust.MirSem.*` ↦ `Trust.TrustIr.*`, the operand type swapped to trust-ir's
// `Operand` — the SAME port discipline as `check_call_return_instance` above).
// Closes the SAME "Call-then-Compare" named residue on the trust-ir side: reuses
// the SAME PROVEN `callRefinesContract` transport lemma, applied at a WRAPPED
// predicate — never a new axiom.
// ---------------------------------------------------------------------------

/// Trust: CALL-THEN-PUREOP — the PER-CALL-SITE instance of
/// [`TRUSTIR_CALL_REFINES_CONTRACT`] APPLIED at a WRAPPED predicate. Port of
/// `mirsem::MIRSEM_CALL_THEN_PUREOP_INSTANCE`.
pub const TRUSTIR_CALL_THEN_PUREOP_INSTANCE: &str = "Trust.TrustIr.callThenPureOpInstance";

/// The `Int.<op> a b` head for a trust-ir arithmetic `BinOp` — BYTE-IDENTICAL to
/// `trustir_anchor::int_binop_expr` (module-private there; duplicated here per this
/// file's own "byte-for-byte port" convention).
fn int_binop_expr(op: crate::trustir_anchor::TrustIrBinOp, a: Expr, b: Expr) -> Expr {
    use crate::trustir_anchor::TrustIrBinOp as B;
    let head = match op {
        B::Add => "Int.add",
        B::Sub => "Int.sub",
        B::Mul => "Int.mul",
        B::SDiv => "Int.div",
        // Trust: witness-tier Rem arm.
        B::SRem => "Int.mod",
        // Trust: M6 rung 6, SHR→TRUST-IR ANCHOR — BYTE-IDENTICAL to
        // `trustir_anchor::int_binop_expr`'s `LShr` arm.
        B::LShr => "Int.shiftRight",
        // Trust: M6 rung 9, ANCHOR BitAnd — BYTE-IDENTICAL to
        // `trustir_anchor::int_binop_expr`'s `And` arm.
        B::And => "Int.land",
    };
    Expr::apps(cst(head), [a, b])
}

/// The closed `Int` literal — BYTE-IDENTICAL to `trustir_anchor::int_lit`.
fn int_lit(n: i128) -> Expr {
    // Trust: EXACT ENCODING (2026-07-24) — see `clean_ground::int_lit_to_expr`. The
    // former `as u64` was `n mod 2^64`, a truncation that made the map non-injective
    // and caused a demonstrated LIVE FALSE ACCEPT. `nat_lit_u128` is a drop-in:
    // `BigNat::from_limbs` normalizes a trailing zero limb back to `Small`, so every
    // `k <= u64::MAX` encodes byte-identically and only the previously-truncated
    // literals change. Keeping this in lockstep is what the byte-identity claim above
    // asserts — it is now TRUE again for the full `i128` range.
    if n >= 0 {
        Expr::app(cst("Int.ofNat"), Expr::nat_lit_u128(n.unsigned_abs()))
    } else {
        Expr::app(cst("Int.negSucc"), Expr::nat_lit_u128(n.unsigned_abs() - 1))
    }
}

/// The Bool-valued term for a comparison `TrustIrCmpOp` applied to two ALREADY-BUILT
/// Int exprs — the trust-ir port of `mirsem::cmp_bool_expr` (byte-for-byte, the SAME
/// prelude primitives: `decide`/`Int.lt`/`Int.le`/`Int.beq`/`Bool.not`/`Int.decLt`/
/// `Int.decLe`).
fn cmp_bool_expr(op: crate::trustir_anchor::TrustIrCmpOp, a: Expr, b: Expr) -> Expr {
    use crate::trustir_anchor::TrustIrCmpOp as C;
    let decide_lt = |x: Expr, y: Expr| {
        Expr::apps(
            cst("decide"),
            [
                Expr::apps(cst("Int.lt"), [x.clone(), y.clone()]),
                Expr::apps(cst("Int.decLt"), [x, y]),
            ],
        )
    };
    let decide_le = |x: Expr, y: Expr| {
        Expr::apps(
            cst("decide"),
            [
                Expr::apps(cst("Int.le"), [x.clone(), y.clone()]),
                Expr::apps(cst("Int.decLe"), [x, y]),
            ],
        )
    };
    match op {
        C::Lt => decide_lt(a, b),
        C::Le => decide_le(a, b),
        C::Eq => Expr::apps(cst("Int.beq"), [a, b]),
        C::Ne => Expr::app(cst("Bool.not"), Expr::apps(cst("Int.beq"), [a, b])),
        C::Gt => decide_lt(b, a),
        C::Ge => decide_le(b, a),
    }
}

/// Encode a Bool-valued expr as 0/1 on the `Int` carrier — the trust-ir port of
/// `mirsem::bool_as_int` (byte-for-byte, the SAME `Bool.rec` idiom).
fn bool_as_int(b: Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Bool"), int_ty());
    Expr::apps(bool_rec, [motive, int_lit(0), int_lit(1), b])
}

/// The pure op a CALL-THEN-PUREOP shape applies, on the trust-ir side — port of
/// `mirsem::CallThenOp`.
#[derive(Debug, Clone, Copy)]
pub enum TrustIrCallThenOp {
    /// An arithmetic op.
    Bin(crate::trustir_anchor::TrustIrBinOp),
    /// A comparison op.
    Cmp(crate::trustir_anchor::TrustIrCmpOp),
}

/// Port of `mirsem::call_then_pureop_instance_type` (byte-for-byte, TRUSTIR names).
fn call_then_pureop_instance_type_ir(
    callee_id: u64,
    call_arg: &IrOperand,
    wrap: &dyn Fn(Expr) -> Expr,
    claimed_concl_pred: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id), call_arg.to_operand_expr(), ret],
        )
    };
    // inside `∀ post ∀ ret`: ret=0, post=1. HYPOTHESIS: post (wrap (callResult C[ret])).
    let hyp =
        Expr::app(Expr::bvar(1), wrap(Expr::app(cst(TRUSTIR_CALL_RESULT), call_at(Expr::bvar(0)))));
    // CONCLUSION (under the `hyp →` arrow, everything +1): <pred> (wrap (callResult C[ret])).
    let concl_pred =
        claimed_concl_pred.cloned().map(|p| p.lift(3)).unwrap_or_else(|| Expr::bvar(2));
    let concl =
        Expr::app(concl_pred, wrap(Expr::app(cst(TRUSTIR_CALL_RESULT), call_at(Expr::bvar(1)))));
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), int_ty(), arrow))
}

/// Port of `mirsem::call_then_pureop_instance_proof` (byte-for-byte, TRUSTIR names).
fn call_then_pureop_instance_proof_ir(
    callee_id: u64,
    call_arg: &IrOperand,
    wrap: &dyn Fn(Expr) -> Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id), call_arg.to_operand_expr(), ret],
        )
    };
    // hyp type inside `λ post λ ret`: ret=0, post=1.
    let hyp_ty =
        Expr::app(Expr::bvar(1), wrap(Expr::app(cst(TRUSTIR_CALL_RESULT), call_at(Expr::bvar(0)))));
    // body inside `λ post λ ret λ h`: h=0, ret=1, post=2. `λ x. post (wrap x)`
    // shifts `post` (was bvar(2)) to bvar(3) inside the new binder; `x` = bvar(0).
    let wrapped_post = Expr::lam(bd(), int_ty(), Expr::app(Expr::bvar(3), wrap(Expr::bvar(0))));
    let body = Expr::apps(
        cst(TRUSTIR_CALL_REFINES_CONTRACT),
        [wrapped_post, call_at(Expr::bvar(1)), Expr::bvar(0)],
    );
    Expr::lam(bd(), int_to_prop, Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, body)))
}

/// Trust: PARAM-OPERAND generalization — the non-call operand's kernel
/// representation on the trust-ir lane: either a CLOSED CONSTANT (the ORIGINAL,
/// byte-identical path) or a function PARAMETER (the NEW path — the concrete
/// param index is irrelevant to the kernel instance, which only needs an
/// arbitrary ∀-bound `Int` standing in for "whatever value this operand denotes";
/// see `mirsem::call_then_pureop_instance_type_param`'s doc, ported here).
#[derive(Debug, Clone, Copy)]
pub enum TrustIrOtherOperand {
    /// A closed constant value.
    Const(i128),
    /// A function parameter (or its move-out form) — threaded as an extra
    /// ∀-bound instance variable, never a fresh axiom.
    Param,
}

/// Port of `mirsem::call_then_pureop_instance_type_param` (byte-for-byte, TRUSTIR
/// names) — the per-call CALL-THEN-PUREOP instance TYPE for the PARAM-operand
/// path: ONE extra ∀-bound `Int` binder (`paramVal`) inserted between `post` and
/// `ret`, threaded into `wrap` in place of a closed literal.
fn call_then_pureop_instance_type_ir_param(
    callee_id: u64,
    call_arg: &IrOperand,
    wrap: &dyn Fn(Expr, Expr) -> Expr,
    claimed_concl_pred: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id), call_arg.to_operand_expr(), ret],
        )
    };
    // inside `∀ post ∀ paramVal ∀ ret`: ret=0, paramVal=1, post=2.
    let hyp = Expr::app(
        Expr::bvar(2),
        wrap(Expr::bvar(1), Expr::app(cst(TRUSTIR_CALL_RESULT), call_at(Expr::bvar(0)))),
    );
    // CONCLUSION (under the `hyp →` arrow, everything +1): ret=1, paramVal=2, post=3.
    let concl_pred =
        claimed_concl_pred.cloned().map(|p| p.lift(4)).unwrap_or_else(|| Expr::bvar(3));
    let concl = Expr::app(
        concl_pred,
        wrap(Expr::bvar(2), Expr::app(cst(TRUSTIR_CALL_RESULT), call_at(Expr::bvar(1)))),
    );
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), arrow)))
}

/// Port of `mirsem::call_then_pureop_instance_proof_param` (byte-for-byte,
/// TRUSTIR names) — the PARAM-operand path's instance PROOF.
fn call_then_pureop_instance_proof_ir_param(
    callee_id: u64,
    call_arg: &IrOperand,
    wrap: &dyn Fn(Expr, Expr) -> Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id), call_arg.to_operand_expr(), ret],
        )
    };
    // hyp type inside `λ post λ paramVal λ ret`: ret=0, paramVal=1, post=2.
    let hyp_ty = Expr::app(
        Expr::bvar(2),
        wrap(Expr::bvar(1), Expr::app(cst(TRUSTIR_CALL_RESULT), call_at(Expr::bvar(0)))),
    );
    // body inside `λ post λ paramVal λ ret λ h`: h=0, ret=1, paramVal=2, post=3.
    // `λ x. post (wrap paramVal x)` shifts `post` (bvar(3)→bvar(4)) and `paramVal`
    // (bvar(2)→bvar(3)) inside the new binder; `x` = bvar(0).
    let wrapped_post =
        Expr::lam(bd(), int_ty(), Expr::app(Expr::bvar(4), wrap(Expr::bvar(3), Expr::bvar(0))));
    let body = Expr::apps(
        cst(TRUSTIR_CALL_REFINES_CONTRACT),
        [wrapped_post, call_at(Expr::bvar(1)), Expr::bvar(0)],
    );
    Expr::lam(
        bd(),
        int_to_prop,
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, body))),
    )
}

/// Check the per-call CALL-THEN-PUREOP instance against the real clean-kernel on
/// the TRUST-IR env. `other` is the non-call operand's kernel representation —
/// Trust: PARAM-OPERAND generalization — either a CLOSED CONSTANT (the original
/// path) or a function PARAMETER ([`TrustIrOtherOperand::Param`], threaded as an
/// extra ∀-bound instance variable — the SAME generalization
/// `mirsem::call_then_pureop_instance_verdict` carries on the MirSem lane).
/// Fail-closed on every kernel rejection.
#[must_use]
pub fn check_call_then_pureop_instance(
    callee_id: u64,
    call_arg: &IrOperand,
    op: TrustIrCallThenOp,
    other: TrustIrOtherOperand,
    call_is_lhs: bool,
) -> RefinementVerdict {
    check_call_then_pureop_instance_inner(callee_id, call_arg, op, other, call_is_lhs, None)
}

/// Inner check with the fail-closed hook: `claimed_concl_pred = Some(p)` overrides
/// the instance conclusion's postcondition predicate (a WRONG postcondition must
/// NOT prove).
fn check_call_then_pureop_instance_inner(
    callee_id: u64,
    call_arg: &IrOperand,
    op: TrustIrCallThenOp,
    other: TrustIrOtherOperand,
    call_is_lhs: bool,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match trustir_call_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let (inst_ty, inst_proof) = match other {
        TrustIrOtherOperand::Const(other_const) => {
            let wrap: Box<dyn Fn(Expr) -> Expr> = match op {
                TrustIrCallThenOp::Bin(o) => Box::new(move |x: Expr| {
                    let lit = int_lit(other_const);
                    if call_is_lhs { int_binop_expr(o, x, lit) } else { int_binop_expr(o, lit, x) }
                }),
                TrustIrCallThenOp::Cmp(o) => Box::new(move |x: Expr| {
                    let lit = int_lit(other_const);
                    let (a, b) = if call_is_lhs { (x, lit) } else { (lit, x) };
                    bool_as_int(cmp_bool_expr(o, a, b))
                }),
            };
            (
                call_then_pureop_instance_type_ir(callee_id, call_arg, &wrap, claimed_concl_pred),
                call_then_pureop_instance_proof_ir(callee_id, call_arg, &wrap),
            )
        }
        TrustIrOtherOperand::Param => {
            let wrap: Box<dyn Fn(Expr, Expr) -> Expr> = match op {
                TrustIrCallThenOp::Bin(o) => Box::new(move |p: Expr, x: Expr| {
                    if call_is_lhs { int_binop_expr(o, x, p) } else { int_binop_expr(o, p, x) }
                }),
                TrustIrCallThenOp::Cmp(o) => Box::new(move |p: Expr, x: Expr| {
                    let (a, b) = if call_is_lhs { (x, p) } else { (p, x) };
                    bool_as_int(cmp_bool_expr(o, a, b))
                }),
            };
            (
                call_then_pureop_instance_type_ir_param(
                    callee_id,
                    call_arg,
                    &wrap,
                    claimed_concl_pred,
                ),
                call_then_pureop_instance_proof_ir_param(callee_id, call_arg, &wrap),
            )
        }
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "TrustIr.callThenPureOpInstance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string(TRUSTIR_CALL_THEN_PUREOP_INSTANCE);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!(
            "add TrustIr.callThenPureOpInstance: {e:?}"
        ));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected(
            "TrustIr.callThenPureOpInstance decl not found".to_string(),
        ),
    }
}

// ---------------------------------------------------------------------------
// Trust: CALL-OP-CALL — the trust-ir PORT of `mirsem::call_op_call_instance_
// type`/`_proof`/`_verdict` (byte-for-byte, `Trust.MirSem.*` ↦ `Trust.TrustIr.*`,
// the operand type swapped to trust-ir's `Operand` — the SAME port discipline as
// `check_call_then_pureop_instance` above). Closes the SAME residue on the
// trust-ir side: reuses the SAME PROVEN `callRefinesContract` transport lemma,
// applied TWICE (once per call), nested — never a new axiom.
// ---------------------------------------------------------------------------

/// Trust: CALL-OP-CALL — the PER-CALL-PAIR instance of
/// [`TRUSTIR_CALL_REFINES_CONTRACT`], applied TWICE (nested) at a WRAPPED
/// predicate over BOTH calls' results. Port of `mirsem::MIRSEM_CALL_OP_CALL_
/// INSTANCE`.
pub const TRUSTIR_CALL_OP_CALL_INSTANCE: &str = "Trust.TrustIr.callOpCallInstance";

/// Port of `mirsem::call_op_call_instance_type` (byte-for-byte, TRUSTIR names).
fn call_op_call_instance_type_ir(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
    wrap: &dyn Fn(Expr, Expr) -> Expr,
    claimed_concl_pred: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at_a = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_a), call_arg_a.to_operand_expr(), ret],
        )
    };
    let call_at_b = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_b), call_arg_b.to_operand_expr(), ret],
        )
    };
    let cr_a = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_a(ret));
    let cr_b = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_b(ret));
    // inside `∀ post ∀ retA ∀ retB`: retB=0, retA=1, post=2.
    let hyp = Expr::app(Expr::bvar(2), wrap(cr_a(Expr::bvar(1)), cr_b(Expr::bvar(0))));
    // CONCLUSION (under the `hyp →` arrow, everything +1): retB=1, retA=2, post=3.
    let concl_pred =
        claimed_concl_pred.cloned().map(|p| p.lift(4)).unwrap_or_else(|| Expr::bvar(3));
    let concl = Expr::app(concl_pred, wrap(cr_a(Expr::bvar(2)), cr_b(Expr::bvar(1))));
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), arrow)))
}

/// Port of `mirsem::call_op_call_instance_proof` (byte-for-byte, TRUSTIR names).
fn call_op_call_instance_proof_ir(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
    wrap: &dyn Fn(Expr, Expr) -> Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at_a = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_a), call_arg_a.to_operand_expr(), ret],
        )
    };
    let call_at_b = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_b), call_arg_b.to_operand_expr(), ret],
        )
    };
    let cr_a = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_a(ret));
    let cr_b = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_b(ret));

    // hyp type inside `λ post λ retA λ retB`: retB=0, retA=1, post=2.
    let hyp_ty = Expr::app(Expr::bvar(2), wrap(cr_a(Expr::bvar(1)), cr_b(Expr::bvar(0))));

    // Body inside `λ post λ retA λ retB λ h`: h=0, retB=1, retA=2, post=3.
    let post_b = Expr::lam(
        bd(),
        int_ty(),
        Expr::app(Expr::bvar(4), wrap(cr_a(Expr::bvar(3)), Expr::bvar(0))),
    );
    let inner_app = Expr::apps(
        cst(TRUSTIR_CALL_REFINES_CONTRACT),
        [post_b, call_at_b(Expr::bvar(1)), Expr::bvar(0)],
    );
    let post_a = Expr::lam(
        bd(),
        int_ty(),
        Expr::app(Expr::bvar(4), wrap(Expr::bvar(0), cr_b(Expr::bvar(2)))),
    );
    let body = Expr::apps(
        cst(TRUSTIR_CALL_REFINES_CONTRACT),
        [post_a, call_at_a(Expr::bvar(2)), inner_app],
    );

    Expr::lam(
        bd(),
        int_to_prop,
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, body))),
    )
}

/// Check the per-call-pair CALL-OP-CALL instance against the real clean-kernel
/// on the TRUST-IR env. `op` builds `wrap(a, b) = op(a, b)` (or, for a
/// comparison, `bool_as_int(cmp(a, b))`) — REUSING the SAME `int_binop_expr`/
/// `cmp_bool_expr`/`bool_as_int` fragments [`check_call_then_pureop_instance`]
/// already uses. No scope gate is needed (unlike the CALL-THEN-PUREOP port's
/// param-vs-const split): BOTH operands are ALWAYS call results by
/// construction. Fail-closed on every kernel rejection.
#[must_use]
pub fn check_call_op_call_instance(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
    op: TrustIrCallThenOp,
) -> RefinementVerdict {
    check_call_op_call_instance_inner(callee_id_a, call_arg_a, callee_id_b, call_arg_b, op, None)
}

/// Inner check with the fail-closed hook: `claimed_concl_pred = Some(p)`
/// overrides the instance conclusion's postcondition predicate (a WRONG
/// postcondition must NOT prove).
fn check_call_op_call_instance_inner(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
    op: TrustIrCallThenOp,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match trustir_call_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let wrap: Box<dyn Fn(Expr, Expr) -> Expr> = match op {
        TrustIrCallThenOp::Bin(o) => Box::new(move |a: Expr, b: Expr| int_binop_expr(o, a, b)),
        TrustIrCallThenOp::Cmp(o) => {
            Box::new(move |a: Expr, b: Expr| bool_as_int(cmp_bool_expr(o, a, b)))
        }
    };
    let inst_ty = call_op_call_instance_type_ir(
        callee_id_a,
        call_arg_a,
        callee_id_b,
        call_arg_b,
        &wrap,
        claimed_concl_pred,
    );
    let inst_proof =
        call_op_call_instance_proof_ir(callee_id_a, call_arg_a, callee_id_b, call_arg_b, &wrap);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "TrustIr.callOpCallInstance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string(TRUSTIR_CALL_OP_CALL_INSTANCE);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add TrustIr.callOpCallInstance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected(
            "TrustIr.callOpCallInstance decl not found".to_string(),
        ),
    }
}

// ---------------------------------------------------------------------------
// Trust: M6 rung 8 — CALL-OR-CALL (short-circuit `||` of TWO CALLS). The
// trust-ir kernel witness for [`crate::mirsem::sem_call_or_call_of_mir`]'s
// recognized shape (`callee_a(..) || callee_b(..)`).
//
// STRUCTURE: byte-for-byte the SAME shape as CALL-OP-CALL above (the SAME
// PROVEN `callRefinesContract` transport lemma, applied TWICE / nested, at a
// WRAPPED predicate over BOTH calls' results) — but with the wrap FIXED to the
// short-circuit `||` value composition instead of a generic arithmetic/compare
// op: `wrap(a, b) = if a ≠ 0 then 1 else b` (`call_or_call_wrap`, built from
// the SAME `Bool.rec`/`cmp_bool_expr` idiom `check_call_op_call_instance`'s
// `Cmp` arm already uses via `bool_as_int`/`cmp_bool_expr`).
//
// SHORT-CIRCUIT HONESTY (read precisely, do not over-claim): the kernel
// theorem below is PARAMETRIC over arbitrary `retA`/`retB` (it never assumes a
// concrete call outcome) — exactly like every other instance in this file. It
// therefore proves a VALUE-COMPOSITION fact ("whatever `postA`/wrap-predicate
// you already established about `wrap(callResult callA, callResult callB)`
// transports to the call site"), NOT a CONTROL-FLOW fact ("`callee_b` is not
// invoked when `callee_a` is true") — this tier has no `Term`/`Cond`/`evalCfg`
// counterpart able to state the latter (the trust-ir anchor's `Cond` is a
// single-comparison `Cmp`, and `IrTerm::CallReturn` is a TERMINAL return; see
// the mission's own residue note). The SHORT-CIRCUIT FAITHFULNESS claim this
// tier actually earns rests ENTIRELY on the Rust-side recognizer
// (`sem_call_or_call_of_mir`): it admits `callee_b` ONLY as the MIR switch's
// own false-arm terminator (never as a straight-line-preceding call — that
// shape is `sem_call_op_call_of_mir`'s, which structurally cannot recognize a
// branching body), so a caller of this tier NEVER claims `callee_b`
// unconditionally evaluates. This kernel witness is the value half of that
// pairing; declining rather than mis-denoting is the Rust-side recognizer's
// job, not this proof's.
// ---------------------------------------------------------------------------

/// Port-parallel to [`TRUSTIR_CALL_OP_CALL_INSTANCE`], fixed to the `||` wrap.
pub const TRUSTIR_CALL_OR_CALL_INSTANCE: &str = "Trust.TrustIr.callOrCallInstance";

/// The short-circuit `||` VALUE composition: `Bool.rec (λ_.Int) b (1:Int)
/// (decide (a ≠ 0))` — when `a ≠ 0` (callee_a's Bool-as-Int result is truthy)
/// the composed value is the closed literal `1`; when `a = 0` the composed
/// value is `b` (callee_b's result) UNCHANGED, never wrapped/forced further.
/// `decide (a ≠ 0)` is the SAME `Bool.not (Int.beq a 0)` decision procedure
/// [`cmp_bool_expr`]'s `Ne` arm builds — reused directly, not re-derived.
fn call_or_call_wrap(a: Expr, b: Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Bool"), int_ty());
    let discr = cmp_bool_expr(crate::trustir_anchor::TrustIrCmpOp::Ne, a, int_lit(0));
    Expr::apps(bool_rec, [motive, b, int_lit(1), discr])
}

/// Port-parallel to `call_op_call_instance_type_ir`, `wrap` fixed to
/// [`call_or_call_wrap`] (no generic `op` parameter — CALL-OR-CALL is exactly
/// one composition).
fn call_or_call_instance_type_ir(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
    claimed_concl_pred: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at_a = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_a), call_arg_a.to_operand_expr(), ret],
        )
    };
    let call_at_b = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_b), call_arg_b.to_operand_expr(), ret],
        )
    };
    let cr_a = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_a(ret));
    let cr_b = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_b(ret));
    // inside `∀ post ∀ retA ∀ retB`: retB=0, retA=1, post=2.
    let hyp = Expr::app(Expr::bvar(2), call_or_call_wrap(cr_a(Expr::bvar(1)), cr_b(Expr::bvar(0))));
    // CONCLUSION (under the `hyp →` arrow, everything +1): retB=1, retA=2, post=3.
    let concl_pred =
        claimed_concl_pred.cloned().map(|p| p.lift(4)).unwrap_or_else(|| Expr::bvar(3));
    let concl = Expr::app(concl_pred, call_or_call_wrap(cr_a(Expr::bvar(2)), cr_b(Expr::bvar(1))));
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(bd(), int_to_prop, Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), arrow)))
}

/// Port-parallel to `call_op_call_instance_proof_ir`, `wrap` fixed to
/// [`call_or_call_wrap`].
fn call_or_call_instance_proof_ir(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at_a = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_a), call_arg_a.to_operand_expr(), ret],
        )
    };
    let call_at_b = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_b), call_arg_b.to_operand_expr(), ret],
        )
    };
    let cr_a = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_a(ret));
    let cr_b = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_b(ret));

    // hyp type inside `λ post λ retA λ retB`: retB=0, retA=1, post=2.
    let hyp_ty =
        Expr::app(Expr::bvar(2), call_or_call_wrap(cr_a(Expr::bvar(1)), cr_b(Expr::bvar(0))));

    // Body inside `λ post λ retA λ retB λ h`: h=0, retB=1, retA=2, post=3.
    let post_b = Expr::lam(
        bd(),
        int_ty(),
        Expr::app(Expr::bvar(4), call_or_call_wrap(cr_a(Expr::bvar(3)), Expr::bvar(0))),
    );
    let inner_app = Expr::apps(
        cst(TRUSTIR_CALL_REFINES_CONTRACT),
        [post_b, call_at_b(Expr::bvar(1)), Expr::bvar(0)],
    );
    let post_a = Expr::lam(
        bd(),
        int_ty(),
        Expr::app(Expr::bvar(4), call_or_call_wrap(Expr::bvar(0), cr_b(Expr::bvar(2)))),
    );
    let body = Expr::apps(
        cst(TRUSTIR_CALL_REFINES_CONTRACT),
        [post_a, call_at_a(Expr::bvar(2)), inner_app],
    );

    Expr::lam(
        bd(),
        int_to_prop,
        Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, body))),
    )
}

/// Check the per-call-pair CALL-OR-CALL instance against the real clean-kernel
/// on the TRUST-IR env. Fail-closed on every kernel rejection.
#[must_use]
pub fn check_call_or_call_instance(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
) -> RefinementVerdict {
    check_call_or_call_instance_inner(callee_id_a, call_arg_a, callee_id_b, call_arg_b, None)
}

/// Inner check with the fail-closed hook: `claimed_concl_pred = Some(p)`
/// overrides the instance conclusion's postcondition predicate (a WRONG
/// postcondition must NOT prove).
fn check_call_or_call_instance_inner(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match trustir_call_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let inst_ty = call_or_call_instance_type_ir(
        callee_id_a,
        call_arg_a,
        callee_id_b,
        call_arg_b,
        claimed_concl_pred,
    );
    let inst_proof =
        call_or_call_instance_proof_ir(callee_id_a, call_arg_a, callee_id_b, call_arg_b);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "TrustIr.callOrCallInstance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string(TRUSTIR_CALL_OR_CALL_INSTANCE);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add TrustIr.callOrCallInstance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected(
            "TrustIr.callOrCallInstance decl not found".to_string(),
        ),
    }
}

// ---------------------------------------------------------------------------
// Trust: M6 rung 9 — CALL-OR-GUARDED-COMPARE (the RICHER-|| ARM). Generalizes
// CALL-OR-CALL's short-circuit `||` composition from a BARE second call to a
// SMALL GUARDED SUB-COMPUTATION: `callee_a(..) || (fieldVal `cmp` callee_b(..))`
// — `Abstractor::should_descend`'s own real shape (`has_fvar_quick(e) ||
// self.depth < e.loose_bvar_range()`).
//
// STRUCTURE: the SAME nested `callRefinesContract` composition CALL-OR-CALL uses
// (applied TWICE, once per call), but with a THIRD ∀-bound `Int` parameter
// (`fieldVal`) threaded through the wrap — mirroring CALL-THEN-PUREOP's OWN
// PARAM-operand generalization (`call_then_pureop_instance_type_ir_param`'s
// `paramVal` insertion). The composed wrap is:
//
//   wrap(fieldVal, a, b) = if a ≠ 0 then 1 else bool_as_int(cmp_bool_expr(op,
//                                                              fieldVal, b))
//                                    (or `cmp_bool_expr(op, b, fieldVal)` when
//                                    the field is the compare's RHS)
//
// — the SAME `Bool.rec`/`cmp_bool_expr`/`bool_as_int` idioms [`call_or_call_wrap`]
// and [`check_call_then_pureop_instance`]'s `Cmp` arm already build, composed
// rather than re-derived.
//
// SHORT-CIRCUIT HONESTY (the SAME boundary [`TRUSTIR_CALL_OR_CALL_INSTANCE`]'s doc
// states, read precisely here too): this kernel theorem is PARAMETRIC over
// arbitrary `retA`/`retB`/`fieldVal` — it proves a VALUE-COMPOSITION fact, NOT a
// CONTROL-FLOW fact. The SHORT-CIRCUIT FAITHFULNESS claim rests ENTIRELY on the
// Rust-side recognizer ([`crate::mirsem::sem_call_or_guarded_compare_of_mir`]):
// it admits `callee_b` (and the field read) ONLY as the switch's OWN false-arm
// sub-CFG (the field-read statement, then the call, then the compare, all inside
// the false arm's own blocks) — never as an unconditionally-evaluated
// computation. This kernel witness is the value half of that pairing.
// ---------------------------------------------------------------------------

/// Port-parallel to [`TRUSTIR_CALL_OR_CALL_INSTANCE`], generalized with the extra
/// `fieldVal` ∀-binder and the guarded-compare wrap.
pub const TRUSTIR_CALL_OR_GUARDED_COMPARE_INSTANCE: &str =
    "Trust.TrustIr.callOrGuardedCompareInstance";

/// The short-circuit `||`-of-a-guarded-compare VALUE composition:
/// `Bool.rec (λ_.Int) (bool_as_int (cmp_bool_expr op x y)) 1 (decide (a ≠ 0))`
/// where `(x, y) = (fieldVal, b)` if `field_is_lhs` else `(b, fieldVal)` — when
/// `a ≠ 0` (callee_a's Bool-as-Int result is truthy) the composed value is the
/// closed literal `1`; when `a = 0` the composed value is the comparison of
/// `fieldVal` against `b` (callee_b's result), in the recognized operand order.
fn call_or_guarded_compare_wrap(
    op: crate::trustir_anchor::TrustIrCmpOp,
    field_is_lhs: bool,
    field_val: Expr,
    a: Expr,
    b: Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Bool"), int_ty());
    let (x, y) = if field_is_lhs { (field_val, b) } else { (b, field_val) };
    let else_val = bool_as_int(cmp_bool_expr(op, x, y));
    let discr = cmp_bool_expr(crate::trustir_anchor::TrustIrCmpOp::Ne, a, int_lit(0));
    Expr::apps(bool_rec, [motive, else_val, int_lit(1), discr])
}

/// Port-parallel to `call_or_call_instance_type_ir`, generalized with the extra
/// `∀ fieldVal : Int` binder (inserted between `post` and `retA`, mirroring
/// `call_then_pureop_instance_type_ir_param`'s `paramVal` insertion) and `wrap`
/// fixed to [`call_or_guarded_compare_wrap`].
fn call_or_guarded_compare_instance_type_ir(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
    op: crate::trustir_anchor::TrustIrCmpOp,
    field_is_lhs: bool,
    claimed_concl_pred: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at_a = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_a), call_arg_a.to_operand_expr(), ret],
        )
    };
    let call_at_b = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_b), call_arg_b.to_operand_expr(), ret],
        )
    };
    let cr_a = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_a(ret));
    let cr_b = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_b(ret));
    let wrap =
        |fv: Expr, a: Expr, b: Expr| call_or_guarded_compare_wrap(op, field_is_lhs, fv, a, b);
    // inside `∀ post ∀ fieldVal ∀ retA ∀ retB`: retB=0, retA=1, fieldVal=2, post=3.
    let hyp =
        Expr::app(Expr::bvar(3), wrap(Expr::bvar(2), cr_a(Expr::bvar(1)), cr_b(Expr::bvar(0))));
    // CONCLUSION (under the `hyp →` arrow, everything +1): retB=1, retA=2, fieldVal=3, post=4.
    let concl_pred =
        claimed_concl_pred.cloned().map(|p| p.lift(5)).unwrap_or_else(|| Expr::bvar(4));
    let concl =
        Expr::app(concl_pred, wrap(Expr::bvar(3), cr_a(Expr::bvar(2)), cr_b(Expr::bvar(1))));
    let arrow = Expr::pi(bd(), hyp, concl);
    Expr::pi(
        bd(),
        int_to_prop,
        Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), arrow))),
    )
}

/// Port-parallel to `call_or_call_instance_proof_ir`, generalized with the extra
/// `λ fieldVal` binder.
fn call_or_guarded_compare_instance_proof_ir(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
    op: crate::trustir_anchor::TrustIrCmpOp,
    field_is_lhs: bool,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let int_to_prop = Expr::pi(bd(), int_ty(), Expr::prop());
    let call_at_a = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_a), call_arg_a.to_operand_expr(), ret],
        )
    };
    let call_at_b = |ret: Expr| {
        Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(callee_id_b), call_arg_b.to_operand_expr(), ret],
        )
    };
    let cr_a = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_a(ret));
    let cr_b = |ret: Expr| Expr::app(cst(TRUSTIR_CALL_RESULT), call_at_b(ret));
    let wrap =
        |fv: Expr, a: Expr, b: Expr| call_or_guarded_compare_wrap(op, field_is_lhs, fv, a, b);

    // hyp type inside `λ post λ fieldVal λ retA λ retB`: retB=0, retA=1, fieldVal=2, post=3.
    let hyp_ty =
        Expr::app(Expr::bvar(3), wrap(Expr::bvar(2), cr_a(Expr::bvar(1)), cr_b(Expr::bvar(0))));

    // Body inside `λ post λ fieldVal λ retA λ retB λ h`: h=0, retB=1, retA=2,
    // fieldVal=3, post=4.
    // post_b : λ x:Int. post (wrap fieldVal (cr_a retA) x)
    //   inside post_b's own lambda (x=0): h=1, retB=2, retA=3, fieldVal=4, post=5.
    let post_b = Expr::lam(
        bd(),
        int_ty(),
        Expr::app(Expr::bvar(5), wrap(Expr::bvar(4), cr_a(Expr::bvar(3)), Expr::bvar(0))),
    );
    let inner_app = Expr::apps(
        cst(TRUSTIR_CALL_REFINES_CONTRACT),
        [post_b, call_at_b(Expr::bvar(1)), Expr::bvar(0)],
    );
    // post_a : λ y:Int. post (wrap fieldVal y (cr_b retB))
    //   inside post_a's own lambda (y=0): h=1, retB=2, retA=3, fieldVal=4, post=5.
    let post_a = Expr::lam(
        bd(),
        int_ty(),
        Expr::app(Expr::bvar(5), wrap(Expr::bvar(4), Expr::bvar(0), cr_b(Expr::bvar(2)))),
    );
    let body = Expr::apps(
        cst(TRUSTIR_CALL_REFINES_CONTRACT),
        [post_a, call_at_a(Expr::bvar(2)), inner_app],
    );

    Expr::lam(
        bd(),
        int_to_prop,
        Expr::lam(
            bd(),
            int_ty(),
            Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), Expr::lam(bd(), hyp_ty, body))),
        ),
    )
}

/// Check the per-call-pair CALL-OR-GUARDED-COMPARE instance against the real
/// clean-kernel on the TRUST-IR env. Fail-closed on every kernel rejection.
#[must_use]
pub fn check_call_or_guarded_compare_instance(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
    op: crate::trustir_anchor::TrustIrCmpOp,
    field_is_lhs: bool,
) -> RefinementVerdict {
    check_call_or_guarded_compare_instance_inner(
        callee_id_a,
        call_arg_a,
        callee_id_b,
        call_arg_b,
        op,
        field_is_lhs,
        None,
    )
}

/// Inner check with the fail-closed hook: `claimed_concl_pred = Some(p)`
/// overrides the instance conclusion's postcondition predicate (a WRONG
/// postcondition must NOT prove).
#[allow(clippy::too_many_arguments)]
fn check_call_or_guarded_compare_instance_inner(
    callee_id_a: u64,
    call_arg_a: &IrOperand,
    callee_id_b: u64,
    call_arg_b: &IrOperand,
    op: crate::trustir_anchor::TrustIrCmpOp,
    field_is_lhs: bool,
    claimed_concl_pred: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match trustir_call_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let inst_ty = call_or_guarded_compare_instance_type_ir(
        callee_id_a,
        call_arg_a,
        callee_id_b,
        call_arg_b,
        op,
        field_is_lhs,
        claimed_concl_pred,
    );
    let inst_proof = call_or_guarded_compare_instance_proof_ir(
        callee_id_a,
        call_arg_a,
        callee_id_b,
        call_arg_b,
        op,
        field_is_lhs,
    );
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "TrustIr.callOrGuardedCompareInstance check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string(TRUSTIR_CALL_OR_GUARDED_COMPARE_INSTANCE);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!(
            "add TrustIr.callOrGuardedCompareInstance: {e:?}"
        ));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected(
            "TrustIr.callOrGuardedCompareInstance decl not found".to_string(),
        ),
    }
}

// ---------------------------------------------------------------------------
// Trust: BRANCHY call-arm sub-axis — the composed BRANCH+CALL refinement.
//
// A branch whose arms are certified-callee calls (`if c { g(a) } else { h(b) }`,
// or a MIX of a call arm and a plain scalar arm) needs its `evalCfg` reduction
// related to a composition of the branch-condition case-split (the UNMODIFIED
// `Bool.rec`-over-`evalCond` skeleton the plain branch path already uses) with
// EACH arm's opaque call result. `IrTerm::CallReturn` (trustir_anchor.rs) lowers
// to the EXISTING `Term.Return (Operand.Var ret_idx)` — zero new `Term`/`evalCfg`
// registration — so `evalCfg`'s reduction of a call arm is, syntactically,
// `evalOperand E (Operand.Var ret_idx)`. The composed statement below asserts
// that the SAME (unmodified) `evalCfg` reduction equals a hand-built model term
// whose call-arm slot is `callResult (Call.mk callee_id arg (evalOperand E (Var
// ret_idx)))` — SOUND, not vacuous: `callResult` is the REDUCIBLE `Call.rec`
// projection `Call.rec (λ_.Int) (λ _ _ ret. ret)`, so `callResult (Call.mk _ _ X)`
// ι-reduces to `X` for ANY `X` (even a bound variable) — the wrapped and
// unwrapped forms are DEFINITIONALLY equal, so the `Eq.refl` proof below is a
// genuine kernel reduction, not an assumed tautology (mirrors the "MODEL-ONLY"
// honesty tier `trustir_anchor::check_body_refinement_model` already documents
// for the field-read leaf: LHS runs the SAME operational evaluator; RHS is a
// Rust-computed term PROVABLY, not merely claimed, equal to it).
// ---------------------------------------------------------------------------

/// Trust: BRANCHY call-arm sub-axis — walk from block `bb`, building the MODEL
/// composition `Expr` DIRECTLY (bypassing `Formula`/`live_ground_int` entirely —
/// there is no `Formula` for an opaque call): a `Switch` becomes `Bool.rec
/// (λ_.Int) <else> <then> (evalCond E cond)` (the SAME term `evalCfg`'s OWN
/// Switch minor premise reduces to); a `Return(op)` leaf becomes `evalOperand E
/// op` (EXACTLY what `evalCfg`'s Return minor premise reduces to for a
/// ZERO-STMT block, `evalBody E [] ≡ E`); a `CallReturn{callee_id, arg, ret_idx}`
/// leaf becomes `callResult (Call.mk callee_id arg (evalOperand E (Var
/// ret_idx)))`. `env` is the CLOSED `Expr` naming the outer ∀-bound environment
/// (reused for every leaf/guard — every block in this fragment carries NO
/// statements, so there is no per-block env-threading to model: see
/// `sem_branch_call_tree_to_ir_cfg`'s scope note). `None` (fail-closed) on a
/// block carrying any statement (out of THIS increment's scope), a missing
/// block, or a walk exceeding `fuel` (a cycle).
fn branch_call_model_rhs(cfg: &IrCfg, bb: u64, env: &Expr, fuel: u64) -> Option<Expr> {
    if fuel == 0 {
        return None;
    }
    let blk = cfg.blocks.get(usize::try_from(bb).ok()?)?;
    if !blk.stmts.is_empty() {
        return None; // scope: zero-stmt blocks only (Trust: BRANCHY call-arm sub-axis).
    }
    match &blk.term {
        IrTerm::Goto(tgt) => branch_call_model_rhs(cfg, *tgt, env, fuel - 1),
        IrTerm::Return(op) => {
            Some(Expr::apps(cst(TRUSTIR_EVAL_OPERAND), [env.clone(), op.to_operand_expr()]))
        }
        IrTerm::CallReturn { callee_id, arg, ret_idx } => {
            let ret_expr = Expr::apps(
                cst(TRUSTIR_EVAL_OPERAND),
                [env.clone(), IrOperand::Var(*ret_idx).to_operand_expr()],
            );
            let call_val = Expr::apps(
                cst(TRUSTIR_CALL_MK),
                [Expr::nat_lit(*callee_id), arg.to_operand_expr(), ret_expr],
            );
            Some(Expr::app(cst(TRUSTIR_CALL_RESULT), call_val))
        }
        IrTerm::Switch(cond, then_bb, else_bb) => {
            let then_e = branch_call_model_rhs(cfg, *then_bb, env, fuel - 1)?;
            let else_e = branch_call_model_rhs(cfg, *else_bb, env, fuel - 1)?;
            let bd = || BinderData::from(BinderInfo::Default);
            let bool_rec =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
            let cond_e = Expr::apps(cst(TRUSTIR_EVAL_COND), [env.clone(), cond.to_cond_expr()]);
            // Bool.rec minor order is (false, true): FALSE ↦ else, TRUE ↦ then — the
            // SAME polarity `evalCfg`'s own Switch minor premise uses.
            Some(Expr::apps(bool_rec, [int_motive, else_e, then_e, cond_e]))
        }
    }
}

/// Build the composed BRANCH+CALL refinement STATEMENT:
///
/// ```text
/// ∀ (x_0 … x_{n-1} : Int), evalCfg E cfg fuel entry = <branch_call_model_rhs>
/// ```
///
/// `indices` (hence `n` and `E`) come from `cfg.param_indices()` — EVERY
/// parameter AND every call arm's `ret_idx` slot, each its own ∀-bound `Int`.
/// `claimed` overrides the RHS (the fail-closed probe: a WRONG composition —
/// e.g. the wrong callee id, or the then/else arms swapped — must NOT prove).
fn branch_call_refinement_statement(cfg: &IrCfg, claimed: Option<&Expr>) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let indices = cfg.param_indices();
    let n = indices.len();
    let env = refinement_env(&indices);
    let lhs = Expr::apps(
        cst(TRUSTIR_EVAL_CFG),
        [env.clone(), cfg.to_cfg_expr(), Expr::nat_lit(cfg.fuel), Expr::nat_lit(cfg.entry)],
    );
    let rhs = match claimed {
        Some(e) => e.clone(),
        None => branch_call_model_rhs(cfg, cfg.entry, &env, cfg.fuel)?,
    };
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut stmt = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        stmt = Expr::pi(bd(), int_ty(), stmt);
    }
    Some(stmt)
}

/// The composed BRANCH+CALL refinement PROOF: `λ x⃗. @Eq.refl Int
/// <branch_call_model_rhs>`. Sound because `evalCfg`'s (UNMODIFIED) ι-reduction
/// of the call-armed CFG reconstructs EXACTLY the hand-composed model term (see
/// this section's header note) — reflexivity at it inhabits the equality.
fn branch_call_refinement_proof(cfg: &IrCfg) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let indices = cfg.param_indices();
    let n = indices.len();
    let env = refinement_env(&indices);
    let rhs = branch_call_model_rhs(cfg, cfg.entry, &env, cfg.fuel)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check the composed BRANCH+CALL refinement for a call-armed trust-ir CFG,
/// modulo 3, on the TRUST-IR CALL env (`trustir_call_env` — `evalCfg`/`Term` are
/// UNMODIFIED, but the model RHS needs `Call.mk`/`callResult` in scope).
/// `ProvenModulo3` means: `evalCfg`'s reduction of the call-armed CFG is EXACTLY
/// the `Bool.rec`-composed opaque-call-result term — kernel-verified. Fail-closed
/// for a CFG with any statement-bearing block, a fuel bound that does not cover
/// the tree, or (the negative control) a WRONG claimed composition.
#[must_use]
pub fn check_branch_call_refinement(cfg: &IrCfg) -> RefinementVerdict {
    check_branch_call_refinement_inner(cfg, None)
}

/// Inner check with the fail-closed hook: `claimed = Some(wrong)` overrides the
/// composed RHS (a WRONG composition must NOT prove).
fn check_branch_call_refinement_inner(cfg: &IrCfg, claimed: Option<&Expr>) -> RefinementVerdict {
    let mut env = match trustir_call_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let (Some(statement), Some(proof)) =
        (branch_call_refinement_statement(cfg, claimed), branch_call_refinement_proof(cfg))
    else {
        return RefinementVerdict::KernelRejected(
            "branch-call composition declined (out of the modeled call-armed fragment, \
             e.g. a statement-bearing block, or an under-fueled walk)"
                .to_string(),
        );
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("branch_call check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.TrustIr.Refinement.branch_call_adequacy");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add branch_call_adequacy: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected(
            "Trust.TrustIr.Refinement.branch_call_adequacy decl not found".to_string(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A closed WRONG conclusion predicate `λ (_ : Int). True` — distinct from the
    /// ∀-bound `post` the instance transports (mirrors `mirsem`'s
    /// `wrong_int_predicate` control).
    fn wrong_int_predicate() -> Expr {
        let bd = || BinderData::from(BinderInfo::Default);
        Expr::lam(bd(), int_ty(), cst("True"))
    }

    /// The closed `Int` literal — identical to `trustir_anchor::int_lit`.
    fn int_lit(n: i128) -> Expr {
        // Trust: EXACT ENCODING (2026-07-24) — see `clean_ground::int_lit_to_expr`. The
        // former `as u64` was `n mod 2^64`, a truncation that made the map non-injective
        // and caused a demonstrated LIVE FALSE ACCEPT. `nat_lit_u128` is a drop-in:
        // `BigNat::from_limbs` normalizes a trailing zero limb back to `Small`, so every
        // `k <= u64::MAX` encodes byte-identically and only the previously-truncated
        // literals change. Keeping this in lockstep is what the byte-identity claim above
        // asserts — it is now TRUE again for the full `i128` range.
        if n >= 0 {
            Expr::app(cst("Int.ofNat"), Expr::nat_lit_u128(n.unsigned_abs()))
        } else {
            Expr::app(cst("Int.negSucc"), Expr::nat_lit_u128(n.unsigned_abs() - 1))
        }
    }

    /// REGISTRATION probe: the whole CALL theory registers on the trust-ir env with
    /// the proven transport lemma's axiom closure ⊆ the 3 foundational axioms
    /// (EMPTY residue — the audit runs inside the registration, so a 4th axiom
    /// anywhere fails env construction). Also asserts the trust-ir env's
    /// zero-MirSem separation holds for the new decls: no registered call decl
    /// name mentions `MirSem`, the env declares NO `Trust.MirSem.*` call constant,
    /// and the `Trust.TrustIr.*` call names ARE declared.
    #[test]
    fn trustir_call_env_modulo3_and_zero_mirsem_separation() {
        let env = trustir_call_env().expect("call theory must register modulo 3");
        // The proven lemma's residue is EMPTY (the theorem gate).
        let residue = env
            .axiom_deps(&Name::from_string(TRUSTIR_CALL_REFINES_CONTRACT))
            .expect("callRefinesContract registered");
        assert!(
            residue.is_empty(),
            "callRefinesContract must rest on ⊆ the 3 foundational axioms; residue: {residue:?}",
        );
        // THE SEPARATION PROBE (load-bearing): zero MirSem names among the new
        // decls, zero Trust.MirSem.* constants in the env.
        for n in [
            TRUSTIR_CALL,
            TRUSTIR_CALL_MK,
            TRUSTIR_CALL_RESULT,
            TRUSTIR_CALL_CALLEE,
            TRUSTIR_CALL_REFINES_CONTRACT,
            TRUSTIR_CALL_RETURN_INSTANCE,
        ] {
            assert!(!n.contains("MirSem"), "zero-MirSem separation violated by {n}");
        }
        for n in [
            "Trust.MirSem.Call",
            "Trust.MirSem.Call.mk",
            "Trust.MirSem.call_result",
            "Trust.MirSem.call_callee",
            "Trust.MirSem.callRefinesContract",
            "Trust.MirSem.callReturnInstance",
            "Trust.MirSem.Operand",
            "Trust.MirSem.eval",
        ] {
            assert!(
                env.get_const(&Name::from_string(n)).is_none(),
                "the trust-ir call env must NOT declare {n}"
            );
        }
        // And the trust-ir call names ARE declared.
        for n in [TRUSTIR_CALL_MK, TRUSTIR_CALL_RESULT, TRUSTIR_CALL_CALLEE] {
            assert!(
                env.get_const(&Name::from_string(n)).is_some(),
                "the trust-ir call env must declare {n}"
            );
        }
    }

    #[test]
    fn trustir_call_result_projects_the_callee_return() {
        // The call DENOTATION is a genuine recursor projection (NOT a bare
        // identity): `callResult (Call.mk callee arg ret)` ι-reduces to `ret`.
        // Confirms the contract transport reasons over the value flowing out of
        // the call site. Mirror of mirsem's `call_result_projects_the_callee_return`.
        let env = trustir_call_env().expect("env");
        let tc = TypeChecker::new(&env);
        // Call.mk 7 (Operand.Const 3) (Int.ofNat 42)
        let call = Expr::apps(
            cst(TRUSTIR_CALL_MK),
            [Expr::nat_lit(7), IrOperand::Const(3).to_operand_expr(), int_lit(42)],
        );
        let lhs = Expr::app(cst(TRUSTIR_CALL_RESULT), call);
        assert!(
            tc.is_def_eq(&lhs, &int_lit(42)),
            "callResult (Call.mk _ _ 42) must ι-reduce to 42"
        );
    }

    #[test]
    fn trustir_call_return_instance_proven_modulo_3_and_wrong_postcondition_fails_closed() {
        // The PER-CALL instance at the corpus call site's concrete (callee-id,
        // first-arg) kernel-checks modulo 3 on the TRUST-IR env — and the
        // fail-closed hook holds: a WRONG conclusion predicate must NOT prove
        // (the instance proof transports EXACTLY the assumed `post`).
        let arg = IrOperand::Var(0);
        assert_eq!(
            check_call_return_instance(0, &arg),
            RefinementVerdict::ProvenModulo3,
            "the per-call trust-ir instance must prove modulo 3"
        );
        let wrong = wrong_int_predicate();
        let verdict = check_call_return_instance_inner(0, &arg, Some(&wrong));
        assert!(
            matches!(verdict, RefinementVerdict::KernelRejected(_)),
            "a wrong per-call postcondition MUST be kernel-rejected, got {verdict:?}"
        );
        // The Const-arg pin proves too (the corpus caller's second arg shape).
        assert_eq!(
            check_call_return_instance(3, &IrOperand::Const(1)),
            RefinementVerdict::ProvenModulo3,
        );
    }

    #[test]
    fn trustir_call_op_call_instance_proven_modulo_3_and_wrong_postcondition_fails_closed() {
        // The PER-CALL-PAIR instance at the container-corpus `is_full`-shaped call
        // pair (`len() == capacity()`, two DISTINCT callee ids, same `self` arg)
        // kernel-checks modulo 3 on the TRUST-IR env.
        let arg = IrOperand::Var(0);
        assert_eq!(
            check_call_op_call_instance(0, &arg, 1, &arg, TrustIrCallThenOp::Cmp(TrustIrCmpOp::Eq),),
            RefinementVerdict::ProvenModulo3,
            "the per-call-pair trust-ir instance must prove modulo 3 (Cmp)"
        );
        // The SAME callee twice (`double_len`'s `len() + len()`) also proves.
        assert_eq!(
            check_call_op_call_instance(
                0,
                &arg,
                0,
                &arg,
                TrustIrCallThenOp::Bin(crate::trustir_anchor::TrustIrBinOp::Add),
            ),
            RefinementVerdict::ProvenModulo3,
            "the SAME callee called twice must also prove modulo 3 (Bin, double_len shape)"
        );
        // The fail-closed hook: a WRONG conclusion predicate must NOT prove (the
        // instance proof transports EXACTLY the assumed `post`).
        let wrong = wrong_int_predicate();
        let verdict = check_call_op_call_instance_inner(
            0,
            &arg,
            1,
            &arg,
            TrustIrCallThenOp::Cmp(TrustIrCmpOp::Eq),
            Some(&wrong),
        );
        assert!(
            matches!(verdict, RefinementVerdict::KernelRejected(_)),
            "a wrong per-call-pair postcondition MUST be kernel-rejected, got {verdict:?}"
        );
    }

    /// Trust: M6 rung 8 — CALL-OR-CALL. The PER-CALL-PAIR short-circuit `||`
    /// instance kernel-checks modulo 3 (the SAME `callRefinesContract` transport
    /// applied twice, at the `call_or_call_wrap` ite composition) — including
    /// the SAME callee twice (`f() || f()`, mirroring CALL-OP-CALL's
    /// `double_len` precedent) — and a WRONG conclusion predicate fails closed.
    #[test]
    fn trustir_call_or_call_instance_proven_modulo_3_and_wrong_postcondition_fails_closed() {
        let arg = IrOperand::Var(0);
        assert_eq!(
            check_call_or_call_instance(0, &arg, 1, &arg),
            RefinementVerdict::ProvenModulo3,
            "the per-call-pair short-circuit `||` trust-ir instance must prove modulo 3"
        );
        // The SAME callee twice — explicitly allowed, mirroring CALL-OP-CALL.
        assert_eq!(
            check_call_or_call_instance(0, &arg, 0, &arg),
            RefinementVerdict::ProvenModulo3,
            "the SAME callee called twice (`f() || f()`) must also prove modulo 3"
        );
        // The fail-closed hook: a WRONG conclusion predicate must NOT prove.
        let wrong = wrong_int_predicate();
        let verdict = check_call_or_call_instance_inner(0, &arg, 1, &arg, Some(&wrong));
        assert!(
            matches!(verdict, RefinementVerdict::KernelRejected(_)),
            "a wrong per-call-pair postcondition MUST be kernel-rejected, got {verdict:?}"
        );
    }

    /// Trust: M6 rung 8 — the `call_or_call_wrap` composition ITSELF, pinned
    /// against a hand-decoded `Bool.rec` reduction: at a CLOSED literal `a = 1`
    /// (callee_a "true"), `wrap(1, b)` reduces to the closed literal `1`
    /// (SHORT-CIRCUIT: `b` never appears in the reduct); at `a = 0`, `wrap(0,
    /// b)` reduces to `b` UNCHANGED. Checked by kernel `check_type`-ing an
    /// `Eq.refl` proof at each claimed reduct — a WRONG reduct is kernel-
    /// rejected, so this is a genuine reduction pin, not a tautology.
    #[test]
    fn call_or_call_wrap_reduces_to_the_short_circuit_value_at_closed_literals() {
        let env = trustir_call_env().expect("trust-ir call env builds");
        let b = int_lit(42);
        // a = 1 (true): wrap(1, b) claimed to reduce to `1` — the SHORT-CIRCUIT
        // value; `b` (42) must NOT appear anywhere in the true reduct.
        let wrap_true = call_or_call_wrap(int_lit(1), b.clone());
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let stmt_true = Expr::apps(eq.clone(), [int_ty(), wrap_true, int_lit(1)]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let proof_true = Expr::apps(eq_refl.clone(), [int_ty(), int_lit(1)]);
        let tc = TypeChecker::new(&env);
        assert!(
            tc.check_type(&proof_true, &stmt_true).is_ok(),
            "wrap(1, b) must reduce to the closed literal 1 (short-circuit, `b` unused)"
        );
        // A WRONG claim (`wrap(1, b) = b`, i.e. claiming `b` leaks through when
        // `a` is true) must be kernel-rejected — genuinely NOT def-eq.
        let stmt_wrong =
            Expr::apps(eq, [int_ty(), call_or_call_wrap(int_lit(1), b.clone()), b.clone()]);
        let proof_wrong = Expr::apps(eq_refl.clone(), [int_ty(), b.clone()]);
        assert!(
            tc.check_type(&proof_wrong, &stmt_wrong).is_err(),
            "claiming `b` leaks through the true arm MUST be kernel-rejected"
        );
        // a = 0 (false): wrap(0, b) claimed to reduce to `b` UNCHANGED.
        let wrap_false = call_or_call_wrap(int_lit(0), b.clone());
        let stmt_false = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [int_ty(), wrap_false, b.clone()],
        );
        let proof_false = Expr::apps(eq_refl, [int_ty(), b]);
        assert!(
            tc.check_type(&proof_false, &stmt_false).is_ok(),
            "wrap(0, b) must reduce to `b` unchanged (callee_a false ⇒ callee_b's value)"
        );
    }

    /// Trust: M6 rung 9 — CALL-OR-GUARDED-COMPARE (the RICHER-|| ARM). The
    /// PER-CALL-PAIR guarded-compare instance kernel-checks modulo 3, for BOTH
    /// operand orders (`field OP callB` and `callB OP field`) — and a WRONG
    /// conclusion predicate fails closed.
    #[test]
    fn trustir_call_or_guarded_compare_instance_proven_modulo_3_and_wrong_postcondition_fails_closed()
     {
        use crate::trustir_anchor::TrustIrCmpOp;
        let arg = IrOperand::Var(0);
        assert_eq!(
            check_call_or_guarded_compare_instance(0, &arg, 1, &arg, TrustIrCmpOp::Lt, true),
            RefinementVerdict::ProvenModulo3,
            "the per-call-pair guarded-compare (field OP callB) instance must prove modulo 3"
        );
        assert_eq!(
            check_call_or_guarded_compare_instance(0, &arg, 1, &arg, TrustIrCmpOp::Lt, false),
            RefinementVerdict::ProvenModulo3,
            "the per-call-pair guarded-compare (callB OP field) instance must prove modulo 3"
        );
        // The SAME callee twice — explicitly allowed, mirroring CALL-OR-CALL.
        assert_eq!(
            check_call_or_guarded_compare_instance(0, &arg, 0, &arg, TrustIrCmpOp::Eq, true),
            RefinementVerdict::ProvenModulo3,
            "the SAME callee called twice must also prove modulo 3"
        );
        // Every comparison op kernel-checks.
        for op in TrustIrCmpOp::ALL {
            assert_eq!(
                check_call_or_guarded_compare_instance(0, &arg, 1, &arg, op, true),
                RefinementVerdict::ProvenModulo3,
                "op {op:?} did not prove modulo 3",
            );
        }
        // The fail-closed hook: a WRONG conclusion predicate must NOT prove.
        let wrong = wrong_int_predicate();
        let verdict = check_call_or_guarded_compare_instance_inner(
            0,
            &arg,
            1,
            &arg,
            TrustIrCmpOp::Lt,
            true,
            Some(&wrong),
        );
        assert!(
            matches!(verdict, RefinementVerdict::KernelRejected(_)),
            "a wrong per-call-pair postcondition MUST be kernel-rejected, got {verdict:?}"
        );
    }

    /// Trust: M6 rung 9 — the `call_or_guarded_compare_wrap` composition ITSELF,
    /// pinned against a hand-decoded `Bool.rec` reduction: at `a = 1` (callee_a
    /// "true"), the composed value reduces to the closed literal `1`
    /// (SHORT-CIRCUIT: neither `fieldVal` nor `b` appears in the reduct); at
    /// `a = 0`, it reduces to `bool_as_int(cmp_bool_expr(Eq, fieldVal, b))`. A
    /// WRONG reduct is kernel-rejected — a genuine reduction pin, not a
    /// tautology.
    #[test]
    fn call_or_guarded_compare_wrap_reduces_to_the_short_circuit_value_at_closed_literals() {
        use crate::trustir_anchor::TrustIrCmpOp;
        let env = trustir_call_env().expect("trust-ir call env builds");
        let field_val = int_lit(7);
        let b = int_lit(42);
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let tc = TypeChecker::new(&env);
        // a = 1 (true): reduces to the closed literal `1` regardless of fieldVal/b.
        let wrap_true = call_or_guarded_compare_wrap(
            TrustIrCmpOp::Eq,
            true,
            field_val.clone(),
            int_lit(1),
            b.clone(),
        );
        let stmt_true = Expr::apps(eq.clone(), [int_ty(), wrap_true, int_lit(1)]);
        let proof_true = Expr::apps(eq_refl.clone(), [int_ty(), int_lit(1)]);
        assert!(
            tc.check_type(&proof_true, &stmt_true).is_ok(),
            "wrap(fieldVal, 1, b) must reduce to the closed literal 1 (short-circuit)"
        );
        // a = 0 (false): reduces to `bool_as_int(cmp_bool_expr(Eq, fieldVal, b))`
        // — here fieldVal=7, b=42, so Eq is false ⇒ the closed literal `0`.
        let wrap_false = call_or_guarded_compare_wrap(
            TrustIrCmpOp::Eq,
            true,
            field_val.clone(),
            int_lit(0),
            b.clone(),
        );
        let stmt_false = Expr::apps(eq, [int_ty(), wrap_false, int_lit(0)]);
        let proof_false = Expr::apps(eq_refl, [int_ty(), int_lit(0)]);
        assert!(
            tc.check_type(&proof_false, &stmt_false).is_ok(),
            "wrap(fieldVal=7, 0, b=42) must reduce to 0 (7 ≠ 42)"
        );
    }

    // -----------------------------------------------------------------------
    // Trust: BRANCHY call-arm sub-axis — the composed BRANCH+CALL refinement.
    // -----------------------------------------------------------------------

    use crate::trustir_anchor::{IrBlock, IrCond, TrustIrCmpOp};

    /// The canonical call-armed branch CFG: `if x > 0 { call(id=7, arg=x) } else
    /// { call(id=9, arg=Const(5)) }` over parameter `x = Var(0)`. `ret_idx` slots
    /// 1 (then) and 2 (else) are FRESH env slots past the single parameter —
    /// EXACTLY the allocation `sem_branch_call_tree_to_ir_cfg` performs for a
    /// real `if c { g(a) } else { h(5) }` caller. `fuel = 3` comfortably exceeds
    /// the longest acyclic path (entry → arm, one edge).
    fn example_branch_call_cfg() -> IrCfg {
        IrCfg {
            blocks: vec![
                IrBlock {
                    stmts: vec![],
                    term: IrTerm::Switch(
                        IrCond {
                            op: TrustIrCmpOp::Gt,
                            a: IrOperand::Var(0),
                            b: IrOperand::Const(0),
                        },
                        1,
                        2,
                    ),
                },
                IrBlock {
                    stmts: vec![],
                    term: IrTerm::CallReturn { callee_id: 7, arg: IrOperand::Var(0), ret_idx: 1 },
                },
                IrBlock {
                    stmts: vec![],
                    term: IrTerm::CallReturn { callee_id: 9, arg: IrOperand::Const(5), ret_idx: 2 },
                },
            ],
            entry: 0,
            fuel: 3,
        }
    }

    #[test]
    fn branch_call_refinement_proves_modulo_3_for_the_canonical_cfg() {
        // GENUINE, non-vacuous: `evalCfg`'s (UNMODIFIED) reduction of the
        // call-armed CFG equals the hand-composed `Bool.rec`-over-`callResult`
        // model — kernel-checked, not asserted.
        assert_eq!(
            check_branch_call_refinement(&example_branch_call_cfg()),
            RefinementVerdict::ProvenModulo3,
            "the canonical call-armed branch CFG must prove modulo 3"
        );
    }

    #[test]
    fn branch_call_refinement_wrong_composition_fails_closed() {
        // NEGATIVE CONTROL #1 (mission §5 risk 2): a WRONG per-arm composition
        // must NOT prove. HONEST DESIGN NOTE (a genuine finding while writing
        // this control): `callResult` is a PURE `ret`-projection — `callResult
        // (Call.mk callee arg X)` ι-reduces to `X` REGARDLESS of `callee`/`arg`
        // (they carry no runtime content on this axis; callee/arg identity is
        // established SEPARATELY, by the recognizer pinning them per block and
        // by `check_call_return_instance`'s OWN per-arm check). So swapping
        // ONLY the `callee_id`/`arg` LABELS while keeping the CORRECT `ret_idx`
        // per slot does NOT change the reduced term — that claim would still
        // (correctly) prove, and is NOT a genuine soundness gap (the labels
        // are not part of THIS composition's claim). The load-bearing quantity
        // is `ret_idx`: swapping WHICH env slot backs the then/else arm is a
        // genuine falsehood (`evalCfg`'s actual then-reduct reads slot 1, not
        // slot 2 — two DISTINCT ∀-bound variables, not def-eq) — THAT must be
        // rejected, and is:
        let cfg = example_branch_call_cfg();
        let bd = || BinderData::from(BinderInfo::Default);
        let bool_rec =
            Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
        let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
        let indices = cfg.param_indices();
        let env = refinement_env(&indices);
        let cond_e = Expr::apps(
            cst(TRUSTIR_EVAL_COND),
            [
                env.clone(),
                IrCond { op: TrustIrCmpOp::Gt, a: IrOperand::Var(0), b: IrOperand::Const(0) }
                    .to_cond_expr(),
            ],
        );
        // The WRONG RHS: the then/else `ret_idx` SLOTS swapped (callee_id/arg
        // labels correctly paired with their block, but reading the OTHER
        // arm's env slot) — the true then-slot reads Var(1), this claims Var(2).
        let wrong_then = Expr::app(
            cst(TRUSTIR_CALL_RESULT),
            Expr::apps(
                cst(TRUSTIR_CALL_MK),
                [
                    Expr::nat_lit(7),
                    IrOperand::Var(0).to_operand_expr(),
                    Expr::apps(
                        cst(TRUSTIR_EVAL_OPERAND),
                        [env.clone(), IrOperand::Var(2).to_operand_expr()],
                    ),
                ],
            ),
        );
        let wrong_else = Expr::app(
            cst(TRUSTIR_CALL_RESULT),
            Expr::apps(
                cst(TRUSTIR_CALL_MK),
                [
                    Expr::nat_lit(9),
                    IrOperand::Const(5).to_operand_expr(),
                    Expr::apps(
                        cst(TRUSTIR_EVAL_OPERAND),
                        [env.clone(), IrOperand::Var(1).to_operand_expr()],
                    ),
                ],
            ),
        );
        let wrong_rhs = Expr::apps(bool_rec, [int_motive, wrong_else, wrong_then, cond_e]);
        let verdict = check_branch_call_refinement_inner(&cfg, Some(&wrong_rhs));
        assert!(
            matches!(verdict, RefinementVerdict::KernelRejected(_)),
            "a wrong (ret_idx-swapped) branch-call composition MUST be kernel-rejected, \
             got {verdict:?}"
        );
    }

    #[test]
    fn branch_call_refinement_undersized_fuel_fails_closed_not_truncated() {
        // NEGATIVE CONTROL #2 (mission §5 risk 3): an UNDERSIZED fuel bound must
        // FAIL CLOSED (decline), never silently kernel-check against a
        // TRUNCATED (fuel-exhausted) reduct. `fuel = 1` is enough to enter the
        // Switch block (Nat.rec succ case) but NOT enough to recurse into
        // either arm (`ih` needs a further fuel-1 = 0 step, which `evalCfg`'s
        // OWN zero-fuel case reduces to the canonical `Int.ofNat 0` fallback,
        // NOT the arm's real value) — so the hand-composed model RHS (which
        // assumes full reduction) must NOT match, and the kernel must reject.
        let mut cfg = example_branch_call_cfg();
        cfg.fuel = 1;
        let verdict = check_branch_call_refinement(&cfg);
        assert!(
            matches!(verdict, RefinementVerdict::KernelRejected(_)),
            "an under-fueled call-armed CFG must fail closed (not truncate to a \
             false ProvenModulo3), got {verdict:?}"
        );
        // fuel = 0: same requirement.
        let mut cfg0 = example_branch_call_cfg();
        cfg0.fuel = 0;
        assert!(
            matches!(check_branch_call_refinement(&cfg0), RefinementVerdict::KernelRejected(_)),
            "fuel = 0 must also fail closed"
        );
        // The BASELINE (fuel = 3) still proves — confirms the failure above is
        // genuinely about fuel, not a broken fixture.
        assert_eq!(
            check_branch_call_refinement(&example_branch_call_cfg()),
            RefinementVerdict::ProvenModulo3,
            "the baseline fuel=3 CFG must still prove modulo 3"
        );
    }

    #[test]
    fn branch_call_refinement_statement_bearing_block_declines() {
        // SCOPE control: a block carrying a statement is OUT of this
        // increment's modeled fragment (`branch_call_model_rhs` requires every
        // block zero-stmt) — must decline, not silently drop/ignore the stmt.
        let mut cfg = example_branch_call_cfg();
        cfg.blocks[1].stmts.push(crate::trustir_anchor::IrStmt {
            idx: 3,
            rvalue: crate::trustir_anchor::IrRvalue::Use(IrOperand::Const(1)),
        });
        assert!(
            matches!(check_branch_call_refinement(&cfg), RefinementVerdict::KernelRejected(_)),
            "a statement-bearing call-arm block must decline (out of scope)"
        );
    }
}
