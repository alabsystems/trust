// The CFG-level interpreter: program-counter state, `step_cfg`/`exec_cfg`, the
// unroll law and refinement, and the exit-stability and bounded-halt lemmas
// termination at CFG granularity rests on.

use super::*;

// ===========================================================================
// Step 6U — THE UNSTRUCTURED / IRREDUCIBLE CFG REFINEMENT.
// ===========================================================================
/// The `CfgState : Type` type.
pub(super) fn cfg_state_ty() -> Expr {
    cst(MIRSEM_CFG_STATE)
}

/// The CFG transition-function type `Nat → Env → CfgState` (block index + env ↦
/// successor state). The single ARBITRARY parameter the CFG refinement is universal
/// over — modeling any terminator graph, including irreducible edges.
pub(super) fn cfg_next_ty() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), env_ty(), cfg_state_ty()))
}

/// Register `Trust.MirSem.CfgState : Type` (one ctor `CfgState.mk : Nat → Env →
/// CfgState`). Idempotent. See [`MIRSEM_CFG_STATE`].
pub(super) fn register_cfg_state(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CFG_STATE);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // CfgState.mk : Nat → Env → CfgState
    let mk_ctor = Constructor {
        name: Name::from_string(MIRSEM_CFG_STATE_MK),
        type_: Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), env_ty(), cfg_state_ty())),
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
    env.add_inductive(decl).map_err(|e| format!("add_inductive(CfgState): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.cfg_pc : CfgState → Nat` (idempotent) — the program-counter
/// projection via the `CfgState` recursor: `CfgState.rec (λ pc env. pc)`.
pub(super) fn register_cfg_pc(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CFG_PC);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // @CfgState.rec.{1} : motive lands in Nat : Type ⇒ Sort 1.
    let rec =
        Expr::const_(Name::from_string(MIRSEM_CFG_STATE_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cfg_state_ty(), cst("Nat"));
    // minor : λ (pc:Nat)(env:Env). pc   (pc=1)
    let minor = Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), env_ty(), Expr::bvar(1)));
    let body = Expr::apps(rec, [motive, minor, Expr::bvar(0)]);
    let val = Expr::lam(bd(), cfg_state_ty(), body);
    let ty = Expr::pi(bd(), cfg_state_ty(), cst("Nat"));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(cfg_pc): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.cfg_env : CfgState → Env` (idempotent) — the env projection
/// via the `CfgState` recursor: `CfgState.rec (λ pc env. env)`.
pub(super) fn register_cfg_env(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CFG_ENV);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // @CfgState.rec.{1} : motive lands in Env : Type ⇒ Sort 1.
    let rec =
        Expr::const_(Name::from_string(MIRSEM_CFG_STATE_REC), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cfg_state_ty(), env_ty());
    // minor : λ (pc:Nat)(env:Env). env   (env=0)
    let minor = Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), env_ty(), Expr::bvar(0)));
    let body = Expr::apps(rec, [motive, minor, Expr::bvar(0)]);
    let val = Expr::lam(bd(), cfg_state_ty(), body);
    let ty = Expr::pi(bd(), cfg_state_ty(), env_ty());
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(cfg_env): {e:?}"))?;
    Ok(())
}

/// `step_cfg next s : CfgState` applied as a CONSTANT to (next, s) refs.
pub(super) fn step_cfg_app(next_ref: Expr, s_ref: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_STEP_CFG), [next_ref, s_ref])
}

/// Register `Trust.MirSem.step_cfg : (Nat → Env → CfgState) → CfgState → CfgState`
/// (idempotent) = `λ next s. next (cfg_pc s) (cfg_env s)` — follow ONE terminator edge.
pub(super) fn register_step_cfg(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_STEP_CFG);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // λ(next : Nat → Env → CfgState).λ(s : CfgState). next (cfg_pc s)(cfg_env s)
    //   depth: s=0, next=1.
    let pc = Expr::app(cst(MIRSEM_CFG_PC), Expr::bvar(0));
    let en = Expr::app(cst(MIRSEM_CFG_ENV), Expr::bvar(0));
    let body = Expr::apps(Expr::bvar(1), [pc, en]);
    let val = Expr::lam(bd(), cfg_next_ty(), Expr::lam(bd(), cfg_state_ty(), body));
    let ty = Expr::pi(bd(), cfg_next_ty(), Expr::pi(bd(), cfg_state_ty(), cfg_state_ty()));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(step_cfg): {e:?}"))?;
    Ok(())
}

/// `exec_cfg next fuel s : CfgState` applied as a CONSTANT to its three refs.
pub(super) fn exec_cfg_app(next_ref: Expr, fuel_ref: Expr, s_ref: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_EXEC_CFG), [next_ref, fuel_ref, s_ref])
}

/// Register `Trust.MirSem.exec_cfg : (Nat → Env → CfgState) → Nat → CfgState →
/// CfgState` (idempotent), front-peeling fuel via `Nat.rec` at a `CfgState →
/// CfgState` motive: `exec_cfg next 0 s = s`, `exec_cfg next (succ n) s =
/// exec_cfg next n (step_cfg next s)`. Requires `step_cfg` registered.
pub(super) fn register_exec_cfg(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EXEC_CFG);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let state_to_state = Expr::pi(bd(), cfg_state_ty(), cfg_state_ty());
    // @Nat.rec.{1} : motive lands in (CfgState → CfgState) : Type ⇒ Sort 1.
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Nat"), state_to_state.clone());
    // zero case : λ(s' : CfgState). s'   (identity transformer)
    let zero_case = Expr::lam(bd(), cfg_state_ty(), Expr::bvar(0));
    // succ case : λ(n).λ(ih).λ(s'). ih (step_cfg next s')
    //   Under `λ(next)λ(fuel)` then inside λ(n)λ(ih)λ(s'):
    //   s'=0, ih=1, n=2, fuel=3, next=4.
    let succ_case = {
        let step = step_cfg_app(Expr::bvar(4), Expr::bvar(0));
        let ih_app = Expr::app(Expr::bvar(1), step);
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), state_to_state.clone(), Expr::lam(bd(), cfg_state_ty(), ih_app)),
        )
    };
    // @Nat.rec.{1} motive zero_case succ_case fuel   (fuel = bvar(0) under the λ next λ fuel)
    let rec_app = Expr::apps(nat_rec, [motive, zero_case, succ_case, Expr::bvar(0)]);
    // λ(next).λ(fuel).λ(s). (Nat.rec … fuel) s   (s = bvar(0) once added below)
    //   We curry as: λ next. λ fuel. λ s. (rec fuel) s. Inside λ(next)λ(fuel)λ(s): s=0,fuel=1,next=2.
    let rec_app_lifted = rec_app.lift(1); // lift past the new λ(s)
    let applied = Expr::app(rec_app_lifted, Expr::bvar(0));
    let val = Expr::lam(
        bd(),
        cfg_next_ty(),
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), cfg_state_ty(), applied)),
    );
    let ty = Expr::pi(
        bd(),
        cfg_next_ty(),
        Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), cfg_state_ty(), cfg_state_ty())),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(exec_cfg): {e:?}"))?;
    Ok(())
}

/// `@Eq CfgState a b` — equality of CFG states (`CfgState : Type` ⇒ `Eq.{1}`).
pub(super) fn eq_cfg_state(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [cfg_state_ty(), a, b],
    )
}

/// The fuel-indexed CFG UNROLL law TYPE: `∀ (next)(fuel)(s),
/// exec_cfg next fuel (step_cfg next s) = step_cfg next (exec_cfg next fuel s)`.
/// Inside `∀ next ∀ fuel ∀ s`: s=0, fuel=1, next=2.
pub(super) fn exec_cfg_unroll_law_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside ∀ next ∀ fuel ∀ s: s=0, fuel=1, next=2.
    let step_s = step_cfg_app(Expr::bvar(2), Expr::bvar(0));
    let lhs = exec_cfg_app(Expr::bvar(2), Expr::bvar(1), step_s);
    let loop_s = exec_cfg_app(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
    let rhs = step_cfg_app(Expr::bvar(2), loop_s);
    let eq = eq_cfg_state(lhs, rhs);
    let body_s = Expr::pi(bd(), cfg_state_ty(), eq);
    let body_fuel = Expr::pi(bd(), cst("Nat"), body_s);
    Expr::pi(bd(), cfg_next_ty(), body_fuel)
}

/// The fuel-indexed CFG UNROLL law PROOF, by `Nat.rec` induction on `fuel`:
/// `λ(next)(fuel). Nat.rec motive zero_proof succ_proof fuel`. BASE: both sides
/// ι-reduce to `step_cfg next s` ⇒ `Eq.refl`. STEP: `λ n ih s. ih (step_cfg next s)`
/// — the IH applied at the STEPPED state (genuine induction, never `Eq.refl`).
pub(super) fn exec_cfg_unroll_law_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // proof = λ(next)λ(fuel). Nat.rec motive zero succ fuel.
    // motive : Nat → Prop = λ(fuel'). ∀ s, exec_cfg next fuel' (step_cfg next s)
    //   = step_cfg next (exec_cfg next fuel' s). Inside `λ(next)λ(fuel)λ(fuel')∀ s`:
    //   s=0, fuel'=1, fuel=2, next=3.
    let motive = {
        let step_s = step_cfg_app(Expr::bvar(3), Expr::bvar(0));
        let lhs = exec_cfg_app(Expr::bvar(3), Expr::bvar(1), step_s);
        let loop_s = exec_cfg_app(Expr::bvar(3), Expr::bvar(1), Expr::bvar(0));
        let rhs = step_cfg_app(Expr::bvar(3), loop_s);
        let inner = Expr::pi(bd(), cfg_state_ty(), eq_cfg_state(lhs, rhs));
        Expr::lam(bd(), cst("Nat"), inner)
    };
    // zero_proof : ∀ s, exec_cfg next 0 (step_cfg next s) = step_cfg next (exec_cfg next 0 s)
    //   exec_cfg _ 0 ι-reduces to identity ⇒ LHS ≡ step_cfg next s, RHS ≡ step_cfg next s.
    //   ⇒ Eq.refl CfgState (step_cfg next s). Inside `λ(next)λ(fuel)λ(s)`: s=0,fuel=1,next=2.
    let zero_proof = {
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let step_s = step_cfg_app(Expr::bvar(2), Expr::bvar(0));
        Expr::lam(bd(), cfg_state_ty(), Expr::apps(eq_refl, [cfg_state_ty(), step_s]))
    };
    // succ_proof : λ(n)(ih)(s). ih (step_cfg next s)
    //   Inside `λ(next)λ(fuel)λ(n)λ(ih)λ(s)`: s=0, ih=1, n=2, fuel=3, next=4.
    let succ_proof = {
        let step_s = step_cfg_app(Expr::bvar(4), Expr::bvar(0));
        let ih_app = Expr::app(Expr::bvar(1), step_s);
        // ih's TYPE = motive n. Built after `λ(n)` (before `λ(ih)`):
        //   inside `λ(next)λ(fuel)λ(n)∀ s`: s=0, n=1, fuel=2, next=3.
        let ih_ty = {
            let step_s2 = step_cfg_app(Expr::bvar(3), Expr::bvar(0));
            let lhs = exec_cfg_app(Expr::bvar(3), Expr::bvar(1), step_s2);
            let loop_s = exec_cfg_app(Expr::bvar(3), Expr::bvar(1), Expr::bvar(0));
            let rhs = step_cfg_app(Expr::bvar(3), loop_s);
            Expr::pi(bd(), cfg_state_ty(), eq_cfg_state(lhs, rhs))
        };
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), ih_ty, Expr::lam(bd(), cfg_state_ty(), ih_app)))
    };
    // @Nat.rec.{0} motive zero succ fuel   (Prop motive ⇒ level 0). Inside `λ(next)λ(fuel)`: fuel=0.
    let nat_rec_prop = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_app = Expr::apps(nat_rec_prop, [motive, zero_proof, succ_proof, Expr::bvar(0)]);
    Expr::lam(bd(), cfg_next_ty(), Expr::lam(bd(), cst("Nat"), rec_app))
}

/// Register `Trust.MirSem.cfg_threaded : (Nat → Env → CfgState) → Nat → CfgState →
/// CfgState` (idempotent) = `λ next fuel s. exec_cfg next (succ fuel) s`.
pub(super) fn register_cfg_threaded(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CFG_THREADED);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    // λ(next).λ(fuel).λ(s). exec_cfg next (succ fuel) s   depth: s=0, fuel=1, next=2.
    let succ_fuel = Expr::app(nat_succ, Expr::bvar(1));
    let body = exec_cfg_app(Expr::bvar(2), succ_fuel, Expr::bvar(0));
    let val = Expr::lam(
        bd(),
        cfg_next_ty(),
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), cfg_state_ty(), body)),
    );
    let ty = Expr::pi(
        bd(),
        cfg_next_ty(),
        Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), cfg_state_ty(), cfg_state_ty())),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(cfg_threaded): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.cfg_substituted : (Nat → Env → CfgState) → Nat → CfgState →
/// CfgState` (idempotent) = `λ next fuel s. step_cfg next (exec_cfg next fuel s)`.
pub(super) fn register_cfg_substituted(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CFG_SUBST);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // λ(next).λ(fuel).λ(s). step_cfg next (exec_cfg next fuel s)   depth: s=0, fuel=1, next=2.
    let sub = exec_cfg_app(Expr::bvar(2), Expr::bvar(1), Expr::bvar(0));
    let body = step_cfg_app(Expr::bvar(2), sub);
    let val = Expr::lam(
        bd(),
        cfg_next_ty(),
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), cfg_state_ty(), body)),
    );
    let ty = Expr::pi(
        bd(),
        cfg_next_ty(),
        Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), cfg_state_ty(), cfg_state_ty())),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(cfg_substituted): {e:?}"))?;
    Ok(())
}

/// The CFG REFINEMENT theorem TYPE: `∀ (next)(fuel)(s),
/// cfg_threaded next fuel s = cfg_substituted next fuel s`. Inside `∀ next ∀ fuel ∀ s`:
/// s=0, fuel=1, next=2. `claimed_rhs` overrides the RHS (fail-closed hook).
pub(super) fn cfg_refinement_type(claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let args = [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)];
    let lhs = Expr::apps(cst(MIRSEM_CFG_THREADED), args.clone());
    let rhs = claimed_rhs.cloned().unwrap_or_else(|| Expr::apps(cst(MIRSEM_CFG_SUBST), args));
    let eq = eq_cfg_state(lhs, rhs);
    Expr::pi(bd(), cfg_next_ty(), Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), cfg_state_ty(), eq)))
}

/// The CFG REFINEMENT theorem PROOF: both whole-CFG denotations are
/// `exec_cfg`/`step_cfg` of a state; the equality `exec_cfg next (succ fuel) s =
/// step_cfg next (exec_cfg next fuel s)` IS `execCfgUnrollLaw` (because
/// `exec_cfg next (succ fuel) s` ι-reduces — front-peel — to
/// `exec_cfg next fuel (step_cfg next s)`, which the law equates to
/// `step_cfg next (exec_cfg next fuel s)`). So the law inhabits the refinement
/// up to def-eq directly. `λ(next)(fuel)(s). execCfgUnrollLaw next fuel s`.
pub(super) fn cfg_refinement_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // depth inside λ(next)λ(fuel)λ(s): s=0, fuel=1, next=2.
    // execCfgUnrollLaw next fuel s
    //   : exec_cfg next fuel (step_cfg next s) = step_cfg next (exec_cfg next fuel s).
    //   cfg_threaded next fuel s ι-reduces (exec_cfg (succ fuel) front-peel) to
    //   exec_cfg next fuel (step_cfg next s) = the law's LHS; cfg_substituted IS the RHS.
    let law =
        Expr::apps(cst(MIRSEM_EXEC_CFG_UNROLL_LAW), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        cfg_next_ty(),
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), cfg_state_ty(), law)),
    )
}

/// Register the full UNSTRUCTURED-CFG refinement chain into `env`: the `CfgState`
/// inductive, its two projections, `step_cfg`, `exec_cfg`, the two whole-CFG
/// denotations, the inductive unroll law, and the refinement theorem — all
/// kernel-checked, modulo 3. Idempotent.
pub(super) fn register_cfg_refinement(env: &mut Environment) -> Result<(), String> {
    register_cfg_state(env)?;
    register_cfg_pc(env)?;
    register_cfg_env(env)?;
    register_step_cfg(env)?;
    register_exec_cfg(env)?;
    register_cfg_threaded(env)?;
    register_cfg_substituted(env)?;
    // The inductive fuel-level unroll law (Nat.rec on fuel).
    let law_name = Name::from_string(MIRSEM_EXEC_CFG_UNROLL_LAW);
    if env.get_const(&law_name).is_none() {
        let law_ty = exec_cfg_unroll_law_type();
        let law_proof = exec_cfg_unroll_law_proof();
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&law_proof, &law_ty)
                .map_err(|e| format!("execCfgUnrollLaw check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem {
            name: law_name,
            level_params: vec![],
            type_: law_ty,
            value: law_proof,
        })
        .map_err(|e| format!("add_decl(execCfgUnrollLaw): {e:?}"))?;
    }
    // The refinement theorem (the unroll law, transported up to def-eq).
    let ref_name = Name::from_string(MIRSEM_CFG_REFINEMENT);
    if env.get_const(&ref_name).is_none() {
        let ref_ty = cfg_refinement_type(None);
        let ref_proof = cfg_refinement_proof();
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&ref_proof, &ref_ty)
                .map_err(|e| format!("cfgRefinement check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem {
            name: ref_name,
            level_params: vec![],
            type_: ref_ty,
            value: ref_proof,
        })
        .map_err(|e| format!("add_decl(cfgRefinement): {e:?}"))?;
    }
    Ok(())
}

// ===========================================================================
// Step 6X — THE UNBOUNDED IRREDUCIBLE-CFG TERMINATION rule via a CFG-state
// RANKING. Composes the well-founded Nat descent with CfgState/step_cfg/exec_cfg.
// ===========================================================================
/// The CFG ranking-function type `CfgState → Nat` — the well-founded measure the
/// termination rule is universal over (a real `CfgState → Nat` PARAMETER).
pub(super) fn cfg_rank_ty() -> Expr {
    Expr::pi(BinderData::from(BinderInfo::Default), cfg_state_ty(), cst("Nat"))
}

/// The CFG exit-predicate type `CfgState → Bool` — `at_exit s = true` ⇔ the run has
/// reached an exit/stable state (a `return`/sink terminator).
pub(super) fn cfg_at_exit_ty() -> Expr {
    Expr::pi(BinderData::from(BinderInfo::Default), cfg_state_ty(), cst("Bool"))
}

/// `at_exit s : Bool`.
pub(super) fn at_exit_app(ae: Expr, s: Expr) -> Expr {
    Expr::app(ae, s)
}

/// The CFG-HALTED predicate `at_exit (exec_cfg next fuel s) = true` — after `fuel`
/// terminator steps the run is at an exit/stable state. The CFG total-correctness
/// termination conclusion (the analog of `loop_halts_prop`).
pub(super) fn cfg_halts_prop(ae: Expr, next: Expr, fuel: Expr, s: Expr) -> Expr {
    let run = exec_cfg_app(next, fuel, s);
    eq_bool_true(at_exit_app(ae, run))
}

/// The CFG EXIT-STABILITY hypothesis `∀ (s : CfgState), at_exit s = true →
/// step_cfg next s = s` — exit states are FIXPOINTS of one terminator step.
/// `ae_ref`/`next_ref` denote `at_exit`/`next` at the depth this builder is called
/// (BEFORE the `∀ s`); they are lifted internally.
pub(super) fn cfg_stable_hyp_type(ae_ref: &Expr, next_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    // ∀ (s:CfgState), at_exit s = true → step_cfg next s = s
    //   dom (under ∀ s): s=0, refs +1.
    let dom = eq_bool_true(at_exit_app(lift(ae_ref, 1), Expr::bvar(0)));
    //   cod (under ∀ s + 1 arrow): s=1, refs +2.
    let step_s = step_cfg_app(lift(next_ref, 2), Expr::bvar(1));
    let cod = eq_cfg_state(step_s, Expr::bvar(1));
    Expr::pi(bd(), cfg_state_ty(), Expr::pi(bd(), dom, cod))
}

/// The CFG RANK-DECREASE hypothesis `∀ (s : CfgState), at_exit s = false →
/// Nat.lt (R (step_cfg next s)) (R s)` — the rank STRICTLY DROPS on every terminator
/// step while NOT at exit. `r_ref`/`ae_ref`/`next_ref` denote `R`/`at_exit`/`next` at
/// the depth this builder is called (BEFORE the `∀ s`); lifted internally.
pub(super) fn cfg_decrease_hyp_type(r_ref: &Expr, ae_ref: &Expr, next_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    // ∀ (s:CfgState), (at_exit s = false) → Nat.lt (R (step_cfg next s)) (R s)
    //   dom (under ∀ s): s=0, refs +1.
    let dom = eq_bool_false(at_exit_app(lift(ae_ref, 1), Expr::bvar(0)));
    //   cod (under ∀ s + 1 arrow): s=1, refs +2.
    let r_s = Expr::app(lift(r_ref, 2), Expr::bvar(1));
    let r_step = Expr::app(lift(r_ref, 2), step_cfg_app(lift(next_ref, 2), Expr::bvar(1)));
    let cod = nat_lt(r_step, r_s);
    Expr::pi(bd(), cfg_state_ty(), Expr::pi(bd(), dom, cod))
}

/// The CFG EXIT-STABILITY lemma TYPE. See [`MIRSEM_CFG_EXIT_STABLE`].
pub(super) fn cfg_exit_stable_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `∀ at_exit ∀ next`: next=0, at_exit=1.
    let stable = cfg_stable_hyp_type(&Expr::bvar(1), &Expr::bvar(0));
    // conclusion: ∀ k s, at_exit s = true → at_exit (exec_cfg next k s) = true
    //   inside `∀ at_exit ∀ next (stable→) ∀ k ∀ s`: s=0,k=1,stable=2,next=3,at_exit=4.
    let hs = eq_bool_true(at_exit_app(Expr::bvar(4), Expr::bvar(0)));
    // halts (under one more arrow): s=1,k=2,stable=3,next=4,at_exit=5.
    let halts = cfg_halts_prop(Expr::bvar(5), Expr::bvar(4), Expr::bvar(2), Expr::bvar(1));
    let arrow = Expr::pi(bd(), hs, halts);
    let body_s = Expr::pi(bd(), cfg_state_ty(), arrow);
    let body_k = Expr::pi(bd(), cst("Nat"), body_s);
    let after_stable = Expr::pi(bd(), stable, body_k);
    Expr::pi(bd(), cfg_at_exit_ty(), Expr::pi(bd(), cfg_next_ty(), after_stable))
}

/// The CFG EXIT-STABILITY lemma PROOF — `Nat.rec` on the fuel bound `k`. BASE
/// (`exec_cfg next 0 s ≡ s`): the hypothesis `hs`. STEP (`exec_cfg next (succ m) s ≡
/// exec_cfg next m (step_cfg next s)` front-peel): the `stable` hypothesis gives
/// `step_cfg next s = s`, transported via `Eq.rec` so the IH at `s` discharges.
pub(super) fn cfg_exit_stable_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // proof = λ at_exit next stable. @Nat.rec.{0} motive zero succ.
    //   motive/zero/succ built UNDER `λ at_exit λ next λ stable` (no λ k) ⇒ lift by 1;
    //   scrutinee k bound by the TYPE's `∀ k` ⇒ we η-bind k here.
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);

    // motive : Nat → Prop = λ k. ∀ s, at_exit s = true → at_exit (exec_cfg next k s) = true
    //   built UNDER `λ at_exit λ next λ stable` (no final λ k) ⇒ has its OWN `λ k`.
    //   under `..λ stable | λ k`: k=0,stable=1,next=2,at_exit=3; then `∀ s`: s=0,k=1,stable=2,next=3,at_exit=4.
    let motive = {
        let hs = eq_bool_true(at_exit_app(Expr::bvar(4), Expr::bvar(0)));
        // halts (under `∀ s` + the `hs →` arrow): s=1,k=2,stable=3,next=4,at_exit=5.
        let halts = cfg_halts_prop(Expr::bvar(5), Expr::bvar(4), Expr::bvar(2), Expr::bvar(1));
        Expr::lam(bd(), cst("Nat"), Expr::pi(bd(), cfg_state_ty(), Expr::pi(bd(), hs, halts)))
    };

    // zero_case : ∀ s, at_exit s = true → at_exit (exec_cfg next 0 s) = true
    //   exec_cfg next 0 s ≡ s ⇒ codomain ≡ (at_exit s = true) ⇒ λ s hs. hs.
    //   (no-λk) the `hs` DOMAIN sits under `λ at_exit λ next λ stable λ s` ⇒ s=0,stable=1,next=2,at_exit=3.
    let zero_case = {
        let hs_ty = eq_bool_true(at_exit_app(Expr::bvar(3), Expr::bvar(0)));
        Expr::lam(bd(), cfg_state_ty(), Expr::lam(bd(), hs_ty, Expr::bvar(0)))
    };

    // succ_case : λ (m:Nat)(ih : motive m)(s : CfgState)(hs : at_exit s = true).
    //   GOAL ≡ at_exit (exec_cfg next (succ m) s) = true
    //        ≡ at_exit (exec_cfg next m (step_cfg next s)) = true   (front-peel)
    //   From `stable s hs : step_cfg next s = s`, transport via @Eq.rec with motive
    //     M (x:CfgState)(_ : s = x) := at_exit (exec_cfg next m x) = true
    //   base M s ≡ at_exit (exec_cfg next m s) = true = ih s hs;
    //   result M (step_cfg next s) ≡ GOAL, transporting along Eq.symm (stable s hs).
    //   under `λ at_exit λ next λ stable λ m λ ih λ s λ hs`: hs=0,s=1,ih=2,m=3,stable=4,next=5,at_exit=6.
    let succ_case = {
        // ih : motive m  (after `λ m`, before `λ ih`): under `..λ stable λ m`: m=0,stable=1,next=2,at_exit=3.
        let ih_ty = {
            // ∀ s, at_exit s = true → at_exit (exec_cfg next m s) = true
            // under `∀ s`: s=0,m=1,stable=2,next=3,at_exit=4.
            let hs = eq_bool_true(at_exit_app(Expr::bvar(4), Expr::bvar(0)));
            // halts (under arrow): s=1,m=2,stable=3,next=4,at_exit=5.
            let halts = cfg_halts_prop(Expr::bvar(5), Expr::bvar(4), Expr::bvar(2), Expr::bvar(1));
            Expr::pi(bd(), cfg_state_ty(), Expr::pi(bd(), hs, halts))
        };

        // stable s hs : step_cfg next s = s   (at succ body depth: stable=4,s=1,hs=0)
        let stable_app = Expr::apps(Expr::bvar(4), [Expr::bvar(1), Expr::bvar(0)]);
        let step_s = step_cfg_app(Expr::bvar(5), Expr::bvar(1)); // step_cfg next s
        // Eq.symm {CfgState} {step_cfg next s} {s} stable_app : s = step_cfg next s
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]);
        let sym = Expr::apps(eq_symm, [cfg_state_ty(), step_s.clone(), Expr::bvar(1), stable_app]);
        // @Eq.rec.{0,1}: {α : Sort 1}{a : α}{M : (x:α)→a=x→Prop} → M a (refl) → {b:α} → (h:a=b) → M b h
        //   α := CfgState, a := s, b := step_cfg next s, h := sym.
        let eq_rec = Expr::const_(
            Name::from_string("Eq.rec"),
            vec![Level::zero(), Level::succ(Level::zero())],
        );
        // motive M : λ (x:CfgState)(_ : s = x). at_exit (exec_cfg next m x) = true
        //   under succ body (hs=0,s=1,ih=2,m=3,stable=4,next=5,at_exit=6) then `λ x λ heq`:
        //   heq=0,x=1,hs=2,s=3,ih=4,m=5,stable=6,next=7,at_exit=8.
        let m_motive = {
            // domain `s = x` (under `λ x` only): x=0, s=2 (s was 1, +1 for λx).
            let eq_dom = eq_cfg_state(Expr::bvar(2), Expr::bvar(0));
            // codomain (under `λ x λ heq`): x=1, m=5, next=7, at_exit=8.
            let run = exec_cfg_app(Expr::bvar(7), Expr::bvar(5), Expr::bvar(1));
            let cod = eq_bool_true(at_exit_app(Expr::bvar(8), run));
            Expr::lam(bd(), cfg_state_ty(), Expr::lam(bd(), eq_dom, cod))
        };
        // base : M s (refl) ≡ at_exit (exec_cfg next m s) = true = ih s hs
        //   at succ body depth: ih=2,s=1,hs=0.
        let base = Expr::apps(Expr::bvar(2), [Expr::bvar(1), Expr::bvar(0)]);
        let applied = Expr::apps(
            eq_rec,
            [
                cfg_state_ty(), // α
                Expr::bvar(1),  // a := s
                m_motive,       // M
                base,           // M s (refl)
                step_s,         // b := step_cfg next s
                sym,            // h : s = step_cfg next s
            ],
        );
        Expr::lam(
            bd(),
            cst("Nat"), // m
            Expr::lam(
                bd(),
                ih_ty, // ih
                Expr::lam(
                    bd(),
                    cfg_state_ty(), // s
                    Expr::lam(
                        bd(),
                        eq_bool_true(at_exit_app(Expr::bvar(5), Expr::bvar(0))), // hs : at_exit s = true (under `λ at_exit λ next λ stable | λ m λ ih λ s`: s=0,ih=1,m=2,stable=3,next=4,at_exit=5)
                        applied,
                    ),
                ),
            ),
        )
    };

    // λ at_exit next stable k. @Nat.rec.{0} motive zero succ k
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        cfg_at_exit_ty(),
        Expr::lam(
            bd(),
            cfg_next_ty(),
            Expr::lam(
                bd(),
                // stable hyp under `λ at_exit λ next`: next=0,at_exit=1.
                cfg_stable_hyp_type(&Expr::bvar(1), &Expr::bvar(0)),
                Expr::lam(bd(), cst("Nat"), rec_applied),
            ),
        ),
    )
}

/// Register `Trust.MirSem.cfgExitStable` (idempotent). Requires
/// `step_cfg`/`exec_cfg` registered.
pub(super) fn register_cfg_exit_stable(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CFG_EXIT_STABLE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = cfg_exit_stable_type();
    let val = cfg_exit_stable_proof();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty).map_err(|e| format!("cfgExitStable check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(cfgExitStable): {e:?}"))?;
    Ok(())
}

/// The CFG BOUNDED-HALT lemma TYPE. See [`MIRSEM_CFG_BOUNDED_HALT`].
pub(super) fn cfg_bounded_halt_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `∀ R ∀ at_exit ∀ next`: next=0,at_exit=1,R=2.
    let stable = cfg_stable_hyp_type(&Expr::bvar(1), &Expr::bvar(0));
    // decrease (under `stable→`): next=1,at_exit=2,R=3.
    let decrease = cfg_decrease_hyp_type(&Expr::bvar(3), &Expr::bvar(2), &Expr::bvar(1));
    // conclusion: ∀ k s, Nat.le (R s) k → at_exit (exec_cfg next k s) = true
    //   inside `∀ R ∀ at_exit ∀ next (stable→)(decrease→) ∀ k ∀ s`:
    //   s=0,k=1,decrease=2,stable=3,next=4,at_exit=5,R=6.
    let r_s = Expr::app(Expr::bvar(6), Expr::bvar(0));
    let le_hyp = nat_le(r_s, Expr::bvar(1));
    // halts (under one more arrow): s=1,k=2,decrease=3,stable=4,next=5,at_exit=6,R=7.
    let halts = cfg_halts_prop(Expr::bvar(6), Expr::bvar(5), Expr::bvar(2), Expr::bvar(1));
    let arrow = Expr::pi(bd(), le_hyp, halts);
    let body_s = Expr::pi(bd(), cfg_state_ty(), arrow);
    let body_k = Expr::pi(bd(), cst("Nat"), body_s);
    let after_decrease = Expr::pi(bd(), decrease, body_k);
    let after_stable = Expr::pi(bd(), stable, after_decrease);
    Expr::pi(
        bd(),
        cfg_rank_ty(),
        Expr::pi(bd(), cfg_at_exit_ty(), Expr::pi(bd(), cfg_next_ty(), after_stable)),
    )
}

/// The CFG BOUNDED-HALT lemma PROOF — well-founded descent by `Nat.rec` on the fuel
/// bound `k`, the CFG analog of `boundedHalt`. The Bool.rec on `at_exit s` splits:
/// the false arm (still running) uses `decrease` + `nat_le_trans` + the IH on
/// `step_cfg next s`; the true arm (halted) uses `cfgExitStable`.
pub(super) fn cfg_bounded_halt_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec0 = || Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let eq_refl_bool = |b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), b],
        )
    };

    // depth inside `λ R λ at_exit λ next λ stable λ decrease`: decrease=0,stable=1,next=2,at_exit=3,R=4.

    // motive P : Nat → Prop = λ k. ∀ s, Nat.le (R s) k → cfg_halts at_exit next k s
    //   under `λ R..λ decrease λ k`: k=0,decrease=1,stable=2,next=3,at_exit=4,R=5; then `∀ s`: s=0,k=1,decrease=2,stable=3,next=4,at_exit=5,R=6.
    let motive = {
        let r_s = Expr::app(Expr::bvar(6), Expr::bvar(0));
        let le_hyp = nat_le(r_s, Expr::bvar(1));
        // cfg_halts (under one more arrow): s=1,k=2,decrease=3,stable=4,next=5,at_exit=6,R=7
        let halts = cfg_halts_prop(Expr::bvar(6), Expr::bvar(5), Expr::bvar(2), Expr::bvar(1));
        let arrow = Expr::pi(bd(), le_hyp, halts);
        Expr::lam(bd(), cst("Nat"), Expr::pi(bd(), cfg_state_ty(), arrow))
    };

    // zero_case : ∀ s, Nat.le (R s) 0 → cfg_halts at_exit next 0 s
    //   cfg_halts at_exit next 0 s ≡ (at_exit s = true)  (exec_cfg next 0 s ≡ s).
    //   λ s (hk : Nat.le (R s) 0). @Bool.rec.{0} mg false_arm true_arm g (Eq.refl g)
    //   under `λ R..λ decrease λ s λ hk`: hk=0,s=1,decrease=2,stable=3,next=4,at_exit=5,R=6.
    let zero_case = {
        let guard = at_exit_app(Expr::bvar(5), Expr::bvar(1)); // g = at_exit s
        // mg : Bool → Prop = λ b. (g = b) → (at_exit s = true)
        //   under `..λ s λ hk λ b`: b=0,hk=1,s=2,decrease=3,stable=4,next=5,at_exit=6,R=7.
        let mg = {
            let g_inner = at_exit_app(Expr::bvar(6), Expr::bvar(2));
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), g_inner, Expr::bvar(0)],
            );
            // cod: at_exit s = true (under λ b + arrow): b=1,hk=2,s=3 ⇒ at_exit=7.
            let g_cod = at_exit_app(Expr::bvar(7), Expr::bvar(3));
            let cod = eq_bool_true(g_cod);
            Expr::lam(bd(), cst("Bool"), Expr::pi(bd(), eq_dom, cod))
        };
        // false_arm : (g = false) → (at_exit s = true)
        //   from hf:g=false (NOT at exit), decrease s hf : Nat.lt (R(step_cfg next s)) (R s)
        //     ≡ Nat.le (succ (R(step_cfg next s))) (R s);
        //   nat_le_trans (succ (R(step))) (R s) 0 (decrease s hf) hk : Nat.le (succ (R(step))) 0;
        //   Nat.not_succ_le_zero (R(step)) <that> : False; @False.elim (at_exit s = true) <False>.
        //   under `..λ s λ hk λ hf`: hf=0,hk=1,s=2,decrease=3,stable=4,next=5,at_exit=6,R=7.
        let false_arm = {
            // `λ hf` DOMAIN sits under `λ s λ hk` (BEFORE λ hf): s=1,at_exit=5 (hk=0,s=1,decrease=2,stable=3,next=4,at_exit=5,R=6).
            let g_dom = at_exit_app(Expr::bvar(5), Expr::bvar(1));
            let eq_false = eq_bool_false(g_dom);
            // body under `λ hf`: hf=0,hk=1,s=2,decrease=3,stable=4,next=5,at_exit=6,R=7.
            let step_s = step_cfg_app(Expr::bvar(5), Expr::bvar(2)); // step_cfg next s
            let r_step = Expr::app(Expr::bvar(7), step_s); // R (step_cfg next s)
            let r_s = Expr::app(Expr::bvar(7), Expr::bvar(2)); // R s
            // decrease s hf : Nat.lt (R step) (R s) ≡ Nat.le (succ (R step)) (R s)
            let dec_app = Expr::apps(Expr::bvar(3), [Expr::bvar(2), Expr::bvar(0)]);
            // nat_le_trans (succ r_step) (R s) 0 dec_app hk
            let trans = Expr::apps(
                cst(MIRSEM_NAT_LE_TRANS),
                [
                    nat_succ(r_step.clone()),
                    r_s,
                    Expr::nat_lit(0),
                    dec_app,
                    Expr::bvar(1), // hk
                ],
            );
            let false_pf = Expr::apps(
                Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
                [r_step, trans],
            );
            // @False.elim.{0} (at_exit s = true) false_pf
            let goal = eq_bool_true(at_exit_app(Expr::bvar(6), Expr::bvar(2)));
            let false_elim = Expr::apps(
                Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                [goal, false_pf],
            );
            Expr::lam(bd(), eq_false, false_elim)
        };
        // true_arm : (g = true) → (at_exit s = true) = λ ht. ht
        let true_arm = {
            let g_dom = at_exit_app(Expr::bvar(5), Expr::bvar(1));
            Expr::lam(bd(), eq_bool_true(g_dom), Expr::bvar(0))
        };
        let ghelper = Expr::apps(bool_rec0(), [mg, false_arm, true_arm, guard.clone()]);
        let applied = Expr::app(ghelper, eq_refl_bool(guard));
        // λ s (hk : Nat.le (R s) 0). applied
        //   hk : Nat.le (R s) 0  (under λ s: s=0,decrease=1,stable=2,next=3,at_exit=4,R=5)
        let hk_ty = nat_le(Expr::app(Expr::bvar(5), Expr::bvar(0)), Expr::nat_lit(0));
        Expr::lam(bd(), cfg_state_ty(), Expr::lam(bd(), hk_ty, applied))
    };

    // succ_case : λ (k':Nat)(ih : P k')(s : CfgState)(hk : Nat.le (R s) (succ k')).
    //   GOAL ≡ at_exit (exec_cfg next (succ k') s) = true
    //        ≡ at_exit (exec_cfg next k' (step_cfg next s)) = true   (front-peel)
    //   @Bool.rec.{0} mg false_arm true_arm g (Eq.refl g).
    //   under `λ R..λ decrease λ k' λ ih λ s λ hk`: hk=0,s=1,ih=2,k'=3,decrease=4,stable=5,next=6,at_exit=7,R=8.
    let succ_case = {
        // ih : P k'  (after `λ k'`, before `λ ih`): under `..λ decrease λ k'`: k'=0,decrease=1,stable=2,next=3,at_exit=4,R=5.
        let ih_ty = {
            // ∀ s, Nat.le (R s) k' → cfg_halts at_exit next k' s
            // under `∀ s`: s=0,k'=1,decrease=2,stable=3,next=4,at_exit=5,R=6
            let le_hyp = nat_le(Expr::app(Expr::bvar(6), Expr::bvar(0)), Expr::bvar(1));
            // cfg_halts (under arrow): s=1,k'=2,decrease=3,stable=4,next=5,at_exit=6,R=7
            let halts = cfg_halts_prop(Expr::bvar(6), Expr::bvar(5), Expr::bvar(2), Expr::bvar(1));
            Expr::pi(bd(), cfg_state_ty(), Expr::pi(bd(), le_hyp, halts))
        };

        let guard = at_exit_app(Expr::bvar(7), Expr::bvar(1)); // g = at_exit s (s=1,at_exit=7)

        // mg : Bool → Prop = λ b. (g = b) →
        //        at_exit (exec_cfg next k' (Bool.rec (λ_.CfgState) ??? )) — but the scrutinee here is
        //   the STATE we step from. The front-peeled goal `exec_cfg next k' (step_cfg next s)` does
        //   NOT branch on `b` directly; instead the two arms differ in WHICH lemma discharges. We
        //   generalise the GUARD itself so each arm gets the matching hypothesis:
        //     mg b := (g = b) → at_exit (exec_cfg next k' (step_cfg next s)) = true.
        //   (The codomain is the SAME front-peeled goal in both arms; `b` only feeds the arm its
        //   `g = false` / `g = true` hypothesis. Sound: each arm proves the SAME goal from its case.)
        //   under `..λ hk λ b`: b=0,hk=1,s=2,ih=3,k'=4,decrease=5,stable=6,next=7,at_exit=8,R=9.
        let mg = {
            let g_inner = at_exit_app(Expr::bvar(8), Expr::bvar(2));
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), g_inner, Expr::bvar(0)],
            );
            // cod (under λ b + arrow): b=1,hk=2,s=3,ih=4,k'=5,decrease=6,stable=7,next=8,at_exit=9,R=10.
            let step_s = step_cfg_app(Expr::bvar(8), Expr::bvar(3)); // step_cfg next s
            let cod = cfg_halts_prop(Expr::bvar(9), Expr::bvar(8), Expr::bvar(5), step_s);
            Expr::lam(bd(), cst("Bool"), Expr::pi(bd(), eq_dom, cod))
        };

        // false_arm : (g = false) → at_exit (exec_cfg next k' (step_cfg next s)) = true
        //   NOT at exit ⇒ decrease applies, IH at the STEPPED state `step_cfg next s`:
        //     decrease s hf : Nat.lt (R(step)) (R s) ≡ Nat.le (succ (R step)) (R s);
        //     nat_le_trans (succ (R step)) (R s) (succ k') (decrease s hf) hk : Nat.le (succ (R step)) (succ k');
        //     Nat.le_of_succ_le_succ (R step) k' <that> : Nat.le (R step) k';
        //     ih (step_cfg next s) <bound> : cfg_halts at_exit next k' (step_cfg next s).
        //   under `..λ hk λ hf`: hf=0,hk=1,s=2,ih=3,k'=4,decrease=5,stable=6,next=7,at_exit=8,R=9.
        let false_arm = {
            // The `λ hf` DOMAIN sits at succ-body depth (BEFORE λ hf): s=1,at_exit=7.
            let g_dom = at_exit_app(Expr::bvar(7), Expr::bvar(1));
            let dom_ty = eq_bool_false(g_dom);
            let step_s = step_cfg_app(Expr::bvar(7), Expr::bvar(2)); // step_cfg next s
            let r_step = Expr::app(Expr::bvar(9), step_s.clone()); // R (step_cfg next s)
            let r_s = Expr::app(Expr::bvar(9), Expr::bvar(2)); // R s
            let dec_app = Expr::apps(Expr::bvar(5), [Expr::bvar(2), Expr::bvar(0)]); // decrease s hf
            // nat_le_trans (succ r_step) (R s) (succ k') dec_app hk
            let trans = Expr::apps(
                cst(MIRSEM_NAT_LE_TRANS),
                [
                    nat_succ(r_step.clone()),
                    r_s,
                    nat_succ(Expr::bvar(4)), // succ k'
                    dec_app,
                    Expr::bvar(1), // hk
                ],
            );
            // Nat.le_of_succ_le_succ r_step k' trans : Nat.le r_step k'
            let bound = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
                [r_step, Expr::bvar(4), trans],
            );
            // ih (step_cfg next s) bound
            let ih_app = Expr::apps(Expr::bvar(3), [step_s, bound]);
            Expr::lam(bd(), dom_ty, ih_app)
        };

        // true_arm : (g = true) → at_exit (exec_cfg next k' (step_cfg next s)) = true
        //   AT exit ⇒ cfgExitStable: stable + (at_exit (step_cfg next s) = true) gives the run stays at exit.
        //   We need `at_exit (step_cfg next s) = true`. From `stable s ht' : step_cfg next s = s` and
        //   ht : at_exit s = true, transport ht along stable to get at_exit (step_cfg next s) = true.
        //   Then cfgExitStable at_exit next stable k' (step_cfg next s) <that>.
        //   under `..λ hk λ ht`: ht=0,hk=1,s=2,ih=3,k'=4,decrease=5,stable=6,next=7,at_exit=8,R=9.
        let true_arm = {
            // The `λ ht` DOMAIN sits at succ-body depth (BEFORE λ ht): s=1,at_exit=7.
            let g_dom = at_exit_app(Expr::bvar(7), Expr::bvar(1));
            let dom_ty = eq_bool_true(g_dom);
            // stable s ht : step_cfg next s = s   (stable=6,s=2,ht=0)
            let stable_app = Expr::apps(Expr::bvar(6), [Expr::bvar(2), Expr::bvar(0)]);
            let step_s = step_cfg_app(Expr::bvar(7), Expr::bvar(2)); // step_cfg next s
            // Transport `ht : at_exit s = true` to `at_exit (step_cfg next s) = true` via @Eq.rec on
            //   stable_app⁻¹ : s = step_cfg next s, motive N (x)(_:s=x) := at_exit x = true.
            let eq_symm =
                Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]);
            let sym =
                Expr::apps(eq_symm, [cfg_state_ty(), step_s.clone(), Expr::bvar(2), stable_app]); // s = step_cfg next s
            let eq_rec = Expr::const_(
                Name::from_string("Eq.rec"),
                vec![Level::zero(), Level::succ(Level::zero())],
            );
            // motive N : λ (x:CfgState)(_:s=x). at_exit x = true
            //   at the point we build N we are at true-arm depth (ht=0,s=2,...,at_exit=8).
            //   domain `s = x` sits under `λ x` ONLY: x=0, s=3.
            //   codomain `at_exit x = true` sits under `λ x λ heq`: heq=0,x=1, s=4, at_exit=10.
            let n_motive = {
                let eq_dom = eq_cfg_state(Expr::bvar(3), Expr::bvar(0)); // s = x  (s=3 under λx)
                let cod = eq_bool_true(at_exit_app(Expr::bvar(10), Expr::bvar(1))); // at_exit x = true
                Expr::lam(bd(), cfg_state_ty(), Expr::lam(bd(), eq_dom, cod))
            };
            // base : N s (refl) ≡ at_exit s = true = ht   (s=2,ht=0)
            let base = Expr::bvar(0); // ht
            let stepped_exit = Expr::apps(
                eq_rec,
                [
                    cfg_state_ty(), // α
                    Expr::bvar(2),  // a := s
                    n_motive,       // N
                    base,           // N s refl = ht
                    step_s.clone(), // b := step_cfg next s
                    sym,            // h : s = step_cfg next s
                ],
            ); // : at_exit (step_cfg next s) = true
            // cfgExitStable at_exit next stable k' (step_cfg next s) stepped_exit
            //   : at_exit (exec_cfg next k' (step_cfg next s)) = true
            let stable_pf = Expr::bvar(6); // stable
            let ces = Expr::apps(
                cst(MIRSEM_CFG_EXIT_STABLE),
                [
                    Expr::bvar(8), // at_exit
                    Expr::bvar(7), // next
                    stable_pf,     // stable
                    Expr::bvar(4), // k'
                    step_s,        // s := step_cfg next s
                    stepped_exit,  // at_exit (step_cfg next s) = true
                ],
            );
            Expr::lam(bd(), dom_ty, ces)
        };

        let ghelper = Expr::apps(bool_rec0(), [mg, false_arm, true_arm, guard.clone()]);
        let applied = Expr::app(ghelper, eq_refl_bool(guard));

        // λ k' (ih : P k') (s : CfgState) (hk : Nat.le (R s) (succ k')). applied
        //   hk under `λ k' λ ih λ s`: s=0,ih=1,k'=2,decrease=3,stable=4,next=5,at_exit=6,R=7.
        let hk_ty = nat_le(Expr::app(Expr::bvar(7), Expr::bvar(0)), nat_succ(Expr::bvar(2)));
        Expr::lam(
            bd(),
            cst("Nat"), // k'
            Expr::lam(
                bd(),
                ih_ty,                                                            // ih
                Expr::lam(bd(), cfg_state_ty(), Expr::lam(bd(), hk_ty, applied)), // s, hk
            ),
        )
    };

    // λ R at_exit next stable decrease k. @Nat.rec.{0} motive zero succ k
    //   motive/zero/succ built UNDER `λ decrease` (no λ k) ⇒ lift by 1; scrutinee k=0.
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        cfg_rank_ty(),
        Expr::lam(
            bd(),
            cfg_at_exit_ty(),
            Expr::lam(
                bd(),
                cfg_next_ty(),
                Expr::lam(
                    bd(),
                    // stable hyp under `λ R λ at_exit λ next`: next=0,at_exit=1,R=2.
                    cfg_stable_hyp_type(&Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(
                        bd(),
                        // decrease hyp under `λ R λ at_exit λ next λ stable`: next=1,at_exit=2,R=3.
                        cfg_decrease_hyp_type(&Expr::bvar(3), &Expr::bvar(2), &Expr::bvar(1)),
                        Expr::lam(bd(), cst("Nat"), rec_applied),
                    ),
                ),
            ),
        ),
    )
}

/// Register `Trust.MirSem.cfgBoundedHalt` (idempotent). Requires
/// `step_cfg`/`exec_cfg`/`cfgExitStable`/`nat_le_trans` registered.
pub(super) fn register_cfg_bounded_halt(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_CFG_BOUNDED_HALT);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = cfg_bounded_halt_type();
    let val = cfg_bounded_halt_proof();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty).map_err(|e| format!("cfgBoundedHalt check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(cfgBoundedHalt): {e:?}"))?;
    Ok(())
}

/// The UNBOUNDED-CFG TERMINATION rule TYPE. `claimed_concl_rank = Some(p)` overrides
/// the rank used in the CONCLUSION's fuel (fail-closed hook: a rank that does NOT
/// match the one the decrease hypothesis constrains — a non-decreasing / wrong
/// measure — must NOT prove). See [`MIRSEM_CFG_RANK_TERMINATES`].
pub(super) fn cfg_rank_terminates_type(claimed_concl_rank: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // inside `∀ R ∀ at_exit ∀ next`: next=0,at_exit=1,R=2.
    let stable = cfg_stable_hyp_type(&Expr::bvar(1), &Expr::bvar(0));
    // decrease (under `stable→`): next=1,at_exit=2,R=3.
    let decrease = cfg_decrease_hyp_type(&Expr::bvar(3), &Expr::bvar(2), &Expr::bvar(1));
    // conclusion: ∀ s, at_exit (exec_cfg next (R s) s) = true
    //   inside `∀ R ∀ at_exit ∀ next (stable→)(decrease→) ∀ s`:
    //   s=0,decrease=1,stable=2,next=3,at_exit=4,R=5.
    let rank = claimed_concl_rank
        .cloned()
        .map(|p| p.lift(6)) // supplied at OUTSIDE depth; lift past R,at_exit,next,stable,decrease,s
        .unwrap_or_else(|| Expr::bvar(5)); // the real R
    let fuel = Expr::app(rank, Expr::bvar(0)); // (R s)
    let halts = cfg_halts_prop(Expr::bvar(4), Expr::bvar(3), fuel, Expr::bvar(0));
    let body_s = Expr::pi(bd(), cfg_state_ty(), halts);
    let after_decrease = Expr::pi(bd(), decrease, body_s);
    let after_stable = Expr::pi(bd(), stable, after_decrease);
    Expr::pi(
        bd(),
        cfg_rank_ty(),
        Expr::pi(bd(), cfg_at_exit_ty(), Expr::pi(bd(), cfg_next_ty(), after_stable)),
    )
}

/// The UNBOUNDED-CFG TERMINATION rule PROOF: instantiate `cfgBoundedHalt`'s fuel
/// bound at the rank itself. `λ R at_exit next stable decrease s.
///   cfgBoundedHalt R at_exit next stable decrease (R s) s (Nat.le.refl (R s))`.
pub(super) fn cfg_rank_terminates_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // under `λ R λ at_exit λ next λ stable λ decrease λ s`: s=0,decrease=1,stable=2,next=3,at_exit=4,R=5.
    let r_s = Expr::app(Expr::bvar(5), Expr::bvar(0)); // R s
    let le_refl = Expr::apps(Expr::const_(Name::from_string("Nat.le.refl"), vec![]), [r_s.clone()]); // Nat.le.refl (R s) : Nat.le (R s) (R s)
    let cbh = Expr::apps(
        cst(MIRSEM_CFG_BOUNDED_HALT),
        [
            Expr::bvar(5), // R
            Expr::bvar(4), // at_exit
            Expr::bvar(3), // next
            Expr::bvar(2), // stable
            Expr::bvar(1), // decrease
            r_s,           // k := R s
            Expr::bvar(0), // s
            le_refl,       // Nat.le (R s) (R s)
        ],
    );
    Expr::lam(
        bd(),
        cfg_rank_ty(),
        Expr::lam(
            bd(),
            cfg_at_exit_ty(),
            Expr::lam(
                bd(),
                cfg_next_ty(),
                Expr::lam(
                    bd(),
                    cfg_stable_hyp_type(&Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(
                        bd(),
                        cfg_decrease_hyp_type(&Expr::bvar(3), &Expr::bvar(2), &Expr::bvar(1)),
                        Expr::lam(bd(), cfg_state_ty(), cbh),
                    ),
                ),
            ),
        ),
    )
}

/// Register the full UNBOUNDED-CFG TERMINATION chain into `env`: `cfgExitStable`,
/// `cfgBoundedHalt`, then `cfgRankTerminates` — all kernel-checked, modulo 3.
/// Idempotent. Requires the CFG refinement chain (CfgState/step_cfg/exec_cfg) and
/// `nat_le_trans` already registered.
pub(super) fn register_cfg_rank_terminates(env: &mut Environment) -> Result<(), String> {
    register_cfg_exit_stable(env)?;
    register_cfg_bounded_halt(env)?;
    let name = Name::from_string(MIRSEM_CFG_RANK_TERMINATES);
    if env.get_const(&name).is_none() {
        let ty = cfg_rank_terminates_type(None);
        let val = cfg_rank_terminates_proof();
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&val, &ty).map_err(|e| format!("cfgRankTerminates check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
            .map_err(|e| format!("add_decl(cfgRankTerminates): {e:?}"))?;
    }
    Ok(())
}
