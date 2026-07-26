// Loop semantics: fuel-indexed `exec_loop`, the unroll law, and the invariant
// rules for the plain, optional-statement and break-carrying loop forms. Fuel
// makes the interpreter total, so a loop that would diverge yields no
// conclusion rather than an unsound one.

use super::*;

// ===========================================================================
// Step 6L — THE LOOP REFINEMENT: loopRefinement (a bounded/fuel-indexed
// structured loop), the deepest modeled fragment.
//
// THE GAP THIS CLOSES (toward whole-program).
// Step 6's `refinement` covers the STRAIGHT-LINE SSA body; Step 6B's `refinementB`
// the single `SwitchInt` branch. A LOOP — a back-edge / multi-block fixpoint — was
// NOT modeled. This step pins a bounded `while cond { body }` IN CLEAN and proves
// the operational ≡ substitution refinement for it, by INDUCTION on a fuel count.
//
// THE MODEL (fuel-indexed, structurally recursive — NOT a general fixpoint).
//   * `stepLoop e := if eval_cond e cond then exec e body else e`  — one guarded
//      iteration (`Bool.rec` over the guard; `exec e body` threads the body once).
//   * `exec_loop e cond body fuel` — `stepLoop` iterated `fuel` times, FRONT-PEELing
//      the `Nat` via `Nat.rec` at an `Env → Env` motive (the CPS/fold trick `exec`
//      uses for `List`): base `e`, step `exec_loop (stepLoop e) cond body n`.
//   A general unbounded fixpoint `μ` would need domain theory (a least-fixed-point
//   / Knaster–Tarski or a well-founded termination argument) the CIC kernel cannot
//   host directly; the fuel index makes the loop a STRUCTURAL `Nat.rec`, kernel-OK.
//
// THE TWO DENOTATIONS (distinct functions — verified non-def-eq).
//   * `loop_threaded   e cond body fuel ret := eval (exec_loop e cond body (succ fuel)) ret`
//        OPERATIONAL: run `succ fuel` front-peeled guarded iterations, read return.
//   * `loop_substituted e cond body fuel ret := eval (stepLoop (exec_loop e cond body fuel)) ret`
//        SUBSTITUTION: run `fuel` iterations, substitute ONE more guarded step on
//        top, read return. The compositional form (one outer step over a sub-loop).
//   `loop_threaded` recurses on `succ fuel`; `loop_substituted` applies `stepLoop`
//   OUTSIDE a `fuel`-iteration. A bare `Eq.refl` does NOT prove them equal for a
//   VARIABLE `fuel` (tested) — the theorem requires the inductive proof.
//
// THE LOOP REFINEMENT THEOREM (kernel-proven, modulo 3, by Nat.rec induction).
//   loopRefinement : ∀ (e : Env)(cond : Cond)(body : List Stmt)(fuel : Nat)(ret : Operand),
//                      loop_threaded e cond body fuel ret = loop_substituted e cond body fuel ret
//   It is `congrArg (λ env. eval env ret)` over the FUEL-LEVEL unroll law
//   execLoopUnrollLaw : ∀ (fuel : Nat)(e : Env),
//                         exec_loop (stepLoop e) fuel = stepLoop (exec_loop e fuel)
//   (front-peel iterate = outer-peel iterate of `stepLoop`, the classic
//   `f (fⁿ x) = fⁿ (f x)`), proven by STRUCTURAL INDUCTION on `fuel` (`Nat.rec` at
//   a Prop motive):
//     * BASE (fuel = 0): `exec_loop (stepLoop e) 0 ≡ stepLoop e` and
//       `stepLoop (exec_loop e 0) ≡ stepLoop e` — both ι-reduce to `stepLoop e`,
//       closed by `Eq.refl`.
//     * STEP (fuel = succ n, IH : ∀ e, exec_loop (stepLoop e) n = stepLoop (exec_loop e n)):
//       LHS `exec_loop (stepLoop e) (succ n)` front-peel-reduces to
//       `exec_loop (stepLoop (stepLoop e)) n`; RHS `stepLoop (exec_loop e (succ n))`
//       to `stepLoop (exec_loop (stepLoop e) n)`. These are exactly `IH (stepLoop e)`
//       — the IH applied at the STEPPED env. So the step proof is `λ n ih e.
//       ih (stepLoop e)`: it genuinely USES the IH at a different env, the hallmark
//       of a real induction (never `Eq.refl`). [Mirror of the straight-line
//       `execAppendLaw`'s cons step `ih l2 (step e s)`.]
//
// HONEST SCOPE (what the loop theorem PROVES vs. DEFERS).
//   PROVEN: the bounded / FUEL-INDEXED structured loop — the operational front-peel
//   run of `succ fuel` guarded iterations EQUALS the substitution form (a sub-loop
//   of `fuel` iterations with one outer guarded step), for ALL `(e, cond, body,
//   fuel, ret)`, by genuine `Nat.rec` induction, modulo exactly 3 axioms. This is
//   the tractable bullet-4 loop step: a structured `while cond { body }` whose
//   iteration count is bounded by an explicit fuel.
//   DEFERRED (NOT claimed): (a) UNBOUNDED loops — arbitrary termination needs a
//   least-fixpoint / well-founded-invariant argument (domain theory) the fuel index
//   sidesteps; we do NOT prove `∃ fuel. exec_loop … = the real fixpoint`. (b) CALLS
//   — no inter-procedural env / call stack is modeled. (c) the loop BODY here is the
//   same straight-line `List Stmt` fragment Step 6 covers (nested loops/branches in
//   the body are not separately modeled). The theorem says nothing false about those
//   — they are simply outside the modeled `(cond, body, fuel)` shape.
/// Build `stepLoop e cond body = @Bool.rec.{1} (λ_:Bool. Env) e (exec e body)
/// (eval_cond e cond)` as a kernel term — ONE guarded loop iteration — where the
/// supplied refs denote the env/cond/body at the CURRENT binder depth. `e_ref` must
/// be repeatable (it appears three times); callers pass a closure-free `Expr` clone.
pub(super) fn step_loop_body(e_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [e_ref.clone(), cond_ref.clone()]);
    let exec_body = Expr::apps(cst(MIRSEM_EXEC), [e_ref.clone(), body_ref.clone()]);
    // Bool.rec.{1} (λ_.Env) (false ↦ e) (true ↦ exec e body) (eval_cond e cond)
    Expr::apps(bool_rec, [env_motive, e_ref.clone(), exec_body, guard])
}

/// `stepLoop cond body e` applied as a CONSTANT to (cond, body, e) refs — the
/// curried Trust.MirSem.stepLoop. (Argument order: `e`, then `cond`, then `body` —
/// matching the registered signature `Env → Cond → List Stmt → Env`.)
pub(super) fn step_loop_app(e_ref: Expr, cond_ref: Expr, body_ref: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_STEP_LOOP), [e_ref, cond_ref, body_ref])
}

/// Register `Trust.MirSem.stepLoop : Env → Cond → List Stmt → Env` (idempotent) =
/// `λ e cond body. if eval_cond e cond then exec e body else e`. See [`MIRSEM_STEP_LOOP`].
pub(super) fn register_step_loop(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_STEP_LOOP);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // λ(e:Env).λ(cond:Cond).λ(body:List Stmt). step  ; depth: body=0, cond=1, e=2.
    let body = step_loop_body(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(bd(), cst(MIRSEM_COND), Expr::lam(bd(), list_stmt.clone(), body)),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_stmt, env_ty())),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(stepLoop): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.exec_loop : Env → Cond → List Stmt → Nat → Env`
/// (idempotent), front-peeling the fuel via `Nat.rec` at an `Env → Env` motive:
///
/// ```text
/// exec_loop (e : Env) (cond : Cond) (body : List Stmt) : Nat → Env :=
///   fun fuel =>
///     (@Nat.rec (fun _ => Env → Env)
///        (fun e' => e')                                   -- 0    : id transformer
///        (fun (n : Nat) (ih : Env → Env) (e' : Env) =>    -- succ : ih (stepLoop e')
///           ih (stepLoop e' cond body))
///        fuel) e
/// ```
///
/// `exec_loop e cond body (succ n) ι-reduces to `exec_loop (stepLoop e cond body) cond body n`
/// (front-peel): the guarded body runs ONCE at the front, the remaining fuel folds
/// over the result. `Nat.rec`/`Bool.rec`/`exec`/`eval_cond` are prelude/Trust
/// DEFINITIONS, so it carries no non-foundational axiom. Requires `stepLoop` registered.
pub(super) fn register_exec_loop(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EXEC_LOOP);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    // @Nat.rec.{1} : motive lands in (Env → Env) : Type ⇒ Sort 1.
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    // motive : λ(_ : Nat) → (Env → Env)
    let motive = Expr::lam(bd(), cst("Nat"), env_to_env.clone());
    // zero case : λ(e' : Env). e'    (identity transformer)
    let zero_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));
    // succ case : λ(n:Nat). λ(ih:Env→Env). λ(e':Env). ih (stepLoop e' cond body)
    //   Under `λ(e).λ(cond).λ(body).λ(fuel)` (e=…) then inside λ(n)λ(ih)λ(e'):
    //   e' = bvar(0), ih = bvar(1), n = bvar(2), fuel = bvar(3), body = bvar(4),
    //   cond = bvar(5), e = bvar(6).
    let succ_case = {
        let step = step_loop_app(Expr::bvar(0), Expr::bvar(5), Expr::bvar(4));
        let ih_app = Expr::app(Expr::bvar(1), step);
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), ih_app)),
        )
    };
    // @Nat.rec.{1} motive zero_case succ_case fuel    (fuel = bvar(0) under the 4 binders)
    let rec_app = Expr::apps(nat_rec, [motive, zero_case, succ_case, Expr::bvar(0)]);
    // exec_loop e cond body fuel = (Nat.rec … fuel) e    (apply transformer to e = bvar 3)
    let applied = Expr::app(rec_app, Expr::bvar(3));
    // λ(e).λ(cond).λ(body).λ(fuel). applied
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(bd(), list_stmt.clone(), Expr::lam(bd(), cst("Nat"), applied)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(bd(), list_stmt, Expr::pi(bd(), cst("Nat"), env_ty())),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(exec_loop): {e:?}"))?;
    Ok(())
}

/// `exec_loop e cond body fuel` applied as a CONSTANT to its four refs.
pub(super) fn exec_loop_app(e_ref: Expr, cond_ref: Expr, body_ref: Expr, fuel_ref: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_EXEC_LOOP), [e_ref, cond_ref, body_ref, fuel_ref])
}

// ===========================================================================
// Step 6N — the NESTED-LOOP layer: `OStmt`/`execO` + the OUTER Hoare while-rule
// + the inner-loop UNTOUCHED-LOCAL lemma. ADDITIVE: a NEW outer-statement type and
// NEW `O`-suffixed definitions/theorems; `Stmt`/`exec`/`stepLoop`/`exec_loop`/
// `stepPreservesInv`/`loopInvariantRule` are UNTOUCHED (byte-identical), so every
// existing flat-body certificate stays def-eq.
// ===========================================================================
/// `List OStmt` — the outer loop-body list type.
pub(super) fn list_ostmt_ty() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), cst(MIRSEM_OSTMT))
}

/// Register the `Trust.MirSem.OStmt` inductive (idempotent) — the OUTER statement
/// language. Two constructors:
///   `Assign (idx : Nat)(rv : Rvalue) : OStmt`               -- a plain outer assignment
///   `Loop (cond : Cond)(body : List Stmt)(fuel : Nat) : OStmt` -- a FLAT inner loop
/// Both fields of `Loop` use ALREADY-DEFINED types (`Cond`, the flat `List Stmt`,
/// `Nat`), so `OStmt` is a plain (NON-nested, NON-mutual) inductive — its auto-derived
/// `OStmt.rec` is the simple single-motive recursor. Requires `Cond`/`Rvalue`/`Stmt`.
pub(super) fn register_ostmt_inductive(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_OSTMT);
    if env.get_inductive(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ostmt_ty = cst(MIRSEM_OSTMT);
    let assign_ctor = Constructor {
        name: Name::from_string(MIRSEM_OSTMT_ASSIGN),
        type_: Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), rvalue_ty(), ostmt_ty.clone())),
    };
    let loop_ctor = Constructor {
        name: Name::from_string(MIRSEM_OSTMT_LOOP),
        type_: Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(bd(), list_stmt_ty(), Expr::pi(bd(), cst("Nat"), ostmt_ty.clone())),
        ),
    };
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::type_(),
            constructors: vec![assign_ctor, loop_ctor],
        }],
    };
    env.add_inductive(decl).map_err(|e| format!("add_inductive(OStmt): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.execO : Env → List OStmt → Env` (idempotent), the
/// `exec`-analogue over `List OStmt`:
///
/// ```text
/// execO (e : Env) : List OStmt → Env :=
///   @List.rec OStmt (fun _ => Env → Env)
///     (fun e' => e')                                           -- nil : id
///     (fun (s : OStmt) (rest : List OStmt) (ih : Env → Env) (e' : Env) =>
///        ih (@OStmt.rec (fun _ => Env)
///              (fun (i : Nat)(R : Rvalue) => set e' i (eval_rvalue e' R))      -- Assign
///              (fun (c : Cond)(b : List Stmt)(f : Nat) => exec_loop e' c b f)  -- Loop
///              s))
///     stmts e
/// ```
///
/// Identical env-threading fold to `exec`; the `Assign` arm is the SAME `set …
/// (eval_rvalue …)`, the new `Loop` arm runs the inner loop to completion via the
/// EXISTING `exec_loop`. Requires `OStmt`/`set`/`eval_rvalue`/`exec_loop` registered.
pub(super) fn register_exec_o(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EXEC_O);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let ostmt_ty = cst(MIRSEM_OSTMT);
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    let list_ostmt = list_ostmt_ty();
    let ty = Expr::pi(bd(), env_ty(), Expr::pi(bd(), list_ostmt.clone(), env_ty()));

    // @List.rec.{1,0} : levels [motiveLevel=1 (Env→Env : Sort 1), elemUniv=0].
    let list_rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    // @OStmt.rec.{1} : motive lands in Env : Type ⇒ Sort 1.
    let ostmt_rec =
        Expr::const_(Name::from_string(MIRSEM_OSTMT_REC), vec![Level::succ(Level::zero())]);
    let set = cst(MIRSEM_SET);
    let eval_rvalue = cst(MIRSEM_EVAL_RVALUE);

    // motive : λ(_ : List OStmt) → (Env → Env)
    let motive = Expr::lam(bd(), list_ostmt.clone(), env_to_env.clone());
    // nil case : λ(e' : Env). e'
    let nil_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));

    // cons case : λ(s:OStmt). λ(rest:List OStmt). λ(ih:Env→Env). λ(e':Env). ih (stepO e' s)
    //   de-Bruijn at the body: e' = bvar(0), ih = bvar(1), rest = bvar(2), s = bvar(3).
    let cons_case = {
        let ostmt_motive = Expr::lam(bd(), ostmt_ty.clone(), env_ty());
        // Assign minor: λ(i:Nat). λ(R:Rvalue). set e' i (eval_rvalue e' R)
        //   under i, R: R=0, i=1, e'=2 (lifted past i,R), ih=3, rest=4, s=5.
        let assign_minor = {
            let e_inner = Expr::bvar(2);
            let i_inner = Expr::bvar(1);
            let r_inner = Expr::bvar(0);
            let evald = Expr::apps(eval_rvalue.clone(), [e_inner.clone(), r_inner]);
            let set_app = Expr::apps(set.clone(), [e_inner, i_inner, evald]);
            Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), rvalue_ty(), set_app))
        };
        // Loop minor: λ(c:Cond). λ(b:List Stmt). λ(f:Nat). exec_loop e' c b f
        //   under c, b, f: f=0, b=1, c=2, e'=3 (lifted past c,b,f), ih=4, rest=5, s=6.
        let loop_minor = {
            let e_inner = Expr::bvar(3);
            let c_inner = Expr::bvar(2);
            let b_inner = Expr::bvar(1);
            let f_inner = Expr::bvar(0);
            let looped = exec_loop_app(e_inner, c_inner, b_inner, f_inner);
            Expr::lam(
                bd(),
                cst(MIRSEM_COND),
                Expr::lam(bd(), list_stmt_ty(), Expr::lam(bd(), cst("Nat"), looped)),
            )
        };
        // @OStmt.rec.{1} motive assign_minor loop_minor s   (s = bvar(3) before e' binder)
        let s_ref = Expr::bvar(3);
        let step = Expr::apps(ostmt_rec, [ostmt_motive, assign_minor, loop_minor, s_ref]);
        let ih_ref = Expr::bvar(1);
        let body = Expr::app(ih_ref, step);
        Expr::lam(
            bd(),
            ostmt_ty.clone(),
            Expr::lam(
                bd(),
                list_ostmt.clone(),
                Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), body)),
            ),
        )
    };

    // @List.rec.{1,0} OStmt motive nil_case cons_case stmts e
    //   under `λ(e:Env). λ(stmts:List OStmt). …` : stmts = bvar(0), e = bvar(1).
    let rec_app =
        Expr::apps(list_rec, [ostmt_ty.clone(), motive, nil_case, cons_case, Expr::bvar(0)]);
    let applied = Expr::app(rec_app, Expr::bvar(1));
    let val = Expr::lam(bd(), env_ty(), Expr::lam(bd(), list_ostmt, applied));

    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(execO): {e:?}"))?;
    Ok(())
}

/// `stepLoopO`'s body = `Bool.rec (λ_.Env) e (execO e body) (eval_cond e cond)`.
pub(super) fn step_loop_o_body(e_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [e_ref.clone(), cond_ref.clone()]);
    let exec_body = Expr::apps(cst(MIRSEM_EXEC_O), [e_ref.clone(), body_ref.clone()]);
    Expr::apps(bool_rec, [env_motive, e_ref.clone(), exec_body, guard])
}

/// `stepLoopO e cond body` applied as a CONSTANT (signature `Env → Cond → List OStmt → Env`).
pub(super) fn step_loop_o_app(e_ref: Expr, cond_ref: Expr, body_ref: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_STEP_LOOP_O), [e_ref, cond_ref, body_ref])
}

/// Register `Trust.MirSem.stepLoopO : Env → Cond → List OStmt → Env` (idempotent) =
/// `λ e cond body. if eval_cond e cond then execO e body else e`.
pub(super) fn register_step_loop_o(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_STEP_LOOP_O);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_ostmt = list_ostmt_ty();
    let body = step_loop_o_body(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(bd(), cst(MIRSEM_COND), Expr::lam(bd(), list_ostmt.clone(), body)),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_ostmt, env_ty())),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(stepLoopO): {e:?}"))?;
    Ok(())
}

/// `exec_loopO e cond body fuel` applied as a CONSTANT to its four refs.
pub(super) fn exec_loop_o_app(e_ref: Expr, cond_ref: Expr, body_ref: Expr, fuel_ref: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_EXEC_LOOP_O), [e_ref, cond_ref, body_ref, fuel_ref])
}

/// Register `Trust.MirSem.exec_loopO : Env → Cond → List OStmt → Nat → Env`
/// (idempotent), the `exec_loop`-analogue over `stepLoopO`. Front-peels via `Nat.rec`.
pub(super) fn register_exec_loop_o(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EXEC_LOOP_O);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_ostmt = list_ostmt_ty();
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Nat"), env_to_env.clone());
    let zero_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));
    // succ: λ(n)λ(ih)λ(e'). ih (stepLoopO e' cond body)
    //   e'=0, ih=1, n=2, fuel=3, body=4, cond=5, e=6.
    let succ_case = {
        let step = step_loop_o_app(Expr::bvar(0), Expr::bvar(5), Expr::bvar(4));
        let ih_app = Expr::app(Expr::bvar(1), step);
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), ih_app)),
        )
    };
    let rec_app = Expr::apps(nat_rec, [motive, zero_case, succ_case, Expr::bvar(0)]);
    let applied = Expr::app(rec_app, Expr::bvar(3));
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(bd(), list_ostmt.clone(), Expr::lam(bd(), cst("Nat"), applied)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(bd(), list_ostmt, Expr::pi(bd(), cst("Nat"), env_ty())),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(exec_loopO): {e:?}"))?;
    Ok(())
}

/// The OUTER preservation hypothesis `∀ e, I e → eval_cond e cond = true → I (execO e body)`
/// — the `preservation_hyp_type` analogue with `exec` ↦ `execO` and `List Stmt` body.
pub(super) fn preservation_hyp_type_o(i_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    let dom1 = Expr::app(lift(i_ref, 1), Expr::bvar(0));
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), lift(cond_ref, 2)]);
    let dom2 = eq_bool_true(guard);
    let exec_body = Expr::apps(cst(MIRSEM_EXEC_O), [Expr::bvar(2), lift(body_ref, 3)]);
    let cod = Expr::app(lift(i_ref, 3), exec_body);
    let arrows = Expr::pi(bd(), dom1, Expr::pi(bd(), dom2, cod));
    Expr::pi(bd(), env_ty(), arrows)
}

/// Register `Trust.MirSem.stepPreservesInvO` (idempotent) — the OUTER guarded-step
/// invariant-preservation lemma (the `stepPreservesInv` analogue over `execO`/`stepLoopO`).
pub(super) fn register_step_preserves_inv_o(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_STEP_PRESERVES_INV_O);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_ostmt = list_ostmt_ty();

    // TYPE: ∀ I cond body, pres → ∀ e, I e → I (stepLoopO e cond body)
    let ty = {
        let pres = preservation_hyp_type_o(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
        let i_e = Expr::app(Expr::bvar(4), Expr::bvar(0));
        let step = step_loop_o_app(Expr::bvar(1), Expr::bvar(4), Expr::bvar(3));
        let i_step = Expr::app(Expr::bvar(5), step);
        let concl = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, i_step));
        let after_pres = Expr::pi(bd(), pres, concl);
        Expr::pi(
            bd(),
            env_pred_ty(),
            Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_ostmt.clone(), after_pres)),
        )
    };

    // PROOF: same generalised-guard Bool.rec case-split, with exec ↦ execO.
    let val = {
        let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
        let motive_g = {
            let guard_b = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(2), Expr::bvar(5)]);
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_b, Expr::bvar(0)],
            );
            let bool_rec1 =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
            let exec_body = Expr::apps(cst(MIRSEM_EXEC_O), [Expr::bvar(3), Expr::bvar(5)]);
            let stepped =
                Expr::apps(bool_rec1, [env_motive, Expr::bvar(3), exec_body, Expr::bvar(1)]);
            let cod = Expr::app(Expr::bvar(7), stepped);
            let arrow = Expr::pi(bd(), eq_dom, cod);
            Expr::lam(bd(), cst("Bool"), arrow)
        };
        let false_case = {
            let guard_f = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
            let eq_false = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_f, cst("Bool.false")],
            );
            Expr::lam(bd(), eq_false, Expr::bvar(1))
        };
        let true_case = {
            let guard_t = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
            let eq_true = eq_bool_true(guard_t);
            let app = Expr::apps(Expr::bvar(3), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
            Expr::lam(bd(), eq_true, app)
        };
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let ghelper = Expr::apps(bool_rec0, [motive_g, false_case, true_case, guard.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let refl = Expr::apps(eq_refl, [cst("Bool"), guard]);
        let applied = Expr::app(ghelper, refl);
        Expr::lam(
            bd(),
            env_pred_ty(),
            Expr::lam(
                bd(),
                cst(MIRSEM_COND),
                Expr::lam(
                    bd(),
                    list_ostmt.clone(),
                    Expr::lam(
                        bd(),
                        preservation_hyp_type_o(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                        Expr::lam(
                            bd(),
                            env_ty(),
                            Expr::lam(bd(), Expr::app(Expr::bvar(4), Expr::bvar(0)), applied),
                        ),
                    ),
                ),
            ),
        )
    };

    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty).map_err(|e| format!("stepPreservesInvO check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(stepPreservesInvO): {e:?}"))?;
    Ok(())
}

/// The OUTER Hoare while-rule TYPE: `∀ I cond body, pres → ∀ n e, I e →
/// I (exec_loopO e cond body n)`. The `loop_invariant_rule_type` analogue.
pub(super) fn loop_invariant_rule_o_type(claimed_concl_pred: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_ostmt = list_ostmt_ty();
    let pres = preservation_hyp_type_o(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    let i_e = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(5));
        Expr::app(pred, Expr::bvar(0))
    };
    let looped = exec_loop_o_app(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
    let i_loop = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(6));
        let pred = if claimed_concl_pred.is_some() { pred.lift(1) } else { pred };
        Expr::app(pred, looped)
    };
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    let body_n = Expr::pi(bd(), cst("Nat"), body_e);
    let after_pres = Expr::pi(bd(), pres, body_n);
    Expr::pi(
        bd(),
        env_pred_ty(),
        Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_ostmt, after_pres)),
    )
}

/// The OUTER Hoare while-rule PROOF, by `Nat.rec` on the fuel, the
/// `loop_invariant_rule_proof` analogue (exec ↦ execO, stepLoop ↦ stepLoopO,
/// stepPreservesInv ↦ stepPreservesInvO, exec_loop ↦ exec_loopO).
pub(super) fn loop_invariant_rule_o_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_ostmt = list_ostmt_ty();
    let motive = {
        let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        let looped = exec_loop_o_app(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
        let i_loop = Expr::app(Expr::bvar(6), looped);
        let arrow = Expr::pi(bd(), i_e, i_loop);
        let quant_e = Expr::pi(bd(), env_ty(), arrow);
        Expr::lam(bd(), cst("Nat"), quant_e)
    };
    let zero_case = {
        let i_e = Expr::app(Expr::bvar(4), Expr::bvar(0));
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::bvar(0)))
    };
    let succ_case = {
        let ih_ty = {
            let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
            let looped =
                exec_loop_o_app(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
            let i_loop = Expr::app(Expr::bvar(6), looped);
            let arrow = Expr::pi(bd(), i_e, i_loop);
            Expr::pi(bd(), env_ty(), arrow)
        };
        let step = step_loop_o_app(Expr::bvar(1), Expr::bvar(6), Expr::bvar(5));
        let preserves = Expr::apps(
            cst(MIRSEM_STEP_PRESERVES_INV_O),
            [
                Expr::bvar(7),
                Expr::bvar(6),
                Expr::bvar(5),
                Expr::bvar(4),
                Expr::bvar(1),
                Expr::bvar(0),
            ],
        );
        let ih_app = Expr::apps(Expr::bvar(2), [step, preserves]);
        let i_e_hi = Expr::app(Expr::bvar(6), Expr::bvar(0));
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), ih_ty, Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_hi, ih_app))),
        )
    };
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        env_pred_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                list_ostmt,
                Expr::lam(
                    bd(),
                    preservation_hyp_type_o(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(bd(), cst("Nat"), rec_applied),
                ),
            ),
        ),
    )
}

/// Register `Trust.MirSem.loopInvariantRuleO` (idempotent) — the OUTER Hoare
/// while-rule (PARTIAL correctness over `List OStmt` bodies). Requires `execO`/
/// `stepLoopO`/`exec_loopO`/`stepPreservesInvO`.
pub(super) fn register_loop_invariant_rule_o(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_LOOP_INVARIANT_RULE_O);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = loop_invariant_rule_o_type(None);
    let val = loop_invariant_rule_o_proof();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty).map_err(|e| format!("loopInvariantRuleO check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(loopInvariantRuleO): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.loop_threaded : Env → Cond → List Stmt → Nat → Operand →
/// Int` (idempotent) = `λ e cond body fuel ret. eval (exec_loop e cond body (succ fuel)) ret`.
pub(super) fn register_loop_threaded(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_LOOP_THREADED);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    // λ(e).λ(cond).λ(body).λ(fuel).λ(ret). … depth: ret=0, fuel=1, body=2, cond=3, e=4.
    let succ_fuel = Expr::app(nat_succ, Expr::bvar(1));
    let looped = exec_loop_app(Expr::bvar(4), Expr::bvar(3), Expr::bvar(2), succ_fuel);
    let body = Expr::apps(cst(MIRSEM_EVAL), [looped, Expr::bvar(0)]);
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                list_stmt.clone(),
                Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), operand_ty(), body)),
            ),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(
                bd(),
                list_stmt,
                Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), operand_ty(), int_ty())),
            ),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(loop_threaded): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.loop_substituted : Env → Cond → List Stmt → Nat → Operand
/// → Int` (idempotent) = `λ e cond body fuel ret.
/// eval (stepLoop (exec_loop e cond body fuel) cond body) ret`.
pub(super) fn register_loop_substituted(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_LOOP_SUBST);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // λ(e).λ(cond).λ(body).λ(fuel).λ(ret). … depth: ret=0, fuel=1, body=2, cond=3, e=4.
    let sub_loop = exec_loop_app(Expr::bvar(4), Expr::bvar(3), Expr::bvar(2), Expr::bvar(1));
    let stepped = step_loop_app(sub_loop, Expr::bvar(3), Expr::bvar(2));
    let body = Expr::apps(cst(MIRSEM_EVAL), [stepped, Expr::bvar(0)]);
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                list_stmt.clone(),
                Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), operand_ty(), body)),
            ),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(
                bd(),
                list_stmt,
                Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), operand_ty(), int_ty())),
            ),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(loop_substituted): {e:?}"))?;
    Ok(())
}

/// The fuel-level LOOP UNROLL law TYPE: `∀ (fuel : Nat)(e : Env),
/// exec_loop (stepLoop e cond body) cond body fuel
///   = stepLoop (exec_loop e cond body fuel) cond body`.
/// `cond`/`body` are FIXED free parameters (de-Bruijn `cond = cf+1`, `body = cf`
/// counted from the binder context the law is built in). Here, inside the two law
/// binders, `e = bvar(0)`, `fuel = bvar(1)`, and `cond`/`body` are the next two
/// indices ABOVE (the law is registered under a `λ(cond)λ(body)` context in
/// `mirsem_loop_refinement_env`). To keep the law CLOSED over `cond`/`body` we
/// quantify them too: `∀ (cond)(body)(fuel)(e)`. Inside: e=0, fuel=1, body=2, cond=3.
pub(super) fn exec_loop_unroll_law_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // inside ∀cond ∀body ∀fuel ∀e : e=0, fuel=1, body=2, cond=3.
    let step_e = step_loop_app(Expr::bvar(0), Expr::bvar(3), Expr::bvar(2));
    let lhs = exec_loop_app(step_e, Expr::bvar(3), Expr::bvar(2), Expr::bvar(1));
    let loop_e = exec_loop_app(Expr::bvar(0), Expr::bvar(3), Expr::bvar(2), Expr::bvar(1));
    let rhs = step_loop_app(loop_e, Expr::bvar(3), Expr::bvar(2));
    let eq = eq_env_expr(lhs, rhs);
    // ∀ e
    let body_e = Expr::pi(bd(), env_ty(), eq);
    // ∀ fuel
    let body_fuel = Expr::pi(bd(), cst("Nat"), body_e);
    // ∀ body
    let body_body = Expr::pi(bd(), list_stmt, body_fuel);
    // ∀ cond
    Expr::pi(bd(), cst(MIRSEM_COND), body_body)
}

/// The fuel-level LOOP UNROLL law PROOF, by `Nat.rec` induction on `fuel`:
/// `λ(cond)(body)(fuel). @Nat.rec.{0} (motive) zero_proof succ_proof fuel`, where
/// the Prop motive `P fuel := ∀ e, exec_loop (stepLoop e) fuel = stepLoop (exec_loop
/// e fuel)`. BASE: both sides ι-reduce to `stepLoop e` ⇒ `Eq.refl`. STEP:
/// `λ n ih e. ih (stepLoop e)` — the IH applied at the STEPPED env (genuine induction).
pub(super) fn exec_loop_unroll_law_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // The proof is `λ(cond)λ(body)λ(fuel). Nat.rec motive zero_proof succ_proof fuel`.
    // EVERY sub-term (motive/zero/succ) sits UNDER those three proof binders, so the
    // proof's free `cond`/`body`/`fuel` are offset by the proof's binders that
    // enclose the sub-term IN ADDITION to the sub-term's own local binders.
    //
    // motive : Nat → Prop  = `λ(fuel'). ∀ e, exec_loop (stepLoop e) fuel'
    //   = stepLoop (exec_loop e fuel')`. Inside `λ(cond)λ(body)λ(fuel)` then the
    //   motive's own `λ(fuel')` then `∀ e`: e=0, fuel'=1, fuel=2, body=3, cond=4.
    //   (the eq references the motive's recursion var fuel'=1, NOT the proof's fuel).
    let motive = {
        let step_e = step_loop_app(Expr::bvar(0), Expr::bvar(4), Expr::bvar(3));
        let lhs = exec_loop_app(step_e, Expr::bvar(4), Expr::bvar(3), Expr::bvar(1));
        let loop_e = exec_loop_app(Expr::bvar(0), Expr::bvar(4), Expr::bvar(3), Expr::bvar(1));
        let rhs = step_loop_app(loop_e, Expr::bvar(4), Expr::bvar(3));
        let inner = Expr::pi(bd(), env_ty(), eq_env_expr(lhs, rhs));
        Expr::lam(bd(), cst("Nat"), inner)
    };

    // zero_proof : ∀ e, exec_loop (stepLoop e) 0 = stepLoop (exec_loop e 0)
    //   exec_loop _ 0 ι-reduces to identity ⇒ LHS ≡ stepLoop e, RHS ≡ stepLoop e.
    //   ⇒ Eq.refl Env (stepLoop e). Inside `λ(cond)λ(body)λ(fuel)λ(e)`:
    //   e=0, fuel=1, body=2, cond=3.
    let zero_proof = {
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let step_e = step_loop_app(Expr::bvar(0), Expr::bvar(3), Expr::bvar(2));
        Expr::lam(bd(), env_ty(), Expr::apps(eq_refl, [env_ty(), step_e]))
    };

    // succ_proof : λ(n)(ih)(e). ih (stepLoop e)
    //   Inside `λ(cond)λ(body)λ(fuel)λ(n)λ(ih)λ(e)`: e=0, ih=1, n=2, fuel=3, body=4, cond=5.
    //   ih : motive n = ∀ e, exec_loop (stepLoop e) n = stepLoop (exec_loop e n).
    let succ_proof = {
        let step_e = step_loop_app(Expr::bvar(0), Expr::bvar(5), Expr::bvar(4));
        let ih_app = Expr::app(Expr::bvar(1), step_e);
        // ih's TYPE annotation = motive n. Built after `λ(n)` (before `λ(ih)`):
        //   inside `λ(cond)λ(body)λ(fuel)λ(n)` then `∀ e`: e=0, n=1, fuel=2, body=3, cond=4.
        let ih_ty = {
            let step_e2 = step_loop_app(Expr::bvar(0), Expr::bvar(4), Expr::bvar(3));
            let lhs = exec_loop_app(step_e2, Expr::bvar(4), Expr::bvar(3), Expr::bvar(1));
            let loop_e = exec_loop_app(Expr::bvar(0), Expr::bvar(4), Expr::bvar(3), Expr::bvar(1));
            let rhs = step_loop_app(loop_e, Expr::bvar(4), Expr::bvar(3));
            Expr::pi(bd(), env_ty(), eq_env_expr(lhs, rhs))
        };
        Expr::lam(
            bd(),
            cst("Nat"), // n
            Expr::lam(
                bd(),
                ih_ty,                             // ih : motive n
                Expr::lam(bd(), env_ty(), ih_app), // e
            ),
        )
    };

    // @Nat.rec.{0} motive zero_proof succ_proof fuel    (Prop motive ⇒ level 0).
    let nat_rec_prop = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    // Inside `λ(cond)λ(body)λ(fuel)`: fuel = bvar(0).
    let rec_app = Expr::apps(nat_rec_prop, [motive, zero_proof, succ_proof, Expr::bvar(0)]);
    Expr::lam(
        bd(),
        cst(MIRSEM_COND),
        Expr::lam(bd(), list_stmt, Expr::lam(bd(), cst("Nat"), rec_app)),
    )
}

/// The LOOP REFINEMENT theorem TYPE: `∀ (e : Env)(cond : Cond)(body : List Stmt)
/// (fuel : Nat)(ret : Operand), loop_threaded e cond body fuel ret =
/// loop_substituted e cond body fuel ret`. Inside the five binders:
/// `ret=0, fuel=1, body=2, cond=3, e=4`. `claimed` overrides the RHS (fail-closed hook).
pub(super) fn loop_refinement_type(claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let args = [Expr::bvar(4), Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)];
    let lhs = Expr::apps(cst(MIRSEM_LOOP_THREADED), args.clone());
    let rhs = claimed_rhs.cloned().unwrap_or_else(|| Expr::apps(cst(MIRSEM_LOOP_SUBST), args));
    let body = eq_int_expr(lhs, rhs);
    Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(
                bd(),
                list_stmt,
                Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), operand_ty(), body)),
            ),
        ),
    )
}

/// The LOOP REFINEMENT theorem PROOF: `λ(e)(cond)(body)(fuel)(ret). congrArg.{1,1}
/// Env Int (exec_loop e cond body (succ fuel)) (stepLoop (exec_loop e cond body fuel))
/// (λ env. eval env ret) (execLoopUnrollLaw cond body fuel e)`. Both whole-loop
/// denotations are `eval _ ret` of an env; the env equality
/// `exec_loop e (succ fuel) = stepLoop (exec_loop e fuel)` IS `execLoopUnrollLaw`
/// (because `exec_loop e (succ fuel)` ι-reduces — front-peel — to
/// `exec_loop (stepLoop e) fuel`, which the law equates to `stepLoop (exec_loop e fuel)`).
/// `congrArg (eval · ret)` transports it to the `Int` equality
/// `loop_threaded = loop_substituted`.
pub(super) fn loop_refinement_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // depth inside λ(e)λ(cond)λ(body)λ(fuel)λ(ret): ret=0, fuel=1, body=2, cond=3, e=4.
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    // env A = exec_loop e cond body (succ fuel)   (loop_threaded's env)
    let succ_fuel = Expr::app(nat_succ, Expr::bvar(1));
    let env_a = exec_loop_app(Expr::bvar(4), Expr::bvar(3), Expr::bvar(2), succ_fuel);
    // env B = stepLoop (exec_loop e cond body fuel) cond body   (loop_substituted's env)
    let loop_e = exec_loop_app(Expr::bvar(4), Expr::bvar(3), Expr::bvar(2), Expr::bvar(1));
    let env_b = step_loop_app(loop_e, Expr::bvar(3), Expr::bvar(2));
    // f = λ(env : Env). eval env ret   (ret lifted past env ⇒ ret = bvar(1))
    let f = Expr::lam(bd(), env_ty(), Expr::apps(cst(MIRSEM_EVAL), [Expr::bvar(0), Expr::bvar(1)]));
    // execLoopUnrollLaw cond body fuel e
    //   : exec_loop (stepLoop e) fuel = stepLoop (exec_loop e fuel)
    //   and exec_loop e (succ fuel) ι-reduces (front-peel) to exec_loop (stepLoop e) fuel,
    //   so the law's LHS is DEF-EQ to env_a; its RHS IS env_b. So the law inhabits
    //   `env_a = env_b` up to def-eq. (cond=3, body=2, fuel=1, e=4.)
    let law = Expr::apps(
        cst(MIRSEM_EXEC_LOOP_UNROLL_LAW),
        [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(4)],
    );
    // congrArg.{1,1} Env Int env_a env_b f law : (f env_a) = (f env_b)
    //   i.e. eval (exec_loop e (succ fuel)) ret = eval (stepLoop (exec_loop e fuel)) ret
    //      = loop_threaded … = loop_substituted …
    let congr = Expr::const_(
        Name::from_string("congrArg"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );
    let congr_app = Expr::apps(congr, [env_ty(), int_ty(), env_a, env_b, f, law]);
    Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                list_stmt_ty(),
                Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), operand_ty(), congr_app)),
            ),
        ),
    )
}

/// Build the full LOOP-refinement environment: the `MirSem` anchor plus `stepLoop`,
/// `exec_loop`, the two whole-loop denotations (`loop_threaded`, `loop_substituted`),
/// the inductive fuel-level unroll law (`execLoopUnrollLaw`), and the loop
/// refinement theorem itself (`loopRefinement`) — all registered and kernel-checked.
pub fn mirsem_loop_refinement_env() -> Result<Environment, String> {
    let mut env = mirsem_env()?;
    register_step_loop(&mut env)?;
    register_exec_loop(&mut env)?;
    register_loop_threaded(&mut env)?;
    register_loop_substituted(&mut env)?;

    // The inductive fuel-level unroll law (proven by Nat.rec on fuel).
    let law_ty = exec_loop_unroll_law_type();
    let law_proof = exec_loop_unroll_law_proof();
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(&law_proof, &law_ty)
            .map_err(|e| format!("execLoopUnrollLaw check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_EXEC_LOOP_UNROLL_LAW),
        level_params: vec![],
        type_: law_ty,
        value: law_proof,
    })
    .map_err(|e| format!("add_decl(execLoopUnrollLaw): {e:?}"))?;

    // The loop refinement theorem (congrArg over the unroll law).
    let ref_ty = loop_refinement_type(None);
    let ref_proof = loop_refinement_proof();
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(&ref_proof, &ref_ty)
            .map_err(|e| format!("loopRefinement check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_LOOP_REFINEMENT),
        level_params: vec![],
        type_: ref_ty,
        value: ref_proof,
    })
    .map_err(|e| format!("add_decl(loopRefinement): {e:?}"))?;
    Ok(env)
}

/// Pin the LOOP-refinement meta-theorem anchor and audit its axiom closure: confirm
/// `stepLoop`, `exec_loop`, the two denotations, the inductive unroll law, AND the
/// loop refinement theorem each rest on ONLY the 3 foundational axioms (modulo 3,
/// no 4th axiom). Mirrors [`pin_mirsem_refinement_anchor`] for the loop capstone.
#[must_use]
pub fn pin_mirsem_loop_refinement_anchor() -> AnchorVerdict {
    let env = match mirsem_loop_refinement_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for n in [
        MIRSEM_STEP_LOOP,
        MIRSEM_EXEC_LOOP,
        MIRSEM_LOOP_THREADED,
        MIRSEM_LOOP_SUBST,
        MIRSEM_EXEC_LOOP_UNROLL_LAW,
        MIRSEM_LOOP_REFINEMENT,
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

/// Check the GENERAL loop refinement theorem against the real clean-kernel (build
/// the env up to the theorem, kernel-check the proof inhabits the statement). With
/// `claimed_rhs = Some`, the RHS is overridden (fail-closed test hook: a wrong loop
/// refinement claim must NOT type-check).
#[must_use]
pub fn check_loop_refinement() -> RefinementVerdict {
    check_loop_refinement_inner(None)
}

pub(super) fn check_loop_refinement_inner(claimed_rhs: Option<&Expr>) -> RefinementVerdict {
    // Build the env up to (but not including) the loop refinement theorem.
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_step_loop(&mut env)
        .and_then(|()| register_exec_loop(&mut env))
        .and_then(|()| register_loop_threaded(&mut env))
        .and_then(|()| register_loop_substituted(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }

    let law_ty = exec_loop_unroll_law_type();
    let law_proof = exec_loop_unroll_law_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&law_proof, &law_ty) {
            return RefinementVerdict::KernelRejected(format!(
                "execLoopUnrollLaw check_type: {e:?}"
            ));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_EXEC_LOOP_UNROLL_LAW),
        level_params: vec![],
        type_: law_ty,
        value: law_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add execLoopUnrollLaw: {e:?}"));
    }

    let ref_ty = loop_refinement_type(claimed_rhs);
    let ref_proof = loop_refinement_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&ref_proof, &ref_ty) {
            return RefinementVerdict::KernelRejected(format!("loopRefinement check_type: {e:?}"));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_LOOP_REFINEMENT),
        level_params: vec![],
        type_: ref_ty,
        value: ref_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add loopRefinement: {e:?}"));
    }

    match env.axiom_deps(&Name::from_string(MIRSEM_LOOP_REFINEMENT)) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::KernelRejected(format!("loopRefinement axiom residue: {names:?}"))
        }
        None => RefinementVerdict::KernelRejected("loopRefinement decl not found".to_string()),
    }
}

// ===========================================================================
// Step 6W — THE UNBOUNDED-LOOP HOARE WHILE RULE (partial correctness) and the
// inter-procedural CONTRACT-CALL rule (assume-the-callee). Both kernel-proven,
// modulo 3. HONESTY: the while-rule is PARTIAL correctness (the invariant is
// maintained for ANY number of guarded iterations — NO termination claim); the
// contract-call ASSUMES the callee satisfies its contract (modular verification
// — it does NOT prove the callee body). Termination + mutual recursion remain
// the honest deferral.
// ===========================================================================
/// `@Eq Bool b Bool.true` — the guard-true predicate (`Bool : Type ⇒ Eq.{1}`).
pub(super) fn eq_bool_true(b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [cst("Bool"), b, cst("Bool.true")],
    )
}

/// The `Env → Prop` predicate type — the loop-invariant signature `I : Env → Prop`.
pub(super) fn env_pred_ty() -> Expr {
    Expr::pi(BinderData::from(BinderInfo::Default), env_ty(), Expr::prop())
}

/// The PRESERVATION hypothesis as a kernel `Prop`:
/// `∀ (e : Env), I e → eval_cond e cond = true → I (exec e body)`. The supplied
/// refs (`i_ref`, `cond_ref`, `body_ref`) denote `I`/`cond`/`body` at the binder
/// depth the hypothesis is BUILT in; this builder introduces three more binders
/// (`e`, then the two non-dependent arrows are Π's whose domains reference `e`),
/// so callers pass refs ALREADY OFFSET for the outermost `∀ e` only — the inner
/// arrow domains/codomain re-lift internally. Inside `∀ e`: e=0, and the supplied
/// refs are lifted by 1 (we add that here). `lift` = how many binders sit between
/// the supplied refs and THIS call site BEFORE the `∀ e` is introduced.
pub(super) fn preservation_hyp_type(i_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // We build `∀ (e:Env), (I e) → (eval_cond e cond = true) → (I (exec e body))`.
    // Refs come in for the depth OUTSIDE the `∀ e`; inside we lift each by 1 for `e`,
    // and the chained non-dependent Π's add NO extra free-var shift for the refs
    // because each arrow's body is built at successively deeper depth — but since
    // `I`/`cond`/`body` only appear with explicit `Expr::lift`-free clones we must
    // account for depth manually. To keep this simple and ROBUST we shift refs by the
    // number of binders introduced before each use, computed below.
    //
    // depth model inside the result (innermost first):
    //   ∀ e        introduces e (the only binder that the two arrows' domains/cod see);
    //   the two arrows are NON-dependent Π (anonymous), but the kernel still counts them
    //   as binders for anything to their RIGHT. So:
    //     - `I e` (1st arrow domain): under `∀ e` only           ⇒ e=0, refs lifted by 1.
    //     - `eval_cond e cond = true` (2nd arrow domain): under `∀ e` + 1 arrow ⇒ e=1, refs lifted by 2.
    //     - `I (exec e body)` (codomain): under `∀ e` + 2 arrows ⇒ e=2, refs lifted by 3.
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    // 1st arrow domain: I e   (e=0; refs +1)
    let dom1 = Expr::app(lift(i_ref, 1), Expr::bvar(0));
    // 2nd arrow domain: eval_cond e cond = true   (e=1; refs +2)
    let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), lift(cond_ref, 2)]);
    let dom2 = eq_bool_true(guard);
    // codomain: I (exec e body)   (e=2; refs +3)
    let exec_body = Expr::apps(cst(MIRSEM_EXEC), [Expr::bvar(2), lift(body_ref, 3)]);
    let cod = Expr::app(lift(i_ref, 3), exec_body);
    // ∀ e, dom1 → dom2 → cod
    let arrows = Expr::pi(bd(), dom1, Expr::pi(bd(), dom2, cod));
    Expr::pi(bd(), env_ty(), arrows)
}

/// Register `Trust.MirSem.stepPreservesInv` (idempotent) — the guarded-step
/// invariant-preservation lemma. See [`MIRSEM_STEP_PRESERVES_INV`]. The proof
/// generalises the guard `eval_cond e cond : Bool` to a fresh `b`, case-splits
/// (dependent `Bool.rec`), and instantiates at the real guard with `Eq.refl`:
///
/// ```text
/// stepPreservesInv : ∀ (I : Env→Prop)(cond : Cond)(body : List Stmt),
///   (∀ e, I e → eval_cond e cond = true → I (exec e body))
///   → ∀ e, I e → I (stepLoop e cond body)
/// := λ I cond body pres e hI.
///      (@Bool.rec (λ b. eval_cond e cond = b → I (Bool.rec (λ_.Env) e (exec e body) b))
///         (λ _. hI)                         -- false arm: Bool.rec…false ≡ e
///         (λ hg. pres e hI hg)              -- true  arm: Bool.rec…true  ≡ exec e body
///         (eval_cond e cond))
///        (Eq.refl Bool (eval_cond e cond))
/// ```
pub(super) fn register_step_preserves_inv(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_STEP_PRESERVES_INV);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();

    // ---- TYPE ----
    // ∀ (I : Env→Prop)(cond : Cond)(body : List Stmt), preservation → ∀ e, I e → I (stepLoop e cond body)
    let ty = {
        // inside `∀ I ∀ cond ∀ body`: body=0, cond=1, I=2.
        let pres = preservation_hyp_type(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
        // after the `pres →` arrow we are one binder deeper for everything to the right.
        // conclusion: ∀ e, I e → I (stepLoop e cond body)
        //   inside `∀ I ∀ cond ∀ body (pres→) ∀ e`: e=0, pres=1, body=2, cond=3, I=4.
        let i_e = Expr::app(Expr::bvar(4), Expr::bvar(0));
        // I (stepLoop e cond body): under `∀ e` + 1 arrow ⇒ e=1, pres=2, body=3, cond=4, I=5.
        let step = step_loop_app(Expr::bvar(1), Expr::bvar(4), Expr::bvar(3));
        let i_step = Expr::app(Expr::bvar(5), step);
        let concl = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, i_step));
        let after_pres = Expr::pi(bd(), pres, concl);
        Expr::pi(
            bd(),
            env_pred_ty(),
            Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_stmt.clone(), after_pres)),
        )
    };

    // ---- PROOF ----
    // λ I cond body pres e hI. ghelper (eval_cond e cond) (Eq.refl Bool (eval_cond e cond))
    // depth inside `λ I λ cond λ body λ pres λ e λ hI`: hI=0, e=1, pres=2, body=3, cond=4, I=5.
    let val = {
        // The guard `eval_cond e cond` at the proof body's depth (e=1, cond=4). The
        // case-split sub-terms (motive_g/false_case/true_case) build their own bvars
        // inline at the depths they sit.
        let guard = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);

        // motive_g : Bool → Prop
        //   = λ (b : Bool). (eval_cond e cond = b) → I (Bool.rec (λ_.Env) e (exec e body) b)
        //   inside the extra `λ b`: b=0, hI=1, e=2, pres=3, body=4, cond=5, I=6.
        let motive_g = {
            let guard_b = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(2), Expr::bvar(5)]);
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_b, Expr::bvar(0)],
            );
            // codomain `I (Bool.rec (λ_.Env) e (exec e body) b)` — the generalised
            // stepLoop body under the predicate. It sits under `λ b` + the `eq_dom →`
            // arrow, so depth +1 vs the domain: b=1, hI=2, e=3, pres=4, body=5, cond=6, I=7.
            let bool_rec1 =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
            let exec_body = Expr::apps(cst(MIRSEM_EXEC), [Expr::bvar(3), Expr::bvar(5)]);
            let stepped =
                Expr::apps(bool_rec1, [env_motive, Expr::bvar(3), exec_body, Expr::bvar(1)]);
            let cod = Expr::app(Expr::bvar(7), stepped);
            let arrow = Expr::pi(bd(), eq_dom, cod);
            Expr::lam(bd(), cst("Bool"), arrow)
        };

        // false_case : (eval_cond e cond = false) → I (Bool.rec (λ_.Env) e (exec e body) false)
        //   Bool.rec … false ι-reduces to e, so the codomain is `I e`; proof = λ _. hI.
        //   inside the extra `λ (_ : eq)`: _=0, hI=1, e=2, pres=3, body=4, cond=5, I=6.
        let false_case = {
            // dom type `eval_cond e cond = false` is evaluated at PROOF-BODY depth
            // (BEFORE this lambda's binder): e=1, cond=4.
            let guard_f = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
            let eq_false = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_f, cst("Bool.false")],
            );
            // body: under `λ (_:eq_false)` ⇒ +1 ⇒ hI=1.
            Expr::lam(bd(), eq_false, Expr::bvar(1)) // returns hI
        };

        // true_case : (eval_cond e cond = true) → I (Bool.rec (λ_.Env) e (exec e body) true)
        //   Bool.rec … true ι-reduces to exec e body, codomain `I (exec e body)`;
        //   proof = λ (hg : eq). pres e hI hg.
        let true_case = {
            // dom type at PROOF-BODY depth: e=1, cond=4.
            let guard_t = Expr::apps(cst(MIRSEM_EVAL_COND), [Expr::bvar(1), Expr::bvar(4)]);
            let eq_true = eq_bool_true(guard_t);
            // body: under `λ (hg:eq_true)` ⇒ +1 ⇒ hg=0, hI=1, e=2, pres=3.
            //   pres e hI hg : pres=3, e=2, hI=1, hg=0.
            let app = Expr::apps(Expr::bvar(3), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
            Expr::lam(bd(), eq_true, app)
        };

        // ghelper = @Bool.rec.{0} motive_g false_case true_case (eval_cond e cond)
        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let ghelper = Expr::apps(bool_rec0, [motive_g, false_case, true_case, guard.clone()]);
        // ghelper (Eq.refl Bool (eval_cond e cond)) : I (Bool.rec … (eval_cond e cond))
        //   which is def-eq to I (stepLoop e cond body).
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let refl = Expr::apps(eq_refl, [cst("Bool"), guard]);
        let applied = Expr::app(ghelper, refl);

        Expr::lam(
            bd(),
            env_pred_ty(),
            Expr::lam(
                bd(),
                cst(MIRSEM_COND),
                Expr::lam(
                    bd(),
                    list_stmt.clone(),
                    Expr::lam(
                        bd(),
                        preservation_hyp_type(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                        Expr::lam(
                            bd(),
                            env_ty(),
                            // hI : I e   (inside `λ I λ cond λ body λ pres λ e`: e=0, pres=1, body=2, cond=3, I=4)
                            Expr::lam(bd(), Expr::app(Expr::bvar(4), Expr::bvar(0)), applied),
                        ),
                    ),
                ),
            ),
        )
    };

    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty).map_err(|e| format!("stepPreservesInv check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(stepPreservesInv): {e:?}"))?;
    Ok(())
}

/// The LOOP INVARIANT RULE (Hoare while-rule, PARTIAL correctness) TYPE:
/// `∀ (I : Env→Prop)(cond : Cond)(body : List Stmt), preservation
///   → ∀ (n : Nat)(e : Env), I e → I (exec_loop e cond body n)`.
/// `claimed_concl_pred = Some(p)` overrides the conclusion's invariant predicate
/// (fail-closed hook: a NON-preserved / wrong invariant must NOT prove).
pub(super) fn loop_invariant_rule_type(claimed_concl_pred: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // inside `∀ I ∀ cond ∀ body`: body=0, cond=1, I=2.
    let pres = preservation_hyp_type(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    // conclusion: ∀ n e, I e → I (exec_loop e cond body n)
    //   inside `∀ I ∀ cond ∀ body (pres→) ∀ n ∀ e`: e=0, n=1, pres=2, body=3, cond=4, I=5.
    let i_e = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(5));
        Expr::app(pred, Expr::bvar(0))
    };
    // I (exec_loop e cond body n): under one more arrow ⇒ e=1, n=2, pres=3, body=4, cond=5, I=6.
    let looped = exec_loop_app(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
    let i_loop = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(6));
        // when overriding, lift the claimed pred by the extra arrow binder (1) vs i_e's depth.
        let pred = if claimed_concl_pred.is_some() { pred.lift(1) } else { pred };
        Expr::app(pred, looped)
    };
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    let body_n = Expr::pi(bd(), cst("Nat"), body_e);
    let after_pres = Expr::pi(bd(), pres, body_n);
    Expr::pi(
        bd(),
        env_pred_ty(),
        Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_stmt, after_pres)),
    )
}

/// The LOOP INVARIANT RULE PROOF, by genuine `Nat.rec` induction on the iteration
/// count `n` at the Prop motive `λ n. ∀ e, I e → I (exec_loop e cond body n)`:
/// BASE (`n=0`): `exec_loop e 0 ≡ e`, so `λ e hI. hI`. STEP (`n=succ m`):
/// `exec_loop e (succ m) ≡ exec_loop (stepLoop e) m` (front-peel), so
/// `λ m ih e hI. ih (stepLoop e) (stepPreservesInv I cond body pres e hI)` — the
/// IH at the STEPPED env, fed the guarded-step preservation. PARTIAL correctness:
/// no termination is claimed; the invariant simply survives `n` guarded steps.
pub(super) fn loop_invariant_rule_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // λ I λ cond λ body λ pres. (Nat.rec motive zero_case succ_case)
    // depth inside `λ I λ cond λ body λ pres`: pres=0, body=1, cond=2, I=3.

    // motive : Nat → Prop = λ (n:Nat). ∀ e, I e → I (exec_loop e cond body n)
    //   inside `… λ pres` then `λ n` then `∀ e`: e=0, n=1, pres=2, body=3, cond=4, I=5.
    let motive = {
        let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        // under one more arrow (the `I e →`): e=1, n=2, pres=3, body=4, cond=5, I=6.
        let looped = exec_loop_app(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
        let i_loop = Expr::app(Expr::bvar(6), looped);
        let arrow = Expr::pi(bd(), i_e, i_loop);
        let quant_e = Expr::pi(bd(), env_ty(), arrow);
        Expr::lam(bd(), cst("Nat"), quant_e)
    };

    // zero_case : ∀ e, I e → I (exec_loop e cond body 0)
    //   exec_loop e cond body 0 ι-reduces to e ⇒ codomain `I e` ⇒ λ e hI. hI.
    //   inside `… λ pres λ e λ hI`: hI=0, e=1, pres=2, body=3, cond=4, I=5.
    let zero_case = {
        // I e   (e=0, I=4 inside `λ pres λ e`)
        let i_e = Expr::app(Expr::bvar(4), Expr::bvar(0));
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::bvar(0)))
    };

    // succ_case : λ (m:Nat)(ih : motive m)(e : Env)(hI : I e).
    //               ih (stepLoop e cond body) (stepPreservesInv I cond body pres e hI)
    //   inside `… λ pres λ m λ ih λ e λ hI`: hI=0, e=1, ih=2, m=3, pres=4, body=5, cond=6, I=7.
    let succ_case = {
        // ih : motive m  (built after `λ m`, before `λ ih`):
        //   inside `… λ pres λ m`: m=0, pres=1, body=2, cond=3, I=4. Then `∀ e`/arrow.
        let ih_ty = {
            // ∀ e, I e → I (exec_loop e cond body m)
            // under `∀ e`: e=0, m=1, pres=2, body=3, cond=4, I=5.
            let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
            // under one more arrow: e=1, m=2, pres=3, body=4, cond=5, I=6.
            let looped = exec_loop_app(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
            let i_loop = Expr::app(Expr::bvar(6), looped);
            let arrow = Expr::pi(bd(), i_e, i_loop);
            Expr::pi(bd(), env_ty(), arrow)
        };
        // body: ih (stepLoop e cond body) (stepPreservesInv I cond body pres e hI)
        //   inside `λ m λ ih λ e λ hI`: hI=0, e=1, ih=2, m=3, pres=4, body=5, cond=6, I=7.
        let step = step_loop_app(Expr::bvar(1), Expr::bvar(6), Expr::bvar(5));
        let preserves = Expr::apps(
            cst(MIRSEM_STEP_PRESERVES_INV),
            [
                Expr::bvar(7), // I
                Expr::bvar(6), // cond
                Expr::bvar(5), // body
                Expr::bvar(4), // pres
                Expr::bvar(1), // e
                Expr::bvar(0), // hI
            ],
        );
        let ih_app = Expr::apps(Expr::bvar(2), [step, preserves]);
        // hI : I e  (inside `λ m λ ih λ e`: e=0, ih=1, m=2, pres=3, body=4, cond=5, I=6)
        let i_e_hi = Expr::app(Expr::bvar(6), Expr::bvar(0));
        Expr::lam(
            bd(),
            cst("Nat"), // m
            Expr::lam(
                bd(),
                ih_ty, // ih
                Expr::lam(
                    bd(),
                    env_ty(),                        // e
                    Expr::lam(bd(), i_e_hi, ih_app), // hI
                ),
            ),
        )
    };

    // The full proof η-binds the scrutinee `n` AFTER `pres`, then applies the recursor:
    //   λ I λ cond λ body λ pres λ n. @Nat.rec.{0} motive zero_case succ_case n
    // producing `motive n = ∀ e, I e → I (exec_loop e cond body n)` — i.e. the whole
    // conclusion `∀ n, motive n` once `λ n` is bound. (Prop motive ⇒ `Nat.rec.{0}`.)
    // `motive`/`zero_case`/`succ_case` were indexed for depth UNDER `λ pres` (no `λ n`),
    // so under the extra `λ n` we lift each by 1; the scrutinee is `n = bvar(0)`.
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        env_pred_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                list_stmt,
                Expr::lam(
                    bd(),
                    preservation_hyp_type(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(bd(), cst("Nat"), rec_applied),
                ),
            ),
        ),
    )
}

// ===========================================================================
// Step 6BRK — the BREAK / EARLY-EXIT loop layer. A STRATIFIED, fully ADDITIVE family
// `stepLoopBrk`/`exec_loopBrk`/`stepPreservesInvBrk`/`loopInvariantRuleBrk` parallel
// to the base while-rule, whose only difference is the SCRUTINEE: the COMBINED guard
// `Bool.and (eval_cond e cond) (Bool.not (eval_cond e brk))` (run the body while the
// loop guard holds AND the break-condition does NOT). At EITHER exit (guard false OR
// break true) the combined guard is false, so ONE invariant theorem certifies `I` at
// BOTH exit points. `stepLoop`/`exec_loop`/`stepPreservesInv`/`loopInvariantRule` are
// UNTOUCHED (byte-identical). The generalised-guard `Bool.rec` case-split is reused
// VERBATIM (it works on any `Bool` term), so this is the base proof with the scrutinee
// swapped — no new induction shape, no 4th axiom.
// ===========================================================================
/// The COMBINED break-guard `Bool` term `Bool.and (eval_cond e cond) (Bool.not
/// (eval_cond e brk))` — run the body iff the loop guard holds AND the break-condition
/// does NOT. `e_ref`/`cond_ref`/`brk_ref` are the refs at the build site's depth.
pub(super) fn combined_brk_guard(e_ref: &Expr, cond_ref: &Expr, brk_ref: &Expr) -> Expr {
    let g_cond = Expr::apps(cst(MIRSEM_EVAL_COND), [e_ref.clone(), cond_ref.clone()]);
    let g_brk = Expr::apps(cst(MIRSEM_EVAL_COND), [e_ref.clone(), brk_ref.clone()]);
    let not_brk = Expr::app(cst("Bool.not"), g_brk);
    Expr::apps(cst("Bool.and"), [g_cond, not_brk])
}

/// `stepLoopBrk`'s body = `Bool.rec (λ_.Env) e (exec e body) <combined_brk_guard>`.
pub(super) fn step_loop_brk_body(e_ref: &Expr, cond_ref: &Expr, brk_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
    let guard = combined_brk_guard(e_ref, cond_ref, brk_ref);
    let exec_body = Expr::apps(cst(MIRSEM_EXEC), [e_ref.clone(), body_ref.clone()]);
    Expr::apps(bool_rec, [env_motive, e_ref.clone(), exec_body, guard])
}

/// `stepLoopBrk e cond brk body` applied as a CONSTANT (signature `Env → Cond → Cond →
/// List Stmt → Env`).
pub(super) fn step_loop_brk_app(e_ref: Expr, cond_ref: Expr, brk_ref: Expr, body_ref: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_STEP_LOOP_BRK), [e_ref, cond_ref, brk_ref, body_ref])
}

/// Register `Trust.MirSem.stepLoopBrk : Env → Cond → Cond → List Stmt → Env`
/// (idempotent) = `λ e cond brk body. if (eval_cond e cond ∧ ¬eval_cond e brk) then
/// exec e body else e`. Requires `eval_cond`/`exec` registered.
pub(super) fn register_step_loop_brk(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_STEP_LOOP_BRK);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // λ(e).λ(cond).λ(brk).λ(body). step ; depth: body=0, brk=1, cond=2, e=3.
    let body = step_loop_brk_body(&Expr::bvar(3), &Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(bd(), cst(MIRSEM_COND), Expr::lam(bd(), list_stmt.clone(), body)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_stmt, env_ty())),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(stepLoopBrk): {e:?}"))?;
    Ok(())
}

/// `exec_loopBrk e cond brk body fuel` applied as a CONSTANT to its five refs.
pub(super) fn exec_loop_brk_app(e: Expr, cond: Expr, brk: Expr, body: Expr, fuel: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_EXEC_LOOP_BRK), [e, cond, brk, body, fuel])
}

/// Register `Trust.MirSem.exec_loopBrk : Env → Cond → Cond → List Stmt → Nat → Env`
/// (idempotent), front-peeling the fuel via `Nat.rec` over `stepLoopBrk`. Requires
/// `stepLoopBrk` registered.
pub(super) fn register_exec_loop_brk(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EXEC_LOOP_BRK);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_env = Expr::pi(bd(), env_ty(), env_ty());
    let nat_rec = Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]);
    let motive = Expr::lam(bd(), cst("Nat"), env_to_env.clone());
    let zero_case = Expr::lam(bd(), env_ty(), Expr::bvar(0));
    // succ: λ(n).λ(ih).λ(e'). ih (stepLoopBrk e' cond brk body)
    //   e'=0, ih=1, n=2, fuel=3, body=4, brk=5, cond=6, e=7.
    let succ_case = {
        let step = step_loop_brk_app(Expr::bvar(0), Expr::bvar(6), Expr::bvar(5), Expr::bvar(4));
        let ih_app = Expr::app(Expr::bvar(1), step);
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), env_to_env.clone(), Expr::lam(bd(), env_ty(), ih_app)),
        )
    };
    let rec_app = Expr::apps(nat_rec, [motive, zero_case, succ_case, Expr::bvar(0)]);
    let applied = Expr::app(rec_app, Expr::bvar(4));
    // λ(e).λ(cond).λ(brk).λ(body).λ(fuel). applied
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                cst(MIRSEM_COND),
                Expr::lam(bd(), list_stmt.clone(), Expr::lam(bd(), cst("Nat"), applied)),
            ),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(
                bd(),
                cst(MIRSEM_COND),
                Expr::pi(bd(), list_stmt, Expr::pi(bd(), cst("Nat"), env_ty())),
            ),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(exec_loopBrk): {e:?}"))?;
    Ok(())
}

/// The break PRESERVATION hypothesis `∀ (e : Env), I e → (eval_cond e cond ∧
/// ¬eval_cond e brk) = true → I (exec e body)`. The `preservation_hyp_type` analogue
/// with the loop guard replaced by the COMBINED break-guard `Bool`.
pub(super) fn preservation_hyp_type_brk(
    i_ref: &Expr,
    cond_ref: &Expr,
    brk_ref: &Expr,
    body_ref: &Expr,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    // 1st arrow domain: I e   (e=0; refs +1)
    let dom1 = Expr::app(lift(i_ref, 1), Expr::bvar(0));
    // 2nd arrow domain: combined_brk_guard e cond brk = true   (e=1; refs +2)
    let guard = combined_brk_guard(&Expr::bvar(1), &lift(cond_ref, 2), &lift(brk_ref, 2));
    let dom2 = eq_bool_true(guard);
    // codomain: I (exec e body)   (e=2; refs +3)
    let exec_body = Expr::apps(cst(MIRSEM_EXEC), [Expr::bvar(2), lift(body_ref, 3)]);
    let cod = Expr::app(lift(i_ref, 3), exec_body);
    let arrows = Expr::pi(bd(), dom1, Expr::pi(bd(), dom2, cod));
    Expr::pi(bd(), env_ty(), arrows)
}

/// Register `Trust.MirSem.stepPreservesInvBrk` (idempotent) — the break-able
/// guarded-step invariant-preservation lemma. The PROOF is the SAME generalised-guard
/// `Bool.rec` case-split as `stepPreservesInv`, scrutinising the COMBINED break-guard.
pub(super) fn register_step_preserves_inv_brk(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_STEP_PRESERVES_INV_BRK);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();

    // ---- TYPE ----
    // ∀ (I)(cond)(brk)(body), pres → ∀ e, I e → I (stepLoopBrk e cond brk body)
    let ty = {
        // inside `∀ I ∀ cond ∀ brk ∀ body`: body=0, brk=1, cond=2, I=3.
        let pres = preservation_hyp_type_brk(
            &Expr::bvar(3),
            &Expr::bvar(2),
            &Expr::bvar(1),
            &Expr::bvar(0),
        );
        // conclusion: ∀ e, I e → I (stepLoopBrk e cond brk body)
        //   inside `… (pres→) ∀ e`: e=0, pres=1, body=2, brk=3, cond=4, I=5.
        let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        // under one more arrow: e=1, pres=2, body=3, brk=4, cond=5, I=6.
        let step = step_loop_brk_app(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(3));
        let i_step = Expr::app(Expr::bvar(6), step);
        let concl = Expr::pi(bd(), env_ty(), Expr::pi(bd(), i_e, i_step));
        let after_pres = Expr::pi(bd(), pres, concl);
        Expr::pi(
            bd(),
            env_pred_ty(),
            Expr::pi(
                bd(),
                cst(MIRSEM_COND),
                Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_stmt.clone(), after_pres)),
            ),
        )
    };

    // ---- PROOF ----
    // λ I cond brk body pres e hI. ghelper (gG) (Eq.refl Bool (gG))
    //   inside `λ I λ cond λ brk λ body λ pres λ e λ hI`:
    //     hI=0, e=1, pres=2, body=3, brk=4, cond=5, I=6.
    let val = {
        let guard = combined_brk_guard(&Expr::bvar(1), &Expr::bvar(5), &Expr::bvar(4));

        // motive_g : λ (b : Bool). (gG = b) → I (Bool.rec (λ_.Env) e (exec e body) b)
        //   inside extra `λ b`: b=0, hI=1, e=2, pres=3, body=4, brk=5, cond=6, I=7.
        let motive_g = {
            let guard_b = combined_brk_guard(&Expr::bvar(2), &Expr::bvar(6), &Expr::bvar(5));
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_b, Expr::bvar(0)],
            );
            // codomain under `λ b` + the `eq_dom →` arrow: b=1, hI=2, e=3, pres=4, body=5,
            //   brk=6, cond=7, I=8.
            let bool_rec1 =
                Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
            let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
            let exec_body = Expr::apps(cst(MIRSEM_EXEC), [Expr::bvar(3), Expr::bvar(5)]);
            let stepped =
                Expr::apps(bool_rec1, [env_motive, Expr::bvar(3), exec_body, Expr::bvar(1)]);
            let cod = Expr::app(Expr::bvar(8), stepped);
            let arrow = Expr::pi(bd(), eq_dom, cod);
            Expr::lam(bd(), cst("Bool"), arrow)
        };

        // false_case : (gG = false) → I (Bool.rec … false) ≡ I e ; proof = λ _. hI.
        //   inside `λ (_:eq)`: _=0, hI=1, e=2, pres=3, body=4, brk=5, cond=6, I=7.
        let false_case = {
            let guard_f = combined_brk_guard(&Expr::bvar(1), &Expr::bvar(5), &Expr::bvar(4));
            let eq_false = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), guard_f, cst("Bool.false")],
            );
            Expr::lam(bd(), eq_false, Expr::bvar(1)) // returns hI
        };

        // true_case : (gG = true) → I (Bool.rec … true) ≡ I (exec e body) ; proof = λ hg. pres e hI hg.
        let true_case = {
            let guard_t = combined_brk_guard(&Expr::bvar(1), &Expr::bvar(5), &Expr::bvar(4));
            let eq_true = eq_bool_true(guard_t);
            // body under `λ (hg:eq_true)`: hg=0, hI=1, e=2, pres=3.
            let app = Expr::apps(Expr::bvar(3), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
            Expr::lam(bd(), eq_true, app)
        };

        let bool_rec0 = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
        let ghelper = Expr::apps(bool_rec0, [motive_g, false_case, true_case, guard.clone()]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
        let refl = Expr::apps(eq_refl, [cst("Bool"), guard]);
        let applied = Expr::app(ghelper, refl);

        Expr::lam(
            bd(),
            env_pred_ty(),
            Expr::lam(
                bd(),
                cst(MIRSEM_COND),
                Expr::lam(
                    bd(),
                    cst(MIRSEM_COND),
                    Expr::lam(
                        bd(),
                        list_stmt.clone(),
                        Expr::lam(
                            bd(),
                            preservation_hyp_type_brk(
                                &Expr::bvar(3),
                                &Expr::bvar(2),
                                &Expr::bvar(1),
                                &Expr::bvar(0),
                            ),
                            Expr::lam(
                                bd(),
                                env_ty(),
                                // hI : I e   (inside `λ I λ cond λ brk λ body λ pres λ e`:
                                //   e=0, pres=1, body=2, brk=3, cond=4, I=5)
                                Expr::lam(bd(), Expr::app(Expr::bvar(5), Expr::bvar(0)), applied),
                            ),
                        ),
                    ),
                ),
            ),
        )
    };

    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty).map_err(|e| format!("stepPreservesInvBrk check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(stepPreservesInvBrk): {e:?}"))?;
    Ok(())
}

/// The break-able Hoare while-rule TYPE: `∀ I cond brk body, pres → ∀ n e, I e →
/// I (exec_loopBrk e cond brk body n)`. `claimed_concl_pred = Some(p)` overrides the
/// conclusion's invariant predicate (fail-closed hook).
pub(super) fn loop_invariant_rule_brk_type(claimed_concl_pred: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // inside `∀ I ∀ cond ∀ brk ∀ body`: body=0, brk=1, cond=2, I=3.
    let pres =
        preservation_hyp_type_brk(&Expr::bvar(3), &Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    // conclusion: ∀ n e, I e → I (exec_loopBrk e cond brk body n)
    //   inside `… (pres→) ∀ n ∀ e`: e=0, n=1, pres=2, body=3, brk=4, cond=5, I=6.
    let i_e = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(6));
        Expr::app(pred, Expr::bvar(0))
    };
    // under one more arrow: e=1, n=2, pres=3, body=4, brk=5, cond=6, I=7.
    let looped = exec_loop_brk_app(
        Expr::bvar(1),
        Expr::bvar(6),
        Expr::bvar(5),
        Expr::bvar(4),
        Expr::bvar(2),
    );
    let i_loop = {
        let pred = claimed_concl_pred.cloned().unwrap_or_else(|| Expr::bvar(7));
        let pred = if claimed_concl_pred.is_some() { pred.lift(1) } else { pred };
        Expr::app(pred, looped)
    };
    let i_arrow = Expr::pi(bd(), i_e, i_loop);
    let body_e = Expr::pi(bd(), env_ty(), i_arrow);
    let body_n = Expr::pi(bd(), cst("Nat"), body_e);
    let after_pres = Expr::pi(bd(), pres, body_n);
    Expr::pi(
        bd(),
        env_pred_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_stmt, after_pres)),
        ),
    )
}

/// The break-able Hoare while-rule PROOF, by genuine `Nat.rec` on the fuel `n`, the
/// `loop_invariant_rule_proof` analogue (stepLoop ↦ stepLoopBrk, stepPreservesInv ↦
/// stepPreservesInvBrk, exec_loop ↦ exec_loopBrk).
pub(super) fn loop_invariant_rule_brk_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // λ I λ cond λ brk λ body λ pres. (Nat.rec …)
    //   inside `λ I λ cond λ brk λ body λ pres`: pres=0, body=1, brk=2, cond=3, I=4.

    // motive : λ (n:Nat). ∀ e, I e → I (exec_loopBrk e cond brk body n)
    //   inside `… λ pres λ n ∀ e`: e=0, n=1, pres=2, body=3, brk=4, cond=5, I=6.
    let motive = {
        let i_e = Expr::app(Expr::bvar(6), Expr::bvar(0));
        // under one more arrow: e=1, n=2, pres=3, body=4, brk=5, cond=6, I=7.
        let looped = exec_loop_brk_app(
            Expr::bvar(1),
            Expr::bvar(6),
            Expr::bvar(5),
            Expr::bvar(4),
            Expr::bvar(2),
        );
        let i_loop = Expr::app(Expr::bvar(7), looped);
        let arrow = Expr::pi(bd(), i_e, i_loop);
        let quant_e = Expr::pi(bd(), env_ty(), arrow);
        Expr::lam(bd(), cst("Nat"), quant_e)
    };

    // zero_case : ∀ e, I e → I (exec_loopBrk e cond brk body 0) ≡ I e ⇒ λ e hI. hI.
    //   inside `… λ pres λ e`: e=0, pres=1, body=2, brk=3, cond=4, I=5.
    let zero_case = {
        let i_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, Expr::bvar(0)))
    };

    // succ_case : λ (m)(ih : motive m)(e)(hI : I e).
    //               ih (stepLoopBrk e cond brk body) (stepPreservesInvBrk I cond brk body pres e hI)
    //   inside `… λ pres λ m λ ih λ e λ hI`: hI=0, e=1, ih=2, m=3, pres=4, body=5, brk=6, cond=7, I=8.
    let succ_case = {
        let ih_ty = {
            // ∀ e, I e → I (exec_loopBrk e cond brk body m)
            //   inside `… λ pres λ m ∀ e`: e=0, m=1, pres=2, body=3, brk=4, cond=5, I=6.
            let i_e = Expr::app(Expr::bvar(6), Expr::bvar(0));
            // under one more arrow: e=1, m=2, pres=3, body=4, brk=5, cond=6, I=7.
            let looped = exec_loop_brk_app(
                Expr::bvar(1),
                Expr::bvar(6),
                Expr::bvar(5),
                Expr::bvar(4),
                Expr::bvar(2),
            );
            let i_loop = Expr::app(Expr::bvar(7), looped);
            let arrow = Expr::pi(bd(), i_e, i_loop);
            Expr::pi(bd(), env_ty(), arrow)
        };
        // body: ih (stepLoopBrk e cond brk body) (stepPreservesInvBrk I cond brk body pres e hI)
        //   inside `λ m λ ih λ e λ hI`: hI=0, e=1, ih=2, m=3, pres=4, body=5, brk=6, cond=7, I=8.
        let step = step_loop_brk_app(Expr::bvar(1), Expr::bvar(7), Expr::bvar(6), Expr::bvar(5));
        let preserves = Expr::apps(
            cst(MIRSEM_STEP_PRESERVES_INV_BRK),
            [
                Expr::bvar(8), // I
                Expr::bvar(7), // cond
                Expr::bvar(6), // brk
                Expr::bvar(5), // body
                Expr::bvar(4), // pres
                Expr::bvar(1), // e
                Expr::bvar(0), // hI
            ],
        );
        let ih_app = Expr::apps(Expr::bvar(2), [step, preserves]);
        // hI : I e  (inside `λ m λ ih λ e`: e=0, ih=1, m=2, pres=3, body=4, brk=5, cond=6, I=7)
        let i_e_hi = Expr::app(Expr::bvar(7), Expr::bvar(0));
        Expr::lam(
            bd(),
            cst("Nat"),
            Expr::lam(bd(), ih_ty, Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e_hi, ih_app))),
        )
    };

    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        env_pred_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                cst(MIRSEM_COND),
                Expr::lam(
                    bd(),
                    list_stmt,
                    Expr::lam(
                        bd(),
                        preservation_hyp_type_brk(
                            &Expr::bvar(3),
                            &Expr::bvar(2),
                            &Expr::bvar(1),
                            &Expr::bvar(0),
                        ),
                        Expr::lam(bd(), cst("Nat"), rec_applied),
                    ),
                ),
            ),
        ),
    )
}

/// Register `Trust.MirSem.loopInvariantRuleBrk` (idempotent) — the BREAK / EARLY-EXIT
/// Hoare while-rule (PARTIAL correctness). Requires `stepLoopBrk`/`exec_loopBrk`/
/// `stepPreservesInvBrk`.
pub(super) fn register_loop_invariant_rule_brk(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_LOOP_INVARIANT_RULE_BRK);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = loop_invariant_rule_brk_type(None);
    let val = loop_invariant_rule_brk_proof();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty).map_err(|e| format!("loopInvariantRuleBrk check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(loopInvariantRuleBrk): {e:?}"))?;
    Ok(())
}

// ===========================================================================
// Step 6T — TOTAL correctness: the TERMINATION (well-founded RANKING) while-rule.
// ===========================================================================
/// `Nat.succ e`.
pub(super) fn nat_succ(e: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), e)
}

/// Raw `@Nat.le a b : Prop`.
pub(super) fn nat_le(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Nat.le"), vec![]), [a, b])
}

/// Raw `@Nat.lt a b : Prop` (def-eq to `Nat.le (Nat.succ a) b`).
pub(super) fn nat_lt(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string("Nat.lt"), vec![]), [a, b])
}

/// `eval_cond e cond : Bool`.
pub(super) fn eval_cond_app(e: Expr, cond: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_EVAL_COND), [e, cond])
}

/// `exec e body : Env`.
pub(super) fn exec_app(e: Expr, body: Expr) -> Expr {
    Expr::apps(cst(MIRSEM_EXEC), [e, body])
}

/// `@Eq Bool b Bool.false` — the guard-FALSE predicate (`Bool : Type ⇒ Eq.{1}`).
pub(super) fn eq_bool_false(b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [cst("Bool"), b, cst("Bool.false")],
    )
}

/// The loop-HALTED predicate `eval_cond (exec_loop e cond body fuel) cond = false`
/// — after `fuel` guarded steps the guard is FALSE (the loop has exited / reached
/// a stable env). The total-correctness termination conclusion.
pub(super) fn loop_halts_prop(e: Expr, cond: Expr, body: Expr, fuel: Expr) -> Expr {
    let looped = exec_loop_app(e, cond.clone(), body, fuel);
    eq_bool_false(eval_cond_app(looped, cond))
}

/// The RANK-DECREASE hypothesis `∀ (e : Env), eval_cond e cond = true →
/// Nat.lt (R (exec e body)) (R e)` — the rank STRICTLY DROPS on every GUARDED
/// iteration. `r_ref`/`cond_ref`/`body_ref` denote `R`/`cond`/`body` at the depth
/// this builder is called (BEFORE the `∀ e`); they are lifted internally.
pub(super) fn decrease_hyp_type(r_ref: &Expr, cond_ref: &Expr, body_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let lift = |r: &Expr, k: u32| r.clone().lift(k);
    // ∀ (e:Env), (eval_cond e cond = true) → Nat.lt (R (exec e body)) (R e)
    //   dom (under ∀ e): e=0, refs +1.
    let guard = eval_cond_app(Expr::bvar(0), lift(cond_ref, 1));
    let dom = eq_bool_true(guard);
    //   cod (under ∀ e + 1 arrow): e=1, refs +2.
    let r_e = Expr::app(lift(r_ref, 2), Expr::bvar(1));
    let r_step = Expr::app(lift(r_ref, 2), exec_app(Expr::bvar(1), lift(body_ref, 2)));
    let cod = nat_lt(r_step, r_e);
    Expr::pi(bd(), env_ty(), Expr::pi(bd(), dom, cod))
}

/// Register `Trust.MirSem.nat_le_trans : ∀ (a b c : Nat), Nat.le a b → Nat.le b c
/// → Nat.le a c` (idempotent) — RAW `Nat.le` transitivity via `Nat.le.rec` on the
/// SECOND premise. See [`MIRSEM_NAT_LE_TRANS`].
pub(super) fn register_nat_le_trans(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_NAT_LE_TRANS);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let nat = cst("Nat");

    // TYPE: ∀ a b c, Nat.le a b → Nat.le b c → Nat.le a c
    let ty = {
        // inside ∀a∀b∀c: c=0,b=1,a=2
        let hab = nat_le(Expr::bvar(2), Expr::bvar(1));
        // after `hab →` : c=1,b=2,a=3
        let hbc = nat_le(Expr::bvar(2), Expr::bvar(1));
        // after `hbc →` : c=2,b=3,a=4
        let concl = nat_le(Expr::bvar(4), Expr::bvar(2));
        let arrows = Expr::pi(bd(), hab, Expr::pi(bd(), hbc, concl));
        Expr::pi(
            bd(),
            nat.clone(),
            Expr::pi(bd(), nat.clone(), Expr::pi(bd(), nat.clone(), arrows)),
        )
    };

    // PROOF: λ a b c hab hbc. @Nat.le.rec b motive refl_minor step_minor c hbc
    //   depth inside `λ a λ b λ c λ hab λ hbc`: hbc=0, hab=1, c=2, b=3, a=4.
    let val = {
        let le_rec = Expr::const_(Name::from_string("Nat.le.rec"), vec![]);
        let le_refl = Expr::const_(Name::from_string("Nat.le.refl"), vec![]);
        let le_step = Expr::const_(Name::from_string("Nat.le.step"), vec![]);
        // motive : λ (m:Nat)(_ : Nat.le b m). Nat.le a m
        //   inside the proof body (hbc=0,hab=1,c=2,b=3,a=4) then `λ m λ h`: h=0,m=1,hbc=2,hab=3,c=4,b=5,a=6.
        let motive = {
            let le_bm = nat_le(Expr::bvar(5), Expr::bvar(0)); // Nat.le b m  (b=5 before λh? see below)
            // domain `Nat.le b m`: under `λ m` only ⇒ m=0, b=4 (hbc=1,hab=2,c=3,b=4,a=5).
            let le_bm_dom = nat_le(Expr::bvar(4), Expr::bvar(0));
            // codomain `Nat.le a m`: under `λ m λ (_:Nat.le b m)` ⇒ m=1, a=6 (h=0,m=1,hbc=2,hab=3,c=4,b=5,a=6).
            let le_am = nat_le(Expr::bvar(6), Expr::bvar(1));
            let _ = le_bm;
            Expr::lam(bd(), nat.clone(), Expr::lam(bd(), le_bm_dom, le_am))
        };
        // refl_minor : motive b (Nat.le.refl b) ≡ Nat.le a b = hab
        //   at proof-body depth: hab=1.
        let refl_minor = Expr::bvar(1);
        // step_minor : λ (m:Nat)(h:Nat.le b m)(ih:Nat.le a m). @Nat.le.step a m ih
        //   inside `λ m λ h λ ih`: ih=0,h=1,m=2,hbc=3,hab=4,c=5,b=6,a=7.
        let step_minor = {
            // dom1 `Nat.le b m` (under λm): m=0, b=4 (m=0,hbc=1,hab=2,c=3,b=4,a=5).
            let dom_h = nat_le(Expr::bvar(4), Expr::bvar(0));
            // dom2 `Nat.le a m` (under λm λh): m=1, a=6 (h=0,m=1,hbc=2,hab=3,c=4,b=5,a=6).
            let dom_ih = nat_le(Expr::bvar(6), Expr::bvar(1));
            // body `@Nat.le.step a m ih` (under λm λh λih): ih=0,m=2,a=7.
            let stepped =
                Expr::apps(le_step.clone(), [Expr::bvar(7), Expr::bvar(2), Expr::bvar(0)]);
            Expr::lam(bd(), nat.clone(), Expr::lam(bd(), dom_h, Expr::lam(bd(), dom_ih, stepped)))
        };
        let _ = le_refl;
        // @Nat.le.rec b motive refl_minor step_minor c hbc
        //   at proof body: b=3, c=2, hbc=0.
        let rec_app = Expr::apps(
            le_rec,
            [Expr::bvar(3), motive, refl_minor, step_minor, Expr::bvar(2), Expr::bvar(0)],
        );
        Expr::lam(
            bd(),
            nat.clone(),
            Expr::lam(
                bd(),
                nat.clone(),
                Expr::lam(
                    bd(),
                    nat.clone(),
                    Expr::lam(
                        bd(),
                        nat_le(Expr::bvar(2), Expr::bvar(1)), // hab : Nat.le a b
                        Expr::lam(bd(), nat_le(Expr::bvar(2), Expr::bvar(1)), rec_app), // hbc : Nat.le b c
                    ),
                ),
            ),
        )
    };

    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty).map_err(|e| format!("nat_le_trans check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(nat_le_trans): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.guardFalseStable` (idempotent) — the guard-FALSE
/// stability lemma `∀ cond body n e, eval_cond e cond = false →
/// eval_cond (exec_loop e cond body n) cond = false`. Proven by `Nat.rec` on `n`:
/// base (`exec_loop e 0 ≡ e`) is the hypothesis; step (`exec_loop e (succ m) ≡
/// exec_loop (stepLoop e) m`) uses the generalised-guard `Bool.rec` trick to show
/// `stepLoop e ≡ e` under the false guard, then the IH at `e`. See
/// [`MIRSEM_GUARD_FALSE_STABLE`]. Requires `stepLoop`/`exec_loop` registered.
pub(super) fn register_guard_false_stable(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_GUARD_FALSE_STABLE);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();

    // TYPE: ∀ (cond:Cond)(body:List Stmt)(n:Nat)(e:Env),
    //         eval_cond e cond = false → eval_cond (exec_loop e cond body n) cond = false
    let ty = {
        // inside ∀cond∀body∀n∀e: e=0,n=1,body=2,cond=3
        let hf = eq_bool_false(eval_cond_app(Expr::bvar(0), Expr::bvar(3)));
        // after `hf →`: e=1,n=2,body=3,cond=4
        let concl = loop_halts_prop(Expr::bvar(1), Expr::bvar(4), Expr::bvar(3), Expr::bvar(2));
        let after = Expr::pi(bd(), hf, concl);
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(
                bd(),
                list_stmt.clone(),
                Expr::pi(bd(), cst("Nat"), Expr::pi(bd(), env_ty(), after)),
            ),
        )
    };

    // PROOF: λ cond body. @Nat.rec.{0} motive zero_case succ_case
    //   motive : Nat → Prop = λ n. ∀ e, eval_cond e cond = false → eval_cond (exec_loop e cond body n) cond = false
    //   depth inside `λ cond λ body`: body=0, cond=1.
    let val = {
        let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);

        // motive (under `λ cond λ body λ n`): n=0,body=1,cond=2; then `∀ e` ⇒ e=0,n=1,body=2,cond=3.
        let motive = {
            let hf = eq_bool_false(eval_cond_app(Expr::bvar(0), Expr::bvar(3)));
            // after `hf →`: e=1,n=2,body=3,cond=4
            let concl = loop_halts_prop(Expr::bvar(1), Expr::bvar(4), Expr::bvar(3), Expr::bvar(2));
            let quant_e = Expr::pi(bd(), env_ty(), Expr::pi(bd(), hf, concl));
            Expr::lam(bd(), cst("Nat"), quant_e)
        };

        // zero_case : ∀ e, eval_cond e cond = false → eval_cond (exec_loop e cond body 0) cond = false
        //   exec_loop e 0 ≡ e ⇒ codomain ≡ (eval_cond e cond = false) ⇒ λ e hf. hf.
        //   (no-λn convention) the `hf_ty` DOMAIN sits under `λ cond λ body λ e` ⇒ e=0,body=1,cond=2.
        let zero_case = {
            let hf_ty = eq_bool_false(eval_cond_app(Expr::bvar(0), Expr::bvar(2)));
            Expr::lam(bd(), env_ty(), Expr::lam(bd(), hf_ty, Expr::bvar(0)))
        };

        // succ_case : λ (m:Nat)(ih : motive m)(e:Env)(hf : eval_cond e cond = false).
        //   GOAL: eval_cond (exec_loop e cond body (succ m)) cond = false
        //       ≡ eval_cond (exec_loop (stepLoop e cond body) cond body m) cond = false   (front-peel)
        //   Generalise the guard `g := eval_cond e cond : Bool` via dependent Bool.rec:
        //     motive_g (b:Bool) := (eval_cond e cond = b)
        //       → eval_cond (exec_loop (Bool.rec (λ_.Env) e (exec e body) b) cond body m) cond = false
        //     false arm: Bool.rec…false ≡ e ⇒ eval_cond (exec_loop e cond body m) cond = false = ih e hf'.
        //     true  arm: refuted — but the guard IS false (hf), so we never need a real true arm;
        //                we still must INHABIT it. The true-arm hypothesis `eval_cond e cond = true`
        //                together with `hf : … = false` is contradictory; we discharge via the
        //                false-arm path only because we instantiate at `Eq.refl` AND feed `hf`.
        //   Cleanest: motive_g (b:Bool) := (eval_cond e cond = b) →
        //               eval_cond (exec_loop (Bool.rec (λ_.Env) e (exec e body) b) cond body m) cond = false.
        //   We supply `b := false` PROOF through hf, so only the false arm is forced.
        //   ghelper := @Bool.rec.{0} motive_g false_arm true_arm (eval_cond e cond);
        //   applied to (hf) gives the goal at the REAL guard.
        //   Wait — we must apply ghelper to a proof `eval_cond e cond = (eval_cond e cond)` i.e. Eq.refl,
        //   then the motive's codomain mentions the REAL guard `eval_cond e cond` (not a literal),
        //   so Bool.rec at the real guard does NOT reduce. Instead we case on the guard value and
        //   in BOTH arms use hf to rewrite. Simpler robust route: rewrite the WHOLE step env using hf.
        //
        //   ROBUST PROOF: from hf, `stepLoop e cond body = e`. Build this equality and transport.
        //     stepLoop e ≡ Bool.rec (λ_.Env) e (exec e body) (eval_cond e cond).
        //     Using hf : eval_cond e cond = false, @Eq.rec rewrites the scrutinee to false,
        //     and Bool.rec…false ≡ e. So `stepEqE : stepLoop e cond body = e`.
        //   Then `exec_loop (stepLoop e) cond body m = exec_loop e cond body m` by congrArg,
        //   and the goal `eval_cond (exec_loop (stepLoop e) …) … = false` rewrites to
        //   `eval_cond (exec_loop e …) … = false` = `ih e hf`.
        //   inside `λ cond λ body λ m λ ih λ e λ hf`: hf=0,e=1,ih=2,m=3,body=4,cond=5.
        let succ_case = {
            // ih : motive m  (built after `λ m`, before `λ ih`): inside `λ cond λ body λ m`: m=0,body=1,cond=2.
            let ih_ty = {
                // ∀ e, eval_cond e cond = false → eval_cond (exec_loop e cond body m) cond = false
                // under `∀ e`: e=0,m=1,body=2,cond=3
                let hf = eq_bool_false(eval_cond_app(Expr::bvar(0), Expr::bvar(3)));
                // after `hf →`: e=1,m=2,body=3,cond=4
                let concl =
                    loop_halts_prop(Expr::bvar(1), Expr::bvar(4), Expr::bvar(3), Expr::bvar(2));
                Expr::pi(bd(), env_ty(), Expr::pi(bd(), hf, concl))
            };

            // Build `stepEqE : stepLoop e cond body = e` from `hf : eval_cond e cond = false`.
            //   stepLoop e ≡ @Bool.rec (λ_.Env) e (exec e body) (eval_cond e cond).
            //   @Eq.rec over hf at motive `λ (b:Bool)(_ : eval_cond e cond = b).
            //       @Eq Env (Bool.rec (λ_.Env) e (exec e body) b) e`
            //   base (b := eval_cond e cond): Bool.rec…(eval_cond e cond) ≡ stepLoop e; we need
            //   `stepLoop e = e` as the GOAL, but @Eq.rec gives the statement at b := false after
            //   transport. Cleanest: use @Eq.mpr-free `@Eq.rec` with the motive that yields the
            //   equality `Bool.rec … b = e`; the base case `b = false` is `Bool.rec…false ≡ e`,
            //   witnessed `Eq.refl e`. Transport ALONG hf⁻¹? We instead transport the goal.
            //
            //   Simplest correct construction: prove the GOAL directly by @Eq.rec on hf with motive
            //     M (b:Bool)(_ : eval_cond e cond = b) :=
            //       eval_cond (exec_loop (@Bool.rec (λ_.Env) e (exec e body) b) cond body m) cond = false
            //   - base value at `b := false` is `Eq.refl _`? No: the base of @Eq.rec is M false (refl),
            //     i.e. we must SUPPLY `M false` and @Eq.rec transports to `M (eval_cond e cond)`.
            //     M false ≡ eval_cond (exec_loop (Bool.rec…false) cond body m) cond = false
            //            ≡ eval_cond (exec_loop e cond body m) cond = false  = (ih e hf).
            //     @Eq.rec then yields M (eval_cond e cond) ≡
            //       eval_cond (exec_loop (stepLoop e) cond body m) cond = false ≡ GOAL.  ✓
            //
            // @Eq.rec.{0,1} : {α : Sort 1} {a : α} {motive : (x:α) → a = x → Prop}
            //                 → motive a (Eq.refl a) → {b : α} → (h : a = b) → motive b h
            // Here α := Bool, a := eval_cond e cond, b := false, h := hf.
            let eq_rec = Expr::const_(
                Name::from_string("Eq.rec"),
                vec![Level::zero(), Level::succ(Level::zero())],
            );
            // guard `g := eval_cond e cond` at succ_case body depth (e=1,cond=5).
            let guard = eval_cond_app(Expr::bvar(1), Expr::bvar(5));
            // motive M : λ (x:Bool)(_ : g = x). eval_cond (exec_loop (Bool.rec (λ_.Env) e (exec e body) x) cond body m) cond = false
            //   inside succ body (hf=0,e=1,ih=2,m=3,body=4,cond=5) then `λ x λ heq`: heq=0,x=1,hf=2,e=3,ih=4,m=5,body=6,cond=7.
            let m_motive = {
                let bool_rec1 =
                    Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
                let env_motive = Expr::lam(bd(), cst("Bool"), env_ty());
                // @Eq.rec has `a := Bool.false`, so the motive domain is `false = x` (NOT g = x).
                // domain `false = x` (under `λ x` only): x=0.
                let eq_dom = Expr::apps(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    [cst("Bool"), cst("Bool.false"), Expr::bvar(0)],
                );
                // codomain (under `λ x λ heq`): heq=0,x=1,hf=2,e=3,ih=4,m=5,body=6,cond=7.
                let exec_body = exec_app(Expr::bvar(3), Expr::bvar(6));
                let stepped =
                    Expr::apps(bool_rec1, [env_motive, Expr::bvar(3), exec_body, Expr::bvar(1)]);
                let cod = loop_halts_prop(stepped, Expr::bvar(7), Expr::bvar(6), Expr::bvar(5));
                Expr::lam(bd(), cst("Bool"), Expr::lam(bd(), eq_dom, cod))
            };
            // base : M false ≡ eval_cond (exec_loop e cond body m) cond = false = ih e hf
            //   at succ body depth: ih=2,e=1,hf=0.
            let base = Expr::apps(Expr::bvar(2), [Expr::bvar(1), Expr::bvar(0)]);
            // @Eq.rec α a M base b hf : M b hf ≡ M false hf ... wait we want M (eval_cond e cond)?
            // Eq.rec maps base : M a (refl) to M b h. With a := false? NO. We need a := the guard so
            // that the RESULT M b = M false matches the GOAL? Re-examine:
            //   @Eq.rec {α}{a}{M} (base : M a refl) {b} (h : a = b) : M b h.
            // We have hf : (eval_cond e cond) = false. So a := eval_cond e cond, b := false.
            //   base must be `M a refl` = M (eval_cond e cond) =
            //       eval_cond (exec_loop (stepLoop e) cond body m) cond = false  ≡ GOAL — that's what we WANT, not have.
            //   result `M b h` = M false = eval_cond (exec_loop e cond body m) cond = false  = (ih e hf) — that's what we HAVE.
            // So the directions are swapped: we must transport along hf⁻¹ (Eq.symm hf : false = eval_cond e cond).
            let eq_symm =
                Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]);
            // Eq.symm {Bool} {g} {false} hf : false = g
            let hf_sym =
                Expr::apps(eq_symm, [cst("Bool"), guard.clone(), cst("Bool.false"), Expr::bvar(0)]);
            // Now a := false, b := g, h := hf_sym. base must be `M false refl`:
            //   M false ≡ eval_cond (exec_loop (Bool.rec…false) cond body m) cond = false
            //          ≡ eval_cond (exec_loop e cond body m) cond = false  = ih e hf.  ✓
            //   result `M g hf_sym` ≡ eval_cond (exec_loop (stepLoop e) cond body m) cond = false ≡ GOAL.  ✓
            let applied = Expr::apps(
                eq_rec,
                [
                    cst("Bool"),       // α
                    cst("Bool.false"), // a := false
                    m_motive,          // motive M
                    base,              // M false (Eq.refl)
                    guard,             // b := eval_cond e cond
                    hf_sym,            // h : false = g
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
                        env_ty(), // e
                        Expr::lam(
                            bd(),
                            // hf : eval_cond e cond = false (inside λ m λ ih λ e: e=0,ih=1,m=2,body=3,cond=4)
                            eq_bool_false(eval_cond_app(Expr::bvar(0), Expr::bvar(4))),
                            applied,
                        ),
                    ),
                ),
            )
        };

        // @Nat.rec.{0} motive zero_case succ_case   (a function Nat → motive n; the
        // theorem statement's `∀ n` is the OUTER pi already supplied by the `n` binder
        // in the TYPE). We η-expand: λ cond body. (λ n. Nat.rec … n) — but the TYPE
        // quantifies n AFTER body, so we bind n here and apply the recursor to it.
        // depth inside `λ cond λ body λ n`: n=0,body=1,cond=2; motive/cases were built
        // for depth UNDER `λ cond λ body` (no λ n) ⇒ lift each by 1; scrutinee = n=0.
        let rec_applied = Expr::apps(
            nat_rec0,
            [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)],
        );
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(bd(), list_stmt.clone(), Expr::lam(bd(), cst("Nat"), rec_applied)),
        )
    };

    {
        let tc = TypeChecker::new(env);
        tc.check_type(&val, &ty).map_err(|e| format!("guardFalseStable check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: val })
        .map_err(|e| format!("add_decl(guardFalseStable): {e:?}"))?;
    Ok(())
}

/// The BOUNDED-HALT lemma TYPE: `∀ (R : Env→Nat)(cond)(body), decrease → ∀ (k :
/// Nat)(e : Env), Nat.le (R e) k → eval_cond (exec_loop e cond body k) cond =
/// false`. `claimed_concl_decrease` is unused here (the decrease hypothesis is the
/// fail-closed knob, handled in the public checker via the rank parameter).
pub(super) fn bounded_halt_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_nat = Expr::pi(bd(), env_ty(), cst("Nat"));
    // inside `∀ R ∀ cond ∀ body`: body=0,cond=1,R=2.
    let decrease = decrease_hyp_type(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    // conclusion: ∀ k e, Nat.le (R e) k → loop_halts e cond body k
    //   inside `∀ R ∀ cond ∀ body (decrease→) ∀ k ∀ e`: e=0,k=1,decrease=2,body=3,cond=4,R=5.
    let r_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
    let le_hyp = nat_le(r_e, Expr::bvar(1));
    // loop_halts e cond body k (under one more arrow): e=1,k=2,decrease=3,body=4,cond=5,R=6.
    let halts = loop_halts_prop(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
    let arrow = Expr::pi(bd(), le_hyp, halts);
    let body_e = Expr::pi(bd(), env_ty(), arrow);
    let body_k = Expr::pi(bd(), cst("Nat"), body_e);
    let after_decrease = Expr::pi(bd(), decrease, body_k);
    Expr::pi(
        bd(),
        env_to_nat,
        Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_stmt, after_decrease)),
    )
}

/// The BOUNDED-HALT lemma PROOF — well-founded descent by `Nat.rec` on the fuel
/// bound `k`. See [`MIRSEM_BOUNDED_HALT`]. Requires `stepLoop`/`exec_loop`/
/// `guardFalseStable`/`nat_le_trans` registered.
pub(super) fn bounded_halt_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_nat = Expr::pi(bd(), env_ty(), cst("Nat"));
    let bool_rec0 = || Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let bool_rec1 =
        || Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let env_motive = || Expr::lam(bd(), cst("Bool"), env_ty());
    let eq_refl_bool = |b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]),
            [cst("Bool"), b],
        )
    };

    // depth inside `λ R λ cond λ body λ decrease`: decrease=0,body=1,cond=2,R=3.

    // motive P : Nat → Prop = λ k. ∀ e, Nat.le (R e) k → loop_halts e cond body k
    //   under `λ R..λ decrease λ k`: k=0,decrease=1,body=2,cond=3,R=4; then `∀ e`: e=0,k=1,decrease=2,body=3,cond=4,R=5.
    let motive = {
        let r_e = Expr::app(Expr::bvar(5), Expr::bvar(0));
        let le_hyp = nat_le(r_e, Expr::bvar(1));
        // loop_halts (under one more arrow): e=1,k=2,decrease=3,body=4,cond=5,R=6
        let halts = loop_halts_prop(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
        let arrow = Expr::pi(bd(), le_hyp, halts);
        Expr::lam(bd(), cst("Nat"), Expr::pi(bd(), env_ty(), arrow))
    };

    // zero_case : ∀ e, Nat.le (R e) 0 → loop_halts e cond body 0
    //   loop_halts e cond body 0 ≡ (eval_cond e cond = false).
    //   λ e (hk : Nat.le (R e) 0). @Bool.rec.{0} mg false_arm true_arm g (Eq.refl g)
    //   under `λ R..λ decrease λ e λ hk`: hk=0,e=1,decrease=2,body=3,cond=4,R=5.
    let zero_case = {
        let guard = eval_cond_app(Expr::bvar(1), Expr::bvar(4)); // g = eval_cond e cond
        // mg : Bool → Prop = λ b. (g = b) → (g = false)
        //   under `..λ e λ hk λ b`: b=0,hk=1,e=2,decrease=3,body=4,cond=5,R=6.
        let mg = {
            let g_inner = eval_cond_app(Expr::bvar(2), Expr::bvar(5));
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), g_inner.clone(), Expr::bvar(0)],
            );
            // cod: g = false (under λ b + arrow): b=1,hk=2,e=3 ⇒ g at e=3,cond=6.
            let g_cod = eval_cond_app(Expr::bvar(3), Expr::bvar(6));
            let cod = eq_bool_false(g_cod);
            Expr::lam(bd(), cst("Bool"), Expr::pi(bd(), eq_dom, cod))
        };
        // false_arm : (g = false) → (g = false) = λ h. h
        let false_arm = {
            // dom `g = false` at zero-case body depth (e=1,cond=4): then `λ h`.
            let g_dom = eval_cond_app(Expr::bvar(1), Expr::bvar(4));
            Expr::lam(bd(), eq_bool_false(g_dom), Expr::bvar(0))
        };
        // true_arm : (g = true) → (g = false)
        //   from ht:g=true, decrease e ht : Nat.le (succ (R(exec e body))) (R e);
        //   nat_le_trans (succ (R(exec e body))) (R e) 0 (decrease e ht) hk : Nat.le (succ (R(exec e body))) 0;
        //   Nat.not_succ_le_zero (R(exec e body)) <that> : False; @False.elim (g=false) <False>.
        //   under `..λ e λ hk λ ht`: ht=0,hk=1,e=2,decrease=3,body=4,cond=5,R=6.
        let true_arm = {
            // the `λ ht` DOMAIN sits under `λ e λ hk` (BEFORE λ ht): e=1,cond=4 (hk=0,e=1,decrease=2,body=3,cond=4,R=5).
            let g_dom = eval_cond_app(Expr::bvar(1), Expr::bvar(4));
            let eq_true = eq_bool_true(g_dom);
            // body under `λ ht`: ht=0,hk=1,e=2,decrease=3,body=4,cond=5,R=6.
            let r_exec = {
                let exec = exec_app(Expr::bvar(2), Expr::bvar(4)); // exec e body
                Expr::app(Expr::bvar(6), exec) // R (exec e body)
            };
            // decrease e ht : Nat.lt (R (exec e body)) (R e) ≡ Nat.le (succ (R(exec e body))) (R e)
            let dec_app = Expr::apps(Expr::bvar(3), [Expr::bvar(2), Expr::bvar(0)]);
            let r_e = Expr::app(Expr::bvar(6), Expr::bvar(2)); // R e
            // nat_le_trans (succ r_exec) (R e) 0 dec_app hk
            let trans = Expr::apps(
                cst(MIRSEM_NAT_LE_TRANS),
                [
                    nat_succ(r_exec.clone()),
                    r_e,
                    Expr::nat_lit(0),
                    dec_app,
                    Expr::bvar(1), // hk
                ],
            );
            // Nat.not_succ_le_zero r_exec trans : False
            let false_pf = Expr::apps(
                Expr::const_(Name::from_string("Nat.not_succ_le_zero"), vec![]),
                [r_exec, trans],
            );
            // @False.elim.{0} (g = false) false_pf
            let g_false_goal = eq_bool_false(eval_cond_app(Expr::bvar(2), Expr::bvar(5)));
            let false_elim = Expr::apps(
                Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                [g_false_goal, false_pf],
            );
            Expr::lam(bd(), eq_true, false_elim)
        };
        // @Bool.rec.{0} mg false_arm true_arm g (Eq.refl Bool g)
        let ghelper = Expr::apps(bool_rec0(), [mg, false_arm, true_arm, guard.clone()]);
        let applied = Expr::app(ghelper, eq_refl_bool(guard));
        // λ e (hk : Nat.le (R e) 0). applied
        //   hk : Nat.le (R e) 0  (under λ e: e=0,decrease=1,body=2,cond=3,R=4)
        let hk_ty = nat_le(Expr::app(Expr::bvar(4), Expr::bvar(0)), Expr::nat_lit(0));
        Expr::lam(bd(), env_ty(), Expr::lam(bd(), hk_ty, applied))
    };

    // succ_case : λ (k':Nat)(ih : P k')(e : Env)(hk : Nat.le (R e) (succ k')).
    //   GOAL ≡ eval_cond (exec_loop (stepLoop e cond body) cond body k') cond = false
    //        ≡ eval_cond (exec_loop (Bool.rec (λ_.Env) e (exec e body) g) cond body k') cond = false
    //   @Bool.rec.{0} mg false_arm true_arm g (Eq.refl g).
    //   under `λ R..λ decrease λ k' λ ih λ e λ hk`: hk=0,e=1,ih=2,k'=3,decrease=4,body=5,cond=6,R=7.
    let succ_case = {
        // ih : P k'  (after `λ k'`, before `λ ih`): under `..λ decrease λ k'`: k'=0,decrease=1,body=2,cond=3,R=4.
        let ih_ty = {
            // ∀ e, Nat.le (R e) k' → loop_halts e cond body k'
            // under `∀ e`: e=0,k'=1,decrease=2,body=3,cond=4,R=5
            let le_hyp = nat_le(Expr::app(Expr::bvar(5), Expr::bvar(0)), Expr::bvar(1));
            // loop_halts (under arrow): e=1,k'=2,decrease=3,body=4,cond=5,R=6
            let halts = loop_halts_prop(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), Expr::bvar(2));
            Expr::pi(bd(), env_ty(), Expr::pi(bd(), le_hyp, halts))
        };

        let guard = eval_cond_app(Expr::bvar(1), Expr::bvar(6)); // g = eval_cond e cond (e=1,cond=6)

        // mg : Bool → Prop = λ b. (g = b) →
        //        eval_cond (exec_loop (Bool.rec (λ_.Env) e (exec e body) b) cond body k') cond = false
        //   under `..λ hk λ b`: b=0,hk=1,e=2,ih=3,k'=4,decrease=5,body=6,cond=7,R=8.
        let mg = {
            let g_inner = eval_cond_app(Expr::bvar(2), Expr::bvar(7));
            let eq_dom = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                [cst("Bool"), g_inner, Expr::bvar(0)],
            );
            // cod (under λ b + arrow): b=1,hk=2,e=3,ih=4,k'=5,decrease=6,body=7,cond=8,R=9.
            let exec_body = exec_app(Expr::bvar(3), Expr::bvar(7));
            let stepped =
                Expr::apps(bool_rec1(), [env_motive(), Expr::bvar(3), exec_body, Expr::bvar(1)]);
            let cod = loop_halts_prop(stepped, Expr::bvar(8), Expr::bvar(7), Expr::bvar(5));
            Expr::lam(bd(), cst("Bool"), Expr::pi(bd(), eq_dom, cod))
        };

        // false_arm : (g = false) → eval_cond (exec_loop (Bool.rec…false) cond body k') cond = false
        //   ≡ (g = false) → eval_cond (exec_loop e cond body k') cond = false
        //   = λ hf. guardFalseStable cond body k' e hf.
        //   under `..λ hk λ hf`: hf=0,hk=1,e=2,ih=3,k'=4,decrease=5,body=6,cond=7,R=8.
        let false_arm = {
            let g_dom = eval_cond_app(Expr::bvar(1), Expr::bvar(6)); // BEFORE λ hf: e=1,cond=6
            let dom_ty = eq_bool_false(g_dom);
            // guardFalseStable cond body k' e hf : eval_cond (exec_loop e cond body k') cond = false
            let gfs = Expr::apps(
                cst(MIRSEM_GUARD_FALSE_STABLE),
                [
                    Expr::bvar(7), // cond
                    Expr::bvar(6), // body
                    Expr::bvar(4), // k'
                    Expr::bvar(2), // e
                    Expr::bvar(0), // hf
                ],
            );
            Expr::lam(bd(), dom_ty, gfs)
        };

        // true_arm : (g = true) → eval_cond (exec_loop (Bool.rec…true) cond body k') cond = false
        //   ≡ (g = true) → eval_cond (exec_loop (exec e body) cond body k') cond = false
        //   bound: decrease e ht : Nat.le (succ (R(exec e body))) (R e);
        //          nat_le_trans (succ (R(exec e body))) (R e) (succ k') (decrease e ht) hk : Nat.le (succ (R(exec e body))) (succ k');
        //          Nat.le_of_succ_le_succ (R(exec e body)) k' <that> : Nat.le (R(exec e body)) k';
        //          ih (exec e body) <bound> : eval_cond (exec_loop (exec e body) cond body k') cond = false.
        //   under `..λ hk λ ht`: ht=0,hk=1,e=2,ih=3,k'=4,decrease=5,body=6,cond=7,R=8.
        let true_arm = {
            let g_dom = eval_cond_app(Expr::bvar(1), Expr::bvar(6)); // BEFORE λ ht
            let dom_ty = eq_bool_true(g_dom);
            let exec_eb = exec_app(Expr::bvar(2), Expr::bvar(6)); // exec e body
            let r_exec = Expr::app(Expr::bvar(8), exec_eb.clone()); // R (exec e body)
            let r_e = Expr::app(Expr::bvar(8), Expr::bvar(2)); // R e
            let dec_app = Expr::apps(Expr::bvar(5), [Expr::bvar(2), Expr::bvar(0)]); // decrease e ht
            // nat_le_trans (succ r_exec) (R e) (succ k') dec_app hk
            let trans = Expr::apps(
                cst(MIRSEM_NAT_LE_TRANS),
                [
                    nat_succ(r_exec.clone()),
                    r_e,
                    nat_succ(Expr::bvar(4)), // succ k'
                    dec_app,
                    Expr::bvar(1), // hk
                ],
            );
            // Nat.le_of_succ_le_succ r_exec k' trans : Nat.le r_exec k'
            let bound = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_of_succ_le_succ"), vec![]),
                [r_exec, Expr::bvar(4), trans],
            );
            // ih (exec e body) bound
            let ih_app = Expr::apps(Expr::bvar(3), [exec_eb, bound]);
            Expr::lam(bd(), dom_ty, ih_app)
        };

        // @Bool.rec.{0} mg false_arm true_arm g (Eq.refl g)
        let ghelper = Expr::apps(bool_rec0(), [mg, false_arm, true_arm, guard.clone()]);
        let applied = Expr::app(ghelper, eq_refl_bool(guard));

        // λ k' (ih : P k') (e : Env) (hk : Nat.le (R e) (succ k')). applied
        //   hk under `λ k' λ ih λ e`: e=0,ih=1,k'=2,decrease=3,body=4,cond=5,R=6.
        let hk_ty = nat_le(Expr::app(Expr::bvar(6), Expr::bvar(0)), nat_succ(Expr::bvar(2)));
        Expr::lam(
            bd(),
            cst("Nat"), // k'
            Expr::lam(
                bd(),
                ih_ty,                                                      // ih
                Expr::lam(bd(), env_ty(), Expr::lam(bd(), hk_ty, applied)), // e, hk
            ),
        )
    };

    // λ R cond body decrease k. @Nat.rec.{0} motive zero_case succ_case k
    //   motive/zero/succ built UNDER `λ decrease` (no λ k) ⇒ lift by 1; scrutinee k=0.
    let nat_rec0 = Expr::const_(Name::from_string("Nat.rec"), vec![Level::zero()]);
    let rec_applied =
        Expr::apps(nat_rec0, [motive.lift(1), zero_case.lift(1), succ_case.lift(1), Expr::bvar(0)]);
    Expr::lam(
        bd(),
        env_to_nat,
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                list_stmt,
                Expr::lam(
                    bd(),
                    decrease_hyp_type(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(bd(), cst("Nat"), rec_applied),
                ),
            ),
        ),
    )
}

/// The TOTAL-CORRECTNESS TERMINATION while-rule TYPE: `∀ (R : Env→Nat)(cond)(body),
/// decrease → ∀ e, eval_cond (exec_loop e cond body (R e)) cond = false`.
/// `claimed_concl_rank = Some(p)` overrides the rank used in the CONCLUSION's fuel
/// (fail-closed hook: a rank that does not match the one the decrease hypothesis
/// constrains — e.g. the wrong measure — must NOT prove).
pub(super) fn loop_rank_terminates_type(claimed_concl_rank: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_nat = Expr::pi(bd(), env_ty(), cst("Nat"));
    // inside `∀ R ∀ cond ∀ body`: body=0,cond=1,R=2.
    let decrease = decrease_hyp_type(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0));
    // conclusion: ∀ e, eval_cond (exec_loop e cond body (R e)) cond = false
    //   inside `∀ R ∀ cond ∀ body (decrease→) ∀ e`: e=0,decrease=1,body=2,cond=3,R=4.
    let rank = claimed_concl_rank
        .cloned()
        .map(|p| p.lift(5)) // claimed rank supplied at OUTSIDE depth; lift past R,cond,body,decrease,e
        .unwrap_or_else(|| Expr::bvar(4)); // the real R
    let fuel = Expr::app(rank, Expr::bvar(0)); // (R e)
    let halts = loop_halts_prop(Expr::bvar(0), Expr::bvar(3), Expr::bvar(2), fuel);
    let body_e = Expr::pi(bd(), env_ty(), halts);
    let after_decrease = Expr::pi(bd(), decrease, body_e);
    Expr::pi(
        bd(),
        env_to_nat,
        Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_stmt, after_decrease)),
    )
}

/// The TOTAL-CORRECTNESS TERMINATION while-rule PROOF: instantiate `boundedHalt`'s
/// fuel bound at the rank itself. `λ R cond body decrease e.
///   boundedHalt R cond body decrease (R e) e (Nat.le.refl (R e))`.
pub(super) fn loop_rank_terminates_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_nat = Expr::pi(bd(), env_ty(), cst("Nat"));
    // under `λ R λ cond λ body λ decrease λ e`: e=0,decrease=1,body=2,cond=3,R=4.
    let r_e = Expr::app(Expr::bvar(4), Expr::bvar(0)); // R e
    let le_refl = Expr::apps(Expr::const_(Name::from_string("Nat.le.refl"), vec![]), [r_e.clone()]); // Nat.le.refl (R e) : Nat.le (R e) (R e)
    let bh = Expr::apps(
        cst(MIRSEM_BOUNDED_HALT),
        [
            Expr::bvar(4), // R
            Expr::bvar(3), // cond
            Expr::bvar(2), // body
            Expr::bvar(1), // decrease
            r_e,           // k := R e
            Expr::bvar(0), // e
            le_refl,       // Nat.le (R e) (R e)
        ],
    );
    Expr::lam(
        bd(),
        env_to_nat,
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(
                bd(),
                list_stmt,
                Expr::lam(
                    bd(),
                    decrease_hyp_type(&Expr::bvar(2), &Expr::bvar(1), &Expr::bvar(0)),
                    Expr::lam(bd(), env_ty(), bh),
                ),
            ),
        ),
    )
}

/// Register `boundedHalt` then `loopRankTerminates` into `env`. Requires
/// `stepLoop`/`exec_loop`/`guardFalseStable`/`nat_le_trans` already registered.
pub(super) fn register_loop_rank_terminates(env: &mut Environment) -> Result<(), String> {
    // boundedHalt
    let bh_name = Name::from_string(MIRSEM_BOUNDED_HALT);
    if env.get_const(&bh_name).is_none() {
        let bh_ty = bounded_halt_type();
        let bh_proof = bounded_halt_proof();
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&bh_proof, &bh_ty)
                .map_err(|e| format!("boundedHalt check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem {
            name: bh_name,
            level_params: vec![],
            type_: bh_ty,
            value: bh_proof,
        })
        .map_err(|e| format!("add_decl(boundedHalt): {e:?}"))?;
    }
    // loopRankTerminates
    let lrt_name = Name::from_string(MIRSEM_LOOP_RANK_TERMINATES);
    if env.get_const(&lrt_name).is_none() {
        let lrt_ty = loop_rank_terminates_type(None);
        let lrt_proof = loop_rank_terminates_proof();
        {
            let tc = TypeChecker::new(env);
            tc.check_type(&lrt_proof, &lrt_ty)
                .map_err(|e| format!("loopRankTerminates check_type: {e:?}"))?;
        }
        env.add_decl(Declaration::Theorem {
            name: lrt_name,
            level_params: vec![],
            type_: lrt_ty,
            value: lrt_proof,
        })
        .map_err(|e| format!("add_decl(loopRankTerminates): {e:?}"))?;
    }
    Ok(())
}

// ===========================================================================
// Step 6TC — TOTAL CORRECTNESS AS A SINGLE COMPOSED THEOREM (`loopTotalCorrect`).
// `loopInvariantRule` (partial: invariant survives `n` steps) and
// `loopRankTerminates` (termination: guard goes false within `R e` steps) are two
// SEPARATE lemmas. Total correctness is their CONJUNCTION at the SHARED fuel index
// `n := R e`: the invariant holds AT the halting state AND the loop reaches that
// halting state. We register that conjunction as ONE kernel-checked `And` theorem,
// proven by `And.intro` of the two existing theorems instantiated at `R e` / `e`.
// ===========================================================================
/// Build the conjuncts `(A, B)` of the composed total-correctness conclusion at the
/// shared depth where (from the TOP binders `I,R,cond,body`, then `pres`,`decrease`,
/// `e`,`hI` arrows) the de-Bruijn indices are: hI=0, e=1, decrease=2, pres=3, body=4,
/// cond=5, R=6, I=7. `claimed_concl_rank = Some` overrides the fuel rank (fail-closed
/// hook). Returns `(R_e, A, B)` where `R_e = (R e)`, `A = I (exec_loop e cond body (R e))`
/// (invariant at the halting state), `B = eval_cond (exec_loop e cond body (R e)) cond
/// = false` (the loop halted). Both conjuncts are built at the SAME fuel `R e`.
pub(super) fn loop_total_correct_conjuncts(claimed_concl_rank: Option<&Expr>) -> (Expr, Expr, Expr) {
    // R e : Nat  (R=6, e=1 at this depth; an overridden rank is supplied at OUTSIDE
    // depth — lift it past I,R,cond,body,pres,decrease,e,hI = 8 binders).
    let rank = claimed_concl_rank.cloned().map(|p| p.lift(8)).unwrap_or_else(|| Expr::bvar(6)); // the real R
    let r_e = Expr::app(rank, Expr::bvar(1));
    // exec_loop e cond body (R e)   (e=1, cond=5, body=4)
    let looped = exec_loop_app(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), r_e.clone());
    // A = I (exec_loop e cond body (R e))   (I=7) — the invariant at the HALTING state.
    let a = Expr::app(Expr::bvar(7), looped);
    // B = eval_cond (exec_loop e cond body (R e)) cond = false — the TERMINATION conclusion.
    let b = loop_halts_prop(Expr::bvar(1), Expr::bvar(5), Expr::bvar(4), r_e.clone());
    (r_e, a, b)
}

/// The COMPOSED TOTAL-CORRECTNESS theorem TYPE: the `And` of the partial-correctness
/// (invariant-at-halting-state) conclusion and the termination (halts-within-`R e`)
/// conclusion, under the SAME `pres`/`decrease`/`I e` hypotheses. See
/// [`MIRSEM_LOOP_TOTAL_CORRECT`]. `claimed_concl_rank = Some` overrides the shared fuel
/// rank (fail-closed hook). Binders: `∀ I R cond body, pres → decrease → ∀ e, I e → And A B`.
pub(super) fn loop_total_correct_type(claimed_concl_rank: Option<&Expr>) -> Expr {
    let (_r_e, a, b) = loop_total_correct_conjuncts(claimed_concl_rank);
    loop_total_correct_type_with_concl(Expr::apps(cst("And"), [a, b]))
}

/// Wrap a CONCLUSION (built at the 8-binder-deep scope `hI=0,e=1,decrease=2,pres=3,
/// body=4,cond=5,R=6,I=7`) in the `loopTotalCorrect` binder/hypothesis Π-chain
/// `∀ I R cond body, pres → decrease → ∀ e, I e → <concl>`. Reused by the real type
/// builder and by the genuineness test (to construct wrong-conclusion variants without
/// peeling binders manually).
pub(super) fn loop_total_correct_type_with_concl(concl: Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_nat = Expr::pi(bd(), env_ty(), cst("Nat"));
    // inside `∀ I ∀ R ∀ cond ∀ body`: body=0, cond=1, R=2, I=3.
    let pres = preservation_hyp_type(&Expr::bvar(3), &Expr::bvar(1), &Expr::bvar(0));
    // after the `pres →` arrow everything +1: body=1, cond=2, R=3, I=4.
    let decrease = decrease_hyp_type(&Expr::bvar(3), &Expr::bvar(2), &Expr::bvar(1));
    // conclusion (after `decrease →`, then `∀ e`, then `I e →`): hI=0,e=1,decrease=2,
    //   pres=3,body=4,cond=5,R=6,I=7 — the scope the supplied `concl` is built in.
    // hI : I e   (e=0 inside `∀ e`, I=6 there)
    let i_e = Expr::app(Expr::bvar(6), Expr::bvar(0));
    let after_hi = Expr::pi(bd(), i_e, concl);
    let body_e = Expr::pi(bd(), env_ty(), after_hi);
    let after_decrease = Expr::pi(bd(), decrease, body_e);
    let after_pres = Expr::pi(bd(), pres, after_decrease);
    Expr::pi(
        bd(),
        env_pred_ty(),
        Expr::pi(
            bd(),
            env_to_nat,
            Expr::pi(bd(), cst(MIRSEM_COND), Expr::pi(bd(), list_stmt, after_pres)),
        ),
    )
}

/// The COMPOSED TOTAL-CORRECTNESS theorem PROOF: `And.intro` of the two existing
/// theorems at the shared fuel index `R e` / start env `e`.
/// `λ I R cond body pres decrease e hI.
///   And.intro A B
///     (loopInvariantRule I cond body pres (R e) e hI)   -- (a) PARTIAL at fuel R e
///     (loopRankTerminates R cond body decrease e)`.     -- (b) TERMINATION
/// The conjunction is a GENUINE `And` — dropping either conjunct-hypothesis leaves the
/// corresponding `And.intro` argument unbuildable (fail-closed). NO new induction: it
/// reuses the kernel-checked `loopInvariantRule` / `loopRankTerminates` proofs.
pub(super) fn loop_total_correct_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let env_to_nat = Expr::pi(bd(), env_ty(), cst("Nat"));
    // depth in the body (under λ I λ R λ cond λ body λ pres λ decrease λ e λ hI):
    //   hI=0, e=1, decrease=2, pres=3, body=4, cond=5, R=6, I=7.
    let (r_e, a, b) = loop_total_correct_conjuncts(None);
    // (a) loopInvariantRule I cond body pres (R e) e hI : I (exec_loop e cond body (R e))
    let inv_app = Expr::apps(
        cst(MIRSEM_LOOP_INVARIANT_RULE),
        [
            Expr::bvar(7), // I
            Expr::bvar(5), // cond
            Expr::bvar(4), // body
            Expr::bvar(3), // pres
            r_e,           // n := R e
            Expr::bvar(1), // e
            Expr::bvar(0), // hI
        ],
    );
    // (b) loopRankTerminates R cond body decrease e : eval_cond (exec_loop … (R e)) cond = false
    let term_app = Expr::apps(
        cst(MIRSEM_LOOP_RANK_TERMINATES),
        [
            Expr::bvar(6), // R
            Expr::bvar(5), // cond
            Expr::bvar(4), // body
            Expr::bvar(2), // decrease
            Expr::bvar(1), // e
        ],
    );
    // And.intro A B (a) (b)
    let intro = Expr::apps(cst("And.intro"), [a, b, inv_app, term_app]);
    // hI : I e   (e=0 inside `∀ e`, I=6 there)
    let i_e = Expr::app(Expr::bvar(6), Expr::bvar(0));
    Expr::lam(
        bd(),
        env_pred_ty(),
        Expr::lam(
            bd(),
            env_to_nat,
            Expr::lam(
                bd(),
                cst(MIRSEM_COND),
                Expr::lam(
                    bd(),
                    list_stmt,
                    Expr::lam(
                        bd(),
                        preservation_hyp_type(&Expr::bvar(3), &Expr::bvar(1), &Expr::bvar(0)),
                        Expr::lam(
                            bd(),
                            decrease_hyp_type(&Expr::bvar(3), &Expr::bvar(2), &Expr::bvar(1)),
                            Expr::lam(bd(), env_ty(), Expr::lam(bd(), i_e, intro)),
                        ),
                    ),
                ),
            ),
        ),
    )
}

/// Register `loopTotalCorrect` into `env`. Requires `loopInvariantRule` and
/// `loopRankTerminates` (and their dependencies) already registered. Idempotent.
pub(super) fn register_loop_total_correct(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_LOOP_TOTAL_CORRECT);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let ty = loop_total_correct_type(None);
    let proof = loop_total_correct_proof();
    {
        let tc = TypeChecker::new(env);
        tc.check_type(&proof, &ty).map_err(|e| format!("loopTotalCorrect check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem { name, level_params: vec![], type_: ty, value: proof })
        .map_err(|e| format!("add_decl(loopTotalCorrect): {e:?}"))?;
    Ok(())
}
