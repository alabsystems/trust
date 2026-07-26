// Refinement of a statement sequence: `exec` over an appended list equals the
// threaded composition of its parts. This is the law that lets a multi-statement
// body be discharged one statement at a time, plus the branch and nested-branch
// specialisations.

use super::*;

/// Build the closed `List Stmt` Clean value for an explicit slice of statements
/// (`List.cons s0 (… List.nil)`), de-Bruijn-free (all closed constructors).
pub(super) fn stmts_list_expr(stmts: &[SemStmt]) -> Expr {
    let stmt_ty = cst(MIRSEM_STMT);
    let nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        stmt_ty.clone(),
    );
    stmts.iter().rev().fold(nil, |tail, s| {
        Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [stmt_ty.clone(), s.to_stmt_expr(), tail],
        )
    })
}

/// `List Stmt` as a kernel type.
pub(super) fn list_stmt_ty() -> Expr {
    Expr::app(Expr::const_(Name::from_string("List"), vec![Level::zero()]), cst(MIRSEM_STMT))
}

/// `@Eq Env a b` — equality of environments (`Env : Type` ⇒ `Eq.{1}`).
pub(super) fn eq_env_expr(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [env_ty(), a, b],
    )
}

/// `@Eq Int a b`.
pub(super) fn eq_int_expr(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [int_ty(), a, b],
    )
}

/// Build `step e s = @Stmt.rec.{1} (λ_.Env) (λ i R. set e i (eval_rvalue e R)) s`
/// — the single-statement env update `exec` threads, as a kernel term, where the
/// supplied `e_ref`/`s_ref` denote the env/statement at the CURRENT binder depth.
/// `e_inner_depth` is the de-Bruijn index of `e` from INSIDE the `λ(i)λ(R)` Assign
/// minor (the env lifted past the two field binders).
pub(super) fn step_expr(e_inner_ref: Expr, s_ref: Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let stmt_ty = cst(MIRSEM_STMT);
    let stmt_rec =
        Expr::const_(Name::from_string(MIRSEM_STMT_REC), vec![Level::succ(Level::zero())]);
    let stmt_motive = Expr::lam(bd(), stmt_ty.clone(), env_ty());
    // λ(i:Nat). λ(R:Rvalue). set e i (eval_rvalue e R)   (e = e_inner_ref, past i,R)
    let assign_minor = {
        let i_inner = Expr::bvar(1);
        let r_inner = Expr::bvar(0);
        let evald = Expr::apps(cst(MIRSEM_EVAL_RVALUE), [e_inner_ref.clone(), r_inner]);
        let set_app = Expr::apps(cst(MIRSEM_SET), [e_inner_ref, i_inner, evald]);
        Expr::lam(bd(), cst("Nat"), Expr::lam(bd(), rvalue_ty(), set_app))
    };
    Expr::apps(stmt_rec, [stmt_motive, assign_minor, s_ref])
}

/// Register `Trust.MirSem.appendStmt : List Stmt → List Stmt → List Stmt`
/// (idempotent). See [`MIRSEM_APPEND_STMT`].
pub(super) fn register_append_stmt(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_APPEND_STMT);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let stmt_ty = cst(MIRSEM_STMT);
    let list_stmt = list_stmt_ty();
    let list_rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    // λ(l1).λ(l2). List.rec Stmt (λ_.List Stmt) l2 (λ s rest ih. cons s ih) l1
    let motive = Expr::lam(bd(), list_stmt.clone(), list_stmt.clone());
    let nil_case = Expr::bvar(0); // l2
    let cons_case = {
        // λ s rest ih. List.cons Stmt s ih ; depth: ih=0, rest=1, s=2
        let consed = Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [stmt_ty.clone(), Expr::bvar(2), Expr::bvar(0)],
        );
        Expr::lam(
            bd(),
            stmt_ty.clone(),
            Expr::lam(bd(), list_stmt.clone(), Expr::lam(bd(), list_stmt.clone(), consed)),
        )
    };
    let rec_app =
        Expr::apps(list_rec, [stmt_ty.clone(), motive, nil_case, cons_case, Expr::bvar(1)]);
    let val = Expr::lam(bd(), list_stmt.clone(), Expr::lam(bd(), list_stmt.clone(), rec_app));
    let ty = Expr::pi(bd(), list_stmt.clone(), Expr::pi(bd(), list_stmt.clone(), list_stmt));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(appendStmt): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.exec_threaded : Env → List Stmt → List Stmt → Operand →
/// Int` (idempotent) = `λ e l1 l2 ret. eval (exec e (appendStmt l1 l2)) ret`.
pub(super) fn register_exec_threaded(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_EXEC_THREADED);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // λ(e).λ(l1).λ(l2).λ(ret). eval (exec e (appendStmt l1 l2)) ret
    //   depth: ret=0, l2=1, l1=2, e=3
    let appended = Expr::apps(cst(MIRSEM_APPEND_STMT), [Expr::bvar(2), Expr::bvar(1)]);
    let threaded = Expr::apps(cst(MIRSEM_EXEC), [Expr::bvar(3), appended]);
    let body = Expr::apps(cst(MIRSEM_EVAL), [threaded, Expr::bvar(0)]);
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            list_stmt.clone(),
            Expr::lam(bd(), list_stmt.clone(), Expr::lam(bd(), operand_ty(), body)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            list_stmt.clone(),
            Expr::pi(bd(), list_stmt, Expr::pi(bd(), operand_ty(), int_ty())),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(exec_threaded): {e:?}"))?;
    Ok(())
}

/// Register `Trust.MirSem.denote_substituted : Env → List Stmt → List Stmt →
/// Operand → Int` (idempotent) = `λ e l1 l2 ret. eval (exec (exec e l1) l2) ret`.
pub(super) fn register_denote_substituted(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_DENOTE_SUBST);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    // λ(e).λ(l1).λ(l2).λ(ret). eval (exec (exec e l1) l2) ret  ; depth ret=0,l2=1,l1=2,e=3
    let exec_l1 = Expr::apps(cst(MIRSEM_EXEC), [Expr::bvar(3), Expr::bvar(2)]);
    let exec_l2 = Expr::apps(cst(MIRSEM_EXEC), [exec_l1, Expr::bvar(1)]);
    let body = Expr::apps(cst(MIRSEM_EVAL), [exec_l2, Expr::bvar(0)]);
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            list_stmt.clone(),
            Expr::lam(bd(), list_stmt.clone(), Expr::lam(bd(), operand_ty(), body)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            list_stmt.clone(),
            Expr::pi(bd(), list_stmt, Expr::pi(bd(), operand_ty(), int_ty())),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(denote_substituted): {e:?}"))?;
    Ok(())
}

/// The ENV-LEVEL append/threading law TYPE: `∀ (l1 l2 : List Stmt)(e : Env),
/// exec (exec e l1) l2 = exec e (appendStmt l1 l2)`. Inside the three binders the
/// de-Bruijn indices are `e=0, l2=1, l1=2`.
pub(super) fn exec_append_law_type() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let exec = cst(MIRSEM_EXEC);
    let lhs = Expr::apps(
        exec.clone(),
        [Expr::apps(exec.clone(), [Expr::bvar(0), Expr::bvar(2)]), Expr::bvar(1)],
    );
    let rhs = Expr::apps(
        exec,
        [Expr::bvar(0), Expr::apps(cst(MIRSEM_APPEND_STMT), [Expr::bvar(2), Expr::bvar(1)])],
    );
    let inner = Expr::pi(bd(), env_ty(), eq_env_expr(lhs, rhs));
    let mid = Expr::pi(bd(), list_stmt.clone(), inner);
    Expr::pi(bd(), list_stmt, mid)
}

/// The ENV-LEVEL append/threading law PROOF, by `List.rec` induction on `l1`:
/// `λ(l1). List.rec.{0,0} Stmt motive nil_proof cons_proof l1`. The Prop motive
/// `P l1 := ∀ l2 e, exec (exec e l1) l2 = exec e (appendStmt l1 l2)`. See the
/// module banner for the base/step structure (base = Eq.refl on the empty prefix;
/// step = `ih l2 (step e s)`, the IH at the stepped env).
pub(super) fn exec_append_law_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let stmt_ty = cst(MIRSEM_STMT);
    let exec = cst(MIRSEM_EXEC);
    let append = cst(MIRSEM_APPEND_STMT);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);

    // motive : List Stmt → Prop  = λ(l1). ∀ l2 e, exec (exec e l1) l2 = exec e (append l1 l2)
    //   inside λ(l1): l1=bvar(0); body Pi l2 (=bvar1), Pi e (=bvar0): e=0,l2=1,l1=2.
    let motive = {
        let lhs = Expr::apps(
            exec.clone(),
            [Expr::apps(exec.clone(), [Expr::bvar(0), Expr::bvar(2)]), Expr::bvar(1)],
        );
        let rhs = Expr::apps(
            exec.clone(),
            [Expr::bvar(0), Expr::apps(append.clone(), [Expr::bvar(2), Expr::bvar(1)])],
        );
        let inner = Expr::pi(bd(), env_ty(), eq_env_expr(lhs, rhs));
        let quant = Expr::pi(bd(), list_stmt.clone(), inner);
        Expr::lam(bd(), list_stmt.clone(), quant)
    };

    // nil_proof : ∀ l2 e, exec (exec e nil) l2 = exec e (append nil l2)
    //   both sides ≡ exec e l2 ⇒ Eq.refl Env (exec e l2). depth: e=0,l2=1.
    let nil_proof = {
        let exec_e_l2 = Expr::apps(exec.clone(), [Expr::bvar(0), Expr::bvar(1)]);
        Expr::lam(
            bd(),
            list_stmt.clone(),
            Expr::lam(bd(), env_ty(), Expr::apps(eq_refl.clone(), [env_ty(), exec_e_l2])),
        )
    };

    // cons_proof : λ(s)(rest)(ih)(l2)(e). ih l2 (step e s)
    //   depth inside λ(s)λ(rest)λ(ih)λ(l2)λ(e): e=0,l2=1,ih=2,rest=3,s=4.
    let cons_proof = {
        // step e s — the env update; built at depth where e=bvar(0)+lifts. Inside the
        // Assign minor's λ(i)λ(R) the env is lifted past i,R ⇒ e = bvar(2).
        let step_e_s = step_expr(Expr::bvar(2), Expr::bvar(4));
        // ih l2 (step e s) : ih=bvar(2), l2=bvar(1)
        let ih_app = Expr::apps(Expr::bvar(2), [Expr::bvar(1), step_e_s]);
        // ih's TYPE annotation = motive rest = ∀ l2 e, exec (exec e rest) l2 =
        //   exec e (append rest l2). Built at depth where rest=bvar(0) (inside λs λrest):
        let ih_ty = {
            // for the Pi l2,e body: e=0,l2=1,rest=2.
            let lhs = Expr::apps(
                exec.clone(),
                [Expr::apps(exec.clone(), [Expr::bvar(0), Expr::bvar(2)]), Expr::bvar(1)],
            );
            let rhs = Expr::apps(
                exec.clone(),
                [Expr::bvar(0), Expr::apps(append.clone(), [Expr::bvar(2), Expr::bvar(1)])],
            );
            let inner = Expr::pi(bd(), env_ty(), eq_env_expr(lhs, rhs));
            Expr::pi(bd(), list_stmt.clone(), inner)
        };
        Expr::lam(
            bd(),
            stmt_ty.clone(), // s
            Expr::lam(
                bd(),
                list_stmt.clone(), // rest
                Expr::lam(
                    bd(),
                    ih_ty, // ih : motive rest
                    Expr::lam(
                        bd(),
                        list_stmt.clone(), // l2
                        Expr::lam(bd(), env_ty(), ih_app),
                    ),
                ),
            ),
        )
    };

    // List.rec.{0,0} Stmt motive nil_proof cons_proof l1   (Prop motive ⇒ level 0).
    let list_rec_prop =
        Expr::const_(Name::from_string("List.rec"), vec![Level::zero(), Level::zero()]);
    let rec_app =
        Expr::apps(list_rec_prop, [stmt_ty.clone(), motive, nil_proof, cons_proof, Expr::bvar(0)]);
    Expr::lam(bd(), list_stmt, rec_app)
}

/// The REFINEMENT theorem TYPE: `∀ (e : Env)(l1 l2 : List Stmt)(ret : Operand),
/// exec_threaded e l1 l2 ret = denote_substituted e l1 l2 ret`. Inside the four
/// binders: `ret=0, l2=1, l1=2, e=3`. If `claimed` overrides a side it is used in
/// place of the true RHS denotation (fail-closed test hook).
pub(super) fn refinement_type(claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let list_stmt = list_stmt_ty();
    let args = [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)];
    let lhs = Expr::apps(cst(MIRSEM_EXEC_THREADED), args.clone());
    let rhs = claimed_rhs.cloned().unwrap_or_else(|| Expr::apps(cst(MIRSEM_DENOTE_SUBST), args));
    let body = eq_int_expr(lhs, rhs);
    Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            list_stmt.clone(),
            Expr::pi(bd(), list_stmt, Expr::pi(bd(), operand_ty(), body)),
        ),
    )
}

/// The REFINEMENT theorem PROOF: `λ(e)(l1)(l2)(ret). congrArg.{1,1} Env Int
/// (exec (exec e l1) l2) (exec e (append l1 l2)) (λ env. eval env ret)
/// (execAppendLaw l1 l2 e)`. Both denotations are `eval _ ret` of an env; the env
/// equality is the append law (note ARG ORDER: `execAppendLaw l1 l2 e` gives
/// `exec (exec e l1) l2 = exec e (append l1 l2)`), and `congrArg (eval · ret)`
/// transports it to the `Int` equality `denote_substituted = exec_threaded`. We
/// state the theorem `exec_threaded = denote_substituted`, so we apply the law's
/// SYMMETRIC orientation via `Eq.symm`.
pub(super) fn refinement_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // depth inside λ(e)λ(l1)λ(l2)λ(ret): ret=0, l2=1, l1=2, e=3.
    let exec = cst(MIRSEM_EXEC);
    let append = cst(MIRSEM_APPEND_STMT);
    // env A = exec (exec e l1) l2  (denote_substituted's env)
    let env_a = Expr::apps(
        exec.clone(),
        [Expr::apps(exec.clone(), [Expr::bvar(3), Expr::bvar(2)]), Expr::bvar(1)],
    );
    // env B = exec e (append l1 l2)  (exec_threaded's env)
    let env_b = Expr::apps(
        exec.clone(),
        [Expr::bvar(3), Expr::apps(append.clone(), [Expr::bvar(2), Expr::bvar(1)])],
    );
    // f = λ(env : Env). eval env ret   (ret lifted past env ⇒ ret = bvar(1))
    let f = Expr::lam(bd(), env_ty(), Expr::apps(cst(MIRSEM_EVAL), [Expr::bvar(0), Expr::bvar(1)]));
    // execAppendLaw l1 l2 e : exec (exec e l1) l2 = exec e (append l1 l2)  (= env_a = env_b)
    let law =
        Expr::apps(cst(MIRSEM_EXEC_APPEND_LAW), [Expr::bvar(2), Expr::bvar(1), Expr::bvar(3)]);
    // congrArg.{1,1} Env Int env_a env_b f law : (f env_a) = (f env_b)
    //   i.e. eval (exec(exec e l1)l2) ret = eval (exec e (append l1 l2)) ret
    //      = denote_substituted … = exec_threaded …
    let congr = Expr::const_(
        Name::from_string("congrArg"),
        vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
    );
    let congr_app = Expr::apps(congr, [env_ty(), int_ty(), env_a, env_b, f, law]);
    // That proves `denote_substituted = exec_threaded`; we want the symmetric
    // `exec_threaded = denote_substituted`, so apply Eq.symm.
    // Eq.symm.{1} {Int} {dsub} {exth} (congr_app)
    let dsub = Expr::apps(
        cst(MIRSEM_DENOTE_SUBST),
        [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
    );
    let exth = Expr::apps(
        cst(MIRSEM_EXEC_THREADED),
        [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
    );
    let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![Level::succ(Level::zero())]);
    let symm_app = Expr::apps(eq_symm, [int_ty(), dsub, exth, congr_app]);
    Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            list_stmt_ty(),
            Expr::lam(bd(), list_stmt_ty(), Expr::lam(bd(), operand_ty(), symm_app)),
        ),
    )
}

/// Build the full refinement environment: the `MirSem` anchor plus `appendStmt`,
/// the two denotations (`exec_threaded`, `denote_substituted`), the inductive
/// env-level append law (`execAppendLaw`), and the refinement theorem itself
/// (`refinement`) — all registered and kernel-checked. Returns the environment so
/// callers can audit axiom closure or instantiate the theorem at a function.
pub fn mirsem_refinement_env() -> Result<Environment, String> {
    let mut env = mirsem_env()?;
    register_append_stmt(&mut env)?;
    register_exec_threaded(&mut env)?;
    register_denote_substituted(&mut env)?;

    // The inductive env-level append law (proven by List.rec on l1).
    let law_ty = exec_append_law_type();
    let law_proof = exec_append_law_proof();
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(&law_proof, &law_ty)
            .map_err(|e| format!("execAppendLaw check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_EXEC_APPEND_LAW),
        level_params: vec![],
        type_: law_ty,
        value: law_proof,
    })
    .map_err(|e| format!("add_decl(execAppendLaw): {e:?}"))?;

    // The refinement theorem (congrArg over the law).
    let ref_ty = refinement_type(None);
    let ref_proof = refinement_proof();
    {
        let tc = TypeChecker::new(&env);
        tc.check_type(&ref_proof, &ref_ty).map_err(|e| format!("refinement check_type: {e:?}"))?;
    }
    env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_REFINEMENT),
        level_params: vec![],
        type_: ref_ty,
        value: ref_proof,
    })
    .map_err(|e| format!("add_decl(refinement): {e:?}"))?;
    Ok(env)
}

/// Pin the refinement meta-theorem anchor and audit its axiom closure: confirm the
/// two denotations, the inductive append law, AND the refinement theorem each rest
/// on ONLY the 3 foundational axioms (modulo 3, no 4th axiom). Mirrors
/// [`pin_mirsem_anchor`] for the Step-6 capstone.
#[must_use]
pub fn pin_mirsem_refinement_anchor() -> AnchorVerdict {
    let env = match mirsem_refinement_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for n in [
        MIRSEM_APPEND_STMT,
        MIRSEM_EXEC_THREADED,
        MIRSEM_DENOTE_SUBST,
        MIRSEM_EXEC_APPEND_LAW,
        MIRSEM_REFINEMENT,
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

/// Check the GENERAL refinement theorem against the real clean-kernel (build the
/// statement + the congrArg-over-induction proof, `check_type`, register, audit).
/// `claimed_rhs = Some(e)` overrides the true RHS denotation — the fail-closed hook
/// (a wrong refinement claim must NOT type-check).
#[must_use]
pub fn check_refinement() -> RefinementVerdict {
    check_refinement_inner(None)
}

pub(super) fn check_refinement_inner(claimed_rhs: Option<&Expr>) -> RefinementVerdict {
    // Build the env up to (but not including) the refinement theorem, so we can
    // check a (possibly wrong) claim against the SAME proof term.
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    if let Err(e) = register_append_stmt(&mut env)
        .and_then(|()| register_exec_threaded(&mut env))
        .and_then(|()| register_denote_substituted(&mut env))
    {
        return RefinementVerdict::KernelRejected(e);
    }
    let law_ty = exec_append_law_type();
    let law_proof = exec_append_law_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&law_proof, &law_ty) {
            return RefinementVerdict::KernelRejected(format!("execAppendLaw: {e:?}"));
        }
    }
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(MIRSEM_EXEC_APPEND_LAW),
        level_params: vec![],
        type_: law_ty,
        value: law_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add execAppendLaw: {e:?}"));
    }

    let ref_ty = refinement_type(claimed_rhs);
    let ref_proof = refinement_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&ref_proof, &ref_ty) {
            return RefinementVerdict::KernelRejected(format!("refinement check_type: {e:?}"));
        }
    }
    let name = Name::from_string(MIRSEM_REFINEMENT);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: ref_ty,
        value: ref_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add refinement: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// Instantiate the refinement meta-theorem at a CONCRETE function's
/// `MirSem.Function` value: build `refinement (Var-free) e STMTS [] RET`, where
/// `STMTS` is the function's pinned SSA trace and `RET` its return operand, and
/// kernel-check that the instance holds modulo 3. Because the instance is a direct
/// APPLICATION of the general `refinement` theorem to the function's closed
/// `(stmts, ret)` value, type-checking the application IS the corollary: this
/// function's whole straight-line body is operationally ≡ its substitution
/// denotation, kernel-proven modulo 3, with NO new proof obligation.
///
/// `claimed_ret` overrides the return operand (fail-closed test hook): a refinement
/// claim with the WRONG return must NOT type-check.
pub(super) fn check_function_refinement_inner(
    r: &SemReturn,
    claimed_ret: Option<&SemOperand>,
) -> RefinementVerdict {
    let env = match mirsem_refinement_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let bd = || BinderData::from(BinderInfo::Default);
    // The instance type: ∀ e, exec_threaded e STMTS nil RET = denote_substituted e STMTS nil RET.
    // (Quantify over e only; STMTS/RET/nil are closed.) Inside ∀(e): e = bvar(0).
    let stmts_e = stmts_list_expr(&r.stmts);
    let nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        cst(MIRSEM_STMT),
    );
    let ret_e = claimed_ret.unwrap_or(&r.ret).to_operand_expr();
    let args = move |e: Expr| [e, stmts_e.clone(), nil.clone(), ret_e.clone()];
    let lhs = Expr::apps(cst(MIRSEM_EXEC_THREADED), args(Expr::bvar(0)));
    let rhs = Expr::apps(cst(MIRSEM_DENOTE_SUBST), args(Expr::bvar(0)));
    let inst_ty = Expr::pi(bd(), env_ty(), eq_int_expr(lhs, rhs));
    // The instance proof: λ(e). refinement e STMTS nil RET. This is a direct
    // application of the general theorem — type-checking it IS the corollary.
    let inst_proof = {
        let app = Expr::apps(cst(MIRSEM_REFINEMENT), args(Expr::bvar(0)));
        Expr::lam(bd(), env_ty(), app)
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&inst_proof, &inst_ty) {
            return RefinementVerdict::KernelRejected(format!("instance check_type: {e:?}"));
        }
    }
    let mut env = env;
    let name = Name::from_string("Trust.MirSem.refinement.instance");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: inst_ty,
        value: inst_proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add instance: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("instance decl not found".to_string()),
    }
}

/// THE WHOLE-FUNCTION REFINEMENT HOOK (Goal #4 capstone). For a reflected function
/// in the modeled straight-line fragment, instantiate the general refinement
/// meta-theorem at the function's `MirSem.Function` value and return a
/// kernel-checked refinement certificate — `Some` iff the function's `(stmts, ret)`
/// witness is recoverable (modeled scalar SSA body + return) AND the instance
/// kernel-checks modulo 3. The per-function adequacy is thereby a COROLLARY of the
/// meta-theorem (a direct application), not a separately-proven witness.
///
/// Fail-closed (`None`): a function whose return/body is outside the modeled
/// straight-line fragment (loops, calls, branches, non-arithmetic rvalues) — its
/// `SemReturn` witness is unrecoverable — or whose instance does not kernel-check
/// modulo 3. Never a false certificate.
#[must_use]
pub fn whole_function_refinement_witness(
    func: &trust_types::VerifiableFunction,
) -> Option<RefinementCertificate> {
    trust_vcgen::validate_function(func).ok()?;
    if !crate::assignment_types::all_assignments_match(&func.body) {
        return None;
    }
    let arg_count = func.body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let r = sem_return_of_mir(func, &param_index)?;
    match check_function_refinement_inner(&r, None) {
        RefinementVerdict::ProvenModulo3 => {
            Some(RefinementCertificate { function: r, verdict: RefinementVerdict::ProvenModulo3 })
        }
        _ => None,
    }
}

/// Register `Trust.MirSem.denote_substitutedB : Env → Cond → Rvalue → Rvalue → Int`
/// (idempotent) = `λ e c t f. eval_ite e c t f`. A reducible wrapper over `eval_ite`,
/// pinned as a NAMED branch denotation so `refinementB` connects it to the live grounder.
pub(super) fn register_denote_substituted_b(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_DENOTE_SUBST_B);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // λ(e).λ(c).λ(t).λ(f). eval_ite e c t f   ; depth f=0,t=1,c=2,e=3
    let body = Expr::apps(
        cst(MIRSEM_EVAL_ITE),
        [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
    );
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(bd(), rvalue_ty(), Expr::lam(bd(), rvalue_ty(), body)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(bd(), rvalue_ty(), Expr::pi(bd(), rvalue_ty(), int_ty())),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(denote_substitutedB): {e:?}"))?;
    Ok(())
}

/// Build the branch-refinement environment: the MirSem anchor + `denote_substitutedB`.
pub(crate) fn mirsem_branch_refinement_env() -> Result<Environment, String> {
    let mut env = mirsem_env()?;
    register_denote_substituted_b(&mut env)?;
    Ok(env)
}

/// The branch-refinement *theorem statement* for a guarded return `r`:
///
/// ```text
/// ∀ (x⃗ : Int), denote_substitutedB E c t f = ground_int(r.to_formula())
/// ```
///
/// `E` is the `set`-chain grounding env over `r`'s referenced parameter indices, and the
/// RHS is the LIVE-grounded `Formula::Ite`. `claimed_rhs = Some` swaps the live-grounded
/// RHS (fail-closed test); `None` (the function returns `None`) means the live grounder
/// declined `r.to_formula()`.
pub(super) fn branch_refinement_statement(r: &SemCfReturn, claimed_rhs: Option<&Expr>) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let indices = r.var_indices();
    let n = indices.len();
    let env = grounding_env_expr(&indices, &|i| Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    let lhs = Expr::apps(
        cst(MIRSEM_DENOTE_SUBST_B),
        [env, r.cond.to_cond_expr(), r.then_rv.to_rvalue_expr(), r.else_rv.to_rvalue_expr()],
    );
    let rhs = match claimed_rhs {
        Some(e) => e.clone(),
        None => live_ground_int(&r.to_formula(), &indices)?,
    };
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        body = Expr::pi(bd(), int_ty(), body);
    }
    Some(body)
}

/// The branch-refinement *proof term*: `λ x⃗. @Eq.refl Int (ground_int(r.to_formula()))`.
/// `denote_substitutedB E c t f` ι/δ-reduces (through `eval_ite`/`eval_cond`/
/// `eval_rvalue`) to the live-grounded `Ite` term, so reflexivity at it inhabits the
/// equality. `None` when the live grounder declines `r.to_formula()`.
pub(super) fn branch_refinement_proof(r: &SemCfReturn) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let indices = r.var_indices();
    let n = indices.len();
    let rhs = live_ground_int(&r.to_formula(), &indices)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check the BRANCH REFINEMENT for a guarded return `r` against the REAL clean-kernel:
/// build `∀ x⃗. denote_substitutedB E c t f = ground_int(r.to_formula())` and the
/// reflexivity-after-reduction proof, `check_type`, register, audit the axiom closure.
///
/// A [`RefinementVerdict::ProvenModulo3`] means: the branch operational denotation
/// (`eval_ite`, the conditional eval the guarded control-flow return folds) is EXACTLY
/// the term the LIVE `clean_ground::ground_int` grounds the guarded return's
/// `Formula::Ite` to — kernel-verified modulo 3. So the guarded return's reflection is
/// faithful, mechanically connected to the live grounder.
#[must_use]
pub fn check_branch_refinement(r: &SemCfReturn) -> RefinementVerdict {
    check_branch_refinement_inner(r, None)
}

pub(super) fn check_branch_refinement_inner(r: &SemCfReturn, claimed_rhs: Option<&Expr>) -> RefinementVerdict {
    let mut env = match mirsem_branch_refinement_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let Some(statement) = branch_refinement_statement(r, claimed_rhs) else {
        return RefinementVerdict::KernelRejected(
            "live ground_int declined this guarded return's reflected Ite formula".to_string(),
        );
    };
    let Some(proof) = branch_refinement_proof(r) else {
        return RefinementVerdict::KernelRejected(
            "live ground_int declined this guarded return's reflected Ite formula".to_string(),
        );
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!("refinementB check_type: {e:?}"));
        }
    }
    let name = Name::from_string(MIRSEM_REFINEMENT_B);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add refinementB: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("refinementB decl not found".to_string()),
    }
}

/// Pin the branch-refinement anchor (`denote_substitutedB`) and audit its axiom closure
/// — confirm it rests on ONLY the 3 foundational axioms (modulo 3, no 4th axiom).
#[must_use]
pub fn pin_branch_refinement_anchor() -> AnchorVerdict {
    let env = match mirsem_branch_refinement_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    match env.axiom_deps(&Name::from_string(MIRSEM_DENOTE_SUBST_B)) {
        Some(residue) if residue.is_empty() => AnchorVerdict::Modulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            AnchorVerdict::Residue(names)
        }
        None => AnchorVerdict::KernelRejected(format!("decl not found: {MIRSEM_DENOTE_SUBST_B}")),
    }
}

/// THE BRANCH REFINEMENT HOOK. For a reflected function whose return is a guarded
/// single-branch return in the modeled fragment, recover its `SemCfReturn` witness and
/// kernel-check the branch refinement (`denote_substitutedB` ≡ the live-grounded `Ite`)
/// modulo 3. Fail-closed (`None`): a function whose return is straight-line, a
/// nested/multi-condition guard, or has an arm value outside the modeled scalar
/// fragment — its `SemCfReturn` witness is unrecoverable — or whose refinement does not
/// kernel-check modulo 3. Never a false certificate.
#[must_use]
pub fn branch_refinement_witness(
    func: &trust_types::VerifiableFunction,
) -> Option<BranchRefinementCertificate> {
    let arg_count = func.body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let r = sem_cf_return_of_mir(func, &param_index)?;
    match check_branch_refinement(&r) {
        RefinementVerdict::ProvenModulo3 => {
            Some(BranchRefinementCertificate { ret: r, verdict: RefinementVerdict::ProvenModulo3 })
        }
        _ => None,
    }
}

// ===========================================================================
// Step 6BN — THE NESTED / MULTI-WAY BRANCH REFINEMENT: refinementBNested.
//
// `refinementB` (above) covers a SINGLE `SwitchInt` branch (`if c { t } else { f }`).
// A NESTED guard `if c1 { t1 } else if c2 { t2 } else { e }` (e.g. `sign`, a 3-arm
// clamp) has an ELSE arm that is itself a guarded if-then-else — outside the
// single-branch `SemCfReturn`. This step recovers the recursive `SemBranchTree` witness
// and kernel-proves (modulo 3) that its NESTED `iteI`-tree denotation equals the LIVE
// grounder's nested `Bool.rec` for `tree.to_formula()` — the multi-way generalization
// of `refinementB`, strictly additive (`refinementB`/`SemCfReturn` untouched).
// ===========================================================================
/// Register `Trust.MirSem.denote_substitutedBNested : Env → Cond → Int → Int → Int`
/// (idempotent) = `λ e c t f. iteI e c t f`. A reducible wrapper over `iteI`, pinned as
/// the NAMED nested-branch denotation so `refinementBNested` connects it to the live
/// grounder (the multi-way analogue of `denote_substitutedB`).
pub(super) fn register_denote_substituted_b_nested(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_DENOTE_SUBST_B_NESTED);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // λ(e).λ(c).λ(t:Int).λ(f:Int). iteI e c t f   ; depth f=0,t=1,c=2,e=3
    let body =
        Expr::apps(cst(MIRSEM_ITE_I), [Expr::bvar(3), Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)]);
    let val = Expr::lam(
        bd(),
        env_ty(),
        Expr::lam(
            bd(),
            cst(MIRSEM_COND),
            Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body)),
        ),
    );
    let ty = Expr::pi(
        bd(),
        env_ty(),
        Expr::pi(
            bd(),
            cst(MIRSEM_COND),
            Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), int_ty())),
        ),
    );
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(denote_substitutedBNested): {e:?}"))?;
    Ok(())
}

/// Build the nested-branch-refinement environment: the MirSem anchor (which already
/// registers `iteI`) + `denote_substitutedBNested`.
pub(crate) fn mirsem_nested_branch_refinement_env() -> Result<Environment, String> {
    let mut env = mirsem_env()?;
    register_denote_substituted_b_nested(&mut env)?;
    Ok(env)
}

/// The nested-branch-refinement *theorem statement* for a nested return tree `t`:
///
/// ```text
/// ∀ (x⃗ : Int), <iteI-tree denotation of t under E> = ground_int(t.to_formula())
/// ```
///
/// The LHS is the nested `iteI` term `SemBranchTree::denotation` builds over the `set`-
/// chain grounding env `E`; the RHS is the LIVE-grounded nested `Formula::Ite`.
/// `claimed_rhs = Some` swaps the live-grounded RHS (fail-closed test); `None` (the
/// function returns `None`) means the live grounder declined `t.to_formula()`.
pub(super) fn nested_branch_refinement_statement(
    t: &SemBranchTree,
    claimed_rhs: Option<&Expr>,
) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let indices = t.var_indices();
    let n = indices.len();
    let env = grounding_env_expr(&indices, &|i| Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    let lhs = t.denotation(&env);
    let rhs = match claimed_rhs {
        Some(e) => e.clone(),
        None => live_ground_int(&t.to_formula(), &indices)?,
    };
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        body = Expr::pi(bd(), int_ty(), body);
    }
    Some(body)
}

/// The nested-branch-refinement *proof term*: `λ x⃗. @Eq.refl Int (ground_int(t.to_formula()))`.
/// The `iteI`-tree denotation ι/δ-reduces (each `iteI` → `Bool.rec`, leaves through
/// `eval_rvalue`/`eval_cond`) to the live-grounded nested `Ite` term, so reflexivity at
/// it inhabits the equality. `None` when the live grounder declines `t.to_formula()`.
pub(super) fn nested_branch_refinement_proof(t: &SemBranchTree) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let indices = t.var_indices();
    let n = indices.len();
    let rhs = live_ground_int(&t.to_formula(), &indices)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check the NESTED-BRANCH REFINEMENT for a nested return tree `t` against the REAL
/// clean-kernel: build `∀ x⃗. <iteI-tree> = ground_int(t.to_formula())` and the
/// reflexivity-after-reduction proof, `check_type`, register, audit the axiom closure.
///
/// A [`RefinementVerdict::ProvenModulo3`] means: the nested branch's operational `iteI`
/// denotation is EXACTLY the term the LIVE `clean_ground::ground_int` grounds the
/// multi-way return's nested `Formula::Ite` to — kernel-verified modulo 3. A WRONG
/// nested-arm claim (`claimed_rhs = Some(wrong)`) is kernel-REJECTED (fail-closed).
#[must_use]
pub fn check_nested_branch_refinement(t: &SemBranchTree) -> RefinementVerdict {
    check_nested_branch_refinement_inner(t, None)
}

pub(super) fn check_nested_branch_refinement_inner(
    t: &SemBranchTree,
    claimed_rhs: Option<&Expr>,
) -> RefinementVerdict {
    let mut env = match mirsem_nested_branch_refinement_env() {
        Ok(e) => e,
        Err(e) => return RefinementVerdict::KernelRejected(e),
    };
    let Some(statement) = nested_branch_refinement_statement(t, claimed_rhs) else {
        return RefinementVerdict::KernelRejected(
            "live ground_int declined this nested return's reflected Ite formula".to_string(),
        );
    };
    let Some(proof) = nested_branch_refinement_proof(t) else {
        return RefinementVerdict::KernelRejected(
            "live ground_int declined this nested return's reflected Ite formula".to_string(),
        );
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return RefinementVerdict::KernelRejected(format!(
                "refinementBNested check_type: {e:?}"
            ));
        }
    }
    let name = Name::from_string(MIRSEM_REFINEMENT_B_NESTED);
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return RefinementVerdict::KernelRejected(format!("add refinementBNested: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => RefinementVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            RefinementVerdict::Residue(names)
        }
        None => RefinementVerdict::KernelRejected("refinementBNested decl not found".to_string()),
    }
}

/// Pin the nested-branch-refinement anchor (`iteI` + `denote_substitutedBNested`) and
/// audit its axiom closure — confirm it rests on ONLY the 3 foundational axioms.
#[must_use]
pub fn pin_nested_branch_refinement_anchor() -> AnchorVerdict {
    let env = match mirsem_nested_branch_refinement_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for n in [MIRSEM_ITE_I, MIRSEM_DENOTE_SUBST_B_NESTED] {
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

/// THE NESTED-BRANCH REFINEMENT HOOK. For a reflected function whose return is a NESTED
/// / multi-way guarded return in the modeled fragment, recover its `SemBranchTree`
/// witness and kernel-check the nested-branch refinement (the `iteI`-tree denotation ≡
/// the live-grounded nested `Ite`) modulo 3. Fail-closed (`None`): a function whose
/// return is straight-line, a single-branch guard (handled by `branch_refinement_witness`
/// — a nested witness is only minted for a GENUINELY nested tree), or has an arm value
/// outside the modeled scalar fragment, or whose refinement does not kernel-check
/// modulo 3. Never a false certificate.
#[must_use]
pub fn nested_branch_refinement_witness(
    func: &trust_types::VerifiableFunction,
) -> Option<NestedBranchRefinementCertificate> {
    let arg_count = func.body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    // NON-OVERLAP GATE. The SINGLE-BRANCH path (`sem_cf_return_of_mir`) already covers a
    // bare `if cmp {…}` AND a CONJUNCTIVE `if c1 && c2 {…}` guard (a short-circuit chain
    // whose value-0 paths all reach the SAME else arm — `conj_guard`). That chain is
    // structurally a nested tree (`Ite(c1, Ite(c2, t, e), e)`), so to avoid minting a
    // SECOND certificate for a return the single-branch path already certifies, decline
    // here whenever the single-branch path recognizes the function. The nested path is
    // thus reserved for GENUINELY multi-way returns (≥ 3 distinct arms reaching distinct
    // values — `sign`, a 3-arm clamp) that no existing path handles.
    if sem_cf_return_of_mir(func, &param_index).is_some() {
        return None;
    }
    // Trust: BRANCHY call-arm sub-axis — `callees: None`: this is the MirSem-
    // certifying path (`check_nested_branch_refinement` below has no `Formula` for
    // an opaque call), so it NEVER looks for call-terminated arms — byte-identical
    // to the pre-increment recognizer.
    let t = sem_nested_branch_of_mir(func, &param_index, None)?;
    // Only a GENUINELY nested tree uses this path; a non-nested (single-branch) tree is
    // covered by `branch_refinement_witness`, so we fail-closed here to avoid a second
    // certificate for the same return.
    if !t.is_nested() {
        return None;
    }
    match check_nested_branch_refinement(&t) {
        RefinementVerdict::ProvenModulo3 => Some(NestedBranchRefinementCertificate {
            tree: t,
            verdict: RefinementVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// The PURE SYNTACTIC single-branch recognizer — `sem_cf_return_of_mir` with the standard
/// parameter mapping, minting NO MirSem kernel certificate. (Seam B of the via-trustir
/// de-MirSem-ing: the trust-ir-primary branch / guarded-index paths need only the
/// recognized SHAPE — the trust-ir witness is their kernel evidence — so they consume
/// this extractor instead of `branch_refinement_witness`, which additionally kernel-proves
/// the MirSem branch refinement.) The `Sem*` types are Rust-side recognizer IR, not a
/// Clean trust root. Fail-closed exactly as the underlying extractor.
#[must_use]
pub(crate) fn sem_cf_return_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemCfReturn> {
    let arg_count = func.body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    sem_cf_return_of_mir(func, &param_index)
}

/// The PURE SYNTACTIC nested-branch recognizer — `sem_nested_branch_of_mir` behind the
/// SAME non-overlap + `is_nested` gates `nested_branch_refinement_witness` applies (the
/// nested shape is reserved for genuinely multi-way returns the single-branch recognizer
/// declines), minting NO MirSem kernel certificate. See [`sem_cf_return_shape_of`].
#[must_use]
pub(crate) fn sem_nested_branch_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemBranchTree> {
    let arg_count = func.body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    if sem_cf_return_of_mir(func, &param_index).is_some() {
        return None;
    }
    // Trust: BRANCHY call-arm sub-axis — `callees: None`: this shape-only path
    // certifies a PLAIN (rvalue-only) nested branch via the trust-ir `IrCfg`
    // built by `sem_branch_tree_to_ir_cfg` (`prove.rs`), which has no `CallReturn`
    // handling — it must never see a `CallLeaf`, so it never looks for
    // call-terminated arms. `sem_branch_call_shape_of` below is the call-armed
    // sibling.
    let t = sem_nested_branch_of_mir(func, &param_index, None)?;
    if !t.is_nested() {
        return None;
    }
    Some(t)
}

/// Trust: BRANCHY call-arm sub-axis — the shape-only recognizer for a call-armed
/// branch (`if c { g(a) } else { h(b) }`, or a MIX of a call arm and a plain
/// scalar arm): [`sem_nested_branch_of_mir`] WITH the certified-callee registry
/// threaded in, requiring the resulting tree contain AT LEAST ONE `CallLeaf` (a
/// tree with none is already covered by [`sem_cf_return_shape_of`] /
/// [`sem_nested_branch_shape_of`] — this recognizer is reserved for the
/// genuinely NEW call-armed shape, so it never mints a second certificate for a
/// function those already cover). Unlike the two siblings above, this path does
/// NOT require `is_nested()` — a depth-1 two-call-arm tree (`Node(cond,
/// CallLeaf, CallLeaf)`) IS the target shape (`SemCfReturn` structurally cannot
/// represent a call arm, so there is no overlap risk with the single-branch
/// path at ANY depth). Mints NO MirSem kernel certificate (Seam B: shape only —
/// the trust-ir witness, `prove::branch_call_fully_faithful_via_trustir`, is
/// this path's kernel evidence). Fail-closed exactly as the underlying
/// extractor.
#[must_use]
pub(crate) fn sem_branch_call_shape_of(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemBranchTree> {
    let arg_count = func.body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let t = sem_nested_branch_of_mir(func, &param_index, Some(callees))?;
    if !t.contains_call_leaf() {
        return None; // no call arm anywhere — already covered by the plain paths.
    }
    Some(t)
}
