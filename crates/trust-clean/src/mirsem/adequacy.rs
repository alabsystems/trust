// Adequacy: the claim that a MirSem term denotes the same value the Trust-side
// `Formula` does. Each shape gets a statement, a proof term and a checked
// verdict; the witness functions are the only way an adequacy claim reaches a
// certificate, so an unproved shape must return `None` rather than a default.

use super::*;

/// The canonical free-variable NAME for the parameter at de-Bruijn index `p` — the
/// name `SemOperand::to_formula` keys a parameter `Var p` by, and the name the
/// grounder-connected adequacy binds to its de-Bruijn binder. (Any injective
/// index→name map works; the bridge only requires `to_formula` and the grounding
/// `params` map agree on it.)
pub(super) fn var_name(p: u64) -> String {
    format!("p{p}")
}

// ---------------------------------------------------------------------------
// GROUNDER-CONNECTED adequacy (the LIVE `ground_int` bridge for Lemmas 1A/1B).
//
// THE INTEGRITY FIX (mirrors `safety_vc_is_faithful_formula_aware` for safety VCs).
// The hand-built `denotation()` term mirrors what `ground_int` *should* emit, but is
// reconstructed by THIS module — so the per-op adequacy connects to the live grounder
// only by PROSE. The functions below close that bridge: they ground the operand /
// rvalue's ACTUAL reflected `Formula` (`to_formula()`) through the LIVE
// `clean_ground::ground_int`, and kernel-check that the live-grounded term is def-eq
// (modulo 3) to `eval`'s value, so the per-op adequacy is mechanically
// grounder-connected, never prose.
//
// THE RECONCILIATION (the audit's Var-binder-vs-env-application mismatch).
// `eval e (Var p)` ι-reduces to the ENV APPLICATION `e p`, but the live grounder maps
// `Formula::Var(name)` to a BARE de-Bruijn binder `bvar(k)` (the parameter's own bound
// `Int`), NOT `e p`. These are genuinely different shapes — so we cannot equate them
// under an ARBITRARY `e`. We reconcile HONESTLY by supplying a SPECIFIC `e`: an env
// built by a `set`-chain so that `e p_i` ι-reduces to EXACTLY the `i`-th bound `Int`
// binder (the SAME binder `ground_int` emits for `Var name`). Then `eval e (Var p_i)`
// reduces (env application → `set`-lookup, `Nat.beq p_i p_i → Bool.true`) to that
// binder, and the live-grounded RHS is that same binder — def-eq by reflexivity. A
// `Const c` carries no binder: `eval e (Const c) = c` and `ground_int(Int c) =
// int_lit_to_expr(c) = int_lit(c)` are the SAME closed literal. This is not papering
// over the mismatch — it pins the precise `e` under which the operational evaluator and
// the live grounder denote the same Int.
// ---------------------------------------------------------------------------
/// A closed "base" env `fun (_ : Nat) => Int.ofNat 0` — the floor a grounder-connected
/// adequacy `set`-chain overwrites at each referenced parameter index. Its value at an
/// unreferenced index is irrelevant (the operand never reads it).
pub(super) fn base_env_expr() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    Expr::lam(bd(), cst("Nat"), int_lit(0))
}

/// Build the env `e` that binds each referenced parameter index to its de-Bruijn
/// `Int` binder, so `eval e (Var p_i)` ι-reduces to the SAME binder the LIVE
/// `ground_int` emits for `Formula::Var(var_name(p_i))`.
///
/// `indices[i]` is the parameter index whose binder is `binder_of(i)` (an `Expr` for
/// the de-Bruijn position of that operand's `Int` binder at the CURRENT depth). The env
/// is `set (set (… base …) p_0 x_0) … p_{n-1} x_{n-1}`; because the indices are
/// DISTINCT, `e p_i` reduces through the `set`-chain (`Nat.beq p_j p_i → false` for
/// `j ≠ i`, `→ true` at `j = i`) to `x_i`.
pub(super) fn grounding_env_expr(indices: &[u64], binder_of: &dyn Fn(usize) -> Expr) -> Expr {
    let mut e = base_env_expr();
    for (i, p) in indices.iter().enumerate() {
        e = Expr::apps(cst(MIRSEM_SET), [e, Expr::nat_lit(*p), binder_of(i)]);
    }
    e
}

/// The de-Bruijn grounding `params` map + a `binder_of` closure for the LIVE grounder,
/// over the operand variable indices `indices`, under `indices.len()` leading `Int`
/// binders (`∀ x_0 … x_{n-1}`). Mirrors `clean_ground`'s convention: the FIRST-bound
/// variable is the OUTERMOST binder (highest de-Bruijn index). `var_name(p_i)` maps to
/// `bvar(n-1-i)`, the same binder `grounding_env_expr` writes at index `p_i`.
pub(super) fn grounding_params(indices: &[u64]) -> std::collections::HashMap<String, Expr> {
    let n = indices.len();
    let mut m = std::collections::HashMap::new();
    for (i, p) in indices.iter().enumerate() {
        m.insert(var_name(*p), Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    }
    m
}

/// Live-ground `f` (an operand/rvalue's reflected `Formula`) through
/// `clean_ground::ground_int` under the de-Bruijn binders for `indices`, returning the
/// EXACT `Int` term the §6 pipeline grounds. `None` (fail closed) if the live grounder
/// declines the formula (outside the grounded fragment).
pub(super) fn live_ground_int(f: &trust_types::Formula, indices: &[u64]) -> Option<Expr> {
    crate::clean_ground::ground_int(f, &grounding_params(indices))
}

/// The GROUNDER-CONNECTED Lemma-1A *theorem statement* for operand `O`, as a kernel
/// type — the RHS is the ACTUAL term the LIVE `clean_ground::ground_int` emits for
/// `O.to_formula()`, NOT a hand-built denotation:
///
/// ```text
/// ∀ (x_0 … x_{n-1} : Int), Trust.MirSem.eval E O = ground_int(O.to_formula())
/// ```
///
/// where `n` is the count of distinct parameter indices `O` references, the `x_i` are
/// their bound `Int`s, `E` is the `set`-chain env binding each referenced index to its
/// binder (`grounding_env_expr`), and the RHS is `live_ground_int(O.to_formula(),
/// indices)`. `eval E (Var p_i)` ι-reduces (env application → `set`-lookup) to `x_i` —
/// the SAME binder `ground_int` emits — so the two sides are def-eq. A `Const` has `n
/// = 0` (no binder): both sides are the closed literal. If `claimed_rhs` is `Some` it
/// REPLACES the live-grounded RHS (the fail-closed test: a wrong claim must NOT prove);
/// `None` is returned when the live grounder declines `O.to_formula()`.
pub(super) fn adequacy_statement(op: &SemOperand, claimed_rhs: Option<&Expr>) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut indices = Vec::new();
    op.var_indices(&mut indices);
    let n = indices.len();
    // Inside the `n` Int binders, the env binds each index to its de-Bruijn binder.
    let env = grounding_env_expr(&indices, &|i| Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    let lhs = Expr::apps(cst(MIRSEM_EVAL), [env, op.to_operand_expr()]);
    let rhs = match claimed_rhs {
        Some(e) => e.clone(),
        None => live_ground_int(&op.to_formula(), &indices)?,
    };
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        body = Expr::pi(bd(), int_ty(), body);
    }
    Some(body)
}

/// The GROUNDER-CONNECTED Lemma-1A *proof term* for operand `O`: `λ (x_0 … x_{n-1} :
/// Int). @Eq.refl Int (ground_int(O.to_formula()))`. `eval E O` ι-reduces to the live
/// grounder's term (see [`adequacy_statement`]), so reflexivity at the grounded term
/// inhabits the equality. `None` when the live grounder declines `O.to_formula()`.
pub(super) fn adequacy_proof(op: &SemOperand) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let mut indices = Vec::new();
    op.var_indices(&mut indices);
    let n = indices.len();
    let rhs = live_ground_int(&op.to_formula(), &indices)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check Lemma 1A for one operand form against the REAL clean-kernel: register the
/// `MirSem` anchor, build the GROUNDER-CONNECTED statement `∀ x⃗. eval E O =
/// ground_int(O.to_formula())` and the reflexivity proof, `check_type` the proof
/// against the statement, register it, and audit the axiom closure via `axiom_deps`.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term the LIVE
/// `clean_ground::ground_int` grounds `O` to is EXACTLY what the MIR operational
/// semantics evaluates `O` to (under the env binding each parameter to its value),
/// kernel-verified modulo the 3 foundational axioms — the faithfulness content for
/// that operand, mechanically connected to the live grounder, not prose.
#[must_use]
pub fn check_operand_adequacy(op: &SemOperand) -> AdequacyVerdict {
    check_operand_adequacy_inner(op, None)
}

/// Internal: `claimed_rhs = Some(e)` overrides the true denotation (the fail-closed
/// path — a wrong RHS must make the reflexivity proof fail to type-check).
pub(super) fn check_operand_adequacy_inner(op: &SemOperand, claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let Some(statement) = adequacy_statement(op, claimed_rhs) else {
        return AdequacyVerdict::KernelRejected(
            "live ground_int declined this operand's reflected formula".to_string(),
        );
    };
    let Some(proof) = adequacy_proof(op) else {
        return AdequacyVerdict::KernelRejected(
            "live ground_int declined this operand's reflected formula".to_string(),
        );
    };

    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma1A.operand_adequacy");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return AdequacyVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => AdequacyVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            AdequacyVerdict::Residue(names)
        }
        None => AdequacyVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// The GROUNDER-CONNECTED Lemma-1B *theorem statement* for rvalue `R` — the RHS is the
/// ACTUAL term the LIVE `clean_ground::ground_int` emits for `R.to_formula()`:
///
/// ```text
/// ∀ (x_0 … x_{n-1} : Int), Trust.MirSem.eval_rvalue E R = ground_int(R.to_formula())
/// ```
///
/// `E` is the `set`-chain env binding each referenced parameter index to its binder
/// (`grounding_env_expr`). For `Bin(op, a, b)`, `eval_rvalue E R` ι-reduces (through
/// `Rvalue.rec`/`BinOp.rec`) to `Int.<op> (eval E a) (eval E b)`, and each `eval E
/// (Var p_i)` ι-reduces to `x_i` — the SAME binder `ground_int` emits for `Var
/// name`, so `Int.<op> x_a x_b` matches `ground_int(Add/Sub/Mul/Div(a,b))` exactly.
/// `claimed_rhs = Some` swaps the live-grounded RHS for the fail-closed test; `None`
/// (the function returns `None`) means the live grounder declined `R.to_formula()`.
pub(super) fn rvalue_adequacy_statement(rv: &SemRvalue, claimed_rhs: Option<&Expr>) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let indices = rv.var_indices();
    let n = indices.len();
    let env = grounding_env_expr(&indices, &|i| Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    let lhs = Expr::apps(cst(MIRSEM_EVAL_RVALUE), [env, rv.to_rvalue_expr()]);
    let rhs = match claimed_rhs {
        Some(e) => e.clone(),
        None => live_ground_int(&rv.to_formula(), &indices)?,
    };
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    for _ in 0..n {
        body = Expr::pi(bd(), int_ty(), body);
    }
    Some(body)
}

/// The GROUNDER-CONNECTED Lemma-1B *proof term* for rvalue `R`: `λ (x_0 … x_{n-1} :
/// Int). @Eq.refl Int (ground_int(R.to_formula()))`. `eval_rvalue E R` ι-reduces to
/// the live-grounded term (see [`rvalue_adequacy_statement`]), so reflexivity at it
/// inhabits the equality. `None` when the live grounder declines `R.to_formula()`.
pub(super) fn rvalue_adequacy_proof(rv: &SemRvalue) -> Option<Expr> {
    let bd = || BinderData::from(BinderInfo::Default);
    let indices = rv.var_indices();
    let n = indices.len();
    let rhs = live_ground_int(&rv.to_formula(), &indices)?;
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    for _ in 0..n {
        refl = Expr::lam(bd(), int_ty(), refl);
    }
    Some(refl)
}

/// Check Lemma 1B for one rvalue form against the REAL clean-kernel: build the
/// GROUNDER-CONNECTED statement `∀ x⃗. eval_rvalue E R = ground_int(R.to_formula())`
/// and the reflexivity proof, `check_type`, register, and audit the axiom closure.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term the LIVE
/// `clean_ground::ground_int` grounds `R` to is EXACTLY what the MIR operational
/// semantics evaluates `R` to (over the prelude's `Int.add`/`sub`/`mul`/`div`),
/// kernel-verified modulo the 3 foundational axioms — mechanically connected to the
/// live grounder, not prose.
#[must_use]
pub fn check_rvalue_adequacy(rv: &SemRvalue) -> AdequacyVerdict {
    check_rvalue_adequacy_inner(rv, None)
}

pub(super) fn check_rvalue_adequacy_inner(rv: &SemRvalue, claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let Some(statement) = rvalue_adequacy_statement(rv, claimed_rhs) else {
        return AdequacyVerdict::KernelRejected(
            "live ground_int declined this rvalue's reflected formula".to_string(),
        );
    };
    let Some(proof) = rvalue_adequacy_proof(rv) else {
        return AdequacyVerdict::KernelRejected(
            "live ground_int declined this rvalue's reflected formula".to_string(),
        );
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma1B.rvalue_adequacy");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return AdequacyVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => AdequacyVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            AdequacyVerdict::Residue(names)
        }
        None => AdequacyVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// Strip transparent moves down to the underlying operand (a `Var`/`Const`).
pub(super) fn operand_core(op: &SemOperand) -> &SemOperand {
    match op {
        SemOperand::Move(src) => operand_core(src),
        other => other,
    }
}

/// If the return operand resolves (through transparent moves) to a parameter/temp
/// `Var k`, return `k`; else `None` (a `Const` return).
pub(super) fn return_var_index(r: &SemReturn) -> Option<u64> {
    match operand_core(&r.ret) {
        SemOperand::Var(k) => Some(*k),
        _ => None,
    }
}

/// The SSA assignment whose target index is the returned `Var k`, if any — the
/// OPEN-case discriminator. SSA gives at most one such assignment; defensively we
/// take the LAST `Assign(k, R)` in program order (the value live at the return).
/// `None` when no statement assigns the returned index (the CLOSED case).
pub(super) fn return_assigned_rvalue(r: &SemReturn) -> Option<(u64, &SemRvalue)> {
    let k = return_var_index(r)?;
    r.stmts.iter().rev().find(|s| s.idx == k).map(|s| (k, &s.rvalue))
}

/// Whether a return witness is in the CLOSED fragment Lemma 1C proves DIRECTLY (no
/// `exec` fold): the returned operand is a parameter (`Var`)/constant
/// (`Const`)/transparent-move thereof whose value does NOT depend on the preceding
/// SSA assignments — i.e. the returned index is NOT assigned by any statement in the
/// trace. Then the return value is `eval e ret` regardless of the (possibly empty)
/// assignment prefix, and adequacy is reflexivity at the return position (Lemma 1A).
///
/// A return that traces an ASSIGNED temp (e.g. `_0 := x+1; return _0`) is the
/// SSA-TEMP case — handled by the env-threading `exec` fold (`return_is_ssa_temp`),
/// NOT here.
pub(super) fn return_is_closed(r: &SemReturn) -> bool {
    // Const return: always closed. Var return: closed iff its index is unassigned.
    // Index/Len/Field returns: closed (an operand-shaped value, not an SSA-assigned
    // temp) — they only ever appear as guarded ARM/GUARD operands (or, Trust:
    // field-read leaf, nested inside an assigned temp's `SemRvalue::Use`), never as
    // the DIRECT return operand in the modeled fragment, but the match stays total
    // and fail-safe.
    match operand_core(&r.ret) {
        SemOperand::Const(_)
        | SemOperand::Index(..)
        | SemOperand::Len(_)
        | SemOperand::Field(..)
        | SemOperand::Discriminant(_)
        // Trust: CAST-TEMP GUARD READ — an operand-shaped value (the SAME
        // opaque-carrier reasoning as Index/Field/Discriminant), never an
        // SSA-assigned temp itself.
        | SemOperand::Cast(..)
        // A pure operation over a closed operand is likewise not an SSA temp.
        | SemOperand::PreOp(..)
        // Trust: ITER-NEXT VALUE-PATH — an entry-time handle carrier is an operand-shaped
        // value (a function of the pinned param), never an SSA-assigned temp. It never
        // reaches this MirSem-return lane (minted only into the trust-ir `SemAdtReturn`),
        // but the match stays total and classifies it with the other opaque carriers.
        | SemOperand::IterRegion(_) => true,
        SemOperand::Var(_) => return_assigned_rvalue(r).is_none(),
        SemOperand::Move(_) => unreachable!("operand_core strips moves"),
    }
}

/// Whether a return witness is in the SSA-TEMP fragment the `exec` fold proves: the
/// returned operand is a `Var k` (through transparent moves) AND some statement
/// `Assign(k, R)` in the trace binds that index — so the returned value is the value
/// `exec` writes to index `k`, namely `eval_rvalue e R`. This is the OPEN case Lemma
/// 1C now closes via the env-threading fold. (The production dispatch reads
/// `return_assigned_rvalue` directly; this named predicate documents the fragment
/// boundary and is exercised by the SSA-temp adequacy tests.)
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn return_is_ssa_temp(r: &SemReturn) -> bool {
    return_assigned_rvalue(r).is_some()
}

/// The Lemma-1C *theorem statement* for the CLOSED return witness `r`:
///
/// ```text
/// ∀ (e : Env), Trust.MirSem.eval e r.ret = E_ret
/// ```
///
/// HONEST SCOPE. For the closed cases the preceding assignments do not bind the
/// (parameter/constant) return operand, so the return value IS `eval e r.ret`, and
/// that equals `E_ret` (the grounded reflection of `extract_return_formula`'s output)
/// by Lemma 1A at the return position. This IS the faithfulness content of the
/// return trace for the identity/constant/param cases. We do NOT register a general
/// env-threading `exec` fold here (that — resolving a return that traces an assigned
/// temp through the statement list — is the DEFERRED breadth); the `Stmt` syntax and
/// the `List Stmt` trace ARE pinned (`to_stmts_expr`), so the trace is modeled even
/// where the closed-case theorem evaluates the return operand directly.
pub(super) fn return_adequacy_statement(r: &SemReturn, claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let e_ref = Expr::bvar(0);
    let lhs = Expr::apps(cst(MIRSEM_EVAL), [e_ref.clone(), r.ret.to_operand_expr()]);
    let rhs = claimed_rhs.cloned().unwrap_or_else(|| r.denotation(&e_ref));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    Expr::pi(bd(), env_ty(), body)
}

/// The Lemma-1C *proof term* for the closed return witness — reflexivity, since
/// `eval e ret` ι-reduces to `E_ret` (Lemma 1A's content at the return position).
pub(super) fn return_adequacy_proof(r: &SemReturn) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let e_ref = Expr::bvar(0);
    let rhs = r.denotation(&e_ref);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    Expr::lam(bd(), env_ty(), refl)
}

/// The Lemma-1C *theorem statement* for the SSA-TEMP return witness `r` — the
/// env-threading `exec` fold form:
///
/// ```text
/// ∀ (e : Env), Trust.MirSem.eval (Trust.MirSem.exec e stmts) (Var k) = E_ret
/// ```
///
/// where `stmts` is the (pinned) `List Stmt` SSA trace, `k` is the returned temp's
/// index, and `E_ret` is the grounded reflection `ground_int` emits after
/// `extract_return_formula` traces `_k` back through its `Assign(k, R)` — i.e. the
/// denotation of the assigned rvalue `R`. The LHS runs the SSA prefix through `exec`
/// (updating index `k` to `eval_rvalue e R`) and then evaluates the returned temp
/// under the threaded env. `claimed_rhs = Some` swaps the true denotation for the
/// fail-closed test.
pub(super) fn ssa_temp_return_statement(r: &SemReturn, rv: &SemRvalue, claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let e_ref = Expr::bvar(0);
    // exec e stmts
    let exec_env = Expr::apps(cst(MIRSEM_EXEC), [e_ref.clone(), r.to_stmts_expr()]);
    // eval (exec e stmts) (Var k)  — the returned operand evaluated under the threaded env.
    let lhs = Expr::apps(cst(MIRSEM_EVAL), [exec_env, r.ret.to_operand_expr()]);
    // E_ret = denotation of the assigned rvalue R (what the SSA trace grounds to).
    let rhs = claimed_rhs.cloned().unwrap_or_else(|| rv.denotation(&e_ref));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    Expr::pi(bd(), env_ty(), body)
}

/// The Lemma-1C *proof term* for the SSA-TEMP return witness — reflexivity. The LHS
/// `eval (exec e stmts) (Var k)` ι-reduces: `exec` folds the trace to
/// `set … k (eval_rvalue e R) …`, the `Var k` lookup hits the `set` at index `k`
/// whose `Nat.beq k k ι-reduces to `Bool.true` (so the `Bool.rec` picks the written
/// value), leaving `eval_rvalue e R`, which Lemma 1B's content def-eq-reduces to the
/// rvalue denotation `E_ret`. Both sides are therefore def-eq, so the witness is
/// `λ(e:Env). @Eq.refl Int E_ret`. (Composes Lemma 1B inside the fold: the same
/// `eval_rvalue ≡ denotation` reduction 1B pins.)
pub(super) fn ssa_temp_return_proof(rv: &SemRvalue) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let e_ref = Expr::bvar(0);
    let rhs = rv.denotation(&e_ref);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    Expr::lam(bd(), env_ty(), refl)
}

/// Check Lemma 1C for a return witness against the REAL clean-kernel. Two modeled
/// fragments certify (each by reflexivity over a different LHS):
///
///   * CLOSED — the returned operand is a parameter/constant (its index is NOT
///     assigned in the trace): `∀e. eval e ret = E_ret`. The assignment prefix is
///     irrelevant to the return value.
///   * SSA-TEMP — the returned operand is a `Var k` that some `Assign(k, R)` binds:
///     `∀e. eval (exec e stmts) (Var k) = E_ret`. The env-threading `exec` fold runs
///     the prefix, the `Var k` lookup picks up `set`'s written value, and Lemma 1B
///     pins `eval_rvalue e R = E_ret`.
///
/// Fail-closed: a return that is NEITHER a closed param/const NOR an SSA temp the
/// `exec` fold can def-eq-reduce (loops, calls, an rvalue outside the modeled
/// fragment) is `KernelRejected` — NOT proven.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means the grounded reflection of the
/// function's return is EXACTLY what the MIR operational semantics returns,
/// kernel-verified modulo 3.
#[must_use]
pub fn check_return_adequacy(r: &SemReturn) -> AdequacyVerdict {
    check_return_adequacy_inner(r, None)
}

pub(super) fn check_return_adequacy_inner(r: &SemReturn, claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    // Build the statement + proof for whichever modeled fragment this return is in.
    // SSA-temp takes precedence (a returned Var that IS assigned), else closed; a
    // return in neither fragment fails closed.
    let (statement, proof) = if let Some((_k, rv)) = return_assigned_rvalue(r) {
        (ssa_temp_return_statement(r, rv, claimed_rhs), ssa_temp_return_proof(rv))
    } else if return_is_closed(r) {
        (return_adequacy_statement(r, claimed_rhs), return_adequacy_proof(r))
    } else {
        return AdequacyVerdict::KernelRejected(
            "return trace outside the modeled Lemma-1C fragment (not a closed \
             param/const and not an exec-foldable SSA temp)"
                .to_string(),
        );
    };

    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma1C.return_adequacy");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return AdequacyVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => AdequacyVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            AdequacyVerdict::Residue(names)
        }
        None => AdequacyVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// THE §6 PIPELINE HOOK. For a reflected scalar operand, return its kernel-checked
/// adequacy certificate — `Some` iff the operand is in the modeled fragment AND the
/// adequacy proof kernel-checks modulo 3. The §6 driver attaches one of these per
/// obligation whose operand reflections are faithful, feeding the
/// `faithfulness_certified` metric.
///
/// Returns `None` (fail-closed) for an operand outside the MirSem scalar fragment
/// or whose adequacy proof does not kernel-check modulo 3 — never a false certificate.
#[must_use]
pub fn operand_adequacy_witness(op: &SemOperand) -> Option<AdequacyCertificate> {
    let verdict = check_operand_adequacy(op);
    match verdict {
        AdequacyVerdict::ProvenModulo3 => {
            Some(AdequacyCertificate { operand: op.clone(), verdict })
        }
        _ => None,
    }
}

/// THE LEMMA-1B PIPELINE HOOK. For a reflected rvalue, return its kernel-checked
/// adequacy certificate — `Some` iff the rvalue is in the modeled fragment AND the
/// adequacy proof kernel-checks modulo 3. Fail-closed otherwise.
#[must_use]
pub fn rvalue_adequacy_witness(rv: &SemRvalue) -> Option<RvalueAdequacyCertificate> {
    match check_rvalue_adequacy(rv) {
        AdequacyVerdict::ProvenModulo3 => Some(RvalueAdequacyCertificate {
            rvalue: rv.clone(),
            verdict: AdequacyVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// THE LEMMA-1C PIPELINE HOOK. For a reflected return witness, return its
/// kernel-checked adequacy certificate — `Some` iff the witness is in the CLOSED
/// fragment AND the adequacy proof kernel-checks modulo 3. Fail-closed for an open
/// (temp-traced) return.
#[must_use]
pub fn return_adequacy_witness(r: &SemReturn) -> Option<ReturnAdequacyCertificate> {
    match check_return_adequacy(r) {
        AdequacyVerdict::ProvenModulo3 => Some(ReturnAdequacyCertificate {
            ret: r.clone(),
            verdict: AdequacyVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// The Lemma-1C-cf *theorem statement* for a control-flow return witness `r`:
///
/// ```text
/// ∀ (e : Env), Trust.MirSem.eval_ite e c t f
///            = Bool.rec (λ_:Bool. Int) (eval_rvalue e f) (eval_rvalue e t) (eval_cond e c)
/// ```
///
/// The RHS is the explicit if-then-else over the comparison: `Bool.rec` dispatches
/// `eval_cond e c` (the guard's Bool), selecting `eval_rvalue e t` (then) on
/// `Bool.true`, `eval_rvalue e f` (else) on `Bool.false`. The LHS is `eval_ite`,
/// which is DEFINED as exactly that `Bool.rec` term — so adequacy is reflexivity
/// (`eval_ite` ι-reduces to the RHS). This is the faithfulness content of the
/// control-flow return: the conditional eval IS the if-then-else over the guard.
/// `claimed_rhs = Some` swaps the true RHS for the fail-closed (wrong-branch /
/// wrong-polarity) tests.
pub(super) fn cf_return_adequacy_statement(r: &SemCfReturn, claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let e_ref = Expr::bvar(0);
    let lhs = Expr::apps(
        cst(MIRSEM_EVAL_ITE),
        [
            e_ref.clone(),
            r.cond.to_cond_expr(),
            r.then_rv.to_rvalue_expr(),
            r.else_rv.to_rvalue_expr(),
        ],
    );
    let rhs = claimed_rhs.cloned().unwrap_or_else(|| cf_return_denotation(r, &e_ref));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [int_ty(), lhs, rhs]);
    Expr::pi(bd(), env_ty(), body)
}

/// The explicit if-then-else denotation `Bool.rec (λ_.Int) (eval_rvalue e f)
/// (eval_rvalue e t) (eval_cond e c)` — the RHS of the Lemma-1C-cf statement.
pub(super) fn cf_return_denotation(r: &SemCfReturn, e_ref: &Expr) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::succ(Level::zero())]);
    let int_motive = Expr::lam(bd(), cst("Bool"), int_ty());
    let eval_rvalue = cst(MIRSEM_EVAL_RVALUE);
    let eval_f = Expr::apps(eval_rvalue.clone(), [e_ref.clone(), r.else_rv.to_rvalue_expr()]);
    let eval_t = Expr::apps(eval_rvalue, [e_ref.clone(), r.then_rv.to_rvalue_expr()]);
    let cond_b = Expr::apps(cst(MIRSEM_EVAL_COND), [e_ref.clone(), r.cond.to_cond_expr()]);
    Expr::apps(bool_rec, [int_motive, eval_f, eval_t, cond_b])
}

/// The Lemma-1C-cf *proof term* — reflexivity, since `eval_ite e c t f` ι-reduces to
/// the explicit `Bool.rec` if-then-else (the RHS). The witness is
/// `λ(e:Env). @Eq.refl Int RHS`.
pub(super) fn cf_return_adequacy_proof(r: &SemCfReturn) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let e_ref = Expr::bvar(0);
    let rhs = cf_return_denotation(r, &e_ref);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [int_ty(), rhs]);
    Expr::lam(bd(), env_ty(), refl)
}

/// INTERNAL `eval_ite` reduction lemma (NOT a faithfulness certificate). Proves
/// `∀e. eval_ite e c t f = Bool.rec (λ_.Int) (eval_rvalue e f) (eval_rvalue e t)
/// (eval_cond e c)` by reflexivity (`eval_ite` ι-reduces to that `Bool.rec` term).
///
/// HONESTY NOTE (FIX 2). The RHS here is BYTE-IDENTICAL to `eval_ite`'s installed
/// DEFINITION body (`register_eval_ite`), so this lemma is `eval_ite = eval_ite-def`:
/// a definitional unfolding. It certifies NOTHING about the reflected guarded return
/// the §6 pipeline actually grounds — the grounder emits a SCALAR `Int` formula for
/// the return (`extract_return_formula`/`ground_int`), with NO `ite`/`eval_cond`/
/// `Bool.rec`. So this is a MODEL-INTERNAL reduction fact, kept for the `eval_ite`
/// anchor's well-formedness audit, and DELIBERATELY NOT wired into the whole-function
/// or fully-faithful faithfulness tally (`function_adequacy_witness` defers guarded
/// returns). The fail-closed wrong-branch / wrong-polarity tests below still have
/// teeth as reduction-shape guards.
///
/// Fail-closed: a witness whose proof does not kernel-check, or whose axiom closure is
/// not ⊆ the 3 foundational axioms, is `KernelRejected`/`Residue`.
#[must_use]
pub fn check_cf_return_adequacy(r: &SemCfReturn) -> AdequacyVerdict {
    check_cf_return_adequacy_inner(r, None)
}

pub(super) fn check_cf_return_adequacy_inner(r: &SemCfReturn, claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    let statement = cf_return_adequacy_statement(r, claimed_rhs);
    let proof = cf_return_adequacy_proof(r);

    let mut env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma1Ccf.cf_return_adequacy");
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: statement,
        value: proof,
    }) {
        return AdequacyVerdict::KernelRejected(format!("add_decl: {e:?}"));
    }
    match env.axiom_deps(&name) {
        Some(residue) if residue.is_empty() => AdequacyVerdict::ProvenModulo3,
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            AdequacyVerdict::Residue(names)
        }
        None => AdequacyVerdict::KernelRejected("decl not found after add".to_string()),
    }
}

/// THE LEMMA-1C-cf PIPELINE HOOK. For a reflected control-flow return witness, return
/// its kernel-checked adequacy certificate — `Some` iff its adequacy proof
/// kernel-checks modulo 3. Fail-closed (`None`) otherwise, never a false certificate.
#[must_use]
pub fn cf_return_adequacy_witness(r: &SemCfReturn) -> Option<CfReturnAdequacyCertificate> {
    match check_cf_return_adequacy(r) {
        AdequacyVerdict::ProvenModulo3 => Some(CfReturnAdequacyCertificate {
            ret: r.clone(),
            verdict: AdequacyVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// Pin the control-flow-return anchor (`CmpOp`/`Cond`/`eval_cond`/`eval_ite`) and
/// audit its axiom closure: confirm each declaration rests on exactly the 3
/// foundational axioms (modulo 3, no 4th axiom). Mirrors `pin_mirsem_anchor` for the
/// Lemma-1C-cf fragment.
#[must_use]
pub fn pin_cf_return_anchor() -> AnchorVerdict {
    let env = match mirsem_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for n in [
        MIRSEM_CMPOP,
        MIRSEM_CMPOP_REC,
        MIRSEM_COND,
        MIRSEM_COND_REC,
        MIRSEM_EVAL_COND,
        MIRSEM_EVAL_ITE,
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
