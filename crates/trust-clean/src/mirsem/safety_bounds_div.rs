// Index out-of-bounds and division by zero: reflected predicates, environment
// registration and adequacy.

use super::*;

/// Register `Trust.MirSem.idx_oob : Int → Int → Prop` (idempotent):
///
/// ```text
/// idx_oob (len i : Int) : Prop := Int.le len i
/// ```
///
/// This IS the index-out-of-bounds condition of `s[i]` on a collection of length
/// `len`: for a non-negative index `0 ≤ i`, the access is OOB IFF `i ≥ len` IFF
/// `len ≤ i`. The body is the prelude's reducible `Int.le` DEFINITION, so the decl's
/// transitive axiom closure is `⊆ {propext, Quot.sound, Classical.choice}`.
pub(super) fn register_idx_oob(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_IDX_OOB);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // idx_oob : Int → Int → Prop
    let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::prop()));
    // Inside `λ(len:Int). λ(i:Int). …` : i = bvar(0), len = bvar(1).
    let len_ref = Expr::bvar(1);
    let i_ref = Expr::bvar(0);
    // Int.le len i   :  Prop
    let body = Expr::apps(cst("Int.le"), [len_ref, i_ref]);
    let val = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(idx_oob): {e:?}"))?;
    Ok(())
}

/// The GROUNDED REFLECTION of the bounds OOB disjunct `Ge(index, len)`, under
/// de-Bruijn terms `len_ref`/`i_ref` for the length and index — the EXACT term
/// `clean_ground::ground_prop` produces for that `Formula`:
///
/// ```text
/// ground_prop(Ge(index, len)) = Int.le (ground_int len) (ground_int index)
///                             = Int.le len i
/// ```
///
/// (`Ge(x,y)` grounds with the arguments SWAPPED: `Int.le (g y) (g x)`.) This is the
/// term Lemma 3 claims is def-eq to `idx_oob len i`.
pub(super) fn reflected_bounds_disjunct(len_ref: &Expr, i_ref: &Expr) -> Expr {
    Expr::apps(cst("Int.le"), [len_ref.clone(), i_ref.clone()])
}

/// The Lemma-3 *theorem statement* — the array-bounds-VC adequacy:
///
/// ```text
/// ∀ (len i : Int), <reflected OOB disjunct> = idx_oob len i      (in Prop)
/// ```
///
/// i.e. `@Eq Prop (Int.le len i) (idx_oob len i)`, universally over the length and
/// index Ints. `claimed_rhs = Some` swaps the spec for the fail-closed test.
pub(super) fn bounds_adequacy_statement(claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Inside `∀(len:Int).∀(i:Int), …` : i = bvar(0), len = bvar(1).
    let len_ref = Expr::bvar(1);
    let i_ref = Expr::bvar(0);
    let lhs = reflected_bounds_disjunct(&len_ref, &i_ref);
    let rhs = claimed_rhs
        .cloned()
        .unwrap_or_else(|| Expr::apps(cst(MIRSEM_IDX_OOB), [len_ref.clone(), i_ref.clone()]));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [Expr::prop(), lhs, rhs]);
    Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), body))
}

/// The Lemma-3 *proof term* — reflexivity. `idx_oob len i` δ/ι-reduces (unfolding the
/// reducible definition) to `Int.le len i`, which is LITERALLY the reflected OOB
/// disjunct, so the two `Prop` terms are def-eq and the witness is
/// `λ(len i:Int). @Eq.refl Prop <reflected disjunct>`.
pub(super) fn bounds_adequacy_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let len_ref = Expr::bvar(1);
    let i_ref = Expr::bvar(0);
    let lhs = reflected_bounds_disjunct(&len_ref, &i_ref);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [Expr::prop(), lhs]);
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), refl))
}

/// Check Lemma 3 (array-bounds-VC adequacy) against the REAL clean-kernel: register
/// the MirSem + `idx_oob` anchor, build the statement
/// `∀ len i. <reflected OOB disjunct> = idx_oob len i` and the reflexivity proof,
/// `check_type` it, register it, and audit the axiom closure via `axiom_deps`.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term trust-vcgen+`ground_prop`
/// produce for a slice/array index `s[i]` OOB obligation is EXACTLY the pinned
/// out-of-bounds condition `len ≤ i` — kernel-verified modulo the 3 foundational
/// axioms. So a safety proof refuting that VC refutes EXACTLY the OOB condition.
#[must_use]
pub fn check_bounds_adequacy() -> AdequacyVerdict {
    check_bounds_adequacy_inner(None)
}

/// Internal: `claimed_rhs = Some(e)` overrides the spec (the fail-closed path — a
/// strict-vs-non-strict off-by-one / wrong-order claim must fail to type-check).
pub(super) fn check_bounds_adequacy_inner(claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    // `mirsem_safety_env` registers `idx_oob` (a reducible def) so the kernel can
    // δ-unfold it and see the RHS `idx_oob len i` is def-eq to `Int.le len i`.
    let mut env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let statement = bounds_adequacy_statement(claimed_rhs);
    let proof = bounds_adequacy_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma3.bounds_adequacy");
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

/// Register `Trust.MirSem.div_by_zero : Int → Prop` (idempotent):
///
/// ```text
/// div_by_zero (b : Int) : Prop := @Eq Int b (Int.ofNat 0)
/// ```
///
/// This IS the divisor-zero condition of `a / b`: the division (or remainder) panics
/// / is UB IFF `b = 0`. The body is built from the prelude's `Eq`/`Int.ofNat`
/// DEFINITIONS, so the decl's transitive axiom closure is
/// `⊆ {propext, Quot.sound, Classical.choice}`.
pub(super) fn register_div_by_zero(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_DIV_BY_ZERO);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // div_by_zero : Int → Prop
    let ty = Expr::pi(bd(), int_ty(), Expr::prop());
    // Inside `λ(b:Int). …` : b = bvar(0).
    let b_ref = Expr::bvar(0);
    // @Eq Int b (Int.ofNat 0)   :  Prop
    let body = div_by_zero_body(&b_ref);
    let val = Expr::lam(bd(), int_ty(), body);
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(div_by_zero): {e:?}"))?;
    Ok(())
}

/// The GROUNDED REFLECTION of the div-by-zero VC `Eq(b, 0)`, under the de-Bruijn term
/// `b_ref` for the divisor — the EXACT term `clean_ground::ground_prop` produces for
/// that `Formula`:
///
/// ```text
/// ground_prop(Eq(b, Int(0))) = @Eq Int (ground b) (ground (Int 0))
///                            = @Eq Int b (Int.ofNat 0)
/// ```
///
/// This is the term Lemma 4 claims is def-eq to `div_by_zero b`, AND the body the
/// `div_by_zero` definition unfolds to (so the spec and the reflection are the same
/// closed term).
pub(super) fn div_by_zero_body(b_ref: &Expr) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    // @Eq Int b (Int.ofNat 0)
    Expr::apps(eq, [int_ty(), b_ref.clone(), int_lit(0)])
}

/// The Lemma-4 *theorem statement* — the division-by-zero-VC adequacy:
///
/// ```text
/// ∀ (b : Int), <reflected div-by-zero VC> = div_by_zero b      (in Prop)
/// ```
///
/// i.e. `@Eq Prop (@Eq Int b (Int.ofNat 0)) (div_by_zero b)`, universally over the
/// divisor Int. `claimed_rhs = Some` swaps the spec for the fail-closed test.
pub(super) fn div_adequacy_statement(claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Inside `∀(b:Int), …` : b = bvar(0).
    let b_ref = Expr::bvar(0);
    let lhs = div_by_zero_body(&b_ref);
    let rhs =
        claimed_rhs.cloned().unwrap_or_else(|| Expr::app(cst(MIRSEM_DIV_BY_ZERO), b_ref.clone()));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [Expr::prop(), lhs, rhs]);
    Expr::pi(bd(), int_ty(), body)
}

/// The Lemma-4 *proof term* — reflexivity. `div_by_zero b` δ-reduces (unfolding the
/// reducible definition) to `@Eq Int b (Int.ofNat 0)`, which is LITERALLY the
/// reflected div-by-zero VC, so the two `Prop` terms are def-eq and the witness is
/// `λ(b:Int). @Eq.refl Prop <reflected VC>`.
pub(super) fn div_adequacy_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let b_ref = Expr::bvar(0);
    let lhs = div_by_zero_body(&b_ref);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [Expr::prop(), lhs]);
    Expr::lam(bd(), int_ty(), refl)
}

/// Check Lemma 4 (division-by-zero-VC adequacy) against the REAL clean-kernel:
/// register the MirSem + `div_by_zero` anchor, build the statement
/// `∀ b. <reflected div-by-zero VC> = div_by_zero b` and the reflexivity proof,
/// `check_type` it, register it, and audit the axiom closure via `axiom_deps`.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term trust-vcgen+`ground_prop`
/// produce for the integer `BinaryOp(Div|Rem)` divisor-zero obligation is EXACTLY the
/// pinned condition `b = 0` — kernel-verified modulo the 3 foundational axioms. So a
/// safety proof refuting that VC refutes EXACTLY the divisor-zero condition.
#[must_use]
pub fn check_div_adequacy() -> AdequacyVerdict {
    check_div_adequacy_inner(None)
}

/// Internal: `claimed_rhs = Some(e)` overrides the spec (the fail-closed path — a
/// `b = 1` instead of `b = 0` claim must fail to type-check).
pub(super) fn check_div_adequacy_inner(claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    // `mirsem_safety_env` registers `div_by_zero` (a reducible def) so the kernel can
    // δ-unfold it and see the RHS `div_by_zero b` is def-eq to `@Eq Int b (Int.ofNat 0)`.
    let mut env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let statement = div_adequacy_statement(claimed_rhs);
    let proof = div_adequacy_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma4.div_adequacy");
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

/// Pin the bounds + div-by-zero anchors and audit their axiom closure: confirm the
/// `idx_oob` and `div_by_zero` predicates AND both adequacy lemmas rest on exactly the
/// 3 foundational axioms (modulo 3, no 4th axiom). Mirrors `pin_overflow_anchor` for
/// the bounds/div safety-VC fragments.
#[must_use]
pub fn pin_bounds_div_anchor() -> AnchorVerdict {
    // `mirsem_safety_env` already registers `idx_oob` + `div_by_zero`.
    let env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for n in [MIRSEM_IDX_OOB, MIRSEM_DIV_BY_ZERO] {
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
    // The adequacy lemmas themselves must also rest on ⊆ the 3 axioms.
    for verdict in [check_bounds_adequacy(), check_div_adequacy()] {
        match verdict {
            AdequacyVerdict::ProvenModulo3 => {}
            AdequacyVerdict::Residue(names) => return AnchorVerdict::Residue(names),
            AdequacyVerdict::KernelRejected(e) => return AnchorVerdict::KernelRejected(e),
        }
    }
    AnchorVerdict::Modulo3
}
