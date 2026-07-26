// Signed overflow, negation overflow, shift-amount out-of-range and unsigned
// subtraction underflow, plus remainder by zero. Signed classes carry both
// bounds because the asymmetry of two's complement makes `MIN` its own case.

use super::*;

/// The canonical Clean name of the signed machine-overflow predicate
/// `Trust.MirSem.s{add,sub}_overflows_i{W}`. Keyed by op AND width via the
/// op head + the `±2^(W−1)` closed threshold literals.
pub(super) fn signed_overflows_name(op: SignedOp, w: SWidth) -> String {
    format!("Trust.MirSem.s{}_overflows_i{}", op.tag(), w.bits())
}

/// The closed `Int` literal term for the signed MAX `2^(W−1) − 1`, IDENTICAL to
/// `int_lit_to_expr(type_max_formula(W,true))` in the grounder (`Int.ofNat (2^(W−1)−1)`).
pub(super) fn signed_max_expr(w: SWidth) -> Expr {
    int_lit(w.max_value())
}

/// The closed `Int` literal term for the signed MIN `−2^(W−1)`, IDENTICAL to
/// `int_lit_to_expr(type_min_formula(W,true))` in the grounder
/// (`Int.negSucc (2^(W−1)−1)`). Built through the SAME `int_lit` helper, so it is the
/// byte-exact term the grounder produces — NOT `Int.neg (Int.ofNat …)`.
pub(super) fn signed_min_expr(w: SWidth) -> Expr {
    int_lit(w.min_value())
}

/// The `Int`-sorted result term for a signed binop applied to `a_ref`,`b_ref` —
/// `Int.<op> a b`, IDENTICAL to what `ground_int` produces for `Formula::Add/Sub`.
pub(super) fn signed_result_expr(op: SignedOp, a_ref: &Expr, b_ref: &Expr) -> Expr {
    Expr::apps(cst(op.int_head()), [a_ref.clone(), b_ref.clone()])
}

/// The GROUNDED REFLECTION of the FULL signed out-of-range disjunction
/// `Or([Lt(result, MIN), Gt(result, MAX)])`, under de-Bruijn `a_ref`/`b_ref` — the
/// EXACT term `clean_ground::ground_prop` produces for that `Formula`:
///
/// ```text
/// ground_prop(Or([Lt(a∘b, MIN), Gt(a∘b, MAX)]))
///   = Or (Int.lt (Int.<op> a b) (Int.negSucc (2^(W−1)−1)))   -- Lt in order
///        (Int.lt (Int.ofNat (2^(W−1)−1)) (Int.<op> a b))      -- Gt swaps args
/// ```
///
/// This is the term Lemma 5 claims is def-eq to `s<op>_overflows_iW a b`. BOTH
/// disjuncts are live (signed arithmetic underflows AND overflows).
pub(super) fn reflected_signed_out_of_range(op: SignedOp, a_ref: &Expr, b_ref: &Expr, w: SWidth) -> Expr {
    let result = signed_result_expr(op, a_ref, b_ref);
    // Lt(result, MIN) ↦ Int.lt result MIN   (Lt grounds in order)
    let underflow = Expr::apps(cst("Int.lt"), [result.clone(), signed_min_expr(w)]);
    // Gt(result, MAX) ↦ Int.lt MAX result   (Gt swaps args)
    let overflow = Expr::apps(cst("Int.lt"), [signed_max_expr(w), result]);
    // Or p q   (ground_prop folds the 2-element Or as `Or (ground head) (ground tail)`)
    Expr::apps(cst("Or"), [underflow, overflow])
}

/// Register `Trust.MirSem.s{op}_overflows_i{W} : Int → Int → Prop` (idempotent):
///
/// ```text
/// s<op>_overflows_iW (a b : Int) : Prop :=
///   Or (Int.lt (Int.<op> a b) (Int.negSucc (2^(W−1)−1)))
///      (Int.lt (Int.ofNat (2^(W−1)−1)) (Int.<op> a b))
/// ```
///
/// This IS the machine SIGNED-overflow condition of `i_W` `a∘b`: for in-range
/// operands the result overflows IFF it is OUTSIDE `[−2^(W−1), 2^(W−1)−1]`. The body
/// is built from the prelude's reducible `Or`/`Int.lt`/`Int.add`/`Int.sub`/
/// `Int.ofNat`/`Int.negSucc` DEFINITIONS, so the decl's transitive axiom closure is
/// `⊆ {propext, Quot.sound, Classical.choice}`.
pub(super) fn register_signed_overflows(env: &mut Environment, op: SignedOp, w: SWidth) -> Result<(), String> {
    let name = Name::from_string(&signed_overflows_name(op, w));
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // s<op>_overflows_iW : Int → Int → Prop
    let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::prop()));
    // Inside `λ(a:Int). λ(b:Int). …` : b = bvar(0), a = bvar(1).
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let body = reflected_signed_out_of_range(op, &a_ref, &b_ref, w);
    let val = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(s{}_overflows_i{}): {e:?}", op.tag(), w.bits()))?;
    Ok(())
}

/// The Lemma-5 *theorem statement* — the signed-add/sub overflow-VC adequacy:
///
/// ```text
/// ∀ (a b : Int), <reflected signed out-of-range> = s<op>_overflows_iW a b   (in Prop)
/// ```
///
/// i.e. `@Eq Prop <reflected disjunction> (s<op>_overflows_iW a b)`, universally over
/// the two operand Ints. `claimed_rhs = Some` REPLACES the spec on the RHS — used by
/// the fail-closed tests to assert a WRONG threshold / width / dropped-disjunct /
/// direction does NOT prove.
pub(super) fn signed_overflow_adequacy_statement(op: SignedOp, w: SWidth, claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Inside `∀(a:Int).∀(b:Int), …` : b = bvar(0), a = bvar(1).
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let lhs = reflected_signed_out_of_range(op, &a_ref, &b_ref, w);
    let rhs = claimed_rhs.cloned().unwrap_or_else(|| {
        Expr::apps(cst(&signed_overflows_name(op, w)), [a_ref.clone(), b_ref.clone()])
    });
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [Expr::prop(), lhs, rhs]);
    Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), body))
}

/// The Lemma-5 *proof term* — reflexivity. `s<op>_overflows_iW a b` δ/ι-reduces
/// (unfolding the reducible definition) to the reflected signed out-of-range
/// disjunction, so the two `Prop` terms are def-eq and the witness is
/// `λ(a b:Int). @Eq.refl Prop <reflected disjunction>`.
pub(super) fn signed_overflow_adequacy_proof(op: SignedOp, w: SWidth) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let lhs = reflected_signed_out_of_range(op, &a_ref, &b_ref, w);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [Expr::prop(), lhs]);
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), refl))
}

/// Check Lemma 5 (signed-add/sub overflow-VC adequacy) for op `op` + width `w` against
/// the REAL clean-kernel: register the MirSem + signed-overflow anchor, build the
/// statement `∀ a b. <reflected signed out-of-range> = s<op>_overflows_iW a b` and the
/// reflexivity proof, `check_type` it, register it, and audit the axiom closure via
/// `axiom_deps`.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term trust-vcgen+`ground_prop`
/// produce for the signed `BinaryOp(Add|Sub)` overflow obligation is EXACTLY the pinned
/// machine signed-overflow condition `(a∘b) < −2^(W−1) ∨ (2^(W−1)−1) < (a∘b)` —
/// kernel-verified modulo the 3 foundational axioms. So a safety proof refuting that VC
/// refutes EXACTLY the signed-overflow condition: the discharge is FAITHFUL.
#[must_use]
pub fn check_signed_overflow_adequacy(op: SignedOp, w: SWidth) -> AdequacyVerdict {
    check_signed_overflow_adequacy_inner(op, w, None)
}

/// Internal: `claimed_rhs = Some(e)` overrides the spec (the fail-closed path — a
/// wrong threshold / width / dropped-disjunct must make the reflexivity proof fail to
/// type-check).
pub(super) fn check_signed_overflow_adequacy_inner(
    op: SignedOp,
    w: SWidth,
    claimed_rhs: Option<&Expr>,
) -> AdequacyVerdict {
    let mut env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let statement = signed_overflow_adequacy_statement(op, w, claimed_rhs);
    let proof = signed_overflow_adequacy_proof(op, w);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma5.signed_overflow_adequacy");
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

/// Pin the signed machine-overflow anchor and audit its axiom closure: confirm BOTH
/// the per-(op,width) `s{add,sub,mul}_overflows_i{W}` predicates AND the signed-overflow
/// adequacy lemma (op=Add, w=32, the canonical `i32` case) rest on exactly the 3
/// foundational axioms (modulo 3, no 4th axiom). Mirrors `pin_overflow_anchor` for the
/// signed safety-VC fragment.
#[must_use]
pub fn pin_signed_overflow_anchor() -> AnchorVerdict {
    let env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for op in [SignedOp::Add, SignedOp::Sub, SignedOp::Mul] {
        for w in [SWidth::W8, SWidth::W16, SWidth::W32, SWidth::W64] {
            match env.axiom_deps(&Name::from_string(&signed_overflows_name(op, w))) {
                Some(residue) if residue.is_empty() => {}
                Some(residue) => {
                    let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                    names.sort();
                    return AnchorVerdict::Residue(names);
                }
                None => {
                    return AnchorVerdict::KernelRejected(format!(
                        "decl not found: s{}_i{}",
                        op.tag(),
                        w.bits()
                    ));
                }
            }
        }
    }
    // The adequacy lemma itself (op=Add, w=32) must also rest on ⊆ the 3 axioms.
    match check_signed_overflow_adequacy(SignedOp::Add, SWidth::W32) {
        AdequacyVerdict::ProvenModulo3 => {}
        AdequacyVerdict::Residue(names) => return AnchorVerdict::Residue(names),
        AdequacyVerdict::KernelRejected(e) => return AnchorVerdict::KernelRejected(e),
    }
    AnchorVerdict::Modulo3
}

/// THE LEMMA-5 / SAFETY-VC PIPELINE HOOK. For a modeled signed op+width, return the
/// kernel-checked signed-overflow-VC adequacy certificate — `Some` iff the signed
/// overflow VC's reflected formula is PROVEN (modulo 3) def-eq to the machine signed
/// overflow condition. Fail-closed (`None`) for an op+width whose adequacy proof does
/// not kernel-check modulo 3 — never a false certificate.
#[must_use]
pub fn signed_overflow_adequacy_witness(
    op: SignedOp,
    w: SWidth,
) -> Option<SignedOverflowAdequacyCertificate> {
    match check_signed_overflow_adequacy(op, w) {
        AdequacyVerdict::ProvenModulo3 => Some(SignedOverflowAdequacyCertificate {
            op,
            width: w,
            verdict: AdequacyVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Step 2I — Lemma 6: SAFETY-VC adequacy (the NEGATION-OVERFLOW case)
// ---------------------------------------------------------------------------
//
// THE GAP THIS CLOSES (a remaining LIA-tractable unmodeled safety VC).
// A signed unary negation `-x` on `i_W` is UB / panics IFF `x = i_W::MIN = −2^(W−1)`,
// because `−MIN = 2^(W−1)` is unrepresentable in `i_W`. Until now that
// `VcKind::NegationOverflow` VC was UNMODELED, so a function as simple as
// `fn neg(x:i32) -> i32 { -x }` could not be FULLY FAITHFUL: its one safety VC fell
// into the fail-closed "unmodeled" bucket. Lemma 6 closes that for the negation case.
// It pins the machine negation-overflow SEMANTICS in Clean (`neg_overflows_iW`) and
// proves the term trust-vcgen+`ground_prop` produce for a signed `UnaryOp(Neg)`
// obligation IS (def-eq) that machine condition. So discharging the VC refutes EXACTLY
// `x = MIN`, not a reflected formula we merely trust.
//
// THE EXACT EMITTED SHAPE (verified EMPIRICALLY against the real emitter via
// `trust_vcgen::generate_vcs`, NOT assumed — see
// `negation_vc_shape_matches_trust_vcgen_emission`).
//   * A signed `Rvalue::UnaryOp(Neg, x)` whose operand is `i8`/`i16`/`i32`/`i64`
//     raises a `VcKind::NegationOverflow{ty: i_W}` VC. The emitted formula is
//        And([ MIN ≤ x ≤ MAX, Eq(x, MIN) ])
//     where the violation CORE is the single equality `Eq(x, MIN)`, with
//     `MIN = type_min_formula(W,true) = Formula::Int(−2^(W−1))`. For i32 (probed,
//     byte-exact): `Eq(Var x, Int(−2147483648))`. See
//     `crates/trust-vcgen/src/generate/checked_vcs.rs::v2_build_negation_raw_vc` +
//     `crates/trust-vcgen/src/range.rs::{type_min_formula,signed_min}`.
//   * `clean_ground::ground_prop` grounds `Eq(x, y)` to `@Eq Int (ground x) (ground y)`.
//     So the negation-overflow CORE `Eq(x, MIN)` grounds to EXACTLY
//        `@Eq Int x (Int.negSucc (2^(W−1)−1))`   :  Prop
//     i.e. the proposition `x = −2^(W−1)`. (`Int.negSucc (2^(W−1)−1)` IS `−2^(W−1)`,
//     built through the SAME `int_lit` helper the grounder uses — byte-identical, NOT
//     `Int.neg (Int.ofNat …)`.)
//
// THE SPEC. `neg_overflows_iW x` is DEFINED as `x = −2^(W−1)` over Int
// (`@Eq Int x (Int.negSucc (2^(W−1)−1))`). For in-range `−2^(W−1) ≤ x ≤ 2^(W−1)−1`,
// negating `x` overflows `i_W` IFF `x` is the unique value whose negation escapes the
// range — `x = MIN`. (`Eq`/`Int.negSucc`/`Int.ofNat` are reducible prelude
// DEFINITIONS, so the spec carries no non-foundational axiom.)
//
// THE ADEQUACY (Lemma 6). The reflected negation-overflow CORE term is LITERALLY the
// spec term, so adequacy is `@Eq.{1} Prop reflected neg_overflows_iW` witnessed by
// `Eq.refl` — kernel-checked modulo the 3 foundational axioms. A WRONG threshold
// (`MIN±1`, or a WRONG width's MIN) or a WRONG relation (`Int.lt` instead of `Eq`)
// changes the closed `Prop` term, so the `Eq.refl` proof is KERNEL-REJECTED — every
// wrong claim fails closed.
//
// SCOPE / HONEST GAP. This pins the negation-overflow CORE `Eq(x, MIN)` for W ∈
// {8,16,32,64}. A signed `i128` negation is DEFERRED: the emitter models it with
// BITVECTOR reasoning (`x == INT_MIN` over BV — `parse_i64` cannot represent `−2^127`
// on the Int path), so its adequacy needs bitvector reasoning the def-eq kernel cannot
// close by reflexivity. We do NOT fake it — a signed `i128` negation stays UNMODELED
// (fail-closed). The surrounding `And([range, core])` wrapper's range conjunct is the
// in-range premise (the deferred breadth); the load-bearing claim — the negation core
// IS `x = MIN` — is what we prove.
/// The canonical Clean name of the signed machine negation-overflow predicate
/// `Trust.MirSem.neg_overflows_i{W}`, keyed by width via the closed `−2^(W−1)`
/// threshold literal.
pub(super) fn neg_overflows_name(w: SWidth) -> String {
    format!("Trust.MirSem.neg_overflows_i{}", w.bits())
}

/// The GROUNDED REFLECTION of the negation-overflow CORE `Eq(x, MIN)`, under the
/// de-Bruijn term `x_ref` for the negated value — the EXACT term
/// `clean_ground::ground_prop` produces for that `Formula`:
///
/// ```text
/// ground_prop(Eq(x, Int(−2^(W−1)))) = @Eq Int (ground x) (ground (Int(−2^(W−1))))
///                                   = @Eq Int x (Int.negSucc (2^(W−1)−1))
/// ```
///
/// This is the term Lemma 6 claims is def-eq to `neg_overflows_iW x`, AND the body the
/// `neg_overflows_iW` definition unfolds to (so the spec and the reflection are the
/// same closed term). `Int.negSucc (2^(W−1)−1)` is built through the SAME `int_lit`
/// helper the grounder uses, so it is the byte-exact MIN literal.
pub(super) fn neg_overflows_body(x_ref: &Expr, w: SWidth) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    // @Eq Int x (Int.negSucc (2^(W−1)−1))
    Expr::apps(eq, [int_ty(), x_ref.clone(), signed_min_expr(w)])
}

/// Register `Trust.MirSem.neg_overflows_i{W} : Int → Prop` (idempotent):
///
/// ```text
/// neg_overflows_iW (x : Int) : Prop := @Eq Int x (Int.negSucc (2^(W−1)−1))
/// ```
///
/// This IS the machine negation-overflow condition of `i_W` `−x`: the negation
/// overflows IFF `x = −2^(W−1)` (the unique value whose negation is unrepresentable).
/// The body is the prelude's reducible `Eq`/`Int.negSucc` DEFINITIONS, so the decl's
/// transitive axiom closure is `⊆ {propext, Quot.sound, Classical.choice}`.
pub(super) fn register_neg_overflows(env: &mut Environment, w: SWidth) -> Result<(), String> {
    let name = Name::from_string(&neg_overflows_name(w));
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // neg_overflows_iW : Int → Prop
    let ty = Expr::pi(bd(), int_ty(), Expr::prop());
    // Inside `λ(x:Int). …` : x = bvar(0).
    let x_ref = Expr::bvar(0);
    let body = neg_overflows_body(&x_ref, w);
    let val = Expr::lam(bd(), int_ty(), body);
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(neg_overflows_i{}): {e:?}", w.bits()))?;
    Ok(())
}

/// The Lemma-6 *theorem statement* — the negation-overflow-VC adequacy:
///
/// ```text
/// ∀ (x : Int), <reflected negation core> = neg_overflows_iW x      (in Prop)
/// ```
///
/// i.e. `@Eq Prop (@Eq Int x (Int.negSucc (2^(W−1)−1))) (neg_overflows_iW x)`,
/// universally over the negated value Int. `claimed_rhs = Some` REPLACES the spec on
/// the RHS — used by the fail-closed tests to assert a WRONG threshold / width /
/// relation does NOT prove.
pub(super) fn neg_overflow_adequacy_statement(w: SWidth, claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Inside `∀(x:Int), …` : x = bvar(0).
    let x_ref = Expr::bvar(0);
    let lhs = neg_overflows_body(&x_ref, w);
    let rhs = claimed_rhs
        .cloned()
        .unwrap_or_else(|| Expr::app(cst(&neg_overflows_name(w)), x_ref.clone()));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [Expr::prop(), lhs, rhs]);
    Expr::pi(bd(), int_ty(), body)
}

/// The Lemma-6 *proof term* — reflexivity. `neg_overflows_iW x` δ-reduces (unfolding
/// the reducible definition) to `@Eq Int x (Int.negSucc (2^(W−1)−1))`, which is
/// LITERALLY the reflected negation core, so the two `Prop` terms are def-eq and the
/// witness is `λ(x:Int). @Eq.refl Prop <reflected core>`.
pub(super) fn neg_overflow_adequacy_proof(w: SWidth) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let x_ref = Expr::bvar(0);
    let lhs = neg_overflows_body(&x_ref, w);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [Expr::prop(), lhs]);
    Expr::lam(bd(), int_ty(), refl)
}

/// Check Lemma 6 (negation-overflow-VC adequacy) for width `w` against the REAL
/// clean-kernel: register the MirSem + negation-overflow anchor, build the statement
/// `∀ x. <reflected negation core> = neg_overflows_iW x` and the reflexivity proof,
/// `check_type` it, register it, and audit the axiom closure via `axiom_deps`.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term trust-vcgen+`ground_prop`
/// produce for the signed `UnaryOp(Neg)` obligation is EXACTLY the pinned machine
/// negation-overflow condition `x = −2^(W−1)` — kernel-verified modulo the 3
/// foundational axioms. So a safety proof refuting that VC refutes EXACTLY the
/// negation-overflow condition: the discharge is FAITHFUL.
#[must_use]
pub fn check_neg_overflow_adequacy(w: SWidth) -> AdequacyVerdict {
    check_neg_overflow_adequacy_inner(w, None)
}

/// Internal: `claimed_rhs = Some(e)` overrides the spec (the fail-closed path — a wrong
/// threshold / width / relation must make the reflexivity proof fail to type-check).
pub(super) fn check_neg_overflow_adequacy_inner(w: SWidth, claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    let mut env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let statement = neg_overflow_adequacy_statement(w, claimed_rhs);
    let proof = neg_overflow_adequacy_proof(w);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma6.neg_overflow_adequacy");
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

/// Pin the negation machine-overflow anchor and audit its axiom closure: confirm BOTH
/// the per-width `neg_overflows_i{W}` predicates AND the negation-overflow adequacy
/// lemma (w=32, the canonical `i32` case) rest on exactly the 3 foundational axioms
/// (modulo 3, no 4th axiom). Mirrors `pin_signed_overflow_anchor` for the negation
/// safety-VC fragment.
#[must_use]
pub fn pin_negation_anchor() -> AnchorVerdict {
    let env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for w in [SWidth::W8, SWidth::W16, SWidth::W32, SWidth::W64] {
        match env.axiom_deps(&Name::from_string(&neg_overflows_name(w))) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                names.sort();
                return AnchorVerdict::Residue(names);
            }
            None => {
                return AnchorVerdict::KernelRejected(format!("decl not found: neg_i{}", w.bits()));
            }
        }
    }
    // The adequacy lemma itself (w=32) must also rest on ⊆ the 3 axioms.
    match check_neg_overflow_adequacy(SWidth::W32) {
        AdequacyVerdict::ProvenModulo3 => {}
        AdequacyVerdict::Residue(names) => return AnchorVerdict::Residue(names),
        AdequacyVerdict::KernelRejected(e) => return AnchorVerdict::KernelRejected(e),
    }
    AnchorVerdict::Modulo3
}

/// THE LEMMA-6 / SAFETY-VC PIPELINE HOOK. For a modeled signed width, return the
/// kernel-checked negation-overflow-VC adequacy certificate — `Some` iff the negation
/// VC's reflected core is PROVEN (modulo 3) def-eq to the machine condition `x = MIN`.
/// Fail-closed (`None`) for a width whose adequacy proof does not kernel-check modulo 3
/// — never a false certificate.
#[must_use]
pub fn negation_adequacy_witness(w: SWidth) -> Option<NegationAdequacyCertificate> {
    match check_neg_overflow_adequacy(w) {
        AdequacyVerdict::ProvenModulo3 => {
            Some(NegationAdequacyCertificate { width: w, verdict: AdequacyVerdict::ProvenModulo3 })
        }
        _ => None,
    }
}

/// `Trust.MirSem.shift_amount_oob{,_signed}_{W}` — the shift-amount-UB predicate name.
pub(super) fn shift_amount_oob_name(w: ShiftWidth, amount_signed: bool) -> String {
    if amount_signed {
        format!("Trust.MirSem.shift_amount_oob_signed_{}", w.bits())
    } else {
        format!("Trust.MirSem.shift_amount_oob_{}", w.bits())
    }
}

/// The closed `Int` literal term for the shift bit-width threshold `W`, IDENTICAL to
/// `int_lit_to_expr(Int(W))` in the grounder (`Int.ofNat W`).
pub(super) fn shift_width_expr(w: ShiftWidth) -> Expr {
    int_lit(i128::from(w.bits()))
}

/// The GROUNDED REFLECTION of the UNSIGNED-amount shift-OOB CORE `Ge(n, Int(W))`,
/// under the de-Bruijn term `n_ref` for the shift amount — the EXACT term
/// `clean_ground::ground_prop` produces for that `Formula`:
///
/// ```text
/// ground_prop(Ge(n, Int(W))) = Int.le (ground_int (Int W)) (ground_int n)
///                            = Int.le (Int.ofNat W) n
/// ```
///
/// (`Ge(x,y)` grounds with the arguments SWAPPED: `Int.le (g y) (g x)`.) This is the
/// term Lemma 7 claims is def-eq to `shift_amount_oob_W n`.
pub(super) fn reflected_shift_oob_unsigned(n_ref: &Expr, w: ShiftWidth) -> Expr {
    Expr::apps(cst("Int.le"), [shift_width_expr(w), n_ref.clone()])
}

/// The GROUNDED REFLECTION of the SIGNED-amount shift-OOB CORE
/// `Or([Lt(n, Int(0)), Ge(n, Int(W))])`, exactly as `ground_prop` folds a two-element
/// `Formula::Or` (`Or (ground head) (ground tail)`):
///
/// ```text
/// Or (Int.lt n (Int.ofNat 0)) (Int.le (Int.ofNat W) n)
/// ```
///
/// i.e. `n < 0 ∨ W ≤ n`. This is the term Lemma 7 claims is def-eq to
/// `shift_amount_oob_signed_W n` for a signed shift amount.
pub(super) fn reflected_shift_oob_signed(n_ref: &Expr, w: ShiftWidth) -> Expr {
    // Lt(n, 0) ↦ Int.lt n (Int.ofNat 0)   (Lt grounds in order)
    let neg = Expr::apps(cst("Int.lt"), [n_ref.clone(), int_lit(0)]);
    // Ge(n, W) ↦ Int.le (Int.ofNat W) n   (Ge swaps args)
    let oob = reflected_shift_oob_unsigned(n_ref, w);
    Expr::apps(cst("Or"), [neg, oob])
}

/// The grounded reflection of the shift-amount-OOB core for the given amount
/// signedness — `W ≤ n` (unsigned) or `n < 0 ∨ W ≤ n` (signed).
pub(super) fn reflected_shift_oob(n_ref: &Expr, w: ShiftWidth, amount_signed: bool) -> Expr {
    if amount_signed {
        reflected_shift_oob_signed(n_ref, w)
    } else {
        reflected_shift_oob_unsigned(n_ref, w)
    }
}

/// Register `Trust.MirSem.shift_amount_oob{,_signed}_{W} : Int → Prop` (idempotent):
///
/// ```text
/// shift_amount_oob_W        (n : Int) : Prop := Int.le (Int.ofNat W) n          -- W ≤ n
/// shift_amount_oob_signed_W (n : Int) : Prop := Or (Int.lt n 0) (Int.le W n)    -- n<0 ∨ W≤n
/// ```
///
/// This IS the machine shift-amount-UB condition of `x ∘ n` on a `W`-bit value: the
/// shift is UB IFF `n ≥ W` (and, for a signed amount, also IFF `n < 0`). The body is
/// built from the prelude's reducible `Int.le`/`Int.lt`/`Or`/`Int.ofNat` DEFINITIONS,
/// so the decl's transitive axiom closure is `⊆ {propext, Quot.sound, Classical.choice}`.
pub(super) fn register_shift_amount_oob(
    env: &mut Environment,
    w: ShiftWidth,
    amount_signed: bool,
) -> Result<(), String> {
    let name = Name::from_string(&shift_amount_oob_name(w, amount_signed));
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // shift_amount_oob{,_signed}_W : Int → Prop
    let ty = Expr::pi(bd(), int_ty(), Expr::prop());
    // Inside `λ(n:Int). …` : n = bvar(0).
    let n_ref = Expr::bvar(0);
    let body = reflected_shift_oob(&n_ref, w, amount_signed);
    let val = Expr::lam(bd(), int_ty(), body);
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(shift_amount_oob_{}): {e:?}", w.bits()))?;
    Ok(())
}

/// The Lemma-7 *theorem statement* — the shift-amount-OOB-VC adequacy:
///
/// ```text
/// ∀ (n : Int), <reflected shift-OOB core> = shift_amount_oob{,_signed}_W n   (in Prop)
/// ```
///
/// i.e. `@Eq Prop <reflected core> (shift_amount_oob_W n)`, universally over the shift
/// amount Int. `claimed_rhs = Some` REPLACES the spec on the RHS — used by the
/// fail-closed tests to assert a `<`-vs-`≤` off-by-one / wrong width / wrong direction /
/// dropped disjunct does NOT prove.
pub(super) fn shift_oob_adequacy_statement(
    w: ShiftWidth,
    amount_signed: bool,
    claimed_rhs: Option<&Expr>,
) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Inside `∀(n:Int), …` : n = bvar(0).
    let n_ref = Expr::bvar(0);
    let lhs = reflected_shift_oob(&n_ref, w, amount_signed);
    let rhs = claimed_rhs
        .cloned()
        .unwrap_or_else(|| Expr::app(cst(&shift_amount_oob_name(w, amount_signed)), n_ref.clone()));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [Expr::prop(), lhs, rhs]);
    Expr::pi(bd(), int_ty(), body)
}

/// The Lemma-7 *proof term* — reflexivity. `shift_amount_oob_W n` δ-reduces (unfolding
/// the reducible definition) to the reflected shift-OOB core, so the two `Prop` terms
/// are def-eq and the witness is `λ(n:Int). @Eq.refl Prop <reflected core>`.
pub(super) fn shift_oob_adequacy_proof(w: ShiftWidth, amount_signed: bool) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let n_ref = Expr::bvar(0);
    let lhs = reflected_shift_oob(&n_ref, w, amount_signed);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [Expr::prop(), lhs]);
    Expr::lam(bd(), int_ty(), refl)
}

/// Check Lemma 7 (shift-amount-OOB-VC adequacy) for value-width `w` and shift-amount
/// signedness against the REAL clean-kernel: register the MirSem + shift-OOB anchor,
/// build the statement `∀ n. <reflected core> = shift_amount_oob_W n` and the
/// reflexivity proof, `check_type` it, register it, and audit the axiom closure.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term trust-vcgen+`ground_prop`
/// produce for the `BinaryOp(Shl|Shr)` shift-amount obligation is EXACTLY the pinned
/// machine condition `W ≤ n` (unsigned) / `n < 0 ∨ W ≤ n` (signed) — kernel-verified
/// modulo the 3 foundational axioms. So a safety proof refuting that VC refutes EXACTLY
/// the shift-amount-UB condition: the discharge is FAITHFUL.
#[must_use]
pub fn check_shift_oob_adequacy(w: ShiftWidth, amount_signed: bool) -> AdequacyVerdict {
    check_shift_oob_adequacy_inner(w, amount_signed, None)
}

/// Internal: `claimed_rhs = Some(e)` overrides the spec (the fail-closed path — a
/// `<`-vs-`≤` off-by-one / wrong width / wrong direction must fail to type-check).
pub(super) fn check_shift_oob_adequacy_inner(
    w: ShiftWidth,
    amount_signed: bool,
    claimed_rhs: Option<&Expr>,
) -> AdequacyVerdict {
    let mut env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let statement = shift_oob_adequacy_statement(w, amount_signed, claimed_rhs);
    let proof = shift_oob_adequacy_proof(w, amount_signed);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma7.shift_oob_adequacy");
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

/// Pin the shift-amount-OOB machine anchor and audit its axiom closure: confirm BOTH
/// the per-(width, amount-signedness) `shift_amount_oob{,_signed}_W` predicates AND the
/// shift-OOB adequacy lemma (w=32, unsigned amount — the canonical `x:u32 << n:u32`
/// case) rest on exactly the 3 foundational axioms (modulo 3, no 4th axiom). Mirrors
/// `pin_signed_overflow_anchor` for the shift safety-VC fragment.
#[must_use]
pub fn pin_shift_anchor() -> AnchorVerdict {
    let env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for w in ShiftWidth::ALL {
        for amount_signed in [false, true] {
            match env.axiom_deps(&Name::from_string(&shift_amount_oob_name(w, amount_signed))) {
                Some(residue) if residue.is_empty() => {}
                Some(residue) => {
                    let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                    names.sort();
                    return AnchorVerdict::Residue(names);
                }
                None => {
                    return AnchorVerdict::KernelRejected(format!(
                        "decl not found: shift_oob_{}{}",
                        w.bits(),
                        if amount_signed { "_signed" } else { "" }
                    ));
                }
            }
        }
    }
    // The adequacy lemma itself (w=32, unsigned amount) must also rest on ⊆ the 3 axioms.
    match check_shift_oob_adequacy(ShiftWidth::W32, false) {
        AdequacyVerdict::ProvenModulo3 => {}
        AdequacyVerdict::Residue(names) => return AnchorVerdict::Residue(names),
        AdequacyVerdict::KernelRejected(e) => return AnchorVerdict::KernelRejected(e),
    }
    AnchorVerdict::Modulo3
}

/// THE LEMMA-7 / SAFETY-VC PIPELINE HOOK. For a modeled value width + shift-amount
/// signedness, return the kernel-checked shift-amount-OOB-VC adequacy certificate —
/// `Some` iff the shift VC's reflected core is PROVEN (modulo 3) def-eq to the machine
/// condition. Fail-closed (`None`) for a width whose adequacy proof does not
/// kernel-check modulo 3 — never a false certificate.
#[must_use]
pub fn shift_adequacy_witness(
    w: ShiftWidth,
    amount_signed: bool,
) -> Option<ShiftAdequacyCertificate> {
    match check_shift_oob_adequacy(w, amount_signed) {
        AdequacyVerdict::ProvenModulo3 => Some(ShiftAdequacyCertificate {
            width: w,
            amount_signed,
            verdict: AdequacyVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Step 2I — Lemma 8: SAFETY-VC adequacy (the UNSIGNED-SUBTRACTION UNDERFLOW case)
// ---------------------------------------------------------------------------
//
// THE GAP THIS CLOSES (the last clean unsigned-integer safety VC).
// Lemma 2 certifies the unsigned-ADD overflow VC; Lemma 5 the SIGNED add/sub
// overflow VC. But the dominant unsigned-arithmetic obligation OTHER than add is
// `a - b` on `uW`, whose only failure mode is UNDERFLOW (the mathematical result
// goes negative / the machine value wraps). Until now that VC fell into the
// fail-closed "unmodeled" bucket: a function as simple as `fn diff(a:u32,b:u32){a-b}`
// — or the guarded `if a>=b {a-b}` of `guarded_sub` — could not be FULLY FAITHFUL.
// Lemma 8 closes it: it pins the machine unsigned-underflow SEMANTICS in Clean
// (`usub_underflows_uW`) and proves the term trust-vcgen+`ground_prop` produce for
// the unsigned `BinaryOp(Sub)` overflow obligation IS (def-eq) that condition. So
// discharging the VC refutes EXACTLY the underflow condition.
//
// THE EXACT EMITTED SHAPE (verified EMPIRICALLY against the real emitter via
// `trust_vcgen::generate_vcs`, NOT assumed — see
// `usub_underflow_vc_shape_matches_trust_vcgen_emission`).
//   * An unsigned `Rvalue::BinaryOp(Sub, a, b)` (or the assert-guarded
//     `CheckedBinaryOp(Sub,…)` form `guarded_sub`/`usub` carry) whose result local is
//     `u8`/`u16`/`u32`/`u64` raises a `VcKind::ArithmeticOverflow{op:Sub, (u_W,u_W)}`
//     (Int-path) VC. UNLIKE the signed case (a 2-element `Or`), the UNSIGNED-sub
//     emitter drops the tautological `result > MAX` disjunct (`a−b ≤ a ≤ MAX`) and
//     emits ONLY the single underflow disjunct (probed: byte-exact at u32):
//        Lt(Sub(a, b), Int(0))                  (overflow_vc.rs, the `!signed && Sub` arm)
//     i.e. the violation core is `a − b < 0`. (`type_min_formula(W,false) =
//     Formula::Int(0)`.) See `crates/trust-vcgen/src/generate/overflow_vc.rs`
//     (`v2_build_overflow_vc_for_operands`, the `!signed && matches!(op, BinOp::Sub)`
//     branch) + `crates/trust-vcgen/src/range.rs::type_min_formula`.
//   * `clean_ground::ground_prop` grounds that disjunct to a Clean `Prop`:
//        - `Formula::Lt(x, y)`  ↦  `Int.lt (ground x) (ground y)`   (in order)
//        - `Formula::Sub(x, y)` ↦  `Int.sub (ground x) (ground y)`
//        - `Formula::Int(0)`    ↦  `Int.ofNat 0`
//     So the underflow disjunct `Lt(Sub(a,b), 0)` grounds to EXACTLY
//        `Int.lt (Int.sub a b) (Int.ofNat 0)`   :  Prop
//     i.e. the proposition `(a − b) < 0`.
//
// THE SPEC. `usub_underflows_uW a b` is DEFINED as `(a − b) < 0` over Int
// (`Int.lt (Int.sub a b) (Int.ofNat 0)`). For in-range `0 ≤ a,b ≤ 2^W−1` this is the
// machine underflow condition of `u_W` wrapping-sub: the machine difference
// `(a−b) mod 2^W` differs from `a−b` (i.e. wraps) IFF `a < b` IFF `a − b < 0`.
// `Int.lt`/`Int.sub`/`Int.ofNat` are reducible prelude DEFINITIONS, so the spec
// carries no non-foundational axiom. (The threshold here is NOT width-dependent —
// the underflow bound is `0` at every unsigned width — but we key the predicate by
// width anyway, mirroring Lemma 2, so the per-width tally stays honest and the
// classifier and the spec name agree.)
//
// THE ADEQUACY (Lemma 8). The reflected underflow-disjunct term is LITERALLY the spec
// term, so adequacy is `@Eq.{1} Prop reflected usub_underflows_uW` witnessed by
// `Eq.refl` — kernel-checked modulo the 3 foundational axioms. A WRONG DIRECTION
// (`b − a < 0` instead of `a − b < 0`, equivalently `b < a` vs `a < b`), a WRONG
// COMPARATOR (`a − b ≤ 0` instead of `< 0`, i.e. `Int.le` vs `Int.lt`), or a WRONG
// threshold (`a − b < 1` instead of `< 0`) is a different `Prop` term — NOT def-eq —
// and the `Eq.refl` proof is KERNEL-REJECTED. The off-by-one / wrong-direction fails
// closed.
//
// SCOPE / HONEST GAP. This pins the underflow disjunct `Sub(a,b) < 0` — the disjunct
// that IS the underflow condition; the emitter has no other live disjunct for unsigned
// sub (the `> MAX` half is dropped at the source). The wrapping-result bridge
// (`(a−b) mod 2^W = a−b ⟺ a ≥ b`) needs `mod`/order reasoning the def-eq kernel
// cannot close by reflexivity; it is the deferred breadth, NOT faked here. Widths
// W ∈ {8,16,32,64} all reduce by the same reflexivity (the threshold is the closed
// `Int.ofNat 0` literal at every width).
/// The canonical Clean name of the unsigned-subtraction-underflow predicate
/// `Trust.MirSem.usub_underflows_u{W}`. Keyed by width (matching Lemma 2's naming),
/// though the underflow threshold (`0`) is the same closed literal at every width.
pub(super) fn usub_underflows_name(w: UWidth) -> String {
    format!("Trust.MirSem.usub_underflows_u{}", w.bits())
}

/// The GROUNDED REFLECTION of the unsigned-sub UNDERFLOW disjunct `Lt(Sub(a,b), 0)`,
/// under de-Bruijn `a_ref`/`b_ref` — the EXACT term `clean_ground::ground_prop`
/// produces for that `Formula`:
///
/// ```text
/// ground_prop(Lt(Sub(Var a, Var b), Int(0)))
///   = Int.lt (Int.sub a b) (Int.ofNat 0)
/// ```
///
/// (`Lt(x,y)` grounds in order; `Sub(x,y)` ↦ `Int.sub x y`.) This is the term Lemma 8
/// claims is def-eq to `usub_underflows_uW a b`.
pub(super) fn reflected_usub_underflow(a_ref: &Expr, b_ref: &Expr) -> Expr {
    // Int.sub a b
    let diff = Expr::apps(cst("Int.sub"), [a_ref.clone(), b_ref.clone()]);
    // Int.lt (Int.sub a b) (Int.ofNat 0)
    Expr::apps(cst("Int.lt"), [diff, int_lit(0)])
}

/// Register `Trust.MirSem.usub_underflows_u{W} : Int → Int → Prop` (idempotent):
///
/// ```text
/// usub_underflows_uW (a b : Int) : Prop := Int.lt (Int.sub a b) (Int.ofNat 0)
/// ```
///
/// This IS the machine-underflow condition of the `u_W` wrapping-sub overflow flag:
/// for in-range `0 ≤ a,b ≤ 2^W−1`, the difference underflows the width IFF
/// `a − b < 0` (equivalently `a < b`). The body is built from the prelude's reducible
/// `Int.lt`/`Int.sub`/`Int.ofNat` DEFINITIONS, so the decl's transitive axiom closure
/// is `⊆ {propext, Quot.sound, Classical.choice}`.
pub(super) fn register_usub_underflows(env: &mut Environment, w: UWidth) -> Result<(), String> {
    let name = Name::from_string(&usub_underflows_name(w));
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // usub_underflows_uW : Int → Int → Prop
    let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::prop()));
    // Inside `λ(a:Int). λ(b:Int). …` : b = bvar(0), a = bvar(1).
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let body = reflected_usub_underflow(&a_ref, &b_ref);
    let val = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(usub_underflows_u{}): {e:?}", w.bits()))?;
    Ok(())
}

/// The Lemma-8 *theorem statement* — the unsigned-sub underflow-VC adequacy:
///
/// ```text
/// ∀ (a b : Int), <reflected underflow disjunct> = usub_underflows_uW a b   (in Prop)
/// ```
///
/// i.e. `@Eq Prop (Int.lt (Int.sub a b) (Int.ofNat 0)) (usub_underflows_uW a b)`,
/// universally over the two operand Ints. `claimed_rhs = Some` REPLACES the spec on the
/// RHS — used by the fail-closed tests to assert a WRONG direction / comparator /
/// threshold does NOT prove.
pub(super) fn usub_underflow_adequacy_statement(w: UWidth, claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Inside `∀(a:Int).∀(b:Int), …` : b = bvar(0), a = bvar(1).
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let lhs = reflected_usub_underflow(&a_ref, &b_ref);
    let rhs = claimed_rhs.cloned().unwrap_or_else(|| {
        Expr::apps(cst(&usub_underflows_name(w)), [a_ref.clone(), b_ref.clone()])
    });
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [Expr::prop(), lhs, rhs]);
    Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), body))
}

/// The Lemma-8 *proof term* — reflexivity. `usub_underflows_uW a b` δ-reduces
/// (unfolding the reducible definition) to `Int.lt (Int.sub a b) (Int.ofNat 0)`, which
/// is LITERALLY the reflected underflow disjunct, so the two `Prop` terms are def-eq
/// and the witness is `λ(a b:Int). @Eq.refl Prop <reflected disjunct>`.
pub(super) fn usub_underflow_adequacy_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let lhs = reflected_usub_underflow(&a_ref, &b_ref);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [Expr::prop(), lhs]);
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), refl))
}

/// Check Lemma 8 (unsigned-sub underflow-VC adequacy) for width `w` against the REAL
/// clean-kernel: register the MirSem + underflow anchor, build the statement
/// `∀ a b. <reflected underflow disjunct> = usub_underflows_uW a b` and the reflexivity
/// proof, `check_type` it, register it, and audit the axiom closure via `axiom_deps`.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term trust-vcgen+`ground_prop`
/// produce for the unsigned `BinaryOp(Sub)` overflow obligation is EXACTLY the pinned
/// machine-underflow condition `(a − b) < 0` — kernel-verified modulo the 3
/// foundational axioms. So a safety proof refuting that VC refutes EXACTLY the
/// underflow condition: the discharge is FAITHFUL.
#[must_use]
pub fn check_usub_underflow_adequacy(w: UWidth) -> AdequacyVerdict {
    check_usub_underflow_adequacy_inner(w, None)
}

/// Internal: `claimed_rhs = Some(e)` overrides the spec (the fail-closed path — a
/// wrong direction / comparator / threshold must make the reflexivity proof fail to
/// type-check).
pub(super) fn check_usub_underflow_adequacy_inner(w: UWidth, claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    let mut env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let statement = usub_underflow_adequacy_statement(w, claimed_rhs);
    let proof = usub_underflow_adequacy_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma8.usub_underflow_adequacy");
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

/// Pin the unsigned-underflow anchor and audit its axiom closure: confirm BOTH the
/// per-width `usub_underflows` predicates AND the underflow-adequacy lemma (w=32, the
/// canonical `u32` case) rest on exactly the 3 foundational axioms (modulo 3, no 4th
/// axiom). Mirrors `pin_overflow_anchor` for the unsigned-sub safety-VC fragment.
#[must_use]
pub fn pin_usub_underflow_anchor() -> AnchorVerdict {
    let env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for w in [UWidth::W8, UWidth::W16, UWidth::W32, UWidth::W64] {
        match env.axiom_deps(&Name::from_string(&usub_underflows_name(w))) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                names.sort();
                return AnchorVerdict::Residue(names);
            }
            None => return AnchorVerdict::KernelRejected(format!("decl not found: u{}", w.bits())),
        }
    }
    match check_usub_underflow_adequacy(UWidth::W32) {
        AdequacyVerdict::ProvenModulo3 => AnchorVerdict::Modulo3,
        AdequacyVerdict::Residue(names) => AnchorVerdict::Residue(names),
        AdequacyVerdict::KernelRejected(e) => AnchorVerdict::KernelRejected(e),
    }
}

/// THE LEMMA-8 / SAFETY-VC PIPELINE HOOK. For a modeled unsigned width, return the
/// kernel-checked unsigned-sub underflow-VC adequacy certificate — `Some` iff the
/// underflow VC's reflected disjunct is PROVEN (modulo 3) def-eq to the machine
/// underflow condition. Fail-closed (`None`) for a width whose adequacy proof does not
/// kernel-check modulo 3 — never a false certificate.
#[must_use]
pub fn usub_underflow_adequacy_witness(w: UWidth) -> Option<UsubUnderflowAdequacyCertificate> {
    match check_usub_underflow_adequacy(w) {
        AdequacyVerdict::ProvenModulo3 => Some(UsubUnderflowAdequacyCertificate {
            width: w,
            verdict: AdequacyVerdict::ProvenModulo3,
        }),
        _ => None,
    }
}

/// Register `Trust.MirSem.rem_by_zero : Int → Prop` (idempotent):
///
/// ```text
/// rem_by_zero (b : Int) : Prop := @Eq Int b (Int.ofNat 0)
/// ```
///
/// This IS the divisor-zero condition of `a % b`: the remainder panics / is UB IFF
/// `b = 0`. The body is built from the prelude's `Eq`/`Int.ofNat` DEFINITIONS (shared
/// with `div_by_zero`), so the decl's transitive axiom closure is
/// `⊆ {propext, Quot.sound, Classical.choice}`.
pub(super) fn register_rem_by_zero(env: &mut Environment) -> Result<(), String> {
    let name = Name::from_string(MIRSEM_REM_BY_ZERO);
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // rem_by_zero : Int → Prop
    let ty = Expr::pi(bd(), int_ty(), Expr::prop());
    // Inside `λ(b:Int). …` : b = bvar(0).
    let b_ref = Expr::bvar(0);
    // @Eq Int b (Int.ofNat 0)   :  Prop  (the SAME closed body as div_by_zero).
    let body = div_by_zero_body(&b_ref);
    let val = Expr::lam(bd(), int_ty(), body);
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(rem_by_zero): {e:?}"))?;
    Ok(())
}

/// The Lemma-9 *theorem statement* — the remainder-by-zero-VC adequacy:
///
/// ```text
/// ∀ (b : Int), <reflected rem-by-zero VC> = rem_by_zero b      (in Prop)
/// ```
///
/// i.e. `@Eq Prop (@Eq Int b (Int.ofNat 0)) (rem_by_zero b)`, universally over the
/// divisor Int. `claimed_rhs = Some` swaps the spec for the fail-closed test.
pub(super) fn rem_adequacy_statement(claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Inside `∀(b:Int), …` : b = bvar(0).
    let b_ref = Expr::bvar(0);
    let lhs = div_by_zero_body(&b_ref);
    let rhs =
        claimed_rhs.cloned().unwrap_or_else(|| Expr::app(cst(MIRSEM_REM_BY_ZERO), b_ref.clone()));
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [Expr::prop(), lhs, rhs]);
    Expr::pi(bd(), int_ty(), body)
}

/// The Lemma-9 *proof term* — reflexivity. `rem_by_zero b` δ-reduces (unfolding the
/// reducible definition) to `@Eq Int b (Int.ofNat 0)`, which is LITERALLY the reflected
/// rem-by-zero VC, so the two `Prop` terms are def-eq and the witness is
/// `λ(b:Int). @Eq.refl Prop <reflected VC>`.
pub(super) fn rem_adequacy_proof() -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let b_ref = Expr::bvar(0);
    let lhs = div_by_zero_body(&b_ref);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [Expr::prop(), lhs]);
    Expr::lam(bd(), int_ty(), refl)
}

/// Check Lemma 9 (remainder-by-zero-VC adequacy) against the REAL clean-kernel:
/// register the MirSem + `rem_by_zero` anchor, build the statement
/// `∀ b. <reflected rem-by-zero VC> = rem_by_zero b` and the reflexivity proof,
/// `check_type` it, register it, and audit the axiom closure via `axiom_deps`.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term trust-vcgen+`ground_prop`
/// produce for the integer `BinaryOp(Rem)` divisor-zero obligation is EXACTLY the
/// pinned condition `b = 0` — kernel-verified modulo the 3 foundational axioms. So a
/// safety proof refuting that VC refutes EXACTLY the divisor-zero condition.
#[must_use]
pub fn check_rem_adequacy() -> AdequacyVerdict {
    check_rem_adequacy_inner(None)
}

/// Internal: `claimed_rhs = Some(e)` overrides the spec (the fail-closed path — a
/// `b = 1` instead of `b = 0` claim must fail to type-check).
pub(super) fn check_rem_adequacy_inner(claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    // `mirsem_safety_env` registers `rem_by_zero` (a reducible def) so the kernel can
    // δ-unfold it and see the RHS `rem_by_zero b` is def-eq to `@Eq Int b (Int.ofNat 0)`.
    let mut env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let statement = rem_adequacy_statement(claimed_rhs);
    let proof = rem_adequacy_proof();
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma9.rem_adequacy");
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

/// Pin the rem-by-zero anchor and audit its axiom closure: confirm the `rem_by_zero`
/// predicate AND its adequacy lemma rest on exactly the 3 foundational axioms (modulo
/// 3, no 4th axiom). Mirrors `pin_bounds_div_anchor` for the remainder fragment.
#[must_use]
pub fn pin_rem_anchor() -> AnchorVerdict {
    let env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    match env.axiom_deps(&Name::from_string(MIRSEM_REM_BY_ZERO)) {
        Some(residue) if residue.is_empty() => {}
        Some(residue) => {
            let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
            names.sort();
            return AnchorVerdict::Residue(names);
        }
        None => {
            return AnchorVerdict::KernelRejected(format!("decl not found: {MIRSEM_REM_BY_ZERO}"));
        }
    }
    match check_rem_adequacy() {
        AdequacyVerdict::ProvenModulo3 => AnchorVerdict::Modulo3,
        AdequacyVerdict::Residue(names) => AnchorVerdict::Residue(names),
        AdequacyVerdict::KernelRejected(e) => AnchorVerdict::KernelRejected(e),
    }
}

/// THE LEMMA-9 / SAFETY-VC PIPELINE HOOK. Return the kernel-checked rem-by-zero-VC
/// adequacy certificate — `Some` iff the rem VC's reflected formula is PROVEN (modulo
/// 3) def-eq to the divisor-zero condition. Fail-closed (`None`) if the adequacy proof
/// does not kernel-check modulo 3 — never a false certificate.
#[must_use]
pub fn rem_by_zero_adequacy_witness() -> Option<RemByZeroAdequacyCertificate> {
    match check_rem_adequacy() {
        AdequacyVerdict::ProvenModulo3 => {
            Some(RemByZeroAdequacyCertificate { verdict: AdequacyVerdict::ProvenModulo3 })
        }
        _ => None,
    }
}
