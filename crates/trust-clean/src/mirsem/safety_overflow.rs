// Unsigned addition and multiplication overflow: the reflected predicate, its
// registration in the safety environment, and the adequacy check tying it to
// the VC the compiler emits.

use super::*;

/// The canonical Clean name of the machine-overflow predicate
/// `Trust.MirSem.uadd_overflows`. Width-parameterized via the `w`-specific closed
/// threshold literal (one registered definition per modeled width).
pub(super) fn uadd_overflows_name(w: UWidth) -> String {
    format!("Trust.MirSem.uadd_overflows_u{}", w.bits())
}

/// The closed `Int` literal term for the overflow threshold `2^w − 1`, IDENTICAL
/// to what `int_lit_to_expr(type_max_formula(w,false))` produces in the grounder
/// (`Int.ofNat (2^w − 1)`).
pub(super) fn uadd_threshold_expr(w: UWidth) -> Expr {
    int_lit(w.max_value())
}

/// Register `Trust.MirSem.uadd_overflows_u{w} : Int → Int → Prop` (idempotent):
///
/// ```text
/// uadd_overflows_uW (a b : Int) : Prop := Int.lt (Int.ofNat (2^W − 1)) (Int.add a b)
/// ```
///
/// This IS the machine-overflow condition of the `u_W` wrapping-add overflow flag:
/// for in-range `0 ≤ a,b ≤ 2^W−1`, the sum overflows the width IFF
/// `a + b > 2^W − 1` (equivalently `a + b ≥ 2^W`). The body is built from the
/// prelude's reducible `Int.lt`/`Int.add`/`Int.ofNat` DEFINITIONS, so the decl's
/// transitive axiom closure is `⊆ {propext, Quot.sound, Classical.choice}`.
pub(super) fn register_uadd_overflows(env: &mut Environment, w: UWidth) -> Result<(), String> {
    let name = Name::from_string(&uadd_overflows_name(w));
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // uadd_overflows_uW : Int → Int → Prop
    let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::prop()));
    // Inside `λ(a:Int). λ(b:Int). …` : b = bvar(0), a = bvar(1).
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    // Int.add a b
    let sum = Expr::apps(cst("Int.add"), [a_ref, b_ref]);
    // Int.lt (Int.ofNat (2^w − 1)) (Int.add a b)   :  Prop
    let body = Expr::apps(cst("Int.lt"), [uadd_threshold_expr(w), sum]);
    let val = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(uadd_overflows_u{}): {e:?}", w.bits()))?;
    Ok(())
}

/// The canonical Clean name of the machine-overflow predicate
/// `Trust.MirSem.umul_overflows` — the UNSIGNED-MUL twin of `uadd_overflows`.
/// Width-parameterized via the `w`-specific closed threshold literal (one
/// registered definition per modeled width).
pub(super) fn umul_overflows_name(w: UWidth) -> String {
    format!("Trust.MirSem.umul_overflows_u{}", w.bits())
}

/// The GROUNDED REFLECTION of the unsigned-MUL OVERFLOW disjunct `Gt(a*b, MAX)`,
/// under an env binding `a`,`b` to the de-Bruijn `a_ref`,`b_ref` — the EXACT term
/// `clean_ground::ground_prop` produces for that `Formula`:
///
/// ```text
/// ground_prop(Gt(Mul(Var a, Var b), Int(2^w−1)))
///   = Int.lt (ground_int (Int 2^w−1)) (ground_int (Mul (Var a) (Var b)))
///   = Int.lt (Int.ofNat (2^w−1)) (Int.mul a b)
/// ```
///
/// (`Gt(x,y)` grounds with the arguments SWAPPED: `Int.lt (g y) (g x)`; and
/// `ground_int (Mul a b) = Int.mul a b`.) This is the term the unsigned-MUL
/// adequacy claims is def-eq to `umul_overflows_uW a b`. IDENTICAL in shape to
/// [`reflected_overflow_disjunct`] except the computed result head is `Int.mul`
/// instead of `Int.add`.
pub(super) fn reflected_umul_overflow_disjunct(a_ref: &Expr, b_ref: &Expr, w: UWidth) -> Expr {
    let prod = Expr::apps(cst("Int.mul"), [a_ref.clone(), b_ref.clone()]);
    Expr::apps(cst("Int.lt"), [uadd_threshold_expr(w), prod])
}

/// Register `Trust.MirSem.umul_overflows_u{w} : Int → Int → Prop` (idempotent):
///
/// ```text
/// umul_overflows_uW (a b : Int) : Prop := Int.lt (Int.ofNat (2^W − 1)) (Int.mul a b)
/// ```
///
/// This IS the machine-overflow condition of the `u_W` wrapping-MUL overflow flag:
/// for in-range `0 ≤ a,b ≤ 2^W−1`, the product overflows the width IFF
/// `a * b > 2^W − 1` (equivalently `a * b ≥ 2^W`). Byte-for-byte the `uadd`
/// predicate with `Int.mul` in place of `Int.add` — its body is built from the
/// prelude's reducible `Int.lt`/`Int.mul`/`Int.ofNat` DEFINITIONS, so the decl's
/// transitive axiom closure is `⊆ {propext, Quot.sound, Classical.choice}`.
///
/// NOTE — this predicate is the LIA spec for the CONSTANT-multiplier unsigned mul
/// emission (`flag * 32`, `x * 4`), which trust-vcgen routes to the Int/LIA path as
/// `Or([Lt(Mul(a,b),0), Gt(Mul(a,b),MAX)])`. A `var*var` unsigned mul is emitted as a
/// BITVECTOR formula (`And([a≠0, bvudiv(bvmul(a,b),a)≠b])`) with NO `Gt(Mul…)` leaf,
/// so it DECLINES at the formula-aware bridge (fail-closed) — the modeling here is
/// necessary-not-sufficient, exactly as signed MUL is.
pub(super) fn register_umul_overflows(env: &mut Environment, w: UWidth) -> Result<(), String> {
    let name = Name::from_string(&umul_overflows_name(w));
    if env.get_const(&name).is_some() {
        return Ok(());
    }
    let bd = || BinderData::from(BinderInfo::Default);
    // umul_overflows_uW : Int → Int → Prop
    let ty = Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), Expr::prop()));
    // Inside `λ(a:Int). λ(b:Int). …` : b = bvar(0), a = bvar(1).
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let body = reflected_umul_overflow_disjunct(&a_ref, &b_ref, w);
    let val = Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), body));
    env.add_decl(Declaration::Definition {
        name,
        level_params: vec![],
        type_: ty,
        value: val,
        is_reducible: true,
    })
    .map_err(|e| format!("add_decl(umul_overflows_u{}): {e:?}", w.bits()))?;
    Ok(())
}

/// The unsigned-MUL overflow-VC adequacy *theorem statement* (the `uadd` twin):
///
/// ```text
/// ∀ (a b : Int), <reflected umul overflow disjunct> = umul_overflows_uW a b   (in Prop)
/// ```
///
/// If `claimed_rhs` is `Some`, it REPLACES the spec on the RHS — used by the
/// fail-closed test to assert a WRONG threshold / `Int.add`-instead-of-`Int.mul`
/// head does NOT prove.
pub(super) fn umul_overflow_adequacy_statement(w: UWidth, claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let lhs = reflected_umul_overflow_disjunct(&a_ref, &b_ref, w);
    let rhs = claimed_rhs.cloned().unwrap_or_else(|| {
        Expr::apps(cst(&umul_overflows_name(w)), [a_ref.clone(), b_ref.clone()])
    });
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [Expr::prop(), lhs, rhs]);
    Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), body))
}

/// The unsigned-MUL overflow-VC adequacy *proof term* — reflexivity.
/// `umul_overflows_uW a b` δ/ι-reduces to `Int.lt (Int.ofNat (2^w−1)) (Int.mul a b)`,
/// which is LITERALLY the reflected overflow disjunct, so the two `Prop` terms are
/// def-eq and the witness is `λ(a b:Int). @Eq.refl Prop <reflected disjunct>`.
pub(super) fn umul_overflow_adequacy_proof(w: UWidth) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let lhs = reflected_umul_overflow_disjunct(&a_ref, &b_ref, w);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let refl = Expr::apps(eq_refl, [Expr::prop(), lhs]);
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), refl))
}

/// Check the unsigned-MUL overflow-VC adequacy for width `w` against the REAL
/// clean-kernel: register the MirSem + machine-overflow anchor, build the statement
/// `∀ a b. <reflected umul overflow disjunct> = umul_overflows_uW a b` and the
/// reflexivity proof, `check_type` it, register it, and audit the axiom closure.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term trust-vcgen+`ground_prop`
/// produce for the CONSTANT-multiplier unsigned `BinaryOp(Mul)` overflow obligation
/// is EXACTLY the pinned machine-overflow condition `(2^w − 1) < (a * b)` — so a
/// safety proof refuting that VC refutes EXACTLY the machine mul-overflow condition.
#[must_use]
pub fn check_umul_overflow_adequacy(w: UWidth) -> AdequacyVerdict {
    check_umul_overflow_adequacy_inner(w, None)
}

/// Internal: `claimed_rhs = Some(e)` overrides the spec (the fail-closed path — a
/// wrong threshold / `Int.add` head must make the reflexivity proof fail to type-check).
pub(super) fn check_umul_overflow_adequacy_inner(w: UWidth, claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    let mut env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let statement = umul_overflow_adequacy_statement(w, claimed_rhs);
    let proof = umul_overflow_adequacy_proof(w);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.LemmaUMul.overflow_adequacy");
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

/// Build a fresh kernel `Environment` with the prelude + the MirSem anchor + the
/// machine-overflow predicates for every modeled unsigned width. Extends
/// `mirsem_env` so the safety-VC adequacy lemma shares the one environment.
pub fn mirsem_safety_env() -> Result<Environment, String> {
    let mut env = mirsem_env()?;
    for w in [UWidth::W8, UWidth::W16, UWidth::W32, UWidth::W64] {
        register_uadd_overflows(&mut env, w)?;
        // Trust: the UNSIGNED-SUB UNDERFLOW (Lemma 8) machine-semantics predicates —
        // per unsigned width {u8,u16,u32,u64} — share this one safety env.
        register_usub_underflows(&mut env, w)?;
        // Trust: the UNSIGNED-MUL OVERFLOW machine-semantics predicates — per unsigned
        // width {u8,u16,u32,u64}. `umul_overflows_uW a b = (2^W−1) < a*b` is the LIA spec
        // for the CONSTANT-multiplier unsigned mul emission (`flag * 32`); a `var*var`
        // unsigned mul VC (a BV formula, no `Gt(Mul…)` leaf) declines at the
        // formula-aware bridge (fail-closed), exactly as signed MUL does.
        register_umul_overflows(&mut env, w)?;
    }
    // Trust: the bounds (Lemma 3), div-by-zero (Lemma 4), and REMAINDER-by-zero
    // (Lemma 9) machine-semantics predicates share this one safety environment,
    // alongside the overflow predicates.
    register_idx_oob(&mut env)?;
    register_div_by_zero(&mut env)?;
    register_rem_by_zero(&mut env)?;
    // Trust: the SIGNED-overflow (Lemma 5) machine-semantics predicates — per
    // (op ∈ {Add, Sub, Mul}, width ∈ {i8,i16,i32,i64}) — also share this one safety env.
    // Mul's predicate `smul_overflows_iW a b = (a*b<MIN ∨ a*b>MAX)` is the LIA spec for
    // the constant-multiplier mul emission; a `var*var` BV mul VC declines at the
    // formula-aware bridge (see `SignedOp`'s type-level note).
    for op in [SignedOp::Add, SignedOp::Sub, SignedOp::Mul] {
        for w in [SWidth::W8, SWidth::W16, SWidth::W32, SWidth::W64] {
            register_signed_overflows(&mut env, op, w)?;
        }
    }
    // Trust: the NEGATION-overflow (Lemma 6) machine-semantics predicates — per
    // width ∈ {i8,i16,i32,i64} — also share this one safety env.
    for w in [SWidth::W8, SWidth::W16, SWidth::W32, SWidth::W64] {
        register_neg_overflows(&mut env, w)?;
    }
    // Trust: the SHIFT-amount-OOB (Lemma 7) predicates — per shifted-value width ∈
    // {8,16,32,64,128} × amount-signedness. The shift widths INCLUDE 128
    // (`ShiftWidth`, not `SWidth`): the threshold is the width literal itself,
    // which stays a closed `Int.ofNat` at 128 (the "128-bit shift VC width"
    // residue closure).
    for w in ShiftWidth::ALL {
        register_shift_amount_oob(&mut env, w, false)?;
        register_shift_amount_oob(&mut env, w, true)?;
    }
    Ok(env)
}

/// The GROUNDED REFLECTION of the unsigned-add OVERFLOW disjunct `Gt(a+b, MAX)`,
/// under an env binding `a`,`b` to the de-Bruijn `a_ref`,`b_ref` — the EXACT term
/// `clean_ground::ground_prop` produces for that `Formula`:
///
/// ```text
/// ground_prop(Gt(Add(Var a, Var b), Int(2^w−1)))
///   = Int.lt (ground_int (Int 2^w−1)) (ground_int (Add (Var a) (Var b)))
///   = Int.lt (Int.ofNat (2^w−1)) (Int.add a b)
/// ```
///
/// (`Gt(x,y)` grounds with the arguments SWAPPED: `Int.lt (g y) (g x)`.) This is
/// the term Lemma 2 claims is def-eq to `uadd_overflows_uW a b`.
pub(super) fn reflected_overflow_disjunct(a_ref: &Expr, b_ref: &Expr, w: UWidth) -> Expr {
    let sum = Expr::apps(cst("Int.add"), [a_ref.clone(), b_ref.clone()]);
    Expr::apps(cst("Int.lt"), [uadd_threshold_expr(w), sum])
}

/// The grounded REFLECTION of the FULL emitted `out_of_range` disjunction for an
/// unsigned add — `Or([Lt(a+b, 0), Gt(a+b, MAX)])` — exactly as `ground_prop`
/// folds a two-element `Formula::Or` (`Or (ground p) (ground q)`):
///
/// ```text
/// Or (Int.lt (Int.add a b) (Int.ofNat 0)) (Int.lt (Int.ofNat (2^w−1)) (Int.add a b))
/// ```
///
/// The first disjunct is the underflow check (`a+b < 0`, unsatisfiable for
/// unsigned add); the second is the overflow disjunct above. Pinned so the modeled
/// VC matches the emitted formula's violation core byte-for-byte. (Exercised by the
/// `full_out_of_range_disjunction_is_a_well_typed_prop` test, which confirms the
/// whole emitted violation core is a well-typed Clean `Prop`.)
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn reflected_out_of_range(a_ref: &Expr, b_ref: &Expr, w: UWidth) -> Expr {
    let sum = || Expr::apps(cst("Int.add"), [a_ref.clone(), b_ref.clone()]);
    // Lt(a+b, 0) ↦ Int.lt (Int.add a b) (Int.ofNat 0)
    let underflow = Expr::apps(cst("Int.lt"), [sum(), int_lit(0)]);
    let overflow = reflected_overflow_disjunct(a_ref, b_ref, w);
    // Or p q   (ground_prop folds the 2-element Or as `Or (ground head) (ground tail)`)
    Expr::apps(cst("Or"), [underflow, overflow])
}

/// The Lemma-2 *theorem statement* — the unsigned-add overflow-VC adequacy:
///
/// ```text
/// ∀ (a b : Int), <reflected overflow disjunct> = uadd_overflows_uW a b      (in Prop)
/// ```
///
/// i.e. `@Eq Prop (Int.lt (Int.ofNat (2^w−1)) (Int.add a b)) (uadd_overflows_uW a b)`,
/// universally over the two operand Ints. If `claimed_rhs` is `Some`, it REPLACES
/// the spec on the RHS — used by the fail-closed test to assert a WRONG threshold /
/// width does NOT prove.
pub(super) fn overflow_adequacy_statement(w: UWidth, claimed_rhs: Option<&Expr>) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    // Inside `∀(a:Int).∀(b:Int), …` : b = bvar(0), a = bvar(1).
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let lhs = reflected_overflow_disjunct(&a_ref, &b_ref, w);
    let rhs = claimed_rhs.cloned().unwrap_or_else(|| {
        Expr::apps(cst(&uadd_overflows_name(w)), [a_ref.clone(), b_ref.clone()])
    });
    // @Eq.{1} Prop lhs rhs   (Prop : Sort 1, so Eq is at level 1).
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let body = Expr::apps(eq, [Expr::prop(), lhs, rhs]);
    Expr::pi(bd(), int_ty(), Expr::pi(bd(), int_ty(), body))
}

/// The Lemma-2 *proof term* — reflexivity. `uadd_overflows_uW a b` ι/δ-reduces
/// (unfolding the reducible definition) to `Int.lt (Int.ofNat (2^w−1)) (Int.add a b)`,
/// which is LITERALLY the reflected overflow disjunct, so the two `Prop` terms are
/// def-eq and the witness is `λ(a b:Int). @Eq.refl Prop <reflected disjunct>`.
pub(super) fn overflow_adequacy_proof(w: UWidth) -> Expr {
    let bd = || BinderData::from(BinderInfo::Default);
    let a_ref = Expr::bvar(1);
    let b_ref = Expr::bvar(0);
    let lhs = reflected_overflow_disjunct(&a_ref, &b_ref, w);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    // @Eq.refl Prop <reflected disjunct> : @Eq Prop lhs lhs ; def-eq makes it
    // inhabit @Eq Prop lhs (uadd_overflows_uW a b).
    let refl = Expr::apps(eq_refl, [Expr::prop(), lhs]);
    Expr::lam(bd(), int_ty(), Expr::lam(bd(), int_ty(), refl))
}

/// Check Lemma 2 (unsigned-add overflow-VC adequacy) for width `w` against the REAL
/// clean-kernel: register the MirSem + machine-overflow anchor, build the statement
/// `∀ a b. <reflected overflow disjunct> = uadd_overflows_uW a b` and the
/// reflexivity proof, `check_type` it, register it, and audit the axiom closure via
/// `axiom_deps`.
///
/// A [`AdequacyVerdict::ProvenModulo3`] means: the term trust-vcgen+`ground_prop`
/// produce for the unsigned `BinaryOp(Add)` overflow obligation is EXACTLY the pinned
/// machine-overflow condition `(2^w − 1) < (a + b)` — kernel-verified modulo the 3
/// foundational axioms. So a safety proof refuting that VC refutes EXACTLY the
/// machine-overflow condition: the discharge is FAITHFUL, not merely trusted.
#[must_use]
pub fn check_overflow_adequacy(w: UWidth) -> AdequacyVerdict {
    check_overflow_adequacy_inner(w, None)
}

/// Internal: `claimed_rhs = Some(e)` overrides the spec (the fail-closed path — a
/// wrong threshold / width must make the reflexivity proof fail to type-check).
pub(super) fn check_overflow_adequacy_inner(w: UWidth, claimed_rhs: Option<&Expr>) -> AdequacyVerdict {
    let mut env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AdequacyVerdict::KernelRejected(e),
    };
    let statement = overflow_adequacy_statement(w, claimed_rhs);
    let proof = overflow_adequacy_proof(w);
    {
        let tc = TypeChecker::new(&env);
        if let Err(e) = tc.check_type(&proof, &statement) {
            return AdequacyVerdict::KernelRejected(format!("check_type: {e:?}"));
        }
    }
    let name = Name::from_string("Trust.MirSem.Lemma2.overflow_adequacy");
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

/// Pin the machine-overflow anchor and audit its axiom closure: confirm BOTH the
/// per-width `uadd_overflows` predicates AND the overflow-adequacy lemma (w=32, the
/// canonical `u32` case) rest on exactly the 3 foundational axioms (modulo 3, no
/// 4th axiom). Mirrors `pin_mirsem_anchor` for the safety-VC fragment.
#[must_use]
pub fn pin_overflow_anchor() -> AnchorVerdict {
    let env = match mirsem_safety_env() {
        Ok(e) => e,
        Err(e) => return AnchorVerdict::KernelRejected(e),
    };
    for w in [UWidth::W8, UWidth::W16, UWidth::W32, UWidth::W64] {
        match env.axiom_deps(&Name::from_string(&uadd_overflows_name(w))) {
            Some(residue) if residue.is_empty() => {}
            Some(residue) => {
                let mut names: Vec<String> = residue.iter().map(ToString::to_string).collect();
                names.sort();
                return AnchorVerdict::Residue(names);
            }
            None => return AnchorVerdict::KernelRejected(format!("decl not found: u{}", w.bits())),
        }
    }
    AnchorVerdict::Modulo3
}

/// THE LEMMA-2 / SAFETY-VC PIPELINE HOOK. For a modeled unsigned width, return the
/// kernel-checked overflow-VC adequacy certificate — `Some` iff the overflow VC's
/// reflected formula is PROVEN (modulo 3) def-eq to the machine-overflow condition.
/// Fail-closed (`None`) for a width whose adequacy proof does not kernel-check
/// modulo 3 — never a false certificate.
#[must_use]
pub fn overflow_adequacy_witness(w: UWidth) -> Option<OverflowAdequacyCertificate> {
    match check_overflow_adequacy(w) {
        AdequacyVerdict::ProvenModulo3 => {
            Some(OverflowAdequacyCertificate { width: w, verdict: AdequacyVerdict::ProvenModulo3 })
        }
        _ => None,
    }
}

/// Collect the modeled unsigned-add OVERFLOW widths a function's body raises — one
/// per `Rvalue::BinaryOp(Add, …)` / `CheckedBinaryOp(Add, …)` whose result local is
/// an unsigned `u8`/`u16`/`u32`/`u64` (the width whose `ArithmeticOverflow` VC
/// `trust-vcgen` emits over Int). The width is the assigned local's integer type —
/// the type the overflow check is against. A signed add, an unmodeled width
/// (`u128`), or a non-Add binop contributes nothing (out of this fragment).
pub(super) fn function_uadd_overflow_widths(func: &trust_types::VerifiableFunction) -> Vec<UWidth> {
    use trust_types::{BinOp, Rvalue, Statement, Ty};
    let body = &func.body;
    let mut widths: Vec<UWidth> = Vec::new();
    for block in &body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                let is_add = matches!(
                    rvalue,
                    Rvalue::BinaryOp(BinOp::Add, _, _) | Rvalue::CheckedBinaryOp(BinOp::Add, _, _)
                );
                if !is_add || !place.projections.is_empty() {
                    continue;
                }
                // The overflow check is against the assigned local's integer type.
                if let Some(local) = body.locals.get(place.local) {
                    if let Ty::Int { width, signed } = &local.ty {
                        if let Some(w) = UWidth::from_mir(*width, *signed) {
                            if !widths.contains(&w) {
                                widths.push(w);
                            }
                        }
                    }
                }
            }
        }
    }
    widths
}

/// THE SAFETY-VC-FAITHFULNESS HOOK (Goal #4, `safety_vc_faithful` tier). For a
/// reflected function, mint per-width overflow-VC adequacy certificates iff the
/// function raises at least one modeled unsigned-add overflow obligation AND EVERY
/// such width's reflected overflow VC is PROVEN (modulo 3) def-eq to the pinned
/// machine-overflow condition (`uadd_overflows_uW`). Fail-closed: a function with
/// NO modeled unsigned-add overflow VC — or any width whose adequacy proof does not
/// kernel-check modulo 3 — yields `None`, never a false witness.
///
/// A `Some` result means: when the §6 pipeline discharges this function's overflow
/// safety VCs, it is refuting EXACTLY the machine-overflow condition — the safety
/// discharge is kernel-certified FAITHFUL, not merely a reflected formula we trust.
#[must_use]
pub fn function_safety_vc_faithful(
    func: &trust_types::VerifiableFunction,
) -> Option<Vec<OverflowAdequacyCertificate>> {
    let widths = function_uadd_overflow_widths(func);
    if widths.is_empty() {
        return None; // no modeled overflow obligation ⇒ not in the fragment
    }
    let mut certs = Vec::with_capacity(widths.len());
    for w in widths {
        certs.push(overflow_adequacy_witness(w)?); // fail-closed on any uncertified width
    }
    Some(certs)
}
