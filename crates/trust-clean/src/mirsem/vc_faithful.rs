// Deciding whether a safety VC the compiler emitted is faithfully modeled
// here. A VC kind with no modeled counterpart must be reported unmodeled: this
// is the gate that stops a whole-function faithfulness claim from covering an
// obligation nothing checked.

use super::*;

/// Build the de-Bruijn grounding map for a list of operand variable names, assigning
/// `names[0] = bvar(n-1)`, …, `names[n-1] = bvar(0)` — the convention `ground_prop`
/// expects (a leading binder is the OUTERMOST, highest index). A non-`Var` operand
/// (a constant, a struct field, …) is NOT mappable here ⇒ `None` (fail closed).
pub(super) fn debruijn_params(names: &[&str]) -> std::collections::HashMap<String, Expr> {
    let n = names.len();
    let mut m = std::collections::HashMap::new();
    for (i, name) in names.iter().enumerate() {
        m.insert((*name).to_string(), Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    }
    m
}

/// The variable name of an integer `Formula::Var` leaf (the only operand shape the
/// formula-aware grounder maps to a de-Bruijn binder). A constant / arithmetic /
/// field-projection operand returns `None` ⇒ the VC is outside the formula-aware
/// fragment and the function fails closed.
pub(super) fn formula_var_name(f: &trust_types::Formula) -> Option<&str> {
    match f {
        trust_types::Formula::Var(n, _) => Some(n.as_str()),
        _ => None,
    }
}

/// Search a VC `Formula` tree for the FIRST leaf matching `pred`, descending through
/// `And`/`Or`/`Not`/`Implies` (the connective structure block-defs + range bounds +
/// the violation disjunction are built from). Returns the matched sub-formula.
pub(super) fn find_violation_leaf<'a>(
    f: &'a trust_types::Formula,
    pred: &dyn Fn(&trust_types::Formula) -> bool,
) -> Option<&'a trust_types::Formula> {
    use trust_types::Formula as F;
    if pred(f) {
        return Some(f);
    }
    match f {
        F::And(v) | F::Or(v) => v.iter().find_map(|x| find_violation_leaf(x, pred)),
        F::Not(a) => find_violation_leaf(a, pred),
        F::Implies(a, b) => find_violation_leaf(a, pred).or_else(|| find_violation_leaf(b, pred)),
        _ => None,
    }
}

/// Like [`find_violation_leaf`] but ALSO descends into the children of an `Eq` whose
/// predicate does not itself match. This reaches a violation core that the emitter
/// buries inside a GUARD-BINDING equality `Eq(Var aux, <core>)` — e.g. abs's
/// negation-overflow VC, where the precondition wraps the genuine core `Eq(x, MIN)`
/// as the RHS of `Eq(_6, Eq(x, MIN))` (the `_6 := (x == MIN)` SSA binding). The plain
/// `find_violation_leaf` stops at `Eq` (so the unwrapped `neg` function's bare core is
/// still found by it), but a precondition-guarded `abs` needs the deeper descent. Used
/// ONLY by the NEGATION-overflow certifier; the predicate it is given (`Eq(Var, Int)`)
/// cannot match a guard-binding equality (whose RHS is a comparison, not an `Int`), so
/// descending through `Eq` never produces a false core.
pub(super) fn find_violation_leaf_through_eq<'a>(
    f: &'a trust_types::Formula,
    pred: &dyn Fn(&trust_types::Formula) -> bool,
) -> Option<&'a trust_types::Formula> {
    use trust_types::Formula as F;
    if pred(f) {
        return Some(f);
    }
    match f {
        F::And(v) | F::Or(v) => v.iter().find_map(|x| find_violation_leaf_through_eq(x, pred)),
        F::Not(a) => find_violation_leaf_through_eq(a, pred),
        F::Implies(a, b) => find_violation_leaf_through_eq(a, pred)
            .or_else(|| find_violation_leaf_through_eq(b, pred)),
        F::Eq(a, b) => find_violation_leaf_through_eq(a, pred)
            .or_else(|| find_violation_leaf_through_eq(b, pred)),
        _ => None,
    }
}

/// Kernel-check that the LIVE grounding of `cg.core` (via `clean_ground::ground_prop`)
/// is def-eq, modulo the 3 foundational axioms, to the spec term `spec` (already built
/// over the SAME de-Bruijn refs). This is the bridge check: it certifies the term the
/// reflection pipeline ACTUALLY grounds equals the pinned machine-semantics condition,
/// not a hand-built shape. Returns `true` ONLY on a real modulo-3 kernel def-eq.
pub(super) fn live_ground_def_eq_spec(cg: &CoreGround<'_>, spec: &Expr, binder_count: usize) -> bool {
    let Ok(mut env) = mirsem_safety_env() else {
        return false;
    };
    let Some(grounded) = crate::clean_ground::ground_prop(cg.core, &cg.params) else {
        return false; // the live grounder declined this core ⇒ no cert (fail closed)
    };
    // Kernel-register `theorem … : @Eq Prop grounded spec := Eq.refl Prop grounded`,
    // under `binder_count` Int binders (the operands). It type-checks IFF `grounded`
    // and `spec` are def-eq; then audit the axiom closure ⊆ the 3 axioms.
    let bd = || BinderData::from(BinderInfo::Default);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut statement = Expr::apps(eq, [Expr::prop(), grounded.clone(), spec.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut proof = Expr::apps(eq_refl, [Expr::prop(), grounded]);
    for _ in 0..binder_count {
        statement = Expr::pi(bd(), int_ty(), statement);
        proof = Expr::lam(bd(), int_ty(), proof);
    }
    {
        let tc = TypeChecker::new(&env);
        if tc.check_type(&proof, &statement).is_err() {
            return false; // NOT def-eq ⇒ the emitted core is not the spec ⇒ fail closed
        }
    }
    let name = Name::from_string("Trust.MirSem.FormulaAware.bridge");
    if env
        .add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        })
        .is_err()
    {
        return false;
    }
    matches!(env.axiom_deps(&name), Some(residue) if residue.is_empty())
}

/// Whether an integer operand `Formula` is in the formula-aware fragment — a bare
/// `Var` (mapped to a de-Bruijn binder) OR an integer CONSTANT `Int(k)` (grounded
/// directly to a closed literal by the live `ground_int`, no binder). These are the
/// operand shapes `x + y`, `x + 1`, `1 + x` produce; a nested arithmetic / field /
/// pointer operand is OUTSIDE the fragment ⇒ the caller fails closed.
pub(super) fn operand_in_fragment(t: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    matches!(t, F::Var(_, _) | F::Int(_) | F::UInt(_))
}

/// The two operand `Formula`s of a computed binary sub-term `Add(a,b)` / `Sub(a,b)`,
/// in order — the OVERFLOW-family violation cores carry the operands inside this
/// computed result, not as bare comparison leaves. Each operand may be a `Var` OR an
/// integer constant (`x + 1`); a nested-arithmetic / field operand is OUT of the
/// fragment ⇒ `None` (fail closed).
pub(super) fn binop_operands(
    t: &trust_types::Formula,
) -> Option<(&trust_types::Formula, &trust_types::Formula)> {
    use trust_types::Formula as F;
    match t {
        // `Mul` is included so the formula-aware signed-overflow bridge can extract the
        // operands of a CONSTANT-multiplier mul's LIA `Or([Lt(Mul…),Gt(Mul…)])` core
        // (`ground_int` grounds `F::Mul` to `Int.mul`). A `var*var` mul is NOT emitted as
        // an `F::Mul`-cored disjunction (it is a BV formula), so this never spuriously
        // matches the deferred BV shape.
        F::Add(a, b) | F::Sub(a, b) | F::Mul(a, b)
            if operand_in_fragment(a) && operand_in_fragment(b) =>
        {
            Some((a, b))
        }
        _ => None,
    }
}

/// The distinct `Var` operand names of a list of operand `Formula`s, in first-
/// appearance order (a constant operand contributes no name — it grounds to a closed
/// literal, not a binder).
pub(super) fn distinct_var_names<'a>(operands: &[&'a trust_types::Formula]) -> Vec<&'a str> {
    let mut names: Vec<&str> = Vec::new();
    for op in operands {
        if let Some(n) = formula_var_name(op) {
            if !names.contains(&n) {
                names.push(n);
            }
        }
    }
    names
}

/// FORMULA-AWARE bridge for an OVERFLOW-family core whose operands appear inside a
/// COMPUTED `Add`/`Sub`/`Eq` sub-term (Lemma 2/5/6/8). Ground the EMITTED `core`
/// through the LIVE `clean_ground::ground_prop` and kernel-check it `is_def_eq`
/// (modulo 3) to `spec(g a, g b)` — where `g a`/`g b` are the operands grounded
/// through the SAME LIVE `ground_int` (a `Var` → its de-Bruijn binder; an integer
/// CONSTANT → its closed literal, NO binder), so the spec is built over the exact
/// operand terms the grounder produces (handling repeated operands `x + x` AND mixed
/// const operands `x + 1` uniformly). `spec_of(&[g_op])` builds the registered
/// per-kind predicate applied to those grounded operands. Returns `true` ONLY on a
/// genuine modulo-3 kernel def-eq; the live grounder declining the core/operand, or a
/// spec/grounder shape mismatch, fails closed.
pub(super) fn overflow_family_live_def_eq(
    core: &trust_types::Formula,
    operands: &[&trust_types::Formula],
    spec_of: &dyn Fn(&[Expr]) -> Expr,
) -> bool {
    // Distinct `Var` operand names → de-Bruijn binders (constants carry no binder).
    let distinct = distinct_var_names(operands);
    let params = debruijn_params(&distinct);
    // Ground each operand POSITION through the SAME live `ground_int`, so the spec is
    // applied to the exact de-Bruijn / literal terms the grounder emits.
    let mut grounded_ops: Vec<Expr> = Vec::with_capacity(operands.len());
    for op in operands {
        match crate::clean_ground::ground_int(op, &params) {
            Some(e) => grounded_ops.push(e),
            None => return false, // the live grounder declined this operand ⇒ fail closed
        }
    }
    let spec = spec_of(&grounded_ops);
    let cg = CoreGround { core, params };
    live_ground_def_eq_spec(&cg, &spec, distinct.len())
}

/// FORMULA-AWARE faithfulness for ONE safety VC: ground the ACTUAL emitted violation
/// core through the LIVE grounder and kernel-check it def-eq to the spec for THAT VC,
/// recovering the width/threshold FROM THE EMITTED FORMULA. Returns the modeled
/// `(kind, AdequacyVerdict)` ONLY when the bridge def-eq holds modulo 3; `None` (fail
/// closed) when the core is outside the formula-aware fragment OR the emitted threshold
/// does not match any modeled spec (e.g. the `1i32<<n` desync — emitted `32 ≤ n`, no
/// def-eq to a 64-width spec).
pub(super) fn safety_vc_is_faithful_formula_aware(
    vc: &trust_types::VerificationCondition,
) -> Option<(SafetyVcKind, AdequacyVerdict)> {
    use trust_types::{Formula as F, VcKind as K};
    match &vc.kind {
        // BOUNDS (Lemma 3): the emitted core is `Ge(i, len)`. The INDEX is always a
        // variable; the LENGTH is a variable (a SLICE — `Var len`) OR a constant (a
        // FIXED ARRAY — `Int N`). Live-ground the WHOLE core → `Int.le (g len) (g i)`
        // and build the spec `idx_oob (g len) (g i)` over the SAME grounded operands, so
        // the array (`idx_oob (Int.ofNat N) i`) and slice (`idx_oob len i`) cases BOTH
        // certify by the same def-eq. The index binds at bvar 0; a length VARIABLE binds
        // at bvar 1 (so the proof carries 2 binders), a length CONSTANT carries no binder
        // (1 binder — just the index).
        K::IndexOutOfBounds | K::SliceBoundsCheck => {
            let leaf = find_violation_leaf(&vc.formula, &|f| {
                matches!(f, F::Ge(a, b)
                    if formula_var_name(a).is_some()
                        && (formula_var_name(b).is_some() || matches!(&**b, F::Int(_))))
            })?;
            let F::Ge(i_f, len_f) = leaf else { return None };
            let i_name = formula_var_name(i_f)?;
            // Bind the index at bvar 0; the length VARIABLE (if any) at bvar 1.
            let (params, binder_count, len_expr) = match formula_var_name(len_f) {
                Some(len_name) => {
                    let mut m = std::collections::HashMap::new();
                    m.insert(len_name.to_string(), Expr::bvar(1));
                    m.insert(i_name.to_string(), Expr::bvar(0));
                    (m, 2usize, Expr::bvar(1))
                }
                None => {
                    let F::Int(n) = &**len_f else { return None };
                    let mut m = std::collections::HashMap::new();
                    m.insert(i_name.to_string(), Expr::bvar(0));
                    (m, 1usize, int_lit(*n))
                }
            };
            let cg = CoreGround { core: leaf, params };
            // spec `idx_oob (g len) i` over the SAME grounded length term + index bvar.
            let spec = Expr::apps(cst(MIRSEM_IDX_OOB), [len_expr, Expr::bvar(0)]);
            live_ground_def_eq_spec(&cg, &spec, binder_count)
                .then_some((SafetyVcKind::Bounds, AdequacyVerdict::ProvenModulo3))
        }
        // DIV / REM by zero (Lemma 4/9): the emitted core is `Eq(b, 0)` (divisor zero).
        // Live-ground → `@Eq Int b (Int.ofNat 0)`; spec `div_by_zero b` / `rem_by_zero b`.
        K::DivisionByZero | K::RemainderByZero => {
            let leaf = find_violation_leaf(
                &vc.formula,
                &|f| matches!(f, F::Eq(a, b) if formula_var_name(a).is_some() && matches!(&**b, F::Int(0))),
            )?;
            let F::Eq(b_f, _) = leaf else { return None };
            let b_name = formula_var_name(b_f)?;
            let params = debruijn_params(&[b_name]);
            let cg = CoreGround { core: leaf, params };
            let (spec_name, kind) = if matches!(vc.kind, K::DivisionByZero) {
                (MIRSEM_DIV_BY_ZERO, SafetyVcKind::DivByZero)
            } else {
                (MIRSEM_REM_BY_ZERO, SafetyVcKind::RemByZero)
            };
            let spec = Expr::app(cst(spec_name), Expr::bvar(0));
            live_ground_def_eq_spec(&cg, &spec, 1).then_some((kind, AdequacyVerdict::ProvenModulo3))
        }
        // SHIFT-amount OOB (Lemma 7): the emitted core is `Ge(n, Int(W))` (unsigned
        // amount) — W is the EMITTED threshold, read from the formula (NOT operand_ty,
        // which fabricates i64 for a const shifted value). Live-ground → `Int.le W n`;
        // spec `shift_amount_oob_W n`. The width is whatever the formula actually says,
        // so the `1i32<<n` emitted `32 ≤ n` certifies at W32 and NEVER mints a 64-cert.
        // A signed shift amount adds the `Lt(n,0)` disjunct (the `Or` core).
        K::ShiftOverflow { shift_ty, .. } => {
            let amount_signed = matches!(shift_ty, trust_types::Ty::Int { signed: true, .. });
            // Locate the emitted threshold `Ge(n, Int(W))` and the shift amount `n` —
            // a VARIABLE (the original Lemma-7 shape), or — Trust: M6 rung 6 — a
            // CLOSED LITERAL (`x >> 44`'s emitted `Ge(Int(44), Int(64))`, the
            // `ExprMeta::loose_bvar_range`-class constant shift: the core is a
            // CLOSED Prop, its reflection is `Int.le (ofNat W) (ofNat k)`, and the
            // spec is `shift_amount_oob_W k` applied at the literal — the SAME
            // def-eq bridge, zero binders). UNSIGNED amounts only for the literal
            // arm (a signed literal amount would need the `Or` core located at a
            // literal too — not observed in real MIR, fail-closed).
            let ge = find_violation_leaf(&vc.formula, &|f| {
                matches!(f, F::Ge(a, b)
                    if (formula_var_name(a).is_some() || matches!(&**a, F::Int(_)))
                        && matches!(&**b, F::Int(_)))
            })?;
            let F::Ge(n_f, w_f) = ge else { return None };
            let F::Int(threshold) = &**w_f else { return None };
            // The EMITTED threshold W must be a modeled shift-width literal
            // (`8/16/32/64/128` — the 128-bit value widths ARE in this lane's set).
            let w = ShiftWidth::from_bits(u32::try_from(*threshold).ok()?)?;
            // Trust: M6 rung 6 — the CLOSED-LITERAL amount arm (unsigned only).
            if let F::Int(k) = &**n_f {
                if amount_signed {
                    return None; // literal-amount signed shift — outside the arm.
                }
                let cg = CoreGround { core: ge, params: std::collections::HashMap::new() };
                let spec = Expr::app(cst(&shift_amount_oob_name(w, amount_signed)), int_lit(*k));
                return live_ground_def_eq_spec(&cg, &spec, 0).then_some((
                    SafetyVcKind::ShiftOob(w, amount_signed),
                    AdequacyVerdict::ProvenModulo3,
                ));
            }
            let n_name = formula_var_name(n_f)?;
            let params = debruijn_params(&[n_name]);
            // The core to ground is the unsigned `Ge(n,W)` or the full signed `Or`.
            let core: &F = if amount_signed {
                // Find the `Or([Lt(n,0), Ge(n,W)])` enclosing the threshold disjunct.
                find_violation_leaf(&vc.formula, &|f| {
                    match f {
                    F::Or(v) => v.iter().any(|x| matches!(x, F::Lt(a, b)
                        if formula_var_name(a) == Some(n_name) && matches!(&**b, F::Int(0))))
                        && v.iter().any(|x| matches!(x, F::Ge(a, b)
                        if formula_var_name(a) == Some(n_name) && matches!(&**b, F::Int(t) if *t == *threshold))),
                    _ => false,
                }
                })?
            } else {
                ge
            };
            let cg = CoreGround { core, params };
            let spec = Expr::app(cst(&shift_amount_oob_name(w, amount_signed)), Expr::bvar(0));
            live_ground_def_eq_spec(&cg, &spec, 1).then_some((
                SafetyVcKind::ShiftOob(w, amount_signed),
                AdequacyVerdict::ProvenModulo3,
            ))
        }
        // ARITHMETIC OVERFLOW / UNDERFLOW (Lemma 2/5/8). The violation core carries a
        // COMPUTED `Add(a,b)`/`Sub(a,b)` sub-term (not bare comparison Vars). We
        // discriminate the three modeled shapes by the EMITTED formula itself —
        // operand signedness from the VC's `operand_tys` only selects WHICH shape to
        // look for; the threshold (hence the certified width) is read FROM THE FORMULA.
        K::ArithmeticOverflow { op, operand_tys: (a_ty, b_ty) } => {
            use trust_types::{BinOp, Ty};
            let (Ty::Int { signed: sa, .. }, Ty::Int { signed: sb, .. }) = (a_ty, b_ty) else {
                return None;
            };
            match op {
                // UNSIGNED-ADD OVERFLOW (Lemma 2): the load-bearing disjunct is
                // `Gt(Add(a,b), Int(MAX))` (MAX = 2^w−1) inside the emitted 2-element
                // `Or`. Read MAX from the formula → the modeled UWidth; ground the
                // overflow disjunct live and check def-eq to `uadd_overflows_uW (g a) (g b)`.
                BinOp::Add if !sa && !sb => {
                    let leaf = find_violation_leaf(&vc.formula, &|f| match f {
                        F::Gt(lhs, rhs) => {
                            binop_operands(lhs).is_some() && matches!(&**rhs, F::Int(_))
                        }
                        _ => false,
                    })?;
                    let F::Gt(add_t, max_f) = leaf else { return None };
                    let (a_op, b_op) = binop_operands(add_t)?;
                    let F::Int(max) = &**max_f else { return None };
                    let w = UWidth::from_mir(width_of_unsigned_max(*max)?, false)?;
                    let name = uadd_overflows_name(w);
                    let ok = overflow_family_live_def_eq(leaf, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((SafetyVcKind::Overflow(w), AdequacyVerdict::ProvenModulo3))
                }
                // SIGNED ADD/SUB/MUL OVERFLOW (Lemma 5): the full out-of-range `Or([Lt(a∘b,
                // MIN), Gt(a∘b, MAX)])`. Read MIN+MAX from the formula → the modeled
                // SWidth (and confirm they agree); ground the whole `Or` live and check
                // def-eq to `s<op>_overflows_iW (g a) (g b)`.
                //
                // MUL is included ADDITIVELY: a CONSTANT-multiplier signed mul (`x * 4`)
                // is emitted by trust-vcgen on the LIA Int-path as the SAME
                // `Or([Lt(Mul(a,b),MIN), Gt(Mul(a,b),MAX)])` disjunction, so it certifies
                // by the identical reflexivity (the spec body just heads `Int.mul`). A
                // `var*var` signed mul is emitted as a BITVECTOR formula instead, which has
                // NO such `Or([Lt(Mul…),Gt(Mul…)])` leaf — `find_violation_leaf` returns
                // `None` below ⇒ this arm declines ⇒ the deferred BV mul fails closed (no
                // false cert; the `mul_*`/`sq_nonneg` corpus stays HONESTLY not-faithful).
                BinOp::Add | BinOp::Sub | BinOp::Mul if *sa && *sb => {
                    let sop = match op {
                        BinOp::Add => SignedOp::Add,
                        BinOp::Sub => SignedOp::Sub,
                        _ => SignedOp::Mul,
                    };
                    let or = find_violation_leaf(&vc.formula, &|f| match f {
                        F::Or(v) if v.len() == 2 => {
                            let lt_min = matches!(&v[0], F::Lt(l, r)
                                if binop_operands(l).is_some() && matches!(&**r, F::Int(_)));
                            let gt_max = matches!(&v[1], F::Gt(l, r)
                                if binop_operands(l).is_some() && matches!(&**r, F::Int(_)));
                            lt_min && gt_max
                        }
                        _ => false,
                    })?;
                    let F::Or(v) = or else { return None };
                    let (F::Lt(under_t, min_f), F::Gt(over_t, max_f)) = (&v[0], &v[1]) else {
                        return None;
                    };
                    // Both disjuncts must reference the SAME computed `a∘b` operands.
                    let (a_op, b_op) = binop_operands(under_t)?;
                    if binop_operands(over_t)? != (a_op, b_op) {
                        return None;
                    }
                    let (F::Int(min), F::Int(max)) = (&**min_f, &**max_f) else { return None };
                    let w = swidth_of_signed_bounds(*min, *max)?;
                    let name = signed_overflows_name(sop, w);
                    let ok = overflow_family_live_def_eq(or, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((
                        SafetyVcKind::SignedOverflow(sop, w),
                        AdequacyVerdict::ProvenModulo3,
                    ))
                }
                // UNSIGNED-SUB UNDERFLOW (Lemma 8): the single core `Lt(Sub(a,b),
                // Int(0))`. The underflow bound is `0` at EVERY width (the threshold
                // carries no width), and the spec body is width-invariant — so we ground
                // the live core and check def-eq to `usub_underflows_uW (g a) (g b)` for
                // the operand width the VC carries (sound: the def-eq holds at every
                // modeled width; the width only names the per-kind tally bucket).
                BinOp::Sub if !sa && !sb => {
                    let w = usub_underflow_vc_modeled(&vc.kind)?;
                    let leaf = find_violation_leaf(&vc.formula, &|f| match f {
                        F::Lt(lhs, rhs) => {
                            matches!(&**lhs, F::Sub(_, _))
                                && binop_operands(lhs).is_some()
                                && matches!(&**rhs, F::Int(0))
                        }
                        _ => false,
                    })?;
                    let F::Lt(sub_t, _) = leaf else { return None };
                    let (a_op, b_op) = binop_operands(sub_t)?;
                    let name = usub_underflows_name(w);
                    let ok = overflow_family_live_def_eq(leaf, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((
                        SafetyVcKind::UnsignedSubUnderflow(w),
                        AdequacyVerdict::ProvenModulo3,
                    ))
                }
                // UNSIGNED-MUL OVERFLOW: the load-bearing disjunct is
                // `Gt(Mul(a,b), Int(MAX))` (MAX = 2^w−1) inside the emitted 2-element
                // `Or([Lt(Mul(a,b),0), Gt(Mul(a,b),MAX)])`. This is EXACTLY the
                // unsigned-ADD shape with `Mul` in place of `Add` — read MAX from the
                // formula → the modeled UWidth; ground the overflow disjunct live and
                // check def-eq to `umul_overflows_uW (g a) (g b)`.
                //
                // MUL is here for the CONSTANT-multiplier LIA emission only: trust-vcgen
                // routes `flag * 32` / `x * 4` (a constant operand, no widening cast) to
                // the Int path where `ground_int` grounds `F::Mul` to `Int.mul`. A
                // `var*var` unsigned mul is emitted as a BITVECTOR formula
                // (`And([a≠0, bvudiv(bvmul(a,b),a)≠b])`) — it carries NO `Gt(Mul…)` leaf,
                // so `find_violation_leaf` returns `None` below ⇒ this arm declines ⇒ the
                // deferred BV mul fails closed (no false cert; `wrapping_mul` and every
                // full-range product stay HONESTLY not-faithful). The MODELING here is
                // orthogonal to the DISCHARGE: even a certified-adequate `x*4` VC is
                // discharged only if `x*4 > MAX` refutes under the caller's facts (a
                // full-range `x` leaves it SAT ⇒ undischarged ⇒ SAFETY_GAP, never FF).
                BinOp::Mul if !sa && !sb => {
                    let leaf = find_violation_leaf(&vc.formula, &|f| match f {
                        F::Gt(lhs, rhs) => {
                            matches!(&**lhs, F::Mul(_, _))
                                && binop_operands(lhs).is_some()
                                && matches!(&**rhs, F::Int(_))
                        }
                        _ => false,
                    })?;
                    let F::Gt(mul_t, max_f) = leaf else { return None };
                    let (a_op, b_op) = binop_operands(mul_t)?;
                    let F::Int(max) = &**max_f else { return None };
                    let w = UWidth::from_mir(width_of_unsigned_max(*max)?, false)?;
                    let name = umul_overflows_name(w);
                    let ok = overflow_family_live_def_eq(leaf, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((
                        SafetyVcKind::UnsignedMulOverflow(w),
                        AdequacyVerdict::ProvenModulo3,
                    ))
                }
                _ => None,
            }
        }
        // NEGATION OVERFLOW (Lemma 6): the core `Eq(Var x, Int(MIN))`. Read MIN from the
        // formula → the modeled SWidth; ground the live core and check def-eq to
        // `neg_overflows_iW (g x)`. Use the `Eq`-descending finder so a PRECONDITION-
        // guarded `abs` (whose genuine core `Eq(x, MIN)` is buried as the RHS of the
        // SSA guard-binding `Eq(_6, Eq(x, MIN))`) is reached — the predicate
        // (`Eq(Var, Int)`) cannot match a guard-binding `Eq` (RHS is a comparison, not
        // an `Int`), so the deeper descent finds only the genuine core.
        K::NegationOverflow { .. } => {
            let leaf = find_violation_leaf_through_eq(&vc.formula, &|f| match f {
                F::Eq(lhs, rhs) => formula_var_name(lhs).is_some() && matches!(&**rhs, F::Int(_)),
                _ => false,
            })?;
            let F::Eq(x_f, min_f) = leaf else { return None };
            if formula_var_name(x_f).is_none() {
                return None;
            }
            let F::Int(min) = &**min_f else { return None };
            let w = swidth_of_signed_min(*min)?;
            let name = neg_overflows_name(w);
            let ok = overflow_family_live_def_eq(leaf, &[x_f], &|ops| {
                Expr::app(cst(&name), ops[0].clone())
            });
            ok.then_some((SafetyVcKind::NegationOverflow(w), AdequacyVerdict::ProvenModulo3))
        }
        _ => None,
    }
}

/// Map an unsigned-overflow MAX threshold literal `2^w − 1` (read from the emitted
/// `Gt(a+b, Int(MAX))` disjunct) to its bit width — the INVERSE of `UWidth::max_value`,
/// so the certified width is recovered FROM THE FORMULA, not from `operand_ty`. `None`
/// (fail closed) for a threshold that is not exactly some modeled `2^w − 1`.
pub(super) fn width_of_unsigned_max(max: i128) -> Option<u32> {
    [8u32, 16, 32, 64].into_iter().find(|&w| (1i128 << w) - 1 == max)
}

/// Map a signed out-of-range `(MIN, MAX)` threshold pair (read from the emitted
/// `Or([Lt(a∘b,MIN), Gt(a∘b,MAX)])`) to its modeled `SWidth` — requiring BOTH that
/// `MIN = −2^(w−1)` AND `MAX = 2^(w−1) − 1` for the SAME `w` (a mismatched pair is a
/// real shape inconsistency ⇒ fail closed, never a spuriously-certified width).
pub(super) fn swidth_of_signed_bounds(min: i128, max: i128) -> Option<SWidth> {
    for w in [SWidth::W8, SWidth::W16, SWidth::W32, SWidth::W64] {
        if w.min_value() == min && w.max_value() == max {
            return Some(w);
        }
    }
    None
}

/// Map a negation-overflow MIN threshold literal `−2^(w−1)` (read from the emitted
/// `Eq(x, Int(MIN))` core) to its modeled `SWidth`. `None` (fail closed) for a literal
/// that is not exactly some modeled `−2^(w−1)`.
pub(super) fn swidth_of_signed_min(min: i128) -> Option<SWidth> {
    for w in [SWidth::W8, SWidth::W16, SWidth::W32, SWidth::W64] {
        if w.min_value() == min {
            return Some(w);
        }
    }
    None
}

/// Whether a `VcKind` is a SAFETY obligation (a runtime-UB / panic check the §6
/// pipeline must discharge) — as opposed to a postcondition/precondition/contract or
/// a non-safety property (temporal, taint, …). The generalized metric requires EVERY
/// safety VC the emitter raises to classify into a MODELED kind; a safety VC of an
/// unmodeled kind (shift/cast/negation overflow, float div, unreachable, …) makes the
/// function fail closed.
pub(super) fn is_safety_vc_kind(kind: &trust_types::VcKind) -> bool {
    use trust_types::VcKind as K;
    matches!(
        kind,
        K::ArithmeticOverflow { .. }
            | K::ShiftOverflow { .. }
            | K::DivisionByZero
            | K::RemainderByZero
            | K::IndexOutOfBounds
            | K::SliceBoundsCheck
            | K::CastOverflow { .. }
            | K::NegationOverflow { .. }
            | K::FloatDivisionByZero
    )
}

/// Public accessor for [`is_safety_vc_kind`] — the scorecard's straight-line
/// fully-faithful SOUNDNESS GATE (`prove::function_safety_vcs_all_discharged`) uses it
/// to select the safety VCs whose precondition-aware discharge it requires.
#[must_use]
pub fn is_safety_vc_kind_pub(kind: &trust_types::VcKind) -> bool {
    is_safety_vc_kind(kind)
}

/// If an `ArithmeticOverflow` VC is the UNSIGNED-ADD case of a MODELED width Lemma 2
/// certifies (`op == Add`, both operands unsigned with a `u8`/`u16`/`u32`/`u64`
/// width), return that width. `None` for a signed add, a non-Add op (the signed
/// `Div` `MIN/-1` overflow is an `ArithmeticOverflow{op:Div}`), an unmodeled width
/// (`u128`), or mismatched operand widths — those are UNMODELED ⇒ fail-closed.
pub(super) fn overflow_vc_modeled_width(kind: &trust_types::VcKind) -> Option<UWidth> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op: BinOp::Add, operand_tys: (a, b) } = kind else {
        return None;
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    if wa != wb {
        return None;
    }
    // BOTH operands must be unsigned at the same modeled width.
    let wa = UWidth::from_mir(*wa, *sa)?;
    let wb = UWidth::from_mir(*wb, *sb)?;
    (wa == wb).then_some(wa)
}

/// If an `ArithmeticOverflow` VC is the UNSIGNED-MUL case of a MODELED width
/// (`op == Mul`, both operands unsigned with a `u8`/`u16`/`u32`/`u64` width), return
/// that width. `None` for a signed mul (that is the Lemma-5 case), a non-Mul op, an
/// unmodeled width (`u128`), or mismatched operand widths — those are UNMODELED ⇒
/// fail-closed. MIRRORS [`overflow_vc_modeled_width`] exactly (Add→Mul), and shares its
/// modeled unsigned width set `{u8,u16,u32,u64}`.
///
/// KIND-level accept is NECESSARY-not-sufficient: the load-bearing gate is the
/// formula-aware def-eq bridge (`safety_vc_is_faithful_formula_aware`), which certifies
/// ONLY the CONSTANT-multiplier LIA emission (`Gt(Mul(a,b), MAX)`) and DECLINES the
/// `var*var` BV mul shape. So a full-range `u8 * u8` VC is kind-modeled here but fails
/// closed at the bridge (and, separately, at the discharge) — `wrapping_mul` and every
/// unbounded product stay honestly not-faithful.
pub(super) fn umul_overflow_vc_modeled(kind: &trust_types::VcKind) -> Option<UWidth> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (a, b) } = kind else {
        return None;
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    if wa != wb {
        return None;
    }
    // BOTH operands must be UNSIGNED at the same modeled width (a signed mul is Lemma 5).
    let wa = UWidth::from_mir(*wa, *sa)?;
    let wb = UWidth::from_mir(*wb, *sb)?;
    (wa == wb).then_some(wa)
}

/// If an `ArithmeticOverflow` VC is the UNSIGNED-SUB case of a MODELED width Lemma 8
/// certifies (`op == Sub`, both operands unsigned with a `u8`/`u16`/`u32`/`u64` width),
/// return that width. `None` for a signed sub (that is the Lemma-5 case), a non-Sub op,
/// an unmodeled width (`u128`), or mismatched operand widths — those are UNMODELED ⇒
/// fail-closed. The emitter's unsigned-Sub VC is `ArithmeticOverflow{op:Sub, (u_W,u_W)}`
/// whose violation core is the single underflow disjunct `Lt(Sub(a,b), 0)`.
pub(super) fn usub_underflow_vc_modeled(kind: &trust_types::VcKind) -> Option<UWidth> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (a, b) } = kind else {
        return None;
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    if wa != wb {
        return None;
    }
    // BOTH operands must be UNSIGNED at the same modeled width (a signed sub is Lemma 5).
    let wa = UWidth::from_mir(*wa, *sa)?;
    let wb = UWidth::from_mir(*wb, *sb)?;
    (wa == wb).then_some(wa)
}

/// If an `ArithmeticOverflow` VC is the SIGNED-ADD/SUB/MUL case of a MODELED width Lemma
/// 5 certifies (`op ∈ {Add, Sub, Mul}`, both operands signed), return that `(op, width)`.
/// `None` for an unsigned operand, a non-Add/Sub/Mul op (the signed `Div` `MIN/-1`
/// overflow is an `ArithmeticOverflow{op:Div}`), or an unmodeled check width (`i128`) —
/// those are UNMODELED ⇒ fail-closed. NOTE: signed MUL is kind-modeled here, but the
/// load-bearing gate is the formula-aware def-eq bridge, which certifies only the LIA
/// constant-multiplier shape and declines a `var*var` BV mul (fail-closed).
///
/// The MODELED width is the NARROWER (`min`) of the two operand widths — exactly the
/// type the emitter's overflow check is against (`generate.rs::int_op_type` recovers
/// the true type from the NON-constant operand; an untyped integer constant defaults to
/// the widest `i64`, so when the operand widths differ the real check type is the
/// narrower one, and the emitted `±2^(W−1)` threshold is at that width). For genuine
/// same-width arithmetic (`x:i32 + y:i32`) `min` is just that shared width. This keeps
/// the certified width byte-aligned with the emitted threshold (guarded end-to-end by
/// `signed_overflow_vc_shape_matches_trust_vcgen_emission`).
pub(super) fn signed_overflow_vc_modeled(kind: &trust_types::VcKind) -> Option<(SignedOp, SWidth)> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op, operand_tys: (a, b) } = kind else {
        return None;
    };
    let sop = match op {
        BinOp::Add => SignedOp::Add,
        BinOp::Sub => SignedOp::Sub,
        // Signed MUL is now a MODELED kind (Lemma 5 spec heads `Int.mul`). This kind-level
        // accept is NECESSARY-not-sufficient: the load-bearing gate is the formula-aware
        // def-eq bridge (`safety_vc_is_faithful_formula_aware`), which certifies ONLY the
        // LIA constant-multiplier emission and DECLINES the `var*var` BV mul shape. So the
        // BV mul VC is kind-modeled here but fails closed at the bridge — the `mul_*`/
        // `sq_nonneg` corpus stays not-faithful (its product is genuinely unbounded).
        BinOp::Mul => SignedOp::Mul,
        // Every other op (Div/Rem/shift/…) is not a Lemma-5 shape.
        _ => return None,
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    // BOTH operands must be signed. The check width is the narrower of the two (the
    // emitter's `int_op_type` recovers it from the non-constant — real-typed — operand).
    if !sa || !sb {
        return None;
    }
    let check_width = (*wa).min(*wb);
    let w = SWidth::from_mir(check_width, true)?;
    Some((sop, w))
}

/// If a `NegationOverflow` VC is on a MODELED signed width Lemma 6 certifies
/// (`i8`/`i16`/`i32`/`i64`), return that width. `None` for an unsigned type (negation
/// of an unsigned value carries no overflow obligation; `is_signed` is false) or an
/// unmodeled width (`i128` — the deferred bitvector case) — those are UNMODELED ⇒
/// fail-closed.
pub(super) fn negation_vc_modeled(kind: &trust_types::VcKind) -> Option<SWidth> {
    use trust_types::{Ty, VcKind as K};
    let K::NegationOverflow { ty } = kind else {
        return None;
    };
    let Ty::Int { width, signed } = ty else {
        return None;
    };
    SWidth::from_mir(*width, *signed)
}

/// If a `ShiftOverflow` VC is on a MODELED value width Lemma 7 certifies, return that
/// `(value width, amount signedness)`. The MODELED width is the SHIFTED VALUE's width
/// (the `n ≥ W` UB threshold is `W` = the value width); the bool is the shift AMOUNT's
/// signedness (a signed amount adds the `n < 0` disjunct). The modeled set is
/// `8/16/32/64/128` — INCLUDING the `i128`/`u128` value widths (the former "128-bit
/// shift VC width" residue: the threshold is the width literal itself, which stays a
/// closed `Int.ofNat` at 128). `None` for a non-integer value type or any other
/// width — those are UNMODELED ⇒ fail-closed.
pub(super) fn shift_vc_modeled(kind: &trust_types::VcKind) -> Option<(ShiftWidth, bool)> {
    use trust_types::{Ty, VcKind as K};
    let K::ShiftOverflow { operand_ty, shift_ty, .. } = kind else {
        return None;
    };
    let Ty::Int { width, .. } = operand_ty else {
        return None;
    };
    // The shifted-VALUE width drives the `n ≥ W` threshold. Map any integer value
    // width (signed OR unsigned) to the modeled W ∈ {8,16,32,64,128} (the ShiftWidth
    // names the THRESHOLD W, not the value's signedness).
    let w = ShiftWidth::from_bits(*width)?;
    let Ty::Int { signed: amount_signed, .. } = shift_ty else {
        return None;
    };
    Some((w, *amount_signed))
}

/// Whether a SAFETY `VcKind` is one MirSem models an adequacy lemma for (unsigned-add
/// overflow ∨ UNSIGNED-SUB underflow ∨ SIGNED add/sub overflow ∨ bounds ∨ div ∨ rem ∨
/// NEGATION overflow ∨ SHIFT-amount OOB). A safety VC outside this set is UNMODELED ⇒
/// the function fails closed in the generalized metric. For `ArithmeticOverflow` the
/// modeled set is the unsigned-add-of-modeled-width case (`overflow_vc_modeled_width`,
/// Lemma 2), the unsigned-SUB-of-modeled-width case (`usub_underflow_vc_modeled`,
/// Lemma 8), the signed add/sub/mul-of-modeled-width case (`signed_overflow_vc_modeled`,
/// Lemma 5), OR the UNSIGNED-MUL-of-modeled-width case (`umul_overflow_vc_modeled`). Both
/// signed AND unsigned MUL are kind-modeled, but the formula-aware bridge certifies only
/// the LIA constant-multiplier shape (`Gt(Mul(a,b), MAX)`) — a `var*var` BV mul declines
/// there (fail-closed), so the `var*var` corpus stays effectively deferred. `DivisionByZero`
/// (Lemma 4) and `RemainderByZero` (Lemma 9) are modeled; `NegationOverflow` of a
/// modeled width (Lemma 6) and `ShiftOverflow` of a modeled value width — INCLUDING
/// 128 (Lemma 7) — are modeled; a `CastOverflow` / `FloatDivisionByZero` / `i128`
/// negation remains UNMODELED.
pub(super) fn safety_vc_kind_is_modeled(kind: &trust_types::VcKind) -> bool {
    use trust_types::VcKind as K;
    match kind {
        K::ArithmeticOverflow { .. } => {
            overflow_vc_modeled_width(kind).is_some()
                || usub_underflow_vc_modeled(kind).is_some()
                || signed_overflow_vc_modeled(kind).is_some()
                || umul_overflow_vc_modeled(kind).is_some()
        }
        K::DivisionByZero | K::RemainderByZero | K::IndexOutOfBounds | K::SliceBoundsCheck => true,
        K::NegationOverflow { .. } => negation_vc_modeled(kind).is_some(),
        K::ShiftOverflow { .. } => shift_vc_modeled(kind).is_some(),
        _ => false,
    }
}

/// THE GENERALIZED SAFETY-VC-FAITHFULNESS HOOK (Goal #4, generalized
/// `safety_vc_faithful` tier). For a reflected function, mint per-kind safety-VC
/// adequacy certificates iff:
///
///   1. the function raises AT LEAST ONE modeled safety VC (overflow ∨ bounds ∨ div),
///      AND
///   2. EVERY safety VC the emitter (`trust_vcgen::generate_vcs`) raises classifies
///      into a MODELED kind (no unmodeled shift/cast/negation/float safety VC), AND
///   3. each modeled kind's reflected VC is PROVEN (modulo 3) def-eq to its pinned
///      machine-semantics condition (`uadd_overflows_uW` / `idx_oob` / `div_by_zero`).
///
/// Fail-closed (`None`): a function with NO modeled safety VC, a function whose
/// emitter raises an UNMODELED safety VC kind, or any modeled kind whose adequacy
/// proof does not kernel-check modulo 3 — never a false witness.
///
/// A `Some` result means: when the §6 pipeline discharges this function's safety VCs,
/// it is refuting EXACTLY the machine condition for EACH — overflow `(2^w−1)<a+b`,
/// bounds `len≤i`, or div-zero `b=0` — the safety discharge is kernel-certified
/// FAITHFUL across all the function's modeled safety obligations, not merely trusted.
#[must_use]
pub fn function_safety_vcs_faithful(
    func: &trust_types::VerifiableFunction,
) -> Option<FunctionSafetyVcCertificates> {
    // Drive the REAL emitter so the classification is over the VCs that ACTUALLY get
    // raised (the same empirical grounding Lemma 2's value rested on).
    let vcs = trust_vcgen::generate_vcs(func);

    // ALL modeled safety-VC kinds are now FORMULA-AWARE: each cert is minted by
    // grounding the ACTUAL emitted `vc.formula` violation core through the LIVE
    // `clean_ground::ground_prop` and kernel-checking it def-eq to the per-kind spec
    // (recovering the width/threshold from the FORMULA, not from `operand_ty`). The
    // OVERFLOW-family cores (unsigned-add OVERFLOW, signed ADD/SUB OVERFLOW, unsigned-SUB
    // UNDERFLOW, NEGATION) carry a COMPUTED `Add`/`Sub`/`Eq` sub-term whose operands the
    // live grounder DOES ground — closing the model→grounder bridge for them too. Dedup
    // by the `SafetyVcKind` the formula-aware certifier returns.
    let mut certs = FunctionSafetyVcCertificates::default();
    let mut bounds_cert: Option<SafetyVcCertificate> = None;
    let mut div_cert: Option<SafetyVcCertificate> = None;
    let mut rem_cert: Option<SafetyVcCertificate> = None;
    let mut shift_certs: Vec<SafetyVcCertificate> = Vec::new();
    for vc in &vcs {
        if !is_safety_vc_kind(&vc.kind) {
            continue; // a postcondition / contract / non-safety property — not our concern
        }
        if !safety_vc_kind_is_modeled(&vc.kind) {
            return None; // an UNMODELED safety VC kind ⇒ fail closed (cannot certify ALL)
        }
        // FORMULA-AWARE certification for EVERY modeled safety VC: ground the REAL
        // emitted core live and kernel-check def-eq to its spec. Fail-closed if this
        // VC's core is outside the formula-aware fragment OR not def-eq to the spec —
        // even though `safety_vc_kind_is_modeled` accepted the VcKind, the live-grounded
        // def-eq is the stricter (and load-bearing) bridge check.
        let (kind, verdict) = safety_vc_is_faithful_formula_aware(vc)?;
        match &kind {
            SafetyVcKind::Overflow(_) => {
                if !certs.overflow.iter().any(|c| c.kind == kind) {
                    certs.overflow.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::UnsignedSubUnderflow(_) => {
                if !certs.usub.iter().any(|c| c.kind == kind) {
                    certs.usub.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::SignedOverflow(_, _) => {
                if !certs.signed_overflow.iter().any(|c| c.kind == kind) {
                    certs.signed_overflow.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::UnsignedMulOverflow(_) => {
                if !certs.umul.iter().any(|c| c.kind == kind) {
                    certs.umul.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::NegationOverflow(_) => {
                if !certs.negation.iter().any(|c| c.kind == kind) {
                    certs.negation.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::Bounds => {
                if bounds_cert.is_none() {
                    bounds_cert = Some(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::DivByZero => {
                if div_cert.is_none() {
                    div_cert = Some(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::RemByZero => {
                if rem_cert.is_none() {
                    rem_cert = Some(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::ShiftOob(_, _) => {
                if !shift_certs.iter().any(|c| c.kind == kind) {
                    shift_certs.push(SafetyVcCertificate { kind, verdict });
                }
            }
        }
    }

    certs.bounds = bounds_cert;
    certs.div = div_cert;
    certs.rem = rem_cert;
    certs.shift = shift_certs;

    // Require at least one modeled safety VC (an unmodeled body is not certified).
    if certs.any() { Some(certs) } else { None }
}
