// Copyright 2026 Andrew Yates | Apache-2.0
//! The actual unsigned-Mul Int flag bridge. No BV equivalence is claimed.
use super::*;
use crate::trustir_safety::{IrUWidth, register_unsigned_mul_predicate, umul_overflows_ir_name};

pub(super) const FLAG_ARM: OverflowFlagArmSpec = OverflowFlagArmSpec {
    op: "MulOverflow",
    signed: false,
    lemma: "#53 (unsigned-mul Int out-of-range)",
    form: ArmForm::B,
    reduces_theorem: "overflow_umul_flag_reduces",
    reduces_src: r#"theorem overflow_umul_flag_reduces (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow w false l r =
      Except.ok ((((l * r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 Decidable.decide (l * r ≥ (2:Int)^w) ||
                 @Decidable.decide (l * r < 0) (Int.decLt (l * r) 0)) := rfl
"#,
    extra_src: "",
    connect_theorem: "bridge_overflow_umul_flag",
    connect_src: r#"theorem bridge_overflow_umul_flag (w : Nat) (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow w false l r =
      Except.ok ((((l * r) % ((2:Int)^w) + (2:Int)^w) % ((2:Int)^w)),
                 @Decidable.decide (l * r < 0) (Int.decLt (l * r) 0) ||
                 Decidable.decide (((2:Int)^w - 1) < (l * r))) := by
  rw [overflow_umul_flag_reduces, overflow_threshold_decide_eq, Bool.or_comm]
"#,
};

// An explicit computational proof, independent of imported decide-or aliases.
// Keep the original simultaneous match: the imported-environment regression must
// exercise Clean's dependent packed motive at this real predicate composition.
const DECIDE_OR_SRC: &str = r#"theorem overflow_decide_or (p q : Prop) (dp : Decidable p) (dq : Decidable q) :
    @Decidable.decide (p ∨ q) (@instDecidableOr p q dp dq) =
      (@Decidable.decide p dp || @Decidable.decide q dq) :=
  match dp, dq with
  | .isTrue _, .isTrue _ => rfl
  | .isTrue _, .isFalse _ => rfl
  | .isFalse _, .isTrue _ => rfl
  | .isFalse _, .isFalse _ => rfl
"#;

fn predicate_theorem_name(width: IrUWidth) -> String {
    format!("bridge_overflow_umul_predicate_u{}", width.bits())
}

fn predicate_source(width: IrUWidth) -> String {
    // The predicate is NOT defined in this source: it is the actual checked
    // production declaration registered by trustir_safety's shared constructor.
    r#"theorem $THEOREM (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow $WIDTH false l r =
      Except.ok ((((l * r) % ((2:Int)^$WIDTH) + (2:Int)^$WIDTH) % ((2:Int)^$WIDTH)),
        @Decidable.decide ($PREDICATE l r)
          (@instDecidableOr (l * r < 0) ($MAX < l * r)
            (Int.decLt (l * r) 0) (Int.decLt $MAX (l * r)))) :=
  Eq.trans (bridge_overflow_umul_flag $WIDTH l r)
    (congrArg (fun flag : Bool =>
      (Except.ok ((((l * r) % ((2:Int)^$WIDTH) + (2:Int)^$WIDTH) % ((2:Int)^$WIDTH)), flag) :
        Except TrustIr.SemError (Int × Bool)))
      (overflow_decide_or (l * r < 0) ($MAX < l * r)
        (Int.decLt (l * r) 0) (Int.decLt $MAX (l * r))).symm)
"#
    .replace("$THEOREM", &predicate_theorem_name(width))
    .replace("$PREDICATE", &umul_overflows_ir_name(width))
    .replace("$WIDTH", &width.bits().to_string())
    .replace("$MAX", &width.max_value().to_string())
}

#[derive(Default)]
pub(super) struct PredicateLinks {
    pub(super) bound: Vec<String>,
    pub(super) proved: Vec<String>,
    pub(super) pinned: Vec<String>,
    pub(super) foundational_axioms: Vec<String>,
}

fn foundational_axioms(
    env: &Environment,
    names: &[String],
) -> Result<Vec<String>, BridgeGateError> {
    let mut found = BTreeSet::new();
    for name in names {
        let deps = env.foundational_axiom_deps(&Name::from_string(name)).ok_or_else(|| {
            BridgeGateError::PreludeFailed {
                detail: format!("missing axiom-footprint subject {name}"),
            }
        })?;
        found.extend(deps.into_iter().map(|name| name.to_string()));
    }
    Ok(found.into_iter().collect())
}

fn check_predicate_links(
    env: &mut Environment,
    generic_flag_proved: bool,
) -> Result<PredicateLinks, BridgeGateError> {
    let mut result = PredicateLinks::default();
    for width in IrUWidth::ALL {
        let name = register_unsigned_mul_predicate(env, width)
            .map_err(|detail| BridgeGateError::PreludeFailed { detail })?;
        require_empty_axiom_deps(env, &name)?;
        result.bound.push(name);
    }
    if !generic_flag_proved {
        result.pinned = IrUWidth::ALL
            .into_iter()
            .map(|width| format!("u{}: generic unsigned-Mul flag theorem not proven", width.bits()))
            .collect();
        return Ok(result);
    }
    for name in load_bridge_source(env, DECIDE_OR_SRC)
        .map_err(|detail| BridgeGateError::PreludeFailed { detail })?
    {
        require_empty_axiom_deps(env, &name)?;
    }
    for width in IrUWidth::ALL {
        let name = predicate_theorem_name(width);
        match load_bridge_source(env, &predicate_source(width)) {
            Ok(_) => {
                require_empty_axiom_deps(env, &name)?;
                result.proved.push(name);
            }
            Err(error) => result.pinned.push(format!(
                "u{}: {}",
                width.bits(),
                error.chars().take(200).collect::<String>()
            )),
        }
    }
    result.foundational_axioms = foundational_axioms(env, &result.proved)?;
    Ok(result)
}

const UMUL_FORGERY_PROBES: &[(&str, &str)] = &[
    (
        "unsigned-Mul wrong threshold",
        r#"theorem overflow_umul_wrong_threshold (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow 8 false l r =
      Except.ok ((((l * r) % 256 + 256) % 256),
        Decidable.decide (l * r ≥ (128:Int)) ||
        @Decidable.decide (l * r < 0) (Int.decLt (l * r) 0)) := rfl
"#,
    ),
    (
        "unsigned-Mul lost underflow",
        r#"theorem overflow_umul_lost_underflow (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow 8 false l r =
      Except.ok ((((l * r) % 256 + 256) % 256),
        Decidable.decide (l * r ≥ (256:Int))) := rfl
"#,
    ),
    (
        "unsigned-Mul wrong operation",
        r#"theorem overflow_umul_wrong_operation (l r : Int) :
    TrustIr.semOverflowOp TrustIr.OverflowOp.MulOverflow 8 false l r =
      TrustIr.semOverflowOp TrustIr.OverflowOp.AddOverflow 8 false l r := rfl
"#,
    ),
];

pub(super) struct OverflowEvidence {
    pub(super) overflow_value_bridged: usize,
    pub(super) overflow_value_pinned: usize,
    pub(super) overflow_value_pinned_list: Vec<String>,
    pub(super) overflow_value_bridged_list: Vec<String>,
    pub(super) overflow_flag_bridged: usize,
    pub(super) overflow_flag_pinned: usize,
    pub(super) overflow_flag_pinned_list: Vec<String>,
    pub(super) overflow_flag_bridged_list: Vec<String>,
    pub(super) overflow_flag_guarded: usize,
    pub(super) overflow_composed: bool,
    pub(super) overflow_fail_closed_controls: usize,
    pub(super) overflow_flag_unbridged: Vec<String>,
    pub(super) overflow_umul_predicates_bound: Vec<String>,
    pub(super) overflow_umul_predicate_bridged: Vec<String>,
    pub(super) overflow_umul_predicate_pinned: Vec<String>,
    pub(super) overflow_umul_foundational_axioms: Vec<String>,
    pub(super) overflow_foundational_axioms: Vec<String>,
}

/// Production overflow layer, also directly exercised by the focused kernel test.
pub(super) fn check_overflow_layer(
    env: &mut Environment,
    mode: BridgeGateMode,
) -> Result<OverflowEvidence, BridgeGateError> {
    // -- 17. Overflow threshold-shift prelude (unconditional, both modes: --
    // -- every Overflow FLAG connect proof cites it). --
    let overflow_prelude_names = load_bridge_source(env, OVERFLOW_THRESHOLD_PRELUDE_SRC)
        .map_err(|detail| BridgeGateError::PreludeFailed { detail })?;
    for n in &overflow_prelude_names {
        require_empty_axiom_deps(&env, n)?;
    }

    // -- 18. The Overflow VALUE arms. Failure to prove is PINNED, not fatal. --
    let overflow_value_arm_set: Vec<&OverflowValueArmSpec> = match mode {
        BridgeGateMode::Full => OVERFLOW_VALUE_ARMS.iter().collect(),
        BridgeGateMode::Spot => {
            OVERFLOW_VALUE_ARMS.iter().filter(|a| a.op == "AddOverflow" && !a.signed).collect()
        }
    };
    let mut overflow_value_bridged_list: Vec<String> = Vec::new();
    let mut overflow_value_pinned_list: Vec<String> = Vec::new();
    let mut overflow_value_proved: BTreeSet<&str> = BTreeSet::new();
    for arm in &overflow_value_arm_set {
        match load_bridge_source(env, arm.src) {
            Ok(_) => {
                require_empty_axiom_deps(&env, arm.theorem)?;
                overflow_value_bridged_list.push(format!(
                    "{}[{}]",
                    arm.op,
                    if arm.signed { "s" } else { "u" }
                ));
                overflow_value_proved.insert(arm.theorem);
            }
            Err(e) => overflow_value_pinned_list.push(format!(
                "{}[{}]: {}",
                arm.op,
                if arm.signed { "s" } else { "u" },
                e.chars().take(200).collect::<String>()
            )),
        }
    }

    // -- 19. The Overflow FLAG arms: reduces PIN + (guarded arms') extra --
    // -- helper lemma + connect theorem. Failure to prove is PINNED. --
    let overflow_flag_arm_set: Vec<&OverflowFlagArmSpec> = match mode {
        BridgeGateMode::Full => OVERFLOW_FLAG_ARMS.iter().collect(),
        BridgeGateMode::Spot => {
            OVERFLOW_FLAG_ARMS.iter().filter(|a| a.op == "AddOverflow" && !a.signed).collect()
        }
    };
    let mut overflow_flag_bridged_list: Vec<String> = Vec::new();
    let mut overflow_flag_pinned_list: Vec<String> = Vec::new();
    let mut overflow_flag_proved: BTreeSet<&str> = BTreeSet::new();
    let mut overflow_flag_guarded = 0usize;
    for arm in &overflow_flag_arm_set {
        let label = format!("{}[{}]", arm.op, if arm.signed { "s" } else { "u" });
        // Step (a): the `reduces` PIN (rfl over the imported constant).
        let reduces_ok = match load_bridge_source(env, arm.reduces_src) {
            Ok(_) => {
                require_empty_axiom_deps(&env, arm.reduces_theorem)?;
                true
            }
            Err(e) => {
                overflow_flag_pinned_list
                    .push(format!("{label}: reduces: {}", e.chars().take(200).collect::<String>()));
                false
            }
        };
        // Step (b): the guarded arms' extra helper lemma (empty for the rest).
        let extra_ok = reduces_ok
            && if arm.extra_src.is_empty() {
                true
            } else {
                match load_bridge_source(env, arm.extra_src) {
                    Ok(_) => true,
                    Err(e) => {
                        overflow_flag_pinned_list.push(format!(
                            "{label}: extra: {}",
                            e.chars().take(200).collect::<String>()
                        ));
                        false
                    }
                }
            };
        // Step (c): the `connect` theorem (the Lemma-textbook-spelling identity).
        if extra_ok {
            match load_bridge_source(env, arm.connect_src) {
                Ok(_) => {
                    require_empty_axiom_deps(&env, arm.connect_theorem)?;
                    overflow_flag_bridged_list.push(format!("{label}:{}", arm.lemma));
                    overflow_flag_proved.insert(arm.connect_theorem);
                    if arm.form == ArmForm::BGuarded {
                        overflow_flag_guarded += 1;
                    }
                }
                Err(e) => overflow_flag_pinned_list
                    .push(format!("{label}: connect: {}", e.chars().take(200).collect::<String>())),
            }
        }
    }

    // Bind the actual four production Int predicates, not a Lean re-declaration.
    let predicate_links = if mode == BridgeGateMode::Full {
        check_predicate_links(env, overflow_flag_proved.contains(FLAG_ARM.connect_theorem))?
    } else {
        PredicateLinks::default()
    };

    // -- 20. All twelve generic statements AND all four live predicate links. --
    let mut overflow_composed = false;
    if mode == BridgeGateMode::Full
        && overflow_value_proved.len() == OVERFLOW_VALUE_ARMS.len()
        && overflow_flag_proved.len() == OVERFLOW_FLAG_ARMS.len()
        && predicate_links.proved.len() == IrUWidth::ALL.len()
    {
        match load_bridge_source(env, OVERFLOW_COMPOSED_SRC) {
            Ok(_) => {
                require_empty_axiom_deps(&env, OVERFLOW_COMPOSED_NAME)?;
                overflow_composed = true;
            }
            Err(e) => overflow_flag_pinned_list
                .push(format!("composed: {}", e.chars().take(200).collect::<String>())),
        }
    }

    // -- 21. Overflow forgery probes: wrong claims MUST be rejected. --
    let overflow_probes: &[(&str, &str)] = match mode {
        BridgeGateMode::Full => OVERFLOW_FORGERY_PROBES,
        BridgeGateMode::Spot => &OVERFLOW_FORGERY_PROBES[..1],
    };
    let mut overflow_fail_closed_controls = 0usize;
    for (label, src) in overflow_probes {
        check_semantic_forgery_with_budget(env, label, src, BRIDGE_DECL_BUDGET)?;
        overflow_fail_closed_controls += 1;
    }
    if mode == BridgeGateMode::Full {
        for (label, src) in UMUL_FORGERY_PROBES {
            check_semantic_forgery_with_budget(env, label, src, BRIDGE_DECL_BUDGET)?;
            overflow_fail_closed_controls += 1;
        }
    }
    let overflow_flag_unbridged: Vec<String> =
        OVERFLOW_FLAG_UNBRIDGED.iter().map(|(op, reason)| format!("{op}: {reason}")).collect();

    let mut footprint_names = overflow_prelude_names;
    footprint_names.extend(overflow_value_proved.iter().map(|name| (*name).to_owned()));
    footprint_names.extend(overflow_flag_proved.iter().map(|name| (*name).to_owned()));
    footprint_names.extend(predicate_links.proved.iter().cloned());
    if overflow_composed {
        footprint_names.push(OVERFLOW_COMPOSED_NAME.to_owned());
    }
    let overflow_foundational_axioms = foundational_axioms(env, &footprint_names)?;
    Ok(OverflowEvidence {
        overflow_value_bridged: overflow_value_bridged_list.len(),
        overflow_value_pinned: overflow_value_arm_set.len() - overflow_value_bridged_list.len(),
        overflow_flag_bridged: overflow_flag_bridged_list.len(),
        overflow_flag_pinned: overflow_flag_arm_set.len() - overflow_flag_bridged_list.len(),
        overflow_umul_predicates_bound: predicate_links.bound,
        overflow_umul_predicate_bridged: predicate_links.proved,
        overflow_umul_predicate_pinned: predicate_links.pinned,
        overflow_umul_foundational_axioms: predicate_links.foundational_axioms,
        overflow_foundational_axioms,
        overflow_value_pinned_list,
        overflow_value_bridged_list,
        overflow_flag_pinned_list,
        overflow_flag_bridged_list,
        overflow_flag_guarded,
        overflow_composed,
        overflow_fail_closed_controls,
        overflow_flag_unbridged,
    })
}

#[cfg(test)]
fn predicate_registration_refusals(base: &Environment) {
    use clean_kernel::{BinderData, BinderInfo, Declaration, Expr};

    use crate::trustir_safety::unsigned_mul_predicate_components;
    let constant = |name: &str| Expr::const_(Name::from_string(name), vec![]);
    let literal = |value: i128| Expr::app(constant("Int.ofNat"), Expr::nat_lit_u128(value as u128));
    for width in IrUWidth::ALL {
        for mutation in 0..6 {
            let (name, type_, canonical) = unsigned_mul_predicate_components(width);
            let mut env = base.clone();
            let bd = || BinderData::from(BinderInfo::Default);
            let int = || constant("Int");
            let a = Expr::bvar(1);
            let b = Expr::bvar(0);
            let op = if mutation == 1 { "Int.add" } else { "Int.mul" };
            let product = || Expr::apps(constant(op), [a.clone(), b.clone()]);
            let bound = width.max_value() - if mutation == 0 { 1 } else { 0 };
            let upper = Expr::apps(constant("Int.lt"), [literal(bound), product()]);
            let body = if mutation == 2 {
                upper
            } else {
                Expr::apps(
                    constant("Or"),
                    [Expr::apps(constant("Int.lt"), [product(), literal(0)]), upper],
                )
            };
            let value = if mutation >= 4 {
                canonical
            } else {
                Expr::lam(
                    bd(),
                    int(),
                    Expr::lam(bd(), int(), if mutation == 3 { product() } else { body }),
                )
            };
            let declaration = if mutation == 5 {
                Declaration::Axiom { name: name.clone(), level_params: vec![], type_ }
            } else {
                Declaration::Definition {
                    name: name.clone(),
                    level_params: vec![],
                    type_: if mutation == 3 {
                        Expr::pi(bd(), int(), Expr::pi(bd(), int(), int()))
                    } else {
                        type_
                    },
                    value,
                    is_reducible: mutation != 4,
                }
            };
            env.add_decl(declaration).expect("negative predicate input is well-typed");
            let before = env.get_const(&name).expect("inserted malformed model").clone();
            let error = register_unsigned_mul_predicate(&mut env, width)
                .expect_err("a name alone must not authorize a different predicate");
            assert!(
                error.contains("differs from the registered production constructor"),
                "u{} mutation{mutation}: {error}",
                width.bits()
            );
            assert_eq!(env.get_const(&name), Some(&before), "refusal must not overwrite input");
        }
    }
}

/// Check the original universal helper in the real manifest-selected imported
/// base. This does not replay the imported declaration closure or confer a
/// product/source-to-machine proof grade.
#[cfg(test)]
pub(super) fn check_imported_multi_scrutinee_decidable_or_for_test() {
    use clean_elab::{ElabError, MetaState};
    use clean_kernel::{BinderData, BinderInfo, Expr, Level};

    let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
    let trustir = verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
        .expect("original actual TrustIR manifest");
    let core = verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
        .expect("original actual Lean-core manifest");
    // Bind these imported bytes to the actual selected source, with the same
    // source-reuse authority rule as production (never an expected-pin override).
    let checkout = resolve_trustir_checkout(&config.repo_root).expect("actual IR source pin");
    check_lean_sources_clean(&config.repo_root).expect("actual logical sources are clean");
    if trustir.source_reuse {
        let selected = trust_bridge_closure::source_reuse::verify(
            &config.repo_root,
            trust_bridge_closure::source_reuse::Subject::Checkout,
        )
        .expect("actual source-reuse authority")
        .expect("manifest source-reuse record");
        let selected =
            bind_source_reuse(selected, &trustir, &core).expect("exact captured manifests");
        assert_eq!(selected.trustir_commit, checkout);
    } else {
        assert_eq!(trustir.trustir_commit.as_deref(), Some(checkout.as_str()));
    }
    let mut env = Environment::default();
    env.ensure_native_reducers();
    let roots = BRIDGE_ROOT_MODULES.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>();
    load_verified_modules(&mut env, &roots, &trustir, &core)
        .expect("actual imported module closure");
    for name in load_bridge_source(&mut env, BRIDGE_INSTANCE_SRC).expect("original instances") {
        require_empty_axiom_deps(&env, &name).expect("no non-foundational instance residue");
    }

    let name = Name::from_string("overflow_decide_or");
    assert!(env.get_const(&name).is_none(), "the helper must not already be imported");
    assert_eq!(DECIDE_OR_SRC.matches(" || ").count(), 1, "one intended Bool-or");
    assert_eq!(DECIDE_OR_SRC.matches("=> rfl").count(), 4, "all four original arms");
    let false_source = DECIDE_OR_SRC.replacen(" || ", " && ", 1);
    assert_eq!(false_source.matches(" && ").count(), 1);
    assert_eq!(false_source.replace(" && ", " || "), DECIDE_OR_SRC);

    // The negative runs BEFORE the positive in its own clone of the verified
    // imported base. Duplicate names or a cached positive cannot refute it.
    let mut false_env = env.clone();
    let mut observed = Vec::new();
    let refusal = load_bridge_source_with_budget_observed(
        &mut false_env,
        &false_source,
        BRIDGE_DECL_BUDGET,
        |error, incomplete| {
            let kind = match error {
                ElabError::MatchArmTypeMismatch { .. } => "MatchArmTypeMismatch",
                ElabError::TypeMismatch { .. } => "TypeMismatch",
                ElabError::ProofTypeMismatch { .. } => "ProofTypeMismatch",
                ElabError::KernelCheckFailed { .. } => "KernelCheckFailed",
                _ => "not-a-semantic-refutation",
            };
            observed.push((kind, incomplete));
        },
    );
    assert!(refusal.is_err(), "Bool-or is not Bool-and");
    assert_eq!(observed.len(), 1, "one typed false-helper rejection: {refusal:?}");
    assert_ne!(observed[0].0, "not-a-semantic-refutation", "{refusal:?}");
    assert!(!observed[0].1, "an incomplete check is not a semantic rejection");
    assert!(false_env.get_const(&name).is_none(), "the false helper was not registered");
    assert!(env.get_const(&name).is_none(), "the positive base remains untouched");
    eprintln!("MULTI_SCRUTINEE_DECIDABLE_AND_REFUSED kind={} incomplete=false", observed[0].0);

    let names = load_bridge_source(&mut env, DECIDE_OR_SRC)
        .expect("the original universal four-arm helper must check in the imported base");
    assert_eq!(names, vec!["overflow_decide_or"]);
    let info = env.get_const(&name).expect("actual imported-base theorem");
    let proof = info.value.as_ref().expect("actual checked proof body");
    assert!(info.level_params.is_empty(), "no undeclared universe assumptions");
    for expression in [&info.type_, proof] {
        assert!(!expression.has_sorry(), "no sorry or trusted proof debt");
        assert!(!expression.has_fvar_quick(), "no open variables");
        assert!(!expression.has_loose_bvars_quick(), "closed universal declaration");
        // Elaborator expression metas are tagged FVars, not the kernel's
        // always-false has_expr_mvar_quick compatibility query.
        assert!(!MetaState::expr_has_meta(expression), "no tagged expression metas");
        assert!(!expression.has_level_mvar_quick(), "no unresolved universes");
    }

    // Construct the claim independently: forall p q : Prop, dp : Decidable p,
    // dq : Decidable q, decide (p or q) (instDecidableOr p q dp dq)
    // equals Bool.or (decide p dp) (decide q dq). This is not a finite sample.
    let constant = |name: &str| Expr::const_(Name::from_string(name), vec![]);
    let bd = || BinderData::from(BinderInfo::Default);
    let p = Expr::bvar(3);
    let q = Expr::bvar(2);
    let dp = Expr::bvar(1);
    let dq = Expr::bvar(0);
    let decide = |proposition, instance| Expr::apps(constant("Decidable.decide"), [proposition, instance]);
    let lhs = decide(
        Expr::apps(constant("Or"), [p.clone(), q.clone()]),
        Expr::apps(constant("instDecidableOr"), [p.clone(), q.clone(), dp.clone(), dq.clone()]),
    );
    let rhs = Expr::apps(constant("Bool.or"), [decide(p, dp), decide(q, dq)]);
    let equality = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [constant("Bool"), lhs, rhs],
    );
    let expected = Expr::pi(bd(), Expr::prop(), Expr::pi(bd(), Expr::prop(),
        Expr::pi(bd(), Expr::app(constant("Decidable"), Expr::bvar(1)),
            Expr::pi(bd(), Expr::app(constant("Decidable"), Expr::bvar(1)), equality))));
    let _budget = BridgeDeclBudgetScope::enter(BRIDGE_DECL_BUDGET);
    clean_kernel::tc::reset_declaration_budget();
    let mut checker = TypeChecker::with_mode(&env, env.mode());
    checker.set_level_params(info.level_params.clone());
    checker.check_type(&expected, &Expr::prop()).expect("universal claim is a proposition");
    assert!(checker.is_def_eq(&info.type_, &expected), "exact universal theorem type");
    checker.check_type(proof, &expected).expect("fresh current-kernel check of the actual proof");
    assert!(!clean_kernel::tc::declaration_budget_exhausted(), "fresh check must finish");
    let domain = env.axiom_deps(&name).expect("actual domain-axiom closure");
    let foundational = env.foundational_axiom_deps(&name).expect("actual foundational closure");
    assert!(domain.is_empty(), "unexpected domain axioms: {domain:?}");
    assert!(foundational.is_empty(), "unexpected foundational axioms: {foundational:?}");
    eprintln!("MULTI_SCRUTINEE_DECIDABLE_OR_IMPORTED_PASS universal=p,q,dp,dq arms=4 domain={domain:?} foundational={foundational:?} fresh_kernel=true");
}

/// A real imported-environment check of the exact production overflow layer.
/// It deliberately does not run the whole bridge or claim whole-closure replay.
#[cfg(test)]
pub(super) fn check_imported_overflow_layer_for_test() {
    let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
    let trustir = verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
        .expect("original actual TrustIR manifest");
    let core = verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
        .expect("original actual Lean-core manifest");
    // Bind these imported bytes to the actual selected source, with the same
    // source-reuse authority rule as production (never an expected-pin override).
    let checkout = resolve_trustir_checkout(&config.repo_root).expect("actual IR source pin");
    check_lean_sources_clean(&config.repo_root).expect("actual logical sources are clean");
    if trustir.source_reuse {
        let selected = trust_bridge_closure::source_reuse::verify(
            &config.repo_root,
            trust_bridge_closure::source_reuse::Subject::Checkout,
        )
        .expect("actual source-reuse authority")
        .expect("manifest source-reuse record");
        let selected =
            bind_source_reuse(selected, &trustir, &core).expect("exact captured manifests");
        assert_eq!(selected.trustir_commit, checkout);
    } else {
        assert_eq!(trustir.trustir_commit.as_deref(), Some(checkout.as_str()));
    }
    let mut env = Environment::default();
    env.ensure_native_reducers();
    let roots = BRIDGE_ROOT_MODULES.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>();
    load_verified_modules(&mut env, &roots, &trustir, &core)
        .expect("actual imported module closure");
    for name in load_bridge_source(&mut env, BRIDGE_INSTANCE_SRC).expect("original instances") {
        require_empty_axiom_deps(&env, &name).expect("no non-foundational instance residue");
    }
    // Only these three existing reductions are needed by the six value statements.
    for (name, source) in REDUCTION_SRCS.iter().take(3) {
        load_bridge_source(&mut env, source).unwrap_or_else(|error| panic!("{name}: {error}"));
        require_empty_axiom_deps(&env, name).expect("original value reduction residue");
    }
    predicate_registration_refusals(&env);
    let evidence = check_overflow_layer(&mut env, BridgeGateMode::Full)
        .expect("actual overflow production layer must check");
    eprintln!(
        "overflow layer: value_pins={:?}; flag_pins={:?}; predicate_pins={:?}",
        evidence.overflow_value_pinned_list,
        evidence.overflow_flag_pinned_list,
        evidence.overflow_umul_predicate_pinned
    );
    assert_eq!(evidence.overflow_value_bridged, 6);
    assert_eq!(evidence.overflow_flag_bridged, 6);
    assert_eq!(evidence.overflow_value_pinned, 0);
    assert_eq!(evidence.overflow_flag_pinned, 0);
    assert!(evidence.overflow_composed, "all twelve statements and four live links are required");
    assert_eq!(evidence.overflow_fail_closed_controls, 5);
    assert!(evidence.overflow_flag_unbridged.is_empty());
    assert!(evidence.overflow_umul_predicate_pinned.is_empty());
    assert_eq!(
        evidence.overflow_umul_predicates_bound,
        IrUWidth::ALL.into_iter().map(umul_overflows_ir_name).collect::<Vec<_>>()
    );
    assert_eq!(
        evidence.overflow_umul_predicate_bridged,
        IrUWidth::ALL.into_iter().map(predicate_theorem_name).collect::<Vec<_>>()
    );
    assert_eq!(evidence.overflow_umul_foundational_axioms, vec!["propext"]);
    assert_eq!(evidence.overflow_foundational_axioms, vec!["propext"]);
    let production =
        crate::trustir_safety::trustir_safety_env().expect("actual safety environment");
    for width in IrUWidth::ALL {
        let name = Name::from_string(&umul_overflows_ir_name(width));
        let actual = env.get_const(&name).expect("actual bridge registration");
        let safety = production.get_const(&name).expect("actual production registration");
        assert_eq!(actual.type_, safety.type_);
        assert_eq!(actual.value, safety.value, "one constructor must supply BOTH environments");
        register_unsigned_mul_predicate(&mut env, width).expect("exact registration is idempotent");
        require_empty_axiom_deps(&env, &predicate_theorem_name(width))
            .expect("no domain/trust residue");
    }
    // The new and an existing member are load-bearing in the actual composition.
    for (index, from, to) in [
        (0, "And.intro bridge_overflow_umul_flag", "And.intro bridge_overflow_uadd_flag"),
        (1, "And.intro bridge_overflow_smul_value", "And.intro bridge_overflow_sadd_value"),
    ] {
        assert_eq!(OVERFLOW_COMPOSED_SRC.matches(from).count(), 1);
        let source = OVERFLOW_COMPOSED_SRC
            .replace(from, to)
            .replace(OVERFLOW_COMPOSED_NAME, &format!("overflow_composed_wrong_member_{index}"));
        check_semantic_forgery_with_budget(
            &mut env,
            "wrong twelve-way composition member",
            &source,
            BRIDGE_DECL_BUDGET,
        )
        .expect("well-typed wrong member must be semantically refused");
    }
    eprintln!(
        "UMUL_INT_BRIDGE_PASS values=6 flags=6 predicates=4 composition=12 semantic_refusals=7 predicate_mutants=24 foundational=[propext] BV_equivalence=UNPROVED"
    );
}
