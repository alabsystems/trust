//! Imported notation class metadata is not a missing-registry fallback.
//! Uses the real manifest-bound imported context, not fresh declaration replay
//! or a qualification of generic metadata decoding/native execution.

use clean_kernel::env::KernelClassInfo;
use clean_kernel::{BinderInfo, ExprKind};

use super::*;

const CLASS_NAMES: [&str; 11] =
    ["LE", "LT", "Decidable", "HAdd", "HSub", "HMul", "HMod", "HPow", "Neg", "OfNat", "BEq"];

fn class_metadata(env: &Environment) -> [KernelClassInfo; 11] {
    CLASS_NAMES.map(|class| {
        env.get_class_info(&Name::from_string(class))
            .unwrap_or_else(|| panic!("manifest import did not restore class {class}"))
            .clone()
    })
}

#[test]
fn imported_notation_classes_survive_duplicate_refusal_and_checked_aliases() {
    let config = BridgeGateConfig::locate(BridgeGateMode::Spot);
    let trustir = verify_manifest(&config.trustir_olean_dir, TRUSTIR_MANIFEST_SCHEMA, true)
        .expect("actual TrustIr manifest");
    let core = verify_manifest(&config.lean_core_olean_dir, LEAN_CORE_MANIFEST_SCHEMA, false)
        .expect("actual Lean-core manifest");
    let mut env = Environment::default();
    env.ensure_native_reducers();
    for class in CLASS_NAMES {
        assert!(env.get_class_info(&Name::from_string(class)).is_none(), "fresh context: {class}");
    }
    let roots = BRIDGE_ROOT_MODULES.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>();
    let summaries = load_verified_modules(&mut env, &roots, &trustir, &core)
        .expect("actual complete manifest-verified closure");
    let loaded = summaries
        .iter()
        .filter_map(|summary| summary.module_name.as_ref())
        .map(|module| module.replace('.', "/") + ".olean")
        .collect::<BTreeSet<_>>();
    assert_eq!(loaded, trustir.files.union(&core.files).cloned().collect::<BTreeSet<_>>());
    let imported = class_metadata(&env);

    // Imported declarations carry binder kinds in their Pi type. The separate
    // surface-declaration parameter cache is optional for this import lane.
    let decide_name = Name::from_string("decide_eq_decide");
    let surface_binders = env.get_param_binder_infos(&decide_name).map(<[_]>::to_vec);
    let mut imported_type =
        env.get_const(&decide_name).expect("actual imported decide congruence").type_.clone();
    let mut type_binders = Vec::new();
    while let ExprKind::Pi(data, _, body) = imported_type.kind() {
        type_binders.push(data.info);
        imported_type = (**body).clone();
    }
    assert_eq!(type_binders, vec![BinderInfo::Implicit; 4]);
    if let Some(kinds) = &surface_binders {
        assert_eq!(kinds, &type_binders, "surface metadata must match the imported theorem type");
    }

    // The obsolete source workaround must remain a real semantic refusal,
    // not an accepted/idempotent command or a spent elaboration budget.
    let mut refusals = Vec::new();
    let refusal = load_bridge_source_with_budget_observed(
        &mut env,
        "attribute [class] LE\n",
        BRIDGE_DECL_BUDGET,
        |error, incomplete| {
            let duplicate_le = matches!(
                error,
                clean_elab::ElabError::ClassAlreadyDeclared { name }
                    if name == &Name::from_string("LE")
            );
            refusals.push((duplicate_le, incomplete));
        },
    )
    .expect_err("an imported class must not be redeclared");
    assert_eq!(refusals, [(true, false)], "unexpected refusal: {refusal}");
    assert_eq!(class_metadata(&env), imported, "duplicate refusal changed imported metadata");

    let aliases = load_bridge_source(&mut env, BRIDGE_INSTANCE_SRC)
        .expect("unchanged checked aliases must use the imported classes");
    assert_eq!(
        aliases.iter().map(String::as_str).collect::<Vec<_>>(),
        vec![
            "bridgeIntLE",
            "bridgeIntLT",
            "bridgeIntDecLe",
            "bridgeIntDecLt",
            "bridgeIntDecLeNotation",
            "bridgeIntDecLtNotation",
            "bridgeIntDecGeNotation",
            "bridgeIntAdd",
            "bridgeIntSub",
            "bridgeNatSub",
            "bridgeIntMul",
            "bridgeIntMod",
            "bridgeIntPow",
            "bridgeIntNeg",
            "bridgeIntOfNat",
            "bridgeNatOfNat",
            "bridgeIntDecEq",
            "bridgeBoolDecEq",
            "bridgeIntBEq",
            "bridgeTyBEq",
        ]
    );
    for name in aliases {
        require_empty_axiom_deps(&env, &name)
            .expect("notation alias has no non-foundational axiom residue");
    }
    assert_eq!(class_metadata(&env), imported, "aliases changed imported class metadata");

    let mut old_call_refusals = Vec::new();
    load_bridge_source_with_budget_observed(
        &mut env,
        r#"theorem bridge_threshold_obsolete_call (half exact : Int) :
            Decidable.decide (half - 1 < exact) = Decidable.decide (half ≤ exact) :=
          (decide_eq_decide (half - 1 < exact) (half ≤ exact)).mpr
            (Iff.intro
              (fun (h : half - 1 < exact) => Int.le_of_sub_one_lt h)
              (fun (h : half ≤ exact) => Int.sub_one_lt_of_le h))
"#,
        BRIDGE_DECL_BUDGET,
        |error, incomplete| {
            old_call_refusals.push((
                matches!(error, clean_elab::ElabError::TooManyArguments { .. }),
                incomplete,
            ));
        },
    )
    .expect_err("positional arguments cannot reapply Lean's already inserted implicit parameters");
    assert_eq!(old_call_refusals, [(true, false)]);
    assert!(env.get_const(&Name::from_string("bridge_threshold_obsolete_call")).is_none());

    let thresholds = load_bridge_source(&mut env, OVERFLOW_THRESHOLD_PRELUDE_SRC)
        .expect("explicit imported propositions and decisions must kernel-check");
    assert_eq!(thresholds, ["overflow_threshold_iff2", "overflow_threshold_decide_eq"]);
    for name in thresholds {
        let info = env.get_const(&Name::from_string(&name)).expect("checked threshold theorem");
        let proof = info.value.as_ref().expect("actual threshold proof body");
        assert!(!proof.has_sorry() && !proof.has_fvar_quick() && !proof.has_loose_bvars_quick());
        let _budget = BridgeDeclBudgetScope::enter(BRIDGE_DECL_BUDGET);
        clean_kernel::tc::reset_declaration_budget();
        let mut checker = TypeChecker::with_mode(&env, env.mode());
        checker.set_level_params(info.level_params.clone());
        checker.check_type(proof, &info.type_).expect("fresh current-kernel threshold proof check");
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        require_empty_axiom_deps(&env, &name).expect("threshold theorem has no axiom residue");
    }
    assert_eq!(class_metadata(&env), imported, "threshold proofs changed imported classes");
    assert_eq!(env.get_param_binder_infos(&decide_name), surface_binders.as_deref());
    checked_stepbranch_agreement(&mut env);
    checked_unsigned_subtraction_flag(&mut env);
    assert_eq!(
        class_metadata(&env),
        imported,
        "unsigned-subtraction proof changed imported classes"
    );
}

fn checked_unsigned_subtraction_flag(env: &mut Environment) {
    // The bridge manifest pins Lean4.8: p/Decidable, not_le's endpoints and
    // sub_le_self's b are implicit. Original Pi types are the import authority;
    // the separate surface-parameter cache may legitimately be absent.
    let signatures = [
        (
            "decide_eq_false",
            vec![BinderInfo::Implicit, BinderInfo::InstImplicit, BinderInfo::Default],
        ),
        ("Int.not_le", vec![BinderInfo::Implicit, BinderInfo::Implicit]),
        ("Int.sub_le_self", vec![BinderInfo::Default, BinderInfo::Implicit, BinderInfo::Default]),
    ];
    let mut surface_metadata = Vec::new();
    for (name, expected) in signatures {
        let name = Name::from_string(name);
        let mut ty =
            env.get_const(&name).expect("actual imported order/decision theorem").type_.clone();
        let mut kinds = Vec::new();
        while let ExprKind::Pi(data, _, body) = ty.kind() {
            kinds.push(data.info);
            ty = (**body).clone();
        }
        assert_eq!(kinds, expected, "actual imported binder signature: {name}");
        let surface = env.get_param_binder_infos(&name).map(<[_]>::to_vec);
        if let Some(surface) = &surface {
            assert_eq!(surface, &expected, "surface metadata must match imported type: {name}");
        }
        surface_metadata.push((name, surface));
    }

    let mut old_call_refusals = Vec::new();
    load_bridge_source_with_budget_observed(
        env,
        "theorem bridge_usub_obsolete_decide_call (p : Prop) [Decidable p] (h : ¬ p) : \
         Decidable.decide p = false := decide_eq_false p h",
        BRIDGE_DECL_BUDGET,
        |error, incomplete| {
            old_call_refusals
                .push((matches!(error, clean_elab::ElabError::TypeMismatch { .. }), incomplete));
        },
    )
    .expect_err("the proposition is not the explicit negation-proof argument");
    assert_eq!(old_call_refusals, [(true, false)]);
    assert!(env.get_const(&Name::from_string("bridge_usub_obsolete_decide_call")).is_none());

    let arm = OVERFLOW_FLAG_ARMS
        .iter()
        .find(|arm| arm.op == "SubOverflow" && !arm.signed)
        .expect("original unsigned subtraction flag obligation");
    assert!(arm.form == ArmForm::BGuarded, "both original arithmetic hypotheses remain required");
    for (source, expected) in [
        (arm.reduces_src, arm.reduces_theorem),
        (arm.extra_src, "overflow_usub_flag_vacuous"),
        (arm.connect_src, arm.connect_theorem),
    ] {
        let names =
            load_bridge_source(env, source).expect("exact production unsigned-subtraction proof");
        assert_eq!(names, [expected]);
        let info = env
            .get_const(&Name::from_string(expected))
            .expect("actual checked unsigned-subtraction theorem");
        let proof = info.value.as_ref().expect("actual checked proof body");
        assert!(!proof.has_sorry() && !proof.has_fvar_quick() && !proof.has_loose_bvars_quick());
        let _budget = BridgeDeclBudgetScope::enter(BRIDGE_DECL_BUDGET);
        clean_kernel::tc::reset_declaration_budget();
        let mut checker = TypeChecker::with_mode(env, env.mode());
        checker.set_level_params(info.level_params.clone());
        checker
            .check_type(proof, &info.type_)
            .expect("fresh current-kernel unsigned-subtraction check");
        assert!(!clean_kernel::tc::declaration_budget_exhausted());
        require_empty_axiom_deps(env, expected)
            .expect("unsigned-subtraction theorem has no axiom residue");
    }
    for (name, surface) in surface_metadata {
        assert_eq!(env.get_param_binder_infos(&name), surface.as_deref());
    }
}

fn checked_stepbranch_agreement(env: &mut Environment) {
    // Lean's recursor motive is implicit; @ exposes it without changing the
    // branch obligations or the fully explicit Expr emitted by clean_ground.
    let recursor = Name::from_string("Bool.rec");
    let mut ty = env.get_const(&recursor).expect("actual imported Bool recursor").type_.clone();
    let mut kinds = Vec::new();
    while let ExprKind::Pi(data, _, body) = ty.kind() {
        kinds.push(data.info);
        ty = (**body).clone();
    }
    assert_eq!(
        kinds,
        [BinderInfo::Implicit, BinderInfo::Default, BinderInfo::Default, BinderInfo::Default,]
    );
    let surface = env.get_param_binder_infos(&recursor).map(<[_]>::to_vec);
    if let Some(surface) = &surface {
        assert_eq!(surface, &kinds, "surface metadata must match the imported recursor type");
    }
    for guard in ["true", "false"] {
        let name = format!("bridge_bool_rec_obsolete_{guard}");
        let source = format!(
            "theorem {name} (e t : Int) : \
             (Bool.rec (fun _ => Int) e t {guard} : Int) = \
             {} := rfl",
            if guard == "true" { "t" } else { "e" }
        );
        let mut refusals = Vec::new();
        load_bridge_source_with_budget_observed(
            env,
            &source,
            BRIDGE_DECL_BUDGET,
            |error, incomplete| {
                refusals
                    .push((matches!(error, clean_elab::ElabError::TypeMismatch { .. }), incomplete))
            },
        )
        .expect_err("an implicit motive cannot be supplied as the first minor premise");
        assert_eq!(refusals, [(true, false)], "original malformed {guard} caller");
        assert!(env.get_const(&Name::from_string(&name)).is_none());
    }

    let fixtures = load_bridge_source(env, STEPBRANCH_FIXTURES_SRC)
        .expect("exact production CFG and both explicit-motive recursor helpers");
    assert_eq!(
        fixtures,
        [
            "branchBlockGuard",
            "branchBlockThen",
            "branchBlockElse",
            "branchCfg",
            "bool_rec_true",
            "bool_rec_false",
        ]
    );
    for name in fixtures {
        recheck_stepbranch_declaration(env, &name);
    }
    assert_eq!(STEPBRANCH_ARMS.iter().map(|arm| arm.guard).collect::<Vec<_>>(), ["true", "false"]);
    for arm in STEPBRANCH_ARMS {
        for (source, name) in
            [(arm.chain_src, arm.chain_theorem), (arm.connect_src, arm.connect_theorem)]
        {
            assert_eq!(
                load_bridge_source(env, source)
                    .unwrap_or_else(|error| panic!("{}: {name}: {error}", arm.guard)),
                [name]
            );
            recheck_stepbranch_declaration(env, name);
        }
    }
    assert_eq!(
        load_bridge_source(env, STEPBRANCH_COMPOSED_SRC)
            .expect("both original branch arms must compose"),
        [STEPBRANCH_COMPOSED_NAME]
    );
    recheck_stepbranch_declaration(env, STEPBRANCH_COMPOSED_NAME);
    assert_eq!(STEPBRANCH_FORGERY_PROBES.len(), 2);
    for (label, source) in STEPBRANCH_FORGERY_PROBES {
        check_semantic_forgery_with_budget(env, label, source, BRIDGE_DECL_BUDGET)
            .unwrap_or_else(|error| panic!("{label}: {error}"));
    }
    assert_eq!(env.get_param_binder_infos(&recursor), surface.as_deref());
}

fn recheck_stepbranch_declaration(env: &Environment, name: &str) {
    let info = env.get_const(&Name::from_string(name)).expect("actual checked branch declaration");
    let body = info.value.as_ref().expect("actual branch declaration body");
    assert!(!body.has_sorry() && !body.has_fvar_quick() && !body.has_loose_bvars_quick());
    let _budget = BridgeDeclBudgetScope::enter(BRIDGE_DECL_BUDGET);
    clean_kernel::tc::reset_declaration_budget();
    let mut checker = TypeChecker::with_mode(env, env.mode());
    checker.set_level_params(info.level_params.clone());
    checker.check_type(body, &info.type_).expect("fresh current-kernel branch declaration check");
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    require_empty_axiom_deps(env, name).expect("branch declaration has no axiom residue");
}
