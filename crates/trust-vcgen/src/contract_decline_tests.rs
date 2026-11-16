//! Native producer regression from the unchanged opaque-body SDK failure.

use trust_types::{ContractBodyDeclineCause, Formula, VerifiableFunction};

#[test]
fn native_owned_augmentation_preserves_the_actual_nonproving_decline() {
    let function: VerifiableFunction =
        serde_json::from_str(include_str!("../testdata/native-opaque-return-call-53c.json"))
            .expect("unchanged native 53c opaque CHECK capture");
    let raw = crate::generate_vcs(&function);
    let decline = raw.iter().find(|vc| vc.kind.declined_contract_body().is_some()).unwrap();
    assert_eq!(decline.formula, Formula::Bool(true));
    let (solver, discharged) = crate::generate_vcs_with_discharge(&function);
    let produced = solver
        .iter()
        .chain(discharged.iter().map(|(vc, _)| vc))
        .filter(|vc| vc.kind.declined_contract_body().is_some())
        .collect::<Vec<_>>();
    assert_eq!(produced.len(), 1);
    assert_eq!(
        serde_json::to_vec(produced[0]).unwrap(),
        serde_json::to_vec(decline).unwrap(),
        "the production owned path must preserve the exact current non-proving source question"
    );
    assert!(discharged.iter().all(|(vc, result)| {
        vc.kind.declined_contract_body().is_none()
            || !matches!(result, trust_types::VerificationResult::Proved { .. })
    }));

    let ranges = &function.preconditions[0];
    for formula in [Formula::Bool(true), Formula::Bool(false)] {
        let mut offered = (*decline).clone();
        offered.formula = formula;
        let original = serde_json::to_vec(&offered).unwrap();
        let allocation = offered.location.file.as_ptr();
        let (retained, changed) =
            crate::abstract_interp::discharge::augment_owned_vc_with_env_formula(offered, ranges);
        assert!(!changed);
        assert_eq!(retained.location.file.as_ptr(), allocation, "original owned allocation");
        assert_eq!(serde_json::to_vec(&retained).unwrap(), original);
        assert!(retained.kernel_authority_refusal().is_some());
    }
    let ordinary = trust_types::VerificationCondition {
        kind: trust_types::VcKind::DivisionByZero,
        formula: Formula::Eq(
            Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        contract_metadata: None,
        ..(*decline).clone()
    };
    let before = ordinary.formula.clone();
    let (augmented, changed) =
        crate::abstract_interp::discharge::augment_owned_vc_with_env_formula(ordinary, ranges);
    assert!(changed);
    assert_ne!(augmented.formula, before, "ordinary semantic VCs still receive range facts");
}

#[test]
fn native_unconstrained_return_decline_retains_authored_predicate() {
    // Captured through the maintained e560 --dump-verifier-inputs normal
    // Cargo-check path. The fixture preserves actual sysroot identity and MIR;
    // neither it nor this test supplies proof or runtime authority.
    let function: VerifiableFunction =
        serde_json::from_str(include_str!("../testdata/native-opaque-return-call-e560.json"))
            .expect("actual compiler function capture");
    let rows = crate::generate_vcs(&function);
    let source_rows = rows
        .iter()
        .filter(|row| {
            row.contract_metadata.and_then(|metadata| metadata.source_contract_index) == Some(0)
        })
        .collect::<Vec<_>>();
    assert_eq!(source_rows.len(), 1, "actual capture must reach its one source-indexed refusal");
    let retained = source_rows
        .into_iter()
        .filter_map(|row| row.kind.declined_contract_body().map(|decline| (row, decline)))
        .collect::<Vec<_>>();
    assert_eq!(retained.len(), 1, "one real typed body decline must retain the authored question");
    let (row, decline) = retained[0];
    assert_eq!(decline.source_contract_index, 0);
    assert_eq!(decline.cause, ContractBodyDeclineCause::UnconstrainedReturnCall);
    assert_eq!(decline.source_predicate, function.postconditions[0]);
    assert_eq!(row.formula, Formula::Bool(true), "the refusal query remains non-proving");
    assert!(row.kernel_authority_refusal().is_some(), "a declined body cannot mint proof");

    // Production now shares one environment formula across a whole batch.
    // Both entries must retain the exact non-proving refusal, including a
    // malformed sentinel that augmentation must never repair into evidence.
    let env = crate::abstract_interp::IntervalDomain {
        vars: std::collections::BTreeMap::from([(
            "x".to_string(),
            crate::abstract_interp::Interval::constant(7),
        )]),
        is_unreachable: false,
    };
    let mut malformed = (*row).clone();
    malformed.formula = Formula::Bool(false);
    let ordinary = trust_types::VerificationCondition {
        kind: trust_types::VcKind::DivisionByZero,
        formula: Formula::Eq(
            Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        contract_metadata: None,
        obligation: None,
        ..(*row).clone()
    };
    let augmented = crate::abstract_interp::augment_batch(
        &[(*row).clone(), malformed.clone(), ordinary.clone()],
        &env,
    );
    assert_eq!(serde_json::to_value(&augmented[0]).unwrap(), serde_json::to_value(row).unwrap());
    assert_eq!(
        serde_json::to_value(&augmented[1]).unwrap(),
        serde_json::to_value(&malformed).unwrap()
    );
    assert_ne!(augmented[2].formula, ordinary.formula, "ordinary VCs still receive batch facts");
    assert_eq!(
        serde_json::to_value(crate::abstract_interp::augment_vc_with_abstract_state(row, &env))
            .unwrap(),
        serde_json::to_value(row).unwrap(),
    );
}

#[test]
fn native_unconstrained_return_decline_refuses_unbound_and_constrained_cases() {
    use trust_types::{ConstValue, Operand, Place, Rvalue, Statement, Terminator, VcKind};
    let capture = || -> VerifiableFunction {
        serde_json::from_str(include_str!("../testdata/native-opaque-return-call-e560.json"))
            .unwrap()
    };
    let mut non_sysroot = capture();
    let Terminator::Call { callee_key, .. } = &mut non_sysroot.body.blocks[0].terminator else {
        panic!("actual capture's call");
    };
    callee_key.as_mut().unwrap().krate_is_real_sysroot = false;
    let mut unbound = capture();
    unbound.contracts.clear();
    let mut pinned = capture();
    pinned.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 8))),
        span: pinned.span.clone(),
    });
    for function in [&non_sysroot, &unbound, &pinned] {
        let rows = crate::generate_vcs(function);
        assert!(rows.iter().all(|row| row.kind.declined_contract_body().is_none()));
    }
    // A conservative return does not block a predicate independent of it.
    // Preserve a meaningful postcondition instead of rejecting the function
    // merely because an unrelated call is outside the body encoding.
    let mut independent = capture();
    independent.contracts[0].body = "__trust_lowered_compiler_contract__:x >= 0".into();
    independent.spec.ensures = vec!["x >= 0".into()];
    independent.postconditions = vec![Formula::Ge(
        Box::new(Formula::Var("x".into(), trust_types::Sort::Int)),
        Box::new(Formula::Int(0)),
    )];
    let rows = crate::generate_vcs(&independent);
    assert!(rows.iter().any(|row| matches!(row.kind, VcKind::Postcondition)));
    assert!(rows.iter().all(|row| row.kind.declined_contract_body().is_none()));
}

/// VCGEN-PERF-67-69-VERDICTS-1: the production solver-dispatch path augments
/// through the OWNED spelling (`generate::discharge`), the regeneration path
/// through the borrowed one (`augment_batch`). Both must leave a typed decline
/// byte-identical under every environment — bounded, unreachable (`Bool(false)`,
/// which would otherwise make the sentinel an UNSAT `false` conjunction) and
/// Top — while an ordinary row in the same batch is still augmented by both.
/// On main `fc561eba99` the owned spelling had no decline exemption, so the
/// bounded and unreachable cases returned `(And([env, Bool(true)]), true)`.
#[test]
fn both_augmentation_spellings_leave_a_typed_decline_untouched() {
    use trust_types::Sort;

    use crate::abstract_interp::discharge::augment_owned_vc_with_env_formula;
    let function: VerifiableFunction =
        serde_json::from_str(include_str!("../testdata/native-opaque-return-call-e560.json"))
            .unwrap();
    let rows = crate::generate_vcs(&function);
    let decline = rows
        .iter()
        .find(|row| row.kind.declined_contract_body().is_some())
        .expect("the actual capture's typed decline")
        .clone();
    let bounded = Formula::And(vec![
        Formula::Ge(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(0))),
        Formula::Le(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(255))),
    ]);
    let ordinary = trust_types::VerificationCondition {
        kind: trust_types::VcKind::DivisionByZero,
        formula: Formula::Eq(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(0)),
        ),
        contract_metadata: None,
        obligation: None,
        ..decline.clone()
    };
    for env in [bounded, Formula::Bool(false), Formula::Bool(true)] {
        let (owned, changed) = augment_owned_vc_with_env_formula(decline.clone(), &env);
        assert!(!changed, "the owned spelling must not touch a typed decline under {env:?}");
        assert_eq!(
            serde_json::to_value(&owned).unwrap(),
            serde_json::to_value(&decline).unwrap(),
            "owned spelling, env {env:?}"
        );
        let (ordinary_owned, ordinary_changed) =
            augment_owned_vc_with_env_formula(ordinary.clone(), &env);
        let top = env == Formula::Bool(true);
        assert_eq!(ordinary_changed, !top, "an ordinary row is augmented unless env is Top");
        if !top {
            assert_eq!(
                ordinary_owned.formula,
                Formula::And(vec![env.clone(), ordinary.formula.clone()]),
            );
        }
    }
}
