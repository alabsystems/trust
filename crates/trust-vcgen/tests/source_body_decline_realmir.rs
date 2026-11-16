//! Original product52 captures of the opaque-body and audited-provider N4
//! controls. The public compiler entry, not a reconstructed constructor, owns
//! the returned row shape. These inputs convey no proof or freshness authority.

use trust_types::fx::FxHashSet;
use trust_types::vc_context::VcContext;
use trust_types::{Formula, VerifiableFunction, VerificationCondition};

#[test]
fn captured_opaque_decline_preserves_non_proving_row_through_consumed_generation() {
    let function: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/source_body_decline/opaque_identity_mir.json"))
            .unwrap();
    let context = trust_vcgen::VcgenContext::for_function(function.def_path.clone());
    let mut rows = VcContext::new();
    let generated = trust_vcgen::generate_vcs_with_discharge_and_overflow_origins(
        &function,
        &trust_vcgen::SummaryDatabase::new(),
        false,
        &context,
        &FxHashSet::<(trust_types::BlockId, usize)>::default(),
        &mut rows,
    );
    let declines: Vec<_> = generated
        .solver_vcs
        .iter()
        .filter(|vc| vc.kind.declined_contract_body().is_some())
        .collect();
    assert_eq!(declines.len(), 1, "retain the actual unsupported source question");
    let vc = declines[0];
    assert_eq!(vc.formula, Formula::Bool(true), "a decline is not a solver goal");
    let decline = vc.kind.declined_contract_body().unwrap();
    assert_eq!(decline.source_contract_index, 0);
    assert_eq!(decline.source_predicate, function.postconditions[0]);
    assert!(vc.kernel_authority_refusal().is_some());
    assert!(trust_certify::certify_vc(vc).is_none());
    assert!(generated.discharged.iter().all(|(vc, _)| vc.kind.declined_contract_body().is_none()));
    let (raw, augmented) =
        trust_vcgen::regenerate_postcondition_production_variants(&function).unwrap();
    let raw = raw.iter().find(|vc| vc.kind.declined_contract_body().is_some()).unwrap();
    let augmented = augmented.iter().find(|vc| vc.kind.declined_contract_body().is_some()).unwrap();
    assert_eq!(serde_json::to_value(raw).unwrap(), serde_json::to_value(vc).unwrap());
    assert_eq!(serde_json::to_value(augmented).unwrap(), serde_json::to_value(vc).unwrap());
}

#[test]
fn captured_provider_body_has_its_own_replayable_kernel_certificate() {
    let vc: VerificationCondition = serde_json::from_str(include_str!(
        "fixtures/source_body_decline/provider_add1_body_vc.json"
    ))
    .unwrap();
    let (evidence, stop) = trust_certify::certify_vc_reporting_stop(&vc);
    assert!(stop.is_none(), "certification stopped: {stop:?}");
    let evidence = evidence.expect("the actual body goal needs independently checked evidence");
    assert!(trust_certify::replay_vc_evidence(&vc, &evidence));
    assert!(trust_certify::replay_presented_vc_evidence(&vc, &evidence));
    let mut changed = vc.clone();
    changed.formula = Formula::Bool(true);
    assert!(!trust_certify::replay_vc_evidence(&changed, &evidence));
    assert!(!trust_certify::replay_presented_vc_evidence(&changed, &evidence));
}

#[test]
fn declined_body_never_acquires_an_interval_proof_or_rewritten_sentinel() {
    use trust_vcgen::{
        AbstractDomain, AbstractInterpResult, Interval, IntervalDomain,
        augment_vc_with_abstract_state, try_discharge_vc,
    };
    let function: VerifiableFunction =
        serde_json::from_str(include_str!("fixtures/source_body_decline/opaque_identity_mir.json"))
            .unwrap();
    let mut vc = trust_vcgen::generate_vcs(&function)
        .into_iter()
        .find(|vc| vc.kind.declined_contract_body().is_some())
        .unwrap();
    let mut bounded = IntervalDomain::top();
    bounded.set("x".into(), Interval::new(0, 255));
    for env in [IntervalDomain::top(), bounded, IntervalDomain::bottom()] {
        for formula in [Formula::Bool(true), Formula::Bool(false)] {
            vc.formula = formula;
            assert!(matches!(try_discharge_vc(&vc, &env), AbstractInterpResult::Undetermined));
            assert_eq!(
                serde_json::to_value(augment_vc_with_abstract_state(&vc, &env)).unwrap(),
                serde_json::to_value(&vc).unwrap(),
            );
            assert!(trust_certify::certify_vc(&vc).is_none());
        }
    }
}

fn bv(name: &str) -> Formula {
    Formula::Var(name.into(), trust_types::Sort::BitVec(32))
}

fn add_one() -> Formula {
    Formula::BvAdd(Box::new(bv("x")), Box::new(Formula::BitVec { value: 1, width: 32 }), 32)
}

fn equality(left: Formula, right: Formula) -> Formula {
    Formula::Eq(Box::new(left), Box::new(right))
}

fn equality_vc(formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind: trust_types::VcKind::Postcondition,
        function: "bv_equality_control".into(),
        location: Default::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

#[test]
fn bv_equality_certificate_replays_exact_context_and_full_goal_identity() {
    for reversed in [false, true] {
        let relation = if reversed {
            equality(add_one(), bv("temporary"))
        } else {
            equality(bv("temporary"), add_one())
        };
        let vc = equality_vc(Formula::And(vec![
            relation,
            equality(bv("temporary"), bv("result")),
            Formula::Not(Box::new(equality(bv("result"), add_one()))),
        ]));
        let evidence = trust_certify::certify_vc(&vc).expect("equality transitivity only");
        assert!(trust_certify::replay_presented_vc_evidence(&vc, &evidence));
        assert!(trust_certify::replay_vc_evidence(&vc, &evidence));
        let mut foreign = vc.clone();
        foreign.function = "different_goal".into();
        assert!(!trust_certify::replay_presented_vc_evidence(&foreign, &evidence));
        let mut changed = vc.clone();
        changed.formula = Formula::Not(Box::new(equality(bv("result"), add_one())));
        assert!(!trust_certify::replay_presented_vc_evidence(&changed, &evidence));
        for field in ["term", "context"] {
            let mut encoded = serde_json::to_value(&evidence).unwrap();
            let payload = encoded
                .get_mut("CleanCic")
                .and_then(|value| value.get_mut(field))
                .expect("the actual Clean kernel carrier");
            *payload = serde_json::json!([]);
            let corrupt = serde_json::from_value(encoded).unwrap();
            assert!(!trust_certify::replay_presented_vc_evidence(&vc, &corrupt));
        }
    }
}

#[test]
fn bv_equality_certificate_refuses_missing_hidden_or_different_equalities() {
    let different =
        Formula::BvAdd(Box::new(bv("x")), Box::new(Formula::BitVec { value: 2, width: 32 }), 32);
    let eq = equality(bv("result"), add_one());
    for formula in [
        Formula::Not(Box::new(eq.clone())),
        Formula::And(vec![
            Formula::Or(vec![eq.clone(), Formula::Bool(true)]),
            Formula::Not(Box::new(eq.clone())),
        ]),
        Formula::And(vec![
            eq,
            equality(bv("other"), different),
            Formula::Not(Box::new(equality(bv("result"), bv("other")))),
        ]),
        Formula::And(vec![
            equality(
                bv("result"),
                Formula::Var("wrong_width".into(), trust_types::Sort::BitVec(8)),
            ),
            Formula::Not(Box::new(equality(bv("result"), add_one()))),
        ]),
    ] {
        assert!(trust_certify::certify_vc(&equality_vc(formula)).is_none());
    }
}
