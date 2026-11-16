//! Actual frozen9794 source/query/body capture. This tests generator parity;
//! the candidate call input below conveys no proof authority.

#[test]
fn actual_inferred_return_group_uses_the_production_row_passes() {
    let capture: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/actual-inferred-source-group.json")).unwrap();
    let caller: trust_types::VerifiableFunction =
        serde_json::from_value(capture["caller"]["function"].clone()).unwrap();
    let query: trust_types::CompilerContractBundle =
        serde_json::from_value(capture["caller"]["compiler_contracts"].clone()).unwrap();
    let callee: trust_types::VerifiableFunction =
        serde_json::from_value(capture["callee"]["function"].clone()).unwrap();
    let identity = serde_json::from_value(capture["callee"]["callee_identity"].clone()).unwrap();
    let original: trust_types::VerificationCondition =
        serde_json::from_value(capture["original_body_vc"].clone()).unwrap();
    let candidate = trust_vcgen::infer_return_candidate(&callee).unwrap();
    let input = trust_vcgen::InferredReturnCall::new(identity, &candidate).unwrap();
    let (raw, augmented) =
        trust_vcgen::regenerate_postcondition_production_variants_with_inferred_calls(
            &caller,
            std::slice::from_ref(&input),
        )
        .unwrap();
    assert_eq!(raw.len(), 1);
    assert_eq!(augmented.len(), 1);
    assert_eq!(serde_json::to_vec(&raw[0]).unwrap(), serde_json::to_vec(&original).unwrap());
    let matches = |vcs: &[trust_types::VerificationCondition]| {
        trust_source_contract::exact_boolean_ensures_body_group_with_inferred_calls(
            &caller,
            &query,
            0,
            vcs,
            Some(64),
            std::slice::from_ref(&input),
        )
    };
    assert_eq!(matches(std::slice::from_ref(&original)).unwrap().body_indices(), &[0]);
    assert_eq!(
        trust_source_contract::exact_ensures_body_group(
            &caller,
            &query,
            0,
            std::slice::from_ref(&original),
            Some(64),
            Some(std::slice::from_ref(&input)),
        )
        .unwrap()
        .body_indices(),
        &[0]
    );
    assert!(matches(&[]).is_none());
    let mut changed = original;
    changed.formula = trust_types::Formula::Bool(false);
    assert!(matches(&[changed]).is_none());
}
