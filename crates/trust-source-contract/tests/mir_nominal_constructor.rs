//! Reflected-declaration custody; NOT a kernel AST quotation/source grade.
use trust_source_contract::observe_mir_nominal_constructor;
use trust_types::VerifiableFunction;
fn original() -> VerifiableFunction {
    serde_json::from_str(include_str!("fixtures/law-entry/proof_ref_kind_is_ambiguous.json"))
        .unwrap()
}
fn altered(edit: impl FnOnce(&mut serde_json::Value)) -> VerifiableFunction {
    let mut value = serde_json::to_value(original()).unwrap();
    edit(&mut value);
    serde_json::from_value(value).unwrap()
}
#[test]
fn all_original_declared_constructors_embed_and_execute_without_host_calls() {
    use trust_ir::interpret::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter};
    let f = original();
    let lean = include_str!("../lean/MirNominalSwitch.lean");
    let metadata = serde_json::to_value(&f.body.locals[1].ty).unwrap();
    assert_eq!(metadata["Adt"]["variants"].as_array().unwrap().len(), 16);
    let module = trust_ir_bridge::lower_to_trust_ir(&f).unwrap();
    assert_eq!(module.functions.len(), 1);
    assert_eq!(module.structs[0].name, "trust_ir::proof::obligations::ObligationKindShape");
    for ordinal in 0..16 {
        let c = observe_mir_nominal_constructor(&f, 1, ordinal).unwrap();
        assert!(std::ptr::eq(c.function(), &f));
        assert_eq!((c.parameter_local(), c.ordinal()), (1, ordinal));
        assert_eq!(c.nominal_name(), module.structs[0].name);
        assert_eq!(c.variant().discriminant, ordinal as i128);
        assert!(c.variant().fields.is_empty());
        assert!(lean.contains(&format!("⟨\"{}\",{}⟩", c.variant().name, c.variant().discriminant)));
        let value = InterpretValue::int(trust_ir::ty::Ty::I64, c.variant().discriminant).unwrap();
        assert_eq!(value.as_int().unwrap().as_unsigned(), u128::from(c.word()));
        let argument = InterpretValue {
            ty: module.func_types[0].params[0].clone(),
            kind: InterpretValueKind::Aggregate(vec![value]),
        };
        let result = Interpreter::with_module(&module)
            .with_options(InterpretOptions {
                fuel: 40,
                max_call_depth: 4,
                ..InterpretOptions::default()
            })
            .execute_func(module.functions[0].id, [argument])
            .unwrap();
        assert_eq!(result.host_calls, 0);
        assert_eq!(result.returns[0].as_bool(), Some(matches!(ordinal, 0..=5 | 8 | 9)));
    }
}
#[test]
fn exact_original_discriminant_and_ordered_switch_source_roles() {
    let f = original();
    let value = serde_json::to_value(&f).unwrap();
    let stmt = &value["body"]["blocks"][0]["stmts"][0]["Assign"];
    assert_eq!(stmt["place"], serde_json::json!({"local":3,"projections":[]}));
    assert_eq!(stmt["rvalue"]["Discriminant"], serde_json::json!({"local":1,"projections":[]}));
    assert_eq!(
        value["body"]["locals"][3]["ty"],
        serde_json::json!({"Int":{"width":64,"signed":true}})
    );
    let switch = &value["body"]["blocks"][0]["terminator"]["SwitchInt"];
    assert_eq!(switch["discr"], serde_json::json!({"Copy":{"local":3,"projections":[]}}));
    assert_eq!(
        switch["targets"],
        serde_json::json!([[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 6], [8, 7], [9, 8]])
    );
    assert_eq!(switch["otherwise"], 9);
}
#[test]
fn signed_noncontiguous_tags_are_observed_not_replaced_by_ordinals() {
    let f = altered(|v| {
        v["body"]["locals"][1]["ty"]["Adt"]["variants"][0]["discriminant"] = (-17).into();
        v["body"]["locals"][1]["ty"]["Adt"]["variants"][1]["discriminant"] = 1024.into();
    });
    let c = observe_mir_nominal_constructor(&f, 1, 0).unwrap();
    assert_eq!(c.variant().discriminant, -17);
    assert_eq!(c.word(), u64::MAX - 16);
    assert_eq!(observe_mir_nominal_constructor(&f, 1, 1).unwrap().word(), 1024);
    // This changed declaration is data; it cannot fit the original Lean declaration theorem.
}
#[test]
fn invalid_constructor_and_nonparameter_refuse() {
    let f = original();
    for (local, ordinal) in [(1, 16), (0, 0), (2, 0), (99, 0)] {
        assert!(observe_mir_nominal_constructor(&f, local, ordinal).is_none());
    }
}
#[test]
fn inactive_payload_variant_refuses_entire_declaration() {
    let f = altered(|v| {
        v["body"]["locals"][1]["ty"]["Adt"]["variants"][15]["fields"] =
            serde_json::json!([["x", "Bool"]])
    });
    assert!(observe_mir_nominal_constructor(&f, 1, 0).is_none());
}
#[test]
fn inactive_unrepresentable_tag_and_duplicate_tags_refuse() {
    let huge = altered(|v| {
        v["body"]["locals"][1]["ty"]["Adt"]["variants"][15]["discriminant"] =
            serde_json::json!(9223372036854775808u64)
    });
    assert!(observe_mir_nominal_constructor(&huge, 1, 0).is_none());
    let duplicate =
        altered(|v| v["body"]["locals"][1]["ty"]["Adt"]["variants"][15]["discriminant"] = 0.into());
    assert!(observe_mir_nominal_constructor(&duplicate, 1, 0).is_none());
}
#[test]
fn wrong_legacy_tag_type_and_faithful_route_refuse() {
    let wrong = altered(|v| v["body"]["locals"][1]["ty"]["Adt"]["fields"][0][1] = "Bool".into());
    assert!(observe_mir_nominal_constructor(&wrong, 1, 0).is_none());
    let faithful = altered(|v| {
        v["body"]["locals"][1]["ty"]["Adt"]["faithful_enum_repr"] =
            serde_json::json!({"state":"eligible_rust_default"})
    });
    assert!(observe_mir_nominal_constructor(&faithful, 1, 0).is_none());
}
#[test]
fn name_identity_and_resource_bounds_are_preserved() {
    let foreign =
        altered(|v| v["body"]["locals"][1]["ty"]["Adt"]["name"] = "foreign nominal".into());
    assert_eq!(
        observe_mir_nominal_constructor(&foreign, 1, 0).unwrap().nominal_name(),
        "foreign nominal"
    );
    let too_many = altered(|v| {
        let variant = v["body"]["locals"][1]["ty"]["Adt"]["variants"][0].clone();
        v["body"]["locals"][1]["ty"]["Adt"]["variants"] = vec![variant; 257].into();
    });
    assert!(observe_mir_nominal_constructor(&too_many, 1, 0).is_none());
}
