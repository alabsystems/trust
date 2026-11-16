use trust_types::{Place, VerifiableFunction};

use super::{bounds, guarded_result_read};

fn fixture() -> serde_json::Value {
    serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/monotone_counter_tables_mir.json"
    )))
    .expect("actual stage1 MIR fixture")
}

fn decode(value: serde_json::Value) -> VerifiableFunction {
    serde_json::from_value(value).expect("fixture schema")
}

#[test]
fn checked_counter_success_edge_preserves_original_lower_bound() {
    let func = decode(fixture());
    assert!(guarded_result_read(&func, 12, 6));
    assert_eq!(bounds(&func, 2), (Some(1), None));
    let map = crate::generate::type_ranges::local_value_join_interval_map(&func);
    let name = crate::place_to_var_name(&func, &Place::local(2));
    assert_eq!(map.get(&name), Some(&(Some(1), None)));
}

#[test]
fn projection_before_its_overflow_assert_has_no_global_lower_bound() {
    let mut value = fixture();
    value["body"]["blocks"][0]["stmts"][1]["Assign"]["rvalue"]["Use"]["Constant"]["Uint"][0] =
        serde_json::json!(u64::MAX);
    let read = value["body"]["blocks"][6]["stmts"][0].clone();
    value["body"]["blocks"][6]["stmts"] = serde_json::json!([]);
    value["body"]["blocks"][5]["stmts"].as_array_mut().expect("statements").push(read);
    let func = decode(value);
    assert!(!guarded_result_read(&func, 12, 5));
    assert_eq!(bounds(&func, 2), (None, None));
    let map = crate::generate::type_ranges::local_value_join_interval_map(&func);
    let name = crate::place_to_var_name(&func, &Place::local(2));
    assert!(!map.contains_key(&name));
}

#[test]
fn projection_on_failed_assert_cleanup_has_no_global_lower_bound() {
    let mut value = fixture();
    let read = value["body"]["blocks"][6]["stmts"][0].clone();
    value["body"]["blocks"][5]["terminator"]["Assert"]["unwind"] =
        serde_json::json!({"Cleanup": 8});
    value["body"]["blocks"].as_array_mut().expect("blocks").push(serde_json::json!({
        "id": 8, "stmts": [read], "terminator": "Resume"
    }));
    let func = decode(value);
    assert!(!guarded_result_read(&func, 12, 8));
    assert_eq!(bounds(&func, 2), (None, None));
    let map = crate::generate::type_ranges::local_value_join_interval_map(&func);
    let name = crate::place_to_var_name(&func, &Place::local(2));
    assert!(!map.contains_key(&name));
}

#[test]
fn an_unguarded_parallel_cleanup_edge_cannot_authenticate_success() {
    let mut value = fixture();
    value["body"]["blocks"][5]["terminator"]["Assert"]["unwind"] =
        serde_json::json!({"Cleanup": 6});
    let func = decode(value);
    assert!(!guarded_result_read(&func, 12, 6));
    assert_eq!(bounds(&func, 2), (None, None));
}

#[test]
fn multiple_success_dominated_result_reads_keep_the_original_bound() {
    let mut value = fixture();
    let read = value["body"]["blocks"][6]["stmts"][0].clone();
    value["body"]["blocks"][6]["stmts"].as_array_mut().expect("statements").push(read);
    assert_eq!(bounds(&decode(value), 2), (Some(1), None));
}

#[test]
fn partial_tuple_write_keeps_the_original_unique_definition_refusal() {
    let mut value = fixture();
    let span = value["body"]["blocks"][6]["stmts"][0]["Assign"]["span"].clone();
    value["body"]["blocks"][6]["stmts"].as_array_mut().expect("statements").push(
        serde_json::json!({
            "Assign": {"place": {"local": 12, "projections": [{"Field": 0}]},
                "rvalue": {"Use": {"Constant": {"Uint": [0, 64]}}}, "span": span}
        }),
    );
    assert_eq!(bounds(&decode(value), 2), (None, None));
}

#[test]
fn sparse_block_ids_refuse_instead_of_reusing_dense_dominance() {
    let mut value = fixture();
    value["body"]["blocks"][6]["id"] = serde_json::json!(99);
    let func = decode(value);
    assert!(!guarded_result_read(&func, 12, 6));
    assert_eq!(bounds(&func, 2), (None, None));
}

#[test]
fn inconsistent_checked_result_declarations_refuse_the_bound() {
    for (local, replacement) in [
        (2, serde_json::json!({"Int": {"width": 8, "signed": false}})),
        (
            12,
            serde_json::json!({"Tuple": [{"Int": {"width": 64, "signed": false}}, {"Int": {"width": 8, "signed": false}}]}),
        ),
    ] {
        let mut value = fixture();
        value["body"]["locals"]
            .as_array_mut()
            .expect("locals")
            .iter_mut()
            .find(|decl| decl["index"] == local)
            .expect("decl")["ty"] = replacement;
        assert_eq!(bounds(&decode(value), 2), (None, None));
    }
}

#[test]
fn checked_delta_width_and_overflow_operation_must_match() {
    let mut wrong_width = fixture();
    wrong_width["body"]["blocks"][5]["stmts"][1]["Assign"]["rvalue"]["CheckedBinaryOp"][2]["Constant"]
        ["Uint"][1] = serde_json::json!(8);
    assert_eq!(bounds(&decode(wrong_width), 2), (None, None));
    let mut wrong_op = fixture();
    wrong_op["body"]["blocks"][5]["terminator"]["Assert"]["msg"]["Overflow"] =
        serde_json::json!("Sub");
    assert_eq!(bounds(&decode(wrong_op), 2), (None, None));
}

#[test]
fn duplicate_local_declaration_cannot_supply_an_arithmetic_carrier() {
    let mut value = fixture();
    let duplicate = value["body"]["locals"]
        .as_array()
        .expect("locals")
        .iter()
        .find(|decl| decl["index"] == 2)
        .expect("decl")
        .clone();
    value["body"]["locals"].as_array_mut().expect("locals").push(duplicate);
    assert_eq!(bounds(&decode(value), 2), (None, None));
}
