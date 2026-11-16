//! The new root admission on actual compiler MIR; no solver verdict is inferred here.
use trust_types::VerifiableFunction;

fn fixture(name: &str) -> serde_json::Value {
    let p = format!("{}/tests/fixtures/str-bytes-count/{name}.json", env!("CARGO_MANIFEST_DIR"));
    serde_json::from_str(&std::fs::read_to_string(p).unwrap()).unwrap()
}

fn guards(json: serde_json::Value) -> usize {
    let func: VerifiableFunction = serde_json::from_value(json).unwrap();
    super::super::container_len::build_count_bound_guard_map(&func).len()
}

fn bytes_key(json: &mut serde_json::Value) -> &mut serde_json::Value {
    json["body"]["blocks"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .filter_map(|b| b["terminator"].get_mut("Call"))
        .find(|c| c["callee_key"]["sysroot_item"] == "StrBytes")
        .map(|c| &mut c["callee_key"])
        .expect("actual fixture has the compiler's StrBytes key")
}

#[test]
fn real_filtered_bytes_count_gets_the_existing_licensed_bound() {
    assert!(guards(fixture("bytes_count")) > 0);
}

#[test]
fn a_genuine_rendered_name_without_the_key_grants_nothing() {
    let mut json = fixture("bytes_count");
    *bytes_key(&mut json) = serde_json::Value::Null;
    assert_eq!(guards(json), 0);
}

#[test]
fn a_foreign_crate_cannot_supply_the_byte_producer() {
    let mut json = fixture("bytes_count");
    bytes_key(&mut json)["krate_is_real_sysroot"] = false.into();
    assert_eq!(guards(json), 0);
}

#[test]
fn an_unrecognized_item_cannot_borrow_the_byte_name() {
    let mut json = fixture("bytes_count");
    bytes_key(&mut json)["sysroot_item"] = serde_json::Value::Null;
    assert_eq!(guards(json), 0);
}

#[test]
fn split_and_a_real_user_iterator_do_not_get_a_byte_length_bound() {
    assert_eq!(guards(fixture("split_count_not_bounded_by_bytes")), 0);
    assert_eq!(guards(fixture("custom_count_must_overflow")), 0);
}
