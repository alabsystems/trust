//! A successful unverified compiler exit is not the oracle: inspect actual published IR,
//! coverage and effect-conservation results. Keep the full producer validator enabled.
//! This tests structural registration/refusal, not source refinement or proof authority.
//@ ignore-cross-compile

use std::path::Path;

use run_make_support::{rfs, rustc, serde_json};

fn row<'a>(document: &'a serde_json::Value, key: &str, name: &str) -> &'a serde_json::Value {
    let found: Vec<_> = document[key]
        .as_array()
        .expect("complete row inventory")
        .iter()
        .filter(|row| row["def_path"].as_str() == Some(name))
        .collect();
    assert_eq!(found.len(), 1, "exactly one {key} row for {name}: {found:?}");
    found[0]
}

fn struct_row<'a>(text: &'a str, name: &str) -> &'a str {
    let found: Vec<_> = text
        .lines()
        .filter(|line| {
            line.strip_prefix("struct @")
                .and_then(|rest| rest.split_once(" {"))
                .is_some_and(|(path, _)| path.rsplit("::").next() == Some(name))
        })
        .collect();
    assert_eq!(found.len(), 1, "one actual spelling for {name}: {found:?}\n{text}");
    found[0]
}

fn assert_opaque_refusal(effects: &serde_json::Value, name: &str) {
    let effect = row(effects, "functions", name);
    assert_eq!(effect["verdict"], "refused", "{name}: {effect}");
    assert!(
        effect["tags"]
            .as_array()
            .expect("explicit effect tags")
            .iter()
            .any(|tag| tag == "abstracted(opaque-lane)"),
        "registration must not erase the old RMW abstraction refusal: {name}: {effect}"
    );
}

fn assert_unsupported(coverage: &serde_json::Value, name: &str, reason: &str) {
    let body = row(coverage, "bodies", name);
    assert_eq!(body["lowered"], false, "{name} must still refuse lowering: {body}");
    assert_eq!(body["spliced"], false, "{name} must still refuse: {body}");
    let counted_reason = serde_json::json!([reason, 1]);
    assert!(
        body["unsupported"].as_array().unwrap().iter().any(|tag| tag == &counted_reason),
        "{name} must exercise exactly one actual named refusal {reason}: {body}"
    );
}

fn assert_inventory(coverage: &serde_json::Value) {
    let names = [
        "make",
        "pointer_write_then_read",
        "pointer_read_then_write",
        "pointer_write_then_read_local",
        "pointer_write_then_literal",
        "consume_inner",
        "pointer_write_then_pass",
        "nested_write_then_read",
        "make_counter",
        "pointer_compound_then_read",
        "make_pure",
        "pure_write_then_read",
        "vector_sibling_write",
        "option_sibling_write",
        "admitted_option_write_then_literal",
        "WithZeroArray::z::{constant#0}",
        "zero_array_write_then_literal",
        "mutable_wide_sibling_write",
        "Bits::bytes::{constant#0}",
        "union_sibling_write",
        "union_field_write",
    ];
    // The inventory also includes the two anonymous array-length constant
    // bodies. Pin them explicitly rather than filtering or dropping rows.
    assert_eq!(coverage["bodies"].as_array().unwrap().len(), names.len());
    for name in names {
        row(coverage, "bodies", name);
    }
}

fn check(option_flag: &str) {
    let dir = format!("spelling-{option_flag}");
    let out = Path::new(&dir);
    rfs::create_dir(out);
    rustc()
        .input("subject.rs")
        .crate_name("rmw_spelling")
        .crate_type("lib")
        .edition("2024")
        .emit("metadata")
        .out_dir(out)
        .arg("-Ztrust-verify=off")
        .arg("-Ztrust-ir-lower=on")
        .arg(format!("-Ztrust-dump=ir:{dir}"))
        .arg(format!("-Ztrust-option-flag-lanes={option_flag}"))
        .run()
        .assert_stderr_not_contains("semantic finalization failed");
    assert!(!rfs::read(out.join("rmw_spelling.trust-ir.bin")).is_empty());
    let text = rfs::read_to_string(out.join("rmw_spelling.trust-ir.txt"));
    let coverage: serde_json::Value =
        serde_json::from_slice(&rfs::read(out.join("rmw_spelling.coverage.json"))).unwrap();
    let effects: serde_json::Value =
        serde_json::from_slice(&rfs::read(out.join("rmw_spelling.effect-conservation.json")))
            .unwrap();
    assert_eq!(coverage["proof_authority"], false);
    assert_eq!(coverage["native_verification_requests"], false);
    assert_eq!(coverage["publication"]["commit_marker"], true);
    assert_inventory(&coverage);
    for name in [
        "pointer_write_then_read",
        "pointer_read_then_write",
        "pointer_write_then_read_local",
        "pointer_write_then_literal",
        "nested_write_then_read",
        "pointer_compound_then_read",
        "pure_write_then_read",
        "admitted_option_write_then_literal",
        "zero_array_write_then_literal",
    ] {
        let body = row(&coverage, "bodies", name);
        assert_eq!(body["lowered"], true, "{name}: {body}");
        assert_eq!(body["spliced"], true, "{name}: {body}");
        assert_eq!(body["symbolic"], false, "{name}: {body}");
        assert!(body["unsupported"].as_array().unwrap().is_empty(), "{name}: {body}");
        assert!(body["func_id"].is_u64(), "{name} has an actual function identity");
    }
    for name in ["PointerInner", "CounterInner"] {
        assert!(struct_row(&text, name).contains("p: ptr"), "faithful pointer lane: {name}");
    }
    for name in ["PointerOuter", "CounterOuter", "Envelope", "PureInner", "PureOuter"] {
        struct_row(&text, name);
    }
    let option_row = struct_row(&text, "AdmittedOption");
    assert!(option_row.contains("label: enum."), "faithful admitted Option: {option_row}");
    let array_row = struct_row(&text, "WithZeroArray");
    assert!(
        array_row.contains("z: [") && array_row.contains(" x 0]"),
        "faithful zero-length array: {array_row}"
    );
    for name in [
        "pointer_write_then_read",
        "pointer_write_then_read_local",
        "pointer_write_then_literal",
        "pointer_compound_then_read",
        "vector_sibling_write",
        "option_sibling_write",
        "admitted_option_write_then_literal",
        "zero_array_write_then_literal",
        "mutable_wide_sibling_write",
    ] {
        assert_opaque_refusal(&effects, name);
    }
    for name in ["pure_write_then_read", "pointer_read_then_write"] {
        let effect = row(&effects, "functions", name);
        assert!(
            !effect["tags"].as_array().unwrap().iter().any(|tag| tag == "abstracted(opaque-lane)"),
            "preexisting faithful/pure registration must not gain a new refusal: {name}: {effect}"
        );
    }
    let union = row(&coverage, "bodies", "union_sibling_write");
    assert_eq!(union["spliced"], false, "union placeholder must still refuse: {union}");
    assert_eq!(union["splice_refusal"], "Splice(union placeholder lane)");
    assert_unsupported(&coverage, "union_field_write", "UnionLane(field store)");
    assert_unsupported(&coverage, "pointer_write_then_pass", "Call(rmw-degraded arg spelling)");
}

fn main() {
    check("on");
    check("off");
}
