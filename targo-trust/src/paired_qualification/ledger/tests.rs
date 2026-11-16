use serde_json::{Value, json};

use super::*;

fn rows() -> Vec<Value> {
    ["unknown", "timeout", "skipped"].into_iter().map(|outcome| json!({
        "kind":"divzero", "description":"division by zero", "outcome":outcome,
        "solver":"native-test-observation", "time_ms":0,
            "location":{"file":"src/lib.rs","line_start":7,"line_end":7,"col_start":1,"col_end":2}
    })).collect()
}
pub(in crate::paired_qualification) fn records(node: Node) -> Vec<Value> {
    let plan = super::super::protocol::tests::plan();
    let policy = if node == Node::Advisory { "advisory" } else { "strict" };
    let session = format!(
        "native-ay-{}-{policy}",
        crate::paired_qualification::hex(&plan.consumer.invocation)
    );
    vec![
        json!({"type":"function_result", "function":"ay_proof_common::f",
        "package_name":"ay-proof-common","crate_name":"ay_proof_common","primary_package":true,
        "verification_session":session,"results":rows(),"proved":0,"failed":0,"unknown":3,
        "timed_out":1,"skipped":1,"runtime_checked":0,"total":3}),
        json!({"type":"coverage_summary","crate_name":"ay_proof_common","package_name":"ay-proof-common",
        "primary_package":true,"verification_session":session,"eligible":1,"processed":1,
        "function_identities":{"schema":trust_types::COVERAGE_FUNCTION_IDENTITY_SCHEMA_V1,
            "eligible_functions":["ay_proof_common::f"],"processed_functions":["ay_proof_common::f"]},
        "memory":{"schema":trust_types::MEMORY_SUMMARY_SCHEMA_V1,"counters":{}}}),
        json!({"type":"crate_summary","crate_name":"ay_proof_common","package_name":"ay-proof-common",
        "primary_package":true,"verification_session":session,"functions_analyzed":1,
        "functions_verified":0,"total_proved":0,"total_failed":0,"total_unknown":3,
        "total_timed_out":1,"total_skipped":1,"total_runtime_checked":0,"total_obligations":3}),
    ]
}
fn text(records: &[Value]) -> Vec<u8> {
    records
        .iter()
        .map(|row| format!("{}{}\n", trust_types::TRANSPORT_PREFIX, row))
        .collect::<String>()
        .into_bytes()
}
pub(in crate::paired_qualification) fn ledger(node: Node, records: &[Value]) -> Result<Ledger> {
    Ledger::parse(&super::super::protocol::tests::plan(), node, &text(records))
}
#[test]
fn independent_full_ledgers_preserve_timeout_skipped_and_complete_identity_ties() {
    let a = ledger(Node::Advisory, &records(Node::Advisory)).unwrap();
    let s = ledger(Node::Strict, &records(Node::Strict)).unwrap();
    a.agrees_with(&s).unwrap();
    assert_eq!(a.entries.len(), 3);
    assert_eq!(a.classes[&Class::Timeout], 1);
    assert_eq!(a.classes[&Class::Skipped], 1);
    assert!(a.entries.contains_key("ay_proof_common::f|divzero|src/lib.rs#2"));
    assert_eq!(a.terminal.total_unknown, 3);
    assert!(a.denominator_complete);
    assert!(
        a.agrees_with(&a).is_err(),
        "advisory cannot stand in for independent strict observation"
    );
}
#[test]
fn count_equal_identity_or_verdict_substitution_does_not_agree() {
    let a = ledger(Node::Advisory, &records(Node::Advisory)).unwrap();
    let mut changed = records(Node::Strict);
    changed[0]["results"][0]["kind"] = json!("bounds");
    assert!(a.agrees_with(&ledger(Node::Strict, &changed).unwrap()).is_err());
    let mut changed = records(Node::Strict);
    changed[0]["results"][0]["claim_digest_sha256"] = json!("a".repeat(64));
    assert!(a.agrees_with(&ledger(Node::Strict, &changed).unwrap()).is_err());
    let mut changed = records(Node::Strict);
    changed[0]["source_sha256"] = json!("a".repeat(64));
    assert!(a.agrees_with(&ledger(Node::Strict, &changed).unwrap()).is_err());
}
#[test]
fn line_motion_and_independent_timing_do_not_rename_an_obligation() {
    let a = ledger(Node::Advisory, &records(Node::Advisory)).unwrap();
    let mut changed = records(Node::Strict);
    changed[0]["results"][0]["location"]["line_start"] = json!(201);
    changed[0]["results"][0]["location"]["line_end"] = json!(201);
    changed[0]["results"][0]["time_ms"] = json!(900);
    let s = ledger(Node::Strict, &changed).unwrap();
    a.agrees_with(&s).unwrap();
    assert_ne!(
        a.entries.values().next().unwrap().original.location,
        s.entries.values().next().unwrap().original.location
    );
}
#[test]
fn wrong_scope_session_duplicate_function_and_terminal_order_are_refused() {
    for field in ["package_name", "crate_name", "verification_session"] {
        let mut changed = records(Node::Advisory);
        changed[0][field] = json!("other");
        assert!(ledger(Node::Advisory, &changed).is_err(), "{field}");
    }
    let mut changed = records(Node::Advisory);
    changed[0]["primary_package"] = json!(false);
    assert!(ledger(Node::Advisory, &changed).is_err());
    let original = records(Node::Advisory);
    for changed in [
        vec![original[0].clone(), original[0].clone(), original[1].clone(), original[2].clone()],
        vec![original[1].clone(), original[0].clone(), original[2].clone()],
        vec![original[0].clone(), original[2].clone(), original[1].clone()],
        vec![original[0].clone(), original[1].clone()],
        vec![original[0].clone(), original[1].clone(), original[2].clone(), original[2].clone()],
    ] {
        assert!(ledger(Node::Advisory, &changed).is_err());
    }
}
#[test]
fn duplicate_nested_json_and_rounded_or_overflowed_counters_cannot_be_normalized_away() {
    let plan = super::super::protocol::tests::plan();
    let original = String::from_utf8(text(&records(Node::Advisory))).unwrap();
    for changed in [
        original.replacen("\"time_ms\":0", "\"time_ms\":0,\"time_ms\":7", 1),
        original.replacen("\"total\":3", "\"total\":3.0", 1),
        original.replacen("\"total\":3", "\"total\":18446744073709551616", 1),
    ] {
        assert_ne!(changed, original);
        assert!(Ledger::parse(&plan, Node::Advisory, changed.as_bytes()).is_err());
    }
}
#[test]
fn missing_same_count_function_inventory_and_vcgen_replacement_withhold_completeness() {
    let mut changed = records(Node::Advisory);
    changed[1]["function_identities"]["processed_functions"] =
        json!(["ay_proof_common::different"]);
    assert!(ledger(Node::Advisory, &changed).is_err());
    let mut changed = records(Node::Advisory);
    changed[0]["results"][0]["reason"] = json!("TrustVcGenWorkBudgetExceeded");
    let a = ledger(Node::Advisory, &changed).unwrap();
    assert!(!a.denominator_complete);
    assert_eq!(a.truncated_functions.len(), 1);
    let s = ledger(Node::Strict, &records(Node::Strict)).unwrap();
    assert!(a.agrees_with(&s).is_err());
}

#[test]
fn current_paired_profile_requires_exact_timeout_and_skipped_splits() {
    for field in ["timed_out", "skipped"] {
        let mut changed = records(Node::Advisory);
        changed[0][field] = json!(0);
        assert!(ledger(Node::Advisory, &changed).is_err());
    }
    for field in ["total_timed_out", "total_skipped"] {
        let mut changed = records(Node::Advisory);
        changed[2][field] = json!(0);
        assert!(ledger(Node::Advisory, &changed).is_err());
    }
}

#[test]
fn structural_verdict_is_separate_and_original_i128_counterexample_survives() {
    let mut changed = records(Node::Advisory);
    changed[0]["results"][0]["outcome"] = json!("proved");
    changed[0]["results"][0]["kind"] = json!("no_obligations");
    changed[0]["results"][0]["solver"] = json!("trust-structural");
    changed[0]["proved"] = json!(1);
    changed[0]["unknown"] = json!(2);
    changed[2]["total_proved"] = json!(1);
    changed[2]["total_unknown"] = json!(2);
    let a = ledger(Node::Advisory, &changed).unwrap();
    assert_eq!(a.classes[&Class::ProvedStructural], 1);
    assert!(!a.classes.contains_key(&Class::ProvedSolver));

    let mut changed = records(Node::Advisory);
    changed[0]["results"][0]["counterexample_model"] = json!({"assignments":[
        ["n",{"Int":"-170141183460469231731687303715884105728"}],
        ["m",{"Uint":"340282366920938463463374607431768211455"}]]});
    let a = ledger(Node::Advisory, &changed).unwrap();
    let model = a.entries.values().next().unwrap().original.counterexample_model.as_ref().unwrap();
    assert_eq!(model.assignments[0].1, trust_types::CounterexampleValue::Int(i128::MIN));
    assert_eq!(model.assignments[1].1, trust_types::CounterexampleValue::Uint(u128::MAX));
}
