//! A logical bridge may disclose runtime gaps, never promote source metadata.

use serde_json::Value;
use sha2::{Digest, Sha256};
use trust_clean::trustir_bridge::RuntimeFrontier;

// Immutable IR84a metadata, not an endorsement of that unqualified candidate.
const LEDGER: &[u8] = include_bytes!("../data/runtime-frontier/runtime-boundary-schema1.json");
// Historical incomplete schema2 candidate57c profile, retained byte-for-byte as a negative.
const HISTORICAL_NATIVE_LEDGER: &[u8] =
    include_bytes!("../data/runtime-frontier/runtime-boundary-schema2.json");
// Exact producer970bf5d4af84436824b07a9d302ba87e3b922902 disclosure; not native proof.
const NATIVE_LEDGER: &[u8] =
    include_bytes!("../data/runtime-frontier/runtime-boundary-ir970-schema2.json");

#[test]
fn runtime_frontier_discloses_native_support_without_losing_original_obligations() {
    let frontier = RuntimeFrontier::from_source_bytes(NATIVE_LEDGER).unwrap();
    assert_eq!(frontier.baseline_imported_declarations, 7125);
    assert_eq!(frontier.baseline_logical_declarations, 7084);
    assert_eq!(frontier.unproved_runtime_implementations, 41);
    assert_eq!(frontier.unproved_runtime_interfaces, 15);
    assert_eq!(frontier.unproved_native_support_obligations, 3);
    assert_eq!(frontier.source_ledger_schema, 2);
    assert_eq!(
        frontier.source_ledger_sha256,
        "d482060488377c20af1630e3fbbe3951602a880433a08bbfe1bbf027c337b1de"
    );
}

#[test]
fn runtime_frontier_refuses_the_unchanged_historical_native_profile() {
    assert_eq!(
        format!("{:x}", Sha256::digest(HISTORICAL_NATIVE_LEDGER)),
        "46205e78cf9b641feecfc10cca3f2fe60ae410c8cea9cdb529087a57760c2709"
    );
    assert_eq!(
        RuntimeFrontier::from_source_bytes(HISTORICAL_NATIVE_LEDGER).unwrap_err(),
        "native support source inputs changed"
    );
}

#[test]
fn runtime_frontier_rejects_incomplete_mixed_extra_or_duplicate_source_paths() {
    let current: Value = serde_json::from_slice(NATIVE_LEDGER).unwrap();
    let historical: Value = serde_json::from_slice(HISTORICAL_NATIVE_LEDGER).unwrap();
    let mut cases = Vec::new();
    for row in 0..3 {
        let inputs = current["support_obligations"][row]["source_inputs"].as_array().unwrap();
        for input in 0..inputs.len() {
            let mut ledger = current.clone();
            ledger["support_obligations"][row]["source_inputs"]
                .as_array_mut()
                .unwrap()
                .remove(input);
            cases.push((format!("row {row} dropped input {input}"), ledger));
        }
        let mut ledger = current.clone();
        ledger["support_obligations"][row]["source_inputs"]
            .as_array_mut()
            .unwrap()
            .push(Value::String("lean/trust_ir-semantics/native/foreign.c".to_owned()));
        cases.push((format!("row {row} extra path"), ledger));
        let mut ledger = current.clone();
        ledger["support_obligations"][row]["source_inputs"]
            .as_array_mut()
            .unwrap()
            .push(inputs[0].clone());
        cases.push((format!("row {row} appended duplicate"), ledger));
        let mut ledger = current.clone();
        ledger["support_obligations"][row]["source_inputs"][inputs.len() - 1] = inputs[0].clone();
        cases.push((format!("row {row} same-length duplicate"), ledger));
    }
    // Each newly declared input is required even when every other row is current.
    for row in 0..2 {
        let mut ledger = current.clone();
        ledger["support_obligations"][row]["source_inputs"] =
            historical["support_obligations"][row]["source_inputs"].clone();
        cases.push((format!("mixed historical row {row}"), ledger));
    }
    for (label, ledger) in cases {
        assert_eq!(
            RuntimeFrontier::from_source_bytes(&serde_json::to_vec(&ledger).unwrap()).unwrap_err(),
            "native support source inputs changed",
            "{label}"
        );
    }
}

#[test]
fn runtime_frontier_rejects_hidden_native_support_in_schema1() {
    let mut ledger: Value = serde_json::from_slice(LEDGER).unwrap();
    let native: Value = serde_json::from_slice(NATIVE_LEDGER).unwrap();
    for field in ["native_attachment", "support_obligations"] {
        ledger[field] = native[field].clone();
        assert!(RuntimeFrontier::from_source_bytes(&serde_json::to_vec(&ledger).unwrap()).is_err());
        ledger.as_object_mut().unwrap().remove(field);
    }
}

#[test]
fn runtime_frontier_rejects_missing_rebound_or_certified_native_support() {
    let original: Value = serde_json::from_slice(NATIVE_LEDGER).unwrap();
    let mut cases = Vec::new();
    for field in ["native_attachment", "support_obligations"] {
        let mut ledger = original.clone();
        ledger.as_object_mut().unwrap().remove(field);
        cases.push((field, ledger));
    }
    let mut ledger = original.clone();
    ledger["support_obligations"].as_array_mut().unwrap().pop();
    cases.push(("dropped support row", ledger));
    let mut ledger = original.clone();
    ledger["support_obligations"][1] = original["support_obligations"][0].clone();
    cases.push(("duplicate support identity", ledger));
    for field in ["id", "role", "state", "certified", "source_inputs"] {
        let mut ledger = original.clone();
        ledger["support_obligations"][0][field] = match field {
            "certified" => Value::Bool(true),
            "source_inputs" => serde_json::json!(["../foreign/runtime_init.c"]),
            "role" => Value::String(String::new()),
            _ => Value::String("CERTIFIED".to_owned()),
        };
        cases.push((field, ledger));
    }
    for field in [
        "logical_module",
        "provider_module",
        "activation_module",
        "initializer_symbol",
        "provider_initializer_symbol",
        "initializer_source",
    ] {
        let mut ledger = original.clone();
        ledger["native_attachment"][field] = Value::String("forged".to_owned());
        cases.push((field, ledger));
    }
    let mut ledger = original.clone();
    ledger["native_attachment"]["fixture_modules"][1] =
        original["native_attachment"]["fixture_modules"][0].clone();
    cases.push(("duplicate fixture module", ledger));
    for field in ["scope", "complete_inventory_sha256"] {
        let mut ledger = original.clone();
        ledger["baseline"][field] = Value::String("rebound".to_owned());
        cases.push((field, ledger));
    }
    let mut ledger = original.clone();
    ledger["schema"] = Value::from(3);
    cases.push(("unknown schema", ledger));
    let accepted: Vec<_> = cases
        .into_iter()
        .filter_map(|(label, ledger)| {
            RuntimeFrontier::from_source_bytes(&serde_json::to_vec(&ledger).unwrap())
                .is_ok()
                .then_some(label)
        })
        .collect();
    assert!(accepted.is_empty(), "accepted changed native support: {accepted:?}");
}

#[test]
fn runtime_frontier_rejects_rebound_or_ambiguous_baseline_identities() {
    let original: Value = serde_json::from_slice(LEDGER).unwrap();
    let mut cases = Vec::new();
    for (field, size) in [("root_subject", 40), ("ir_source", 40), ("roster_sha256", 64)] {
        let mut ledger = original.clone();
        ledger["baseline"][field] = Value::String("a".repeat(size));
        cases.push((field, ledger));
    }
    let mut renamed = original.clone();
    for (index, row) in
        renamed["runtime_obligations"].as_array_mut().unwrap().iter_mut().enumerate()
    {
        row["original_full_name"] = Value::String(format!("TrustIr.Forged.original{index}"));
    }
    cases.push(("all original names replaced", renamed));
    let mut duplicate = original.clone();
    duplicate["runtime_obligations"][1]["original_full_name"] =
        original["runtime_obligations"][0]["original_full_name"].clone();
    duplicate["runtime_obligations"][1]["original_module"] =
        Value::String("TrustIr.OtherModule".to_owned());
    cases.push(("same original Name in another module", duplicate));
    let mut duplicate = original.clone();
    let last = duplicate["runtime_obligations"].as_array().unwrap().len() - 1;
    duplicate["runtime_obligations"][last]["runtime_full_name"] =
        original["runtime_obligations"][0]["runtime_full_name"].clone();
    cases.push(("same runtime Name in another module", duplicate));
    let mut duplicate = original.clone();
    duplicate["interfaces"][1]["logical_full_name"] =
        original["interfaces"][0]["logical_full_name"].clone();
    duplicate["interfaces"][1]["logical_module"] = Value::String("TrustIr.OtherModule".to_owned());
    cases.push(("same logical Name in another module", duplicate));
    let accepted: Vec<_> = cases
        .into_iter()
        .filter_map(|(label, ledger)| {
            RuntimeFrontier::from_source_bytes(&serde_json::to_vec(&ledger).unwrap())
                .is_ok()
                .then_some(label)
        })
        .collect();
    assert!(accepted.is_empty(), "accepted changed baseline identities: {accepted:?}");
}

#[test]
fn runtime_frontier_preserves_the_original_imported_population() {
    let frontier = RuntimeFrontier::from_source_bytes(LEDGER).unwrap();
    assert_eq!(frontier.baseline_imported_declarations, 7125);
    assert_eq!(frontier.baseline_logical_declarations, 7084);
    assert_eq!(frontier.unproved_runtime_implementations, 41);
    assert_eq!(frontier.unproved_runtime_interfaces, 15);
    assert_eq!(frontier.unproved_native_support_obligations, 0);
    assert_eq!(frontier.source_ledger_schema, 1);
    assert_eq!(
        frontier.source_ledger_sha256,
        "32ecc46ebddc440c8bf884a2425ade6d3add140ce25c7c62fdf0e406d0136b41"
    );
}

#[test]
fn runtime_frontier_rejects_metadata_that_claims_certification() {
    for family in ["runtime_obligations", "interfaces"] {
        let mut ledger: Value = serde_json::from_slice(LEDGER).unwrap();
        ledger[family][0]["certified"] = Value::Bool(true);
        assert!(RuntimeFrontier::from_source_bytes(&serde_json::to_vec(&ledger).unwrap()).is_err());
    }
    let mut ledger: Value = serde_json::from_slice(LEDGER).unwrap();
    ledger["runtime_obligations"][0]["state"] = Value::String("CERTIFIED".to_owned());
    assert!(RuntimeFrontier::from_source_bytes(&serde_json::to_vec(&ledger).unwrap()).is_err());
}

#[test]
fn runtime_frontier_rejects_lost_or_relabelled_obligations() {
    let mut dropped: Value = serde_json::from_slice(LEDGER).unwrap();
    dropped["runtime_obligations"].as_array_mut().unwrap().pop();
    assert!(RuntimeFrontier::from_source_bytes(&serde_json::to_vec(&dropped).unwrap()).is_err());
    let mut changed: Value = serde_json::from_slice(LEDGER).unwrap();
    changed["interfaces"][0]["runtime_full_name"] =
        Value::String("TrustIr.FORGED.provider".to_owned());
    assert!(RuntimeFrontier::from_source_bytes(&serde_json::to_vec(&changed).unwrap()).is_err());
    let mut duplicate: Value = serde_json::from_slice(LEDGER).unwrap();
    duplicate["runtime_obligations"][1] = duplicate["runtime_obligations"][0].clone();
    assert!(RuntimeFrontier::from_source_bytes(&serde_json::to_vec(&duplicate).unwrap()).is_err());
}
