//! Exact captured bytes and complete borrowed source-content custody.
//! A digest/QName is NOT a resolved Rust DefId or a semantic proof token.
use trust_source_contract::verifier_source_digest;
use trust_types::VerifiableFunction;

const CAPTURE: &[u8] = include_bytes!("fixtures/law-entry/proof_ref_kind_is_ambiguous.json");

fn source() -> serde_json::Value {
    serde_json::from_slice(CAPTURE).unwrap()
}

#[test]
fn kernel_capture_bytes_are_the_original_unmodified_source_carrier() {
    let lean = include_str!("../lean/MirCaptureOriginal.lean");
    let bytes = lean
        .split_once("def sourceBytes : List Nat := [")
        .unwrap()
        .1
        .split_once(']')
        .unwrap()
        .0
        .split(',')
        .map(|n| n.trim().parse::<u8>().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(bytes, CAPTURE);
    assert_eq!(bytes.len(), 16_316);
    assert!(bytes.is_ascii());
}

#[test]
fn full_source_identity_binds_metadata_declaration_and_body_without_assuming_clauses() {
    let original: VerifiableFunction = serde_json::from_slice(CAPTURE).unwrap();
    let digest = verifier_source_digest(&original);
    // The original generated domain is retained in content identity. It is NOT
    // an authored requires and is not an assumption of the Lean body theorem.
    assert!(!original.preconditions.is_empty());
    for pointer in [
        "/name",
        "/def_path",
        "/body/locals/1/name",
        "/body/locals/1/ty/Adt/name",
        "/body/locals/1/ty/Adt/variants/0/name",
    ] {
        let mut mutant = source();
        *mutant.pointer_mut(pointer).unwrap() = "forged_identity".into();
        let mutant: VerifiableFunction = serde_json::from_value(mutant).unwrap();
        assert_ne!(digest, verifier_source_digest(&mutant), "{pointer}");
    }
    for pointer in ["/preconditions", "/body/blocks/1/stmts"] {
        let mut mutant = source();
        *mutant.pointer_mut(pointer).unwrap() = serde_json::json!([]);
        let mutant: VerifiableFunction = serde_json::from_value(mutant).unwrap();
        assert_ne!(digest, verifier_source_digest(&mutant), "{pointer}");
    }
    let mut mutant = source();
    mutant["body"]["locals"][1]["ty"]["Adt"]["variants"][0]["discriminant"] = (-1).into();
    let mutant: VerifiableFunction = serde_json::from_value(mutant).unwrap();
    assert_ne!(digest, verifier_source_digest(&mutant));
}

#[test]
fn unrecorded_nominal_origin_cannot_authenticate_a_capture() {
    let original: VerifiableFunction = serde_json::from_slice(CAPTURE).unwrap();
    let mut forged = source();
    forged["body"]["locals"][1]["ty"]["Adt"]["origin"] =
        serde_json::json!({"Rust": {"stable_crate_id": 1, "def_path_hash": vec![0; 16]}});
    // The legacy carrier does not RECORD a general nominal origin. Its serde
    // acceptance is therefore NOT authentication; the exact Lean key projection
    // separately rejects this extra key, rather than granting it any authority.
    let forged: VerifiableFunction = serde_json::from_value(forged).unwrap();
    assert_eq!(verifier_source_digest(&original), verifier_source_digest(&forged));
}
