//! Trust (T3 L4, C09w; design §8, ROW-IDENTITY-1): the compiler's wire identities that bind a
//! formula by its Merkle digest, the exact-VC claim v3 and the obligation fingerprint v4
//! (trust-mir-extract's VC content digest v2 is tested beside it). Each encoder is mutated
//! in every field it binds, its obligation record's included; each digest is a function of
//! the trees only (I5); and a v2 claim equals no v3 claim, because there is no decoder for
//! it and its domain differs.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::hash::Hash;

use trust_types::formula_merkle::formula_digest;
use trust_types::{
    ContractMetadata, Formula, ObligationRecord, ObligationWrapper, PathGuardTerm, Sort, Symbol,
    VcKind, VerificationCondition,
};

use super::super::*;
use super::test_vc;

fn var(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn below(name: &str, bound: i128) -> Formula {
    Formula::Lt(Box::new(var(name)), Box::new(Formula::Int(bound)))
}

/// A VC with an obligation record of both wrappers, a subject and a width.
fn recorded_vc() -> VerificationCondition {
    let record = ObligationRecord {
        body: below("d", 0),
        wrappers: vec![
            ObligationWrapper::ConjoinFactsLast { facts: vec![below("a", 1), below("b", 2)] },
            ObligationWrapper::PathGuardOr {
                paths: vec![
                    PathGuardTerm::Raw,
                    PathGuardTerm::Guarded { guards: vec![below("g", 3)] },
                ],
            },
        ],
        subject: Some(var("s")),
        width: Some(32),
    };
    VerificationCondition {
        formula: record.reconstruct().expect("the record replays"),
        obligation: Some(record),
        ..test_vc(10)
    }
}

fn record(vc: &mut VerificationCondition) -> &mut ObligationRecord {
    vc.obligation.as_mut().expect("the VC carries its record")
}

fn facts(vc: &mut VerificationCondition) -> &mut Vec<Formula> {
    match &mut record(vc).wrappers[0] {
        ObligationWrapper::ConjoinFactsLast { facts } => facts,
        ObligationWrapper::PathGuardOr { .. } => panic!("the first wrapper conjoins facts"),
    }
}

fn paths(vc: &mut VerificationCondition) -> &mut Vec<PathGuardTerm> {
    match &mut record(vc).wrappers[1] {
        ObligationWrapper::PathGuardOr { paths } => paths,
        ObligationWrapper::ConjoinFactsLast { .. } => panic!("the second wrapper guards paths"),
    }
}

fn claim(vc: &VerificationCondition) -> String {
    exact_vc_claim_digest_sha256(vc, false, None).expect("the VC has a claim digest")
}

/// The same VC rebuilt from its JSON: every formula a separately allocated tree.
fn rebuilt(vc: &VerificationCondition) -> VerificationCondition {
    serde_json::from_str(&serde_json::to_string(vc).expect("serializes")).expect("deserializes")
}

#[test]
fn claim_v3_binds_each_formula_by_its_merkle_digest_and_the_rest_as_v2_did() {
    let vc = recorded_vc();
    let payload: serde_json::Value = serde_json::from_str(
        &canonical_exact_vc_claim_payload(&vc, false, None).expect("the claim serializes"),
    )
    .expect("the claim is JSON");
    let hex = |formula: &Formula| {
        serde_json::Value::String(formula_digest(formula).expect("a digest").to_hex())
    };
    assert_eq!(payload["schema"], EXACT_VC_CLAIM_SCHEMA_VERSION);
    assert_eq!(payload["schema"], "trustc.exact-vc-claim.v3");
    assert_eq!(payload["semantics"]["overflow_checks"], false);
    assert!(payload["semantics"]["target"].is_null());
    let bound = &payload["vc"];
    assert_eq!(bound["kind"], trust_types::canonical_digest_json_value(&vc.kind).unwrap());
    assert_eq!(bound["function"], "test::f");
    assert_eq!(bound["location"], trust_types::canonical_digest_json_value(&vc.location).unwrap());
    assert!(bound["contract_metadata"].is_null());
    assert_eq!(bound["formula"], hex(&vc.formula));
    let record = vc.obligation.as_ref().expect("the record");
    let bound = &bound["obligation"];
    assert_eq!(bound["body"], hex(&record.body));
    assert_eq!(bound["subject"], hex(record.subject.as_ref().expect("a subject")));
    assert_eq!(bound["width"], 32);
    assert_eq!(
        bound["wrappers"],
        serde_json::json!([
            { "tag": "conjoin_facts_last", "facts": [hex(&below("a", 1)), hex(&below("b", 2))] },
            {
                "tag": "path_guard_or",
                "paths": [{ "tag": "raw" }, { "tag": "guarded", "guards": [hex(&below("g", 3))] }],
            },
        ])
    );
    // No formula text rides in the claim: its only formula material is the digests.
    let text = payload.to_string();
    assert!(!text.contains("\"Lt\"") && !text.contains("\"Var\""), "{text}");
}

#[test]
fn claim_v3_moves_with_every_field_it_binds() {
    let base = recorded_vc();
    let mut seen = vec![claim(&base)];
    let mut mutated = |what: &str, change: &dyn Fn(&mut VerificationCondition)| {
        let mut vc = base.clone();
        change(&mut vc);
        let moved = claim(&vc);
        assert!(!seen.contains(&moved), "{what}: the claim must move, to a digest of its own");
        seen.push(moved);
    };
    mutated("kind", &|vc| vc.kind = VcKind::RemainderByZero);
    mutated("function", &|vc| vc.function = Symbol::intern("test::g"));
    mutated("location", &|vc| vc.location.col_end += 1);
    mutated("contract metadata", &|vc| {
        vc.contract_metadata =
            Some(ContractMetadata { has_requires: true, ..ContractMetadata::default() });
    });
    mutated("formula", &|vc| vc.formula = Formula::Bool(false));
    mutated("the record", &|vc| vc.obligation = None);
    mutated("the record's body", &|vc| record(vc).body = below("d", 1));
    mutated("the record's subject", &|vc| record(vc).subject = Some(var("t")));
    mutated("no subject", &|vc| record(vc).subject = None);
    mutated("the record's width", &|vc| record(vc).width = Some(64));
    mutated("no width", &|vc| record(vc).width = None);
    mutated("a fact", &|vc| facts(vc)[1] = below("b", 3));
    mutated("the facts' order", &|vc| facts(vc).swap(0, 1));
    mutated("a fact fewer", &|vc| {
        facts(vc).pop();
    });
    mutated("the wrappers' order", &|vc| record(vc).wrappers.swap(0, 1));
    mutated("a wrapper fewer", &|vc| {
        record(vc).wrappers.pop();
    });
    mutated("a wrapper's tag", &|vc| {
        record(vc).wrappers[0] = ObligationWrapper::PathGuardOr {
            paths: vec![PathGuardTerm::Guarded { guards: vec![below("a", 1), below("b", 2)] }],
        };
    });
    mutated("a path's tag", &|vc| paths(vc)[0] = PathGuardTerm::Guarded { guards: Vec::new() });
    mutated("a guard", &|vc| paths(vc)[1] = PathGuardTerm::Guarded { guards: vec![var("h")] });
    mutated("the paths' order", &|vc| paths(vc).swap(0, 1));
    mutated("a path fewer", &|vc| {
        paths(vc).pop();
    });
    let base_claim = claim(&base);
    for (what, semantics) in [
        ("overflow checks", exact_vc_claim_digest_sha256(&base, true, None)),
        ("target", exact_vc_claim_digest_sha256(&base, false, Some("aarch64-apple-darwin;ptr64"))),
    ] {
        assert_ne!(semantics.as_deref(), Some(base_claim.as_str()), "{what}");
    }
}

#[test]
fn claim_v3_is_a_function_of_the_trees_and_equals_no_v2_claim() {
    let vc = recorded_vc();
    // I5: separately built trees of one shape, sharing nothing, give one claim. (That the
    // formulas a claim digests first do not reach a later one's digest is the first test's:
    // each digest in the claim is its formula's digest alone.)
    assert_eq!(claim(&vc), claim(&rebuilt(&vc)));
    // S1's `Collapsed` path claims as the `Raw` it serializes as, before and after a round
    // trip (which reads it back as `Raw`).
    let mut collapsed = vc.clone();
    paths(&mut collapsed)[0] = PathGuardTerm::Collapsed;
    assert_eq!(claim(&collapsed), claim(&vc));
    assert_eq!(claim(&rebuilt(&collapsed)), claim(&vc));
    // The v2 claim of the same VC, by v2's encoder inlined as the differential: the whole
    // VC as canonical JSON, under v2's schema and domain. It is not v3's claim, and its
    // payload is not v3's under either domain, so a reader joining claim digests never
    // matches a v2 row to a v3 one.
    let v2 = serde_json::json!({
        "schema": "trustc.exact-vc-claim.v2",
        "semantics": { "overflow_checks": false, "target": null },
        "vc": trust_types::canonical_digest_json_value(&vc).unwrap(),
    });
    let mut payload = String::new();
    write_canonical_json_value(&v2, &mut payload).expect("the v2 claim serializes");
    let v2_claim =
        domain_length_bound_sha256_hex("trustc.transport-exact-vc-claim.v2", payload.as_bytes());
    assert_ne!(v2_claim, claim(&vc));
    assert_ne!(
        domain_length_bound_sha256_hex(EXACT_VC_CLAIM_DIGEST_DOMAIN, payload.as_bytes()),
        claim(&vc)
    );
    assert_ne!(EXACT_VC_CLAIM_DIGEST_DOMAIN, "trustc.transport-exact-vc-claim.v2");
}

#[test]
fn obligation_fingerprint_v4_binds_the_formula_by_its_merkle_digest() {
    let base = recorded_vc();
    let fingerprint = compute_obligation_fingerprint(&base);
    // I5: the same trees, built separately.
    assert_eq!(compute_obligation_fingerprint(&rebuilt(&base)), fingerprint);
    // What v3 bound moves it: the function, the kind and the formula.
    let moved = |change: &dyn Fn(&mut VerificationCondition)| {
        let mut vc = base.clone();
        change(&mut vc);
        compute_obligation_fingerprint(&vc)
    };
    assert_ne!(moved(&|vc| vc.function = Symbol::intern("test::g")), fingerprint);
    assert_ne!(moved(&|vc| vc.kind = VcKind::RemainderByZero), fingerprint);
    assert_ne!(moved(&|vc| vc.formula = Formula::Bool(false)), fingerprint);
    let reordered = moved(&|vc| {
        facts(vc).swap(0, 1);
        vc.formula = record(vc).reconstruct().expect("the record replays");
    });
    assert_ne!(reordered, fingerprint, "the formula's conjunct order");
    // What v3 did not bind still does not: the location and the record.
    assert_eq!(moved(&|vc| vc.location.line_start += 3), fingerprint);
    assert_eq!(moved(&|vc| vc.obligation = None), fingerprint);
    // v3's spelling, inlined as the differential, is not v4's.
    let mut hasher = StableHasher::new();
    "trust-obligation-fingerprint-v3".hash(&mut hasher);
    base.function.as_str().hash(&mut hasher);
    vc_kind_fingerprint_key(&base.kind).hash(&mut hasher);
    base.formula.to_smtlib().hash(&mut hasher);
    let v3: Fingerprint = hasher.finish();
    assert_ne!(v3, fingerprint);
}
