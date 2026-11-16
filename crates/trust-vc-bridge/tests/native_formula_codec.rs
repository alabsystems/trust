//! The real native bundle consumer must read one canonical producer formula.
//! These cases use the component's existing body, provenance and request, not
//! the older advisory discharge API that intentionally ignores formula payloads.

#![cfg(feature = "trust-build")]

#[path = "../../../first-party/trust-vc/crates/trust-vc-trust-engine/tests/support/admission_baseline.rs"]
mod admission_baseline;

use trust_ir::{NativeVerificationBundle, ProofId};
use trust_vc_trust_engine::{
    TrustEngineError, TrustVcNativeTrustIrBundleReport, TrustVcNativeTrustIrDischargeOutcome,
    TrustVcNativeTrustIrDischargeStatus, TrustVcTrustEngine,
};

const ORIGINAL: &str = include_str!(
    "../../../first-party/trust-vc/crates/trust-vc-trust-engine/fixtures/trust_ir_native/discharge_scalar_branch.json"
);
const POST: ProofId = ProofId::new(1);

fn question(fields: Option<&str>, rendering: Option<&str>) -> NativeVerificationBundle {
    let mut bundle: NativeVerificationBundle = serde_json::from_str(ORIGINAL).unwrap();
    let formula = bundle
        .module
        .proof_obligations
        .iter_mut()
        .find(|row| row.id == POST)
        .unwrap()
        .formula
        .as_mut()
        .unwrap();
    if let Some(fields) = fields {
        // Keep the actual producer's source metadata intact. Construct malformed
        // wire bytes directly: a Value roundtrip would erase duplicate keys.
        let original: serde_json::Value = serde_json::from_str(&formula.payload).unwrap();
        formula.payload = format!("{{{fields},\"source\":{}}}", original["source"]);
    }
    formula.smtlib = rendering.map(str::to_owned);
    admission_baseline::sync_assertion_atoms(&mut bundle, POST);
    admission_baseline::reseal_module_identity(&mut bundle);
    bundle.validate().expect("only the formula codec, not bundle provenance, is under test");
    bundle
}

fn consume(bundle: &NativeVerificationBundle) -> TrustVcNativeTrustIrBundleReport {
    TrustVcTrustEngine::new()
        .consume_native_trust_ir_bundle(bundle)
        .expect("the real native bundle consumer must answer this admitted question")
}

fn post(report: &TrustVcNativeTrustIrBundleReport) -> &TrustVcNativeTrustIrDischargeOutcome {
    report.requests()[0]
        .discharge()
        .iter()
        .find(|row| row.obligation_id() == POST.index())
        .expect("the production discharge path must answer the actual postcondition")
}

#[test]
fn original_scalar_question_reaches_the_production_formula_reader() {
    let report = consume(&question(None, None));
    assert_eq!(post(&report).outcome(), &TrustVcNativeTrustIrDischargeStatus::Verified);
    assert!(post(&report).formula_payload_sha256().is_some());
    assert!(report.requests()[0].advisory_discharge().is_none());
}

#[test]
fn changing_only_the_original_formula_changes_the_answer() {
    let honest = question(None, None);
    let liar = question(Some(r#""formula":{"Ge":[{"Var":["_0","Int"]},{"Int":20}]}"#), None);
    assert_eq!(honest.module.functions, liar.module.functions, "the body remains identical");
    assert_eq!(post(&consume(&honest)).outcome(), &TrustVcNativeTrustIrDischargeStatus::Verified);
    assert!(matches!(
        post(&consume(&liar)).outcome(),
        TrustVcNativeTrustIrDischargeStatus::Counterexample { .. }
    ));
}

#[test]
fn duplicate_formula_fields_cannot_replace_the_producer_question() {
    for fields in [
        r#""formula":{"Bool":false},"formula":{"Bool":true}"#,
        r#""formula":{"Bool":true},"formula":{"Bool":false}"#,
        r#""formula":{"Bool":false,"Bool":true}"#,
    ] {
        let bundle = question(Some(fields), None);
        let report = match TrustVcTrustEngine::new().consume_native_trust_ir_bundle(&bundle) {
            Err(TrustEngineError::NativeTrustIrAssertionIdRenderingsDisagree {
                reason, ..
            }) => {
                assert!(reason.contains("repeats a key"), "{reason}");
                continue;
            }
            Ok(report) => report,
            Err(error) => panic!("ambiguity must be refused by the input/codec guard: {error}"),
        };
        let answer = post(&report);
        assert!(
            matches!(answer.outcome(), TrustVcNativeTrustIrDischargeStatus::Declined { .. }),
            "ambiguous formula bytes must be refused, rather than decided after dropping a key: {fields}; {answer:?}"
        );
        assert!(report.produced_certificates().is_empty());
        assert!(report.admit_native_proof_artifacts().is_empty());
    }
}

#[test]
fn a_second_rendering_cannot_change_the_formula_being_decided() {
    let report = consume(&question(Some(r#""formula":{"Bool":true}"#), Some("false")));
    assert!(matches!(
        post(&report).outcome(),
        TrustVcNativeTrustIrDischargeStatus::Declined { .. }
    ));
    assert!(post(&report).message().contains("two renderings"));
    assert!(report.produced_certificates().is_empty());
}

// Serialize with the canonical IR vocabulary. This specifically
// exercises the mathematical binders: machine-width arithmetic is separately
// refused rather than silently treating a Rust integer as an unbounded one.
fn canonical_question(node: &str) -> NativeVerificationBundle {
    let formula: trust_types::Formula = serde_json::from_str(node).unwrap();
    let fields = format!("\"formula\":{}", serde_json::to_string(&formula).unwrap());
    // Use the established single-payload lane. A separate test above covers
    // the byte-identical dual-rendering guard, before arithmetic lowering.
    question(Some(&fields), None)
}

fn reject_euclidean_only_claim(node: &str) -> TrustVcNativeTrustIrBundleReport {
    let original = question(None, None);
    let false_claim = canonical_question(node);
    assert_eq!(original.module.functions, false_claim.module.functions);
    let report = consume(&false_claim);
    let answer = post(&report);
    println!("canonical truncated arithmetic: {answer:?}");
    assert!(
        matches!(
            answer.outcome(),
            TrustVcNativeTrustIrDischargeStatus::Counterexample { .. }
                | TrustVcNativeTrustIrDischargeStatus::Unknown { .. }
                | TrustVcNativeTrustIrDischargeStatus::NotProved
        ),
        "a claim false under canonical truncated arithmetic must not gain a Euclidean proof: {answer:?}"
    );
    assert!(
        report
            .produced_certificates()
            .iter()
            .all(|certificate| { certificate.obligation_id() != POST.index() })
    );
    report
}

#[test]
fn a_negative_remainder_cannot_gain_euclidean_nonnegativity() {
    // n = -1 refutes this: canonical Rem(-1, 5) = -1. Euclidean mod is
    // always nonnegative and would turn this false universal claim into true.
    // Truncating remainder has the dividend's sign for either divisor sign.
    // Require the production consumer to expose an independently checked
    // counterexample; an undecided answer leaves this recovery defect open.
    for divisor in [5, -5] {
        let report = reject_euclidean_only_claim(&format!(
            r#"{{"Forall":[[["n","Int"]],{{"Ge":[{{"Rem":[{{"Var":["n","Int"]}},{{"Int":{divisor}}}]}},{{"Int":0}}]}}]}}"#,
        ));
        assert!(
            matches!(
                post(&report).outcome(),
                TrustVcNativeTrustIrDischargeStatus::Counterexample { .. }
            ),
            "the original remainder question needs a checked counterexample for divisor {divisor}: {:?}",
            post(&report)
        );
    }
}

#[test]
fn negative_division_cannot_gain_an_euclidean_quotient() {
    // Canonical Div(-7, 2) = -3, whereas Euclidean div(-7, 2) = -4.
    let report = reject_euclidean_only_claim(
        r#"{"Forall":[[["n","Int"]],{"Implies":[{"Eq":[{"Var":["n","Int"]},{"Int":-7}]},{"Eq":[{"Div":[{"Var":["n","Int"]},{"Int":2}]},{"Int":-4}]}]}]}"#,
    );
    assert!(matches!(
        post(&report).outcome(),
        TrustVcNativeTrustIrDischargeStatus::Counterexample { .. }
    ));
}
