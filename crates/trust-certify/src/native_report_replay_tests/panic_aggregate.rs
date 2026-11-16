//! Original panic-aggregate prerequisite checks, never source/proof authority.

use super::*;

const ORIGINAL_VC: &str = r#"{"kind":{"Assertion":{"message":"panic freedom: no assertion, `unreachable!`, or panic is reachable"}},"function":"trust_ir_laws::laws::assert_class_arithmetic_safety","location":{"file":"crates/trust-ir-laws/src/laws.rs","line_start":1293,"col_start":0,"line_end":1297,"col_end":1},"formula":{"Var":["panic_reachable:vc:trust_ir_laws__laws__assert_class_arithmetic_safety:assertion:panic-freedom:0","Bool"]},"contract_metadata":null,"obligation":null}"#;
const ORIGINAL_ID: &str =
    "vc:trust_ir_laws__laws__assert_class_arithmetic_safety:assertion:panic-freedom:0";
const TARGET: &str = "arm64-apple-macosx;ptr64";

fn snapshot(vc: &VerificationCondition) -> trust_types::OriginalVcSnapshot {
    let digest =
        trust_types::original_vc_snapshot::exact_vc_claim_digest_sha256(vc, true, Some(TARGET))
            .unwrap();
    trust_types::OriginalVcSnapshot::capture(vc, true, TARGET, ORIGINAL_ID, &digest).unwrap()
}

#[test]
fn bare_panic_aggregate_requires_its_own_checked_relation() {
    // Exact original compiler VC from the retained 396-law report, not the
    // native CHC error query or a Boolean synthesized from its verdict.
    let original: VerificationCondition = serde_json::from_str(ORIGINAL_VC).unwrap();
    let saved = snapshot(&original);
    let restored = saved.decode_for_row(ORIGINAL_ID, &saved.claim_digest_sha256).unwrap();
    assert_eq!(serde_json::to_string(&restored).unwrap(), ORIGINAL_VC);
    assert!(restored.obligation.is_none());
    let refusal = restored.kernel_authority_refusal().expect("missing checked relation");
    assert!(refusal.contains("bare Boolean assertion"));
    assert!(certify_vc(&restored).is_none());
    assert!(certify_vc_for_native_planning(&restored).is_none());

    // A record which merely repeats the unbound placeholder is not a relation.
    let mut repeated = restored.clone();
    repeated.obligation = Some(trust_types::ObligationRecord {
        body: repeated.formula.clone(),
        wrappers: Vec::new(),
        subject: None,
        width: None,
    });
    assert!(repeated.kernel_authority_refusal().is_some());
    assert!(certify_vc(&repeated).is_none());
    // The decision must not rely on compiler/function/variable display names.
    let mut renamed = restored.clone();
    renamed.function = "other::function".into();
    renamed.kind = VcKind::Assertion { message: "ordinary assertion".into() };
    renamed.formula = Formula::Var("arbitrary_name".into(), Sort::Bool);
    assert_eq!(renamed.kernel_authority_refusal(), Some(refusal));

    // A real typed violation still reaches the existing producer AFTER the
    // opaque attempt declined. This fixture is not a refinement of ORIGINAL_VC.
    let x = || Formula::Var("relation_x".into(), Sort::Int);
    let mut grounded = restored.clone();
    grounded.formula = Formula::And(vec![
        Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
        Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
    ]);
    assert_eq!(grounded.kernel_authority_refusal(), None);
    let proof = certify_vc(&grounded).expect("actual row-specific kernel refutation");
    assert!(replay_vc_evidence(&grounded, &proof));
    let grounded_saved = snapshot(&grounded);
    assert!(recheck_presented_original_vc_snapshot(
        &grounded_saved,
        &grounded,
        ORIGINAL_ID,
        true,
        TARGET,
        &proof
    ));
    assert!(!recheck_presented_original_vc_snapshot(
        &saved,
        &grounded,
        ORIGINAL_ID,
        true,
        TARGET,
        &proof
    ));
    assert!(!replay_vc_evidence(&restored, &proof));

    // Boolean grounding is equally admissible. As above, this is a constructed
    // contradictory VC, not a checked refinement of the original source/body.
    let p = Formula::Var("bool_relation".into(), Sort::Bool);
    let mut boolean = restored.clone();
    boolean.formula = Formula::And(vec![p.clone(), Formula::Not(Box::new(p.clone()))]);
    assert_eq!(boolean.kernel_authority_refusal(), None);
    let bool_proof = certify_vc(&boolean).expect("Boolean relation kernel refutation");
    assert!(replay_vc_evidence(&boolean, &bool_proof));
    let trust_ir::ProofEvidence::CleanCic { term, context, .. } = &bool_proof else { panic!() };
    assert!(stored_context_check(term, context));
    let bool_snapshot = snapshot(&boolean);
    let decoded = bool_snapshot
        .decode_for_row(ORIGINAL_ID, &bool_snapshot.claim_digest_sha256)
        .expect("exact Boolean snapshot binding");
    assert_eq!(serde_json::to_string(&decoded).unwrap(), serde_json::to_string(&boolean).unwrap());
    // The separate direct-presented audit currently admits linear-Int contexts
    // only. Its intentional refusal must not be confused with general replay.
    assert!(!recheck_presented_original_vc_snapshot(
        &bool_snapshot,
        &boolean,
        ORIGINAL_ID,
        true,
        TARGET,
        &bool_proof
    ));
    let mut wrong_boolean = boolean.clone();
    wrong_boolean.formula = Formula::And(vec![p, Formula::Bool(true)]);
    assert!(certify_vc(&wrong_boolean).is_none());
    let mut forged_boolean = bool_proof;
    let trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. } = &mut forged_boolean
    else {
        panic!()
    };
    *lineage = lineage_digest(term, context, &ObligationIdentity::from_vc(&wrong_boolean).unwrap());
    assert!(!replay_vc_evidence(&wrong_boolean, &forged_boolean));

    // Even a recomputed public lineage cannot make the old proof refute a
    // satisfiable wrong relation or the original free Boolean.
    let mut wrong = grounded.clone();
    wrong.formula = Formula::Lt(Box::new(x()), Box::new(Formula::Int(0)));
    assert!(certify_vc(&wrong).is_none());
    let trust_ir::ProofEvidence::CleanCic { term, context, .. } = proof else { panic!() };
    for candidate in [&wrong, &restored] {
        let forged = trust_ir::ProofEvidence::CleanCic {
            term: term.clone(),
            context: context.clone(),
            lineage: lineage_digest(
                &term,
                &context,
                &ObligationIdentity::from_vc(candidate).unwrap(),
            ),
            kernel_recheck: None,
        };
        assert!(!replay_vc_evidence(candidate, &forged));
        assert!(!recheck_presented_original_vc_snapshot(
            &snapshot(candidate),
            candidate,
            ORIGINAL_ID,
            true,
            TARGET,
            &forged
        ));
    }
}

#[test]
#[ignore = "requires the exact original 1116-row report/digest and a fresh owned output"]
fn audit_original_panic_aggregate_prerequisites() {
    let path = std::env::var_os("TRUST_ORIGINAL_PANIC_REPORT").expect("explicit original report");
    let path = Path::new(&path);
    let digest =
        std::env::var("TRUST_ORIGINAL_PANIC_REPORT_SHA256").expect("explicit report SHA256");
    let output = std::env::var_os("TRUST_ORIGINAL_PANIC_OUTPUT").expect("owned fresh output");
    let output = Path::new(&output);
    capture::require_fresh_output(output).unwrap();
    let raw = bound_read(path, &digest, capture::REPORT_LIMIT).unwrap();
    let wire: Value = trust_types::json_depth::from_slice_deep(&raw).unwrap();
    let mut rows = Vec::new();
    let mut ids = BTreeSet::new();
    let mut sound = 0;
    let mut certified = 0;
    let mut unknown = 0;
    for function in wire["functions"].as_array().unwrap() {
        for row in function["obligations"].as_array().unwrap() {
            let id = row["obligation_id"].as_str().unwrap();
            assert!(ids.insert(id.to_string()), "duplicate original row identity");
            let mut result = json!({"obligation_id": id,
                "reported_outcome": row["outcome"], "source_refinement_checked": false});
            if row["outcome"]["strength"]["assurance"] == "Sound" {
                sound += 1;
                assert_eq!(row["proof_evidence"]["suite"], "trust-mc");
                assert!(
                    !row["proof_evidence"]["artifacts"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|artifact| artifact["kind"] == "clean_cic")
                );
                let transport = &row["transport_evidence"];
                let saved: trust_types::OriginalVcSnapshot =
                    serde_json::from_value(transport["original_vc_snapshot"].clone()).unwrap();
                let claim = transport["claim_digest_sha256"].as_str().unwrap();
                let vc = saved.decode_for_row(id, claim).unwrap();
                assert!(vc.obligation.is_none());
                assert!(matches!(&vc.kind, VcKind::Assertion { message }
                    if message == "panic freedom: no assertion, `unreachable!`, or panic is reachable"));
                assert_eq!(vc.formula, Formula::Var(format!("panic_reachable:{id}"), Sort::Bool));
                let refusal = vc.kernel_authority_refusal().expect("typed relation is absent");
                assert!(refusal.contains("bare Boolean assertion"));
                assert!(certify_vc(&vc).is_none());
                result["original_payload_sha256"] = saved.payload_sha256.into();
                result["claim_digest_sha256"] = claim.into();
                result["kernel_prerequisite_refusal"] = refusal.into();
                result["clean_certificate_minted"] = false.into();
            } else if row["outcome"]["strength"]["assurance"] == "Certified" {
                certified += 1;
            } else {
                assert_eq!(row["outcome"]["status"], "unknown");
                unknown += 1;
            }
            rows.push(result);
        }
    }
    assert_eq!((rows.len(), certified, sound, unknown), (1116, 9, 317, 790));
    bound_read(path, &digest, capture::REPORT_LIMIT).unwrap();
    let receipt = json!({"schema":"trust.original-panic-prerequisite-audit.v1",
        "report":path, "report_sha256":digest, "rows":rows,
        "counts":{"all":1116,"reported_certified":9,"reported_sound":317,"reported_unknown":790},
        "boundary":"diagnostic only; no source refinement, native-to-CIC promotion or report authority",
        "missing_prerequisite":"checked general body/violation relation tied to the original row and source"});
    capture::write_fresh_output(output, &serde_json::to_vec_pretty(&receipt).unwrap()).unwrap();
    println!(
        "original panic prerequisite audit: 1116 retained, 317 explicit refusals; no authority"
    );
}
