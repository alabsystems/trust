//! Current native requests over unchanged historical compiler IR and contracts.
//! Historical request profiles remain terminal refusal controls. This is not
//! a new compiler capture or a compiler-wide coverage claim.

use super::*;

macro_rules! u64_capture {
    ($name:literal) => {{
        let public: TrustContractBundle = serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"), "/../trust-bmc/testdata/intbound-u64/", $name, "/public.json"
        ))).unwrap();
        let requested: Vec<TrustObligation> = serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"), "/../trust-bmc/testdata/intbound-u64/", $name, "/requested.json"
        ))).unwrap();
        let native: NativeVerificationBundle = serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../first-party/trust-wp/crates/trust-wp-lib/tests/body_contract/fixtures/u64_calls/", $name, ".json"
        ))).unwrap();
        let id = concat!("obligation:trust_intbound__", $name, ":postcondition:0");
        let raw: Vec<_> = requested.into_iter().filter(|row| row.obligation_id == id).collect();
        assert_eq!(raw.len(), 1, "the original authored question remains in the denominator");
        (public, raw, native)
    }};
}

/// Re-run the production request planner over the complete original module.
/// The retained compiler input and its public questions stay historical; only
/// the current request producer runs here, without live-source authority.
fn current_requests_for_historical_module(
    historical: &NativeVerificationBundle,
) -> NativeVerificationBundle {
    historical.validate().expect("valid historical compiler input");
    let [owner] = historical.compiler_facts.monomorphizations.as_slice() else {
        panic!("these complete captures must have exactly one original owner");
    };
    let function = owner.function.expect("original monomorphization names its function");
    let source_digest = historical.provenance.source_digest.expect("original source digest");
    assert_eq!(source_digest.algorithm, trust_ir::ProofDigestAlgorithm::Sha256);
    assert_eq!(
        historical.input,
        trust_ir::NativeAdapterInput::RustMir { body_digest: source_digest }
    );
    assert!(historical.compiler_facts.obligation_sources.iter().all(|source| {
        source.function == Some(function) && source.monomorphization == Some(owner.id)
    }));
    let planned = trust_ir_bridge::native_verification_bundle_from_module(
        historical.module.clone(),
        source_digest,
        function,
    )
    .expect("the current production planner must retain the entire original input");
    assert_eq!(planned.module, historical.module, "no body or contract may change");
    assert_eq!(planned.trust_ir_module_digest, historical.trust_ir_module_digest);
    assert_eq!(planned.input, historical.input);
    assert_eq!(planned.provenance.source_digest, historical.provenance.source_digest);
    assert_eq!(planned.compiler_facts, historical.compiler_facts);
    assert_eq!(planned.requests.len(), historical.requests.len());
    for (current, original) in planned.requests.iter().zip(&historical.requests) {
        // Compare every request, including obligations not selected by these
        // consumer tests; never manufacture a smaller proof inventory.
        assert_eq!(current.id(), original.id());
        assert_eq!(current.obligations(), original.obligations());
        match (current, original) {
            (
                trust_ir::NativeVerificationRequest::TrustMc(current),
                trust_ir::NativeVerificationRequest::TrustMc(original),
            ) => {
                assert_eq!(current.function, original.function);
                assert_eq!(current.mode, original.mode);
                assert_eq!(current.options, trust_ir_bridge::trust_mc_chc_request_options());
            }
            (
                trust_ir::NativeVerificationRequest::TrustVc(current),
                trust_ir::NativeVerificationRequest::TrustVc(original),
            ) => {
                assert_eq!(current.function, original.function);
                assert_eq!(current.mode, original.mode);
            }
            (
                trust_ir::NativeVerificationRequest::TrustWp(current),
                trust_ir::NativeVerificationRequest::TrustWp(original),
            ) => {
                assert_eq!(current.function, original.function);
                assert_eq!(current.mode, original.mode);
                assert_eq!(current.options, original.options);
            }
            _ => panic!("the current planner changed an original engine request variant"),
        }
    }
    assert_ne!(planned.stable_digest(), historical.stable_digest());
    planned
}

#[test]
fn historical_mc_request_profiles_remain_terminal_without_wp_credit() {
    let mut captures = vec![
        u64_capture!("clamp_unsigned_to_width"),
        u64_capture!("signed_fits_magnitude"),
        u64_capture!("signed_fits_nonneg"),
        u64_capture!("signed_max"),
        u64_capture!("unsigned_fits"),
        u64_capture!("signed_min_magnitude"),
    ];
    captures.push(captured_shift_mask());
    for (public, requested, historical) in captures {
        let refused = FullVerificationEngine::with_required_native_engines()
            .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                &public,
                &requested,
                &historical,
                &VerifierExecutionContext::new("historical-native-request-profile"),
            );
        assert_eq!(refused.result().summary.proved, 0, "{:#?}", refused.result());
        assert_eq!(
            refused.result().summary.unsupported,
            requested.len(),
            "{:#?}",
            refused.result()
        );
        assert_eq!(refused.result().evidence.len(), requested.len());
        assert!(refused.checked_native_wp_proofs().is_empty());
        for obligation in &requested {
            let rows = refused
                .result()
                .evidence
                .iter()
                .filter(|row| row.obligation_id == obligation.obligation_id)
                .collect::<Vec<_>>();
            assert_eq!(rows.len(), 1, "every original selected question remains accounted for");
            let row = rows[0];
            assert_eq!(row.status, EvidenceStatus::Unsupported);
            assert!(row.decline.is_none(), "an option refusal is terminal");
            assert!(row.proof_strength.is_none() && row.counterexample.is_none());
            assert!(
                !row.artifacts
                    .iter()
                    .any(|artifact| { artifact.kind == EvidenceArtifactKind::ProofCertificate })
            );
        }
    }
}

#[test]
fn captured_u64_calls_use_default_mc_to_wp_with_exact_evidence() {
    for (public, requested, historical) in [
        u64_capture!("clamp_unsigned_to_width"),
        u64_capture!("signed_fits_magnitude"),
        u64_capture!("signed_fits_nonneg"),
        u64_capture!("signed_max"),
        u64_capture!("unsigned_fits"),
    ] {
        let native = current_requests_for_historical_module(&historical);
        let obligation = &requested[0];
        let run = |public: &TrustContractBundle, native: &NativeVerificationBundle| {
            FullVerificationEngine::with_required_native_engines()
                .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                    public,
                    &requested,
                    native,
                    &VerifierExecutionContext::new("original-u64-call"),
                )
        };
        let proved = run(&public, &native);
        assert_eq!(proved.result().summary.proved, 1, "{:#?}", proved.result());
        assert_eq!(proved.checked_native_wp_proofs().len(), 1);
        let row = &proved.result().evidence[0];
        let fact = &proved.checked_native_wp_proofs()[&obligation.obligation_id];
        assert_eq!(row.proof_strength, Some(ProofStrength::deductive()));
        assert!(fact.matches(&public, &native, obligation, row));
        assert!(!fact.matches(&public, &historical, obligation, row));

        let mut changed_public = public.clone();
        let contract = changed_public
            .contracts
            .iter_mut()
            .find(|contract| Some(&contract.contract_id) == obligation.contract_id.as_ref())
            .unwrap();
        let ContractPredicate::TrustIr { value, .. } = &mut contract.predicate else {
            panic!("original typed postcondition");
        };
        value["root"] =
            serde_json::json!({"sort":"bool", "kind":{"node":"bool_literal", "value":false}});
        value["variables"] = serde_json::json!([]);
        assert!(!fact.matches(&changed_public, &native, obligation, row));
        let rejected = run(&changed_public, &native);
        assert_eq!(rejected.result().summary.proved, 0);
        assert!(rejected.checked_native_wp_proofs().is_empty());

        let mut changed_body = native.clone();
        let mut changed = false;
        'functions: for function in &mut changed_body.module.functions {
            for node in function.blocks.iter_mut().flat_map(|block| &mut block.body) {
                if let trust_ir::Inst::Const {
                    ty: trust_ir::Ty::U64,
                    value: trust_ir::Constant::Int(value),
                } = &mut node.inst
                {
                    *value ^= 1;
                    changed = true;
                    break 'functions;
                }
            }
        }
        assert!(changed);
        let digest = changed_body.module.stable_digest();
        changed_body.trust_ir_module_digest = digest;
        for node in &mut changed_body.lineage.nodes {
            node.target_module = digest;
        }
        changed_body.validate().unwrap();
        assert!(!fact.matches(&public, &changed_body, obligation, row));
    }
}

#[test]
fn captured_source_only_u64_clause_remains_refused() {
    let (public, requested, historical) = u64_capture!("signed_min_magnitude");
    let native = current_requests_for_historical_module(&historical);
    let result = FullVerificationEngine::with_required_native_engines()
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            &public,
            &requested,
            &native,
            &VerifierExecutionContext::new("original-source-only-u64"),
        );
    assert_eq!(result.result().summary.proved, 0, "{:#?}", result.result());
    assert!(result.checked_native_wp_proofs().is_empty());
}

fn captured_shift_mask() -> (TrustContractBundle, Vec<TrustObligation>, NativeVerificationBundle) {
    let public = serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../trust-bmc/testdata/widthconv-shift-mask/public.json"
    )))
    .unwrap();
    let requested: Vec<TrustObligation> = serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../trust-bmc/testdata/widthconv-shift-mask/requested.json"
    )))
    .unwrap();
    let native = serde_json::from_str(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../trust-bmc/testdata/widthconv-shift-mask/native.json"
    )))
    .unwrap();
    let raw: Vec<_> = requested
        .into_iter()
        .filter(|row| {
            row.metadata.iter().any(|entry| {
                entry.key == "trust.ir.raw-source-postcondition.v1" && entry.value == "query-bound"
            })
        })
        .collect();
    assert_eq!(raw.len(), 2, "both original authored postconditions must remain selected");
    assert!(raw.iter().all(|row| row.kind == ObligationKind::Postcondition));
    (public, raw, native)
}

#[test]
fn captured_unsigned_postconditions_use_default_mc_to_wp_with_bound_facts() {
    let (public, requested, historical) = captured_shift_mask();
    let native = current_requests_for_historical_module(&historical);
    let run = |public: &TrustContractBundle, native: &NativeVerificationBundle, id: &str| {
        FullVerificationEngine::with_required_native_engines()
            .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                public,
                &requested,
                native,
                &VerifierExecutionContext::new(id),
            )
    };
    let proved = run(&public, &native, "captured-shift-mask-default-native");
    assert_eq!(
        proved.result().summary.proved,
        2,
        "{:#?}\ninner WP results: {:#?}\nderived WP requests: {:#?}",
        proved.result(),
        trust_wp_lib::trust_ir_body::verify_trust_ir_body_contracts(&native),
        trust_wp_lib::trust_ir_body::trust_ir_native_bundle_to_body_verify_requests(&native)
    );
    assert_eq!(proved.result().evidence.len(), 2);
    assert_eq!(proved.checked_native_wp_proofs().len(), 2);
    for obligation in &requested {
        let evidence = proved
            .result()
            .evidence
            .iter()
            .find(|row| row.obligation_id == obligation.obligation_id)
            .unwrap();
        let fact = &proved.checked_native_wp_proofs()[&obligation.obligation_id];
        assert_eq!(evidence.status, EvidenceStatus::Proved);
        assert_eq!(evidence.proof_strength, Some(ProofStrength::deductive()));
        assert!(evidence.satisfies_proof_artifact_policy());
        assert!(fact.matches(&public, &native, obligation, evidence));
        assert!(!fact.matches(&public, &historical, obligation, evidence));
    }

    let mut changed_public = public.clone();
    for obligation in &requested {
        let contract_id = obligation.contract_id.as_ref().unwrap();
        let contract = changed_public
            .contracts
            .iter_mut()
            .find(|contract| &contract.contract_id == contract_id)
            .unwrap();
        let ContractPredicate::TrustIr { value, .. } = &mut contract.predicate else {
            panic!("the capture must retain its original typed public predicate");
        };
        value["root"] = serde_json::json!({
            "sort": "bool", "kind": {"node": "bool_literal", "value": false}
        });
        value["variables"] = serde_json::json!([]);
    }
    let refused = run(&changed_public, &native, "captured-shift-mask-changed-public");
    assert_eq!(refused.result().summary.proved, 0, "{:#?}", refused.result());
    assert!(refused.checked_native_wp_proofs().is_empty());

    let mut false_body = native.clone();
    let function = &mut false_body.module.functions[0];
    let false_value = function
        .blocks
        .iter()
        .flat_map(|block| &block.body)
        .find_map(|node| {
            matches!(
                node.inst,
                trust_ir::Inst::Const { value: trust_ir::Constant::Bool(false), .. }
            )
            .then(|| node.results[0])
        })
        .expect("original false constant");
    let condition = function
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.body)
        .find_map(|node| {
            if let trust_ir::Inst::Assume { cond } = &mut node.inst { Some(cond) } else { None }
        })
        .expect("original range assumption");
    *condition = false_value;
    let digest = false_body.module.stable_digest();
    false_body.trust_ir_module_digest = digest;
    for node in &mut false_body.lineage.nodes {
        node.target_module = digest;
    }
    false_body.validate().expect("valid native transport after changing the body");
    assert!(trust_ir_build::validate_module(&false_body.module).is_empty());
    let rejected = run(&public, &false_body, "captured-shift-mask-false-assume");
    assert_eq!(rejected.result().summary.proved, 0, "{:#?}", rejected.result());
    // The authored public records bind the original body digest. Mutating the
    // body is not authority to regenerate those records: reject the stale
    // binding before any semantic verdict, and never reuse the original facts.
    assert_eq!(rejected.result().summary.unsupported, 2, "{:#?}", rejected.result());
    assert!(rejected.checked_native_wp_proofs().is_empty());
    for obligation in &requested {
        let evidence = proved
            .result()
            .evidence
            .iter()
            .find(|row| row.obligation_id == obligation.obligation_id)
            .unwrap();
        let fact = &proved.checked_native_wp_proofs()[&obligation.obligation_id];
        assert!(!fact.matches(&changed_public, &native, obligation, evidence));
        assert!(!fact.matches(&public, &false_body, obligation, evidence));
    }
}
