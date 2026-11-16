use std::path::Path;
use std::sync::OnceLock;

use sha2::{Digest, Sha256};
use trust_types::*;

fn historical_scoped() -> TransportObligationResult {
    serde_json::from_str::<Vec<TransportObligationResult>>(include_str!(
        "fixtures/native_body_wp_current_v2_transport.json"
    ))
    .unwrap()
    .remove(0)
}

fn current_capture() -> TransportObligationResult {
    // Exact original rustc transport row from source5751. Its native objects
    // were path-backed at capture; these copies are their exact original bytes,
    // independently matched to the raw row and the compiler's inline report.
    let bytes = include_bytes!("fixtures/native_body_wp_full_input_5751/transport.json");
    assert_eq!(
        digest::lowercase_hex(&Sha256::digest(bytes)),
        "6f93deb370fba4a5895ad88272c275cb42e76c7abb6b1b020e710d5c9af7d1a6"
    );
    let mut row: TransportObligationResult = serde_json::from_slice(bytes).unwrap();
    let objects: &[(&str, &[u8])] = &[
        (
            "3e4827751c3bd21db0af466455c631df382cefad2c0cdcfcb2019d6a7a85458b",
            include_bytes!(
                "fixtures/native_body_wp_full_input_5751/objects/3e4827751c3bd21db0af466455c631df382cefad2c0cdcfcb2019d6a7a85458b"
            ),
        ),
        (
            "c5f492681b135653c8572c1a95fd060697c06c74452fa38dbc5c306762128a46",
            include_bytes!(
                "fixtures/native_body_wp_full_input_5751/objects/c5f492681b135653c8572c1a95fd060697c06c74452fa38dbc5c306762128a46"
            ),
        ),
        (
            "f3baef600714a8a38aaa1009de210e45bb2c62081706a363238eabdc9893e292",
            include_bytes!(
                "fixtures/native_body_wp_full_input_5751/objects/f3baef600714a8a38aaa1009de210e45bb2c62081706a363238eabdc9893e292"
            ),
        ),
    ];
    let native = row.native_trust_ir.as_mut().unwrap();
    assert_eq!(native.artifacts.len(), objects.len());
    for artifact in &mut native.artifacts {
        let sha = &artifact.digest.as_ref().unwrap().value;
        let (_, bytes) = objects.iter().find(|(expected, _)| *expected == sha.as_str()).unwrap();
        assert_eq!(digest::lowercase_hex(&Sha256::digest(bytes)), *sha);
        let materialization = artifact.materialization.as_ref().unwrap();
        assert_eq!(u64::try_from(bytes.len()).unwrap(), materialization.byte_len);
        artifact.materialization = TransportArtifactMaterialization::from_exact_bytes(
            bytes,
            materialization.proof_binding_id.clone(),
            materialization.referenced_artifacts.clone(),
        );
    }
    row
}

fn actual() -> TransportObligationResult {
    static VERIFIED: OnceLock<TransportObligationResult> = OnceLock::new();
    VERIFIED
        .get_or_init(|| {
            use trust_ir::ValidatedNativeBundle;
            use trust_wp_lib::trust_ir_body::{
                replay_trust_ir_body_request_validated, verify_trust_ir_body_request_validated,
            };

            // Reuse the complete current compiler input. Generate a new proof
            // from the actual verifier, never normalize a stale schema or
            // relabel a historical proof's question/result.
            let mut row = current_capture();
            let original = row.clone();
            let native = decoded_native_bundle(&row);
            let native_before = native.clone();
            let request = row.proof_evidence.as_ref().unwrap().request_id.as_ref().unwrap();
            let request = trust_ir::NativeRequestId::new(request.parse().unwrap());
            let admitted = ValidatedNativeBundle::new(&native).unwrap();
            let verified = verify_trust_ir_body_request_validated(&admitted, request).unwrap();
            assert_eq!(verified.result().status, trust_wp_lib::VerifyBundleStatus::Verified);
            replay_trust_ir_body_request_validated(
                &admitted,
                request,
                verified.result(),
                Some(verified.witness()),
            )
            .unwrap();
            assert_eq!(verified.witness().native_bundle_digest, native.stable_digest());
            rewrite_payload(&mut row, |certificate| {
                certificate["statement"]["results"] = serde_json::json!([verified.result()]);
                certificate["statement"]["translation_witness"] =
                    serde_json::to_value(verified.witness()).unwrap();
            });
            assert_eq!(native, native_before);
            assert_eq!(row.native_trust_ir, original.native_trust_ir);
            assert_eq!(current_capture(), original, "current captured input stays immutable");
            assert_eq!(defect(&row, None), None);
            row
        })
        .clone()
}

#[test]
fn historical_scoped_certificate_with_stale_schema_is_refused_without_normalization() {
    let row = historical_scoped();
    let original = row.clone();
    assert_eq!(
        defect(&row, None).as_deref(),
        Some(
            "modern body-WP native input identity cannot be decoded: native bundle transport loses fields during typed decoding"
        ),
    );
    assert_eq!(row, original);
}

// Exact source64c failed-unit export, retained solely as a transport-codec
// reproducer. It is not a qualified positive fixture or proof authority.
#[test]
fn historical_inputs_preserve_the_exact_lossless_schema_refusal() {
    use trust_ir::request::{NativeVerificationBundle, transport};

    let bytes = include_bytes!("fixtures/native_body_wp_failed_unit_forensic.json");
    assert_eq!(
        digest::lowercase_hex(&Sha256::digest(bytes)),
        "a030619d5e963e579a64e992737df75edc90018d14a3ac7eafa1a60acc1348f2"
    );
    let mut rows: Vec<TransportObligationResult> = serde_json::from_slice(bytes).unwrap();
    rows.push(historical_scoped());
    let original = rows.clone();
    let mut bundles = 0;
    for row in &rows {
        let native = row.native_trust_ir.as_ref().unwrap();
        for artifact in &native.artifacts {
            let materialization = artifact.materialization.as_ref().unwrap();
            let envelope: serde_json::Value =
                serde_json::from_slice(&materialization.decoded_bytes().unwrap()).unwrap();
            if envelope["role"] != "bundle" {
                continue;
            }
            bundles += 1;
            let payload = &envelope["payload"];
            assert_eq!(payload["encoding"], transport::NATIVE_BUNDLE_REPLAY_FORMULA_REF_ENCODING);
            assert!(
                serde_json::from_value::<NativeVerificationBundle>(payload["bundle"].clone())
                    .is_err(),
                "the original missing-formula failure must remain reproduced"
            );
            assert_eq!(
                transport::rehydrate_native_bundle_transport_payload(payload).unwrap_err(),
                "native bundle transport loses fields during typed decoding"
            );
            // Test-only diagnostic expansion explains the exact refusal; it
            // never feeds normalized input to production or earns proof credit.
            let mut inline = payload["bundle"].clone();
            let formulas: std::collections::BTreeMap<u64, serde_json::Value> =
                inline["module"]["proof_obligations"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|proof| (proof["id"].as_u64().unwrap(), proof["formula"].clone()))
                    .collect();
            for request in inline["requests"].as_array_mut().unwrap() {
                for request in request.as_object_mut().unwrap().values_mut() {
                    let Some(atoms) = request
                        .pointer_mut("/provenance/replay_context/atoms")
                        .and_then(serde_json::Value::as_array_mut)
                    else {
                        continue;
                    };
                    for atom in atoms {
                        if let Some(reference) = atom.as_object_mut().unwrap().remove("formula_ref")
                        {
                            let id = reference["obligation"].as_u64().unwrap();
                            assert_eq!(atom["obligation"].as_u64(), Some(id));
                            assert!(
                                atom.as_object_mut()
                                    .unwrap()
                                    .insert("formula".into(), formulas[&id].clone())
                                    .is_none()
                            );
                        }
                    }
                }
            }
            let typed: NativeVerificationBundle = serde_json::from_value(inline.clone()).unwrap();
            let restored = serde_json::to_value(&typed).unwrap();
            assert!(inline["module"].get("closure_layouts").is_none());
            let mut expected = inline;
            expected["module"]["closure_layouts"] = serde_json::json!([]);
            assert_eq!(
                restored, expected,
                "the ONLY round-trip delta is /module/closure_layouts: absent → []"
            );
        }
    }
    assert_eq!(bundles, rows.len());
    assert!(!rows.is_empty());
    assert_eq!(rows, original, "codec inspection must leave forensic evidence unchanged");
}

#[test]
fn historical_v1_compiler_certificate_cannot_authorize_the_v2_body_family() {
    let row = serde_json::from_str::<Vec<TransportObligationResult>>(include_str!(
        "fixtures/native_body_wp_transport.json"
    ))
    .unwrap()
    .remove(0);
    assert_eq!(
        defect(&row, None).as_deref(),
        Some("modern body-WP certificate header is not the accepted native body family")
    );
}

fn defect(row: &TransportObligationResult, root: Option<&Path>) -> Option<String> {
    let proof = row.proof_evidence.as_ref().unwrap();
    modern_body_wp_proof_defect(
        &proof.artifacts,
        row.obligation_id.as_deref(),
        proof.request_id.as_deref(),
        proof.proof_id.as_deref(),
        proof.strength.as_ref().unwrap(),
        proof.evidence.as_ref().unwrap(),
        row.native_trust_ir.as_ref().unwrap(),
        root,
    )
}

fn rewrite_payload(
    row: &mut TransportObligationResult,
    mutate: impl FnOnce(&mut serde_json::Value),
) {
    let owner = row.obligation_id.as_ref().unwrap().clone();
    let artifact = &mut row.proof_evidence.as_mut().unwrap().artifacts[0];
    let materialization = artifact.materialization.as_ref().unwrap();
    let bytes = materialization.decoded_bytes().unwrap();
    // This test-only editor preserves the existing envelope header. Production
    // uses the shared strict envelope reader and never rewrites accepted bytes.
    let offset = bytes.iter().position(|byte| *byte == b'{').unwrap();
    let mut payload: serde_json::Value = serde_json::from_slice(&bytes[offset..]).unwrap();
    mutate(&mut payload);
    let payload = serde_json::to_vec(&payload).unwrap();
    let mut edited = bytes[..offset - 8].to_vec();
    edited.extend_from_slice(&(payload.len() as u64).to_be_bytes());
    edited.extend_from_slice(&payload);
    artifact.digest.as_mut().unwrap().value = digest::lowercase_hex(&Sha256::digest(&edited));
    artifact.uri = Some(format!(
        "trust-wp-body://{owner}/certificate/sha256/{}",
        artifact.digest.as_ref().unwrap().value
    ));
    artifact.materialization = TransportArtifactMaterialization::from_exact_bytes(
        &edited,
        materialization.proof_binding_id.clone(),
        materialization.referenced_artifacts.clone(),
    );
}

#[test]
fn actual_full_input_verifier_certificate_is_structurally_publishable() {
    let row = actual();
    let original = row.clone();
    assert_eq!(defect(&row, None), None);
    assert!(native_trust_ir_artifact_shape_is_publishable(row.native_trust_ir.as_ref().unwrap()));
    assert_eq!(
        transport_proof_artifact_topology_defect(
            "trust-wp",
            &row.proof_evidence.as_ref().unwrap().artifacts,
            row.obligation_id.as_deref()
        ),
        None
    );
    assert_eq!(row, original);
}

#[test]
fn changed_outer_owner_or_selected_ids_are_rejected() {
    for mutation in 0..5 {
        let mut row = actual();
        match mutation {
            0 => row.obligation_id = Some("another-owner".into()),
            1 => row.proof_evidence.as_mut().unwrap().request_id = Some("4".into()),
            2 => row.proof_evidence.as_mut().unwrap().proof_id = Some("1".into()),
            3 => row.proof_evidence.as_mut().unwrap().request_id = Some("03".into()),
            _ => row.proof_evidence.as_mut().unwrap().proof_id = None,
        }
        assert!(defect(&row, None).is_some(), "mutation {mutation}");
    }
}

#[test]
fn changed_content_digest_uri_and_owner_binding_are_rejected() {
    for mutation in 0..5 {
        let mut row = actual();
        let original = row.clone();
        let artifact = &mut row.proof_evidence.as_mut().unwrap().artifacts[0];
        match mutation {
            0 => artifact.materialization.as_mut().unwrap().encoded_bytes.replace_range(0..2, "00"),
            1 => {
                let digest = &mut artifact.digest.as_mut().unwrap().value;
                let replacement = if digest.starts_with('0') { "1" } else { "0" };
                digest.replace_range(0..1, replacement);
            }
            2 => {
                artifact.uri =
                    Some(artifact.uri.as_ref().unwrap().replace("certificate/", "transcript/"))
            }
            3 => {
                artifact.materialization.as_mut().unwrap().proof_binding_id =
                    "trust_ir-native-trust-wp-request-3-proof-0".into()
            }
            _ => {
                artifact.uri = Some(format!(
                    "trust-wp-body://different_source/certificate/sha256/{}",
                    artifact.digest.as_ref().unwrap().value,
                ))
            }
        }
        assert_ne!(row, original, "mutation {mutation} must change its input");
        assert!(defect(&row, None).is_some(), "mutation {mutation}");
    }
}

#[test]
fn independently_rehashed_wrong_headers_still_refuse() {
    for mutation in 0..14 {
        let mut row = actual();
        let original = row.clone();
        rewrite_payload(&mut row, |payload| match mutation {
            0 => payload["statement"]["request"]["id"] = 4.into(),
            1 => payload["statement"]["request"]["obligations"] = serde_json::json!([1]),
            2 => payload["statement"]["obligation_id"] = "another-owner".into(),
            3 => payload["accepted"] = false.into(),
            4 => payload["authority"] = "Certified".into(),
            5 => payload["statement"]["schema"] = "trust-wp.formula-only.v1".into(),
            6 => {
                payload["statement"]["results"][0]["obligation_results"][0]["obligation_id"] =
                    "trust-ir-r3-proof-1".into()
            }
            7 => payload["statement"]["request"]["obligations"] = serde_json::json!([0, 1]),
            8 => payload["statement"]["request"]["function"] = 1.into(),
            9 => payload["statement"]["request"]["lineage_roots"] = serde_json::json!([1]),
            10 => {
                payload["statement"]["request"]["options"]["max_abduced_preconditions"] = 99.into()
            }
            11 => {
                let byte = &mut payload["statement"]["module_digest"]["bytes"][0];
                *byte = (byte.as_u64().unwrap() ^ 1).into();
            }
            12 => {
                let byte = &mut payload["statement"]["source_digest"]["bytes"][0];
                *byte = (byte.as_u64().unwrap() ^ 1).into();
            }
            _ => payload["statement"]["results"][0]["bundle_id"] = "legacy-formula-only".into(),
        });
        assert_ne!(row, original, "mutation {mutation} must change its input");
        assert!(defect(&row, None).is_some(), "mutation {mutation}");
    }
}

#[test]
fn a_digest_shaped_result_id_does_not_replace_the_complete_original_input() {
    let original = actual();
    assert_eq!(defect(&original, None), None);
    for digit in 0..64 {
        let mut row = original.clone();
        rewrite_payload(&mut row, |payload| {
            let id = payload["statement"]["results"][0]["bundle_id"].as_str().unwrap();
            let (prefix, digest) = id.rsplit_once(":input:sha256:").unwrap();
            assert_eq!(digest.len(), 64);
            let mut changed = digest.as_bytes().to_vec();
            changed[digit] = if changed[digit] == b'0' { b'1' } else { b'0' };
            payload["statement"]["results"][0]["bundle_id"] =
                format!("{prefix}:input:sha256:{}", String::from_utf8(changed).unwrap()).into();
        });
        assert_eq!(
            defect(&row, None).as_deref(),
            Some("modern body-WP result does not bind the complete original native input"),
            "digest digit {digit}"
        );
    }
}

#[test]
fn independently_rehashed_native_provenance_still_needs_its_own_wp_input_identity() {
    let mut row = actual();
    assert_eq!(defect(&row, None), None);
    rewrite_native_bundle(&mut row, |bundle| {
        let version = bundle["provenance"]["producer_version"].as_str().unwrap();
        bundle["provenance"]["producer_version"] = format!("{version}+another-input").into();
    });
    assert_eq!(
        defect(&row, None).as_deref(),
        Some("modern body-WP result does not bind the complete original native input")
    );
}

#[test]
fn independently_rehashed_unselected_request_still_changes_the_full_wp_input() {
    let mut row = actual();
    assert_eq!(defect(&row, None), None);
    let selected_before = row.proof_evidence.clone();
    rewrite_native_bundle(&mut row, |bundle| {
        let request = bundle["requests"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find_map(|request| request.get_mut("TrustMc"))
            .unwrap();
        let old = request["diagnostics"]["emit_counterexamples"].as_bool().unwrap();
        request["diagnostics"]["emit_counterexamples"] = (!old).into();
    });
    assert_eq!(row.proof_evidence, selected_before, "the genuine selected proof is unchanged");
    assert_eq!(
        defect(&row, None).as_deref(),
        Some("modern body-WP result does not bind the complete original native input"),
    );
}

#[test]
fn optional_diagnostic_witness_is_not_required_for_native_publication() {
    let mut row = actual();
    rewrite_payload(&mut row, |certificate| {
        assert!(
            certificate["statement"]
                .as_object_mut()
                .unwrap()
                .remove("translation_witness")
                .is_some()
        );
    });
    assert_eq!(defect(&row, None), None);
}

fn rewrite_native_bundle(
    row: &mut TransportObligationResult,
    mutate: impl FnOnce(&mut serde_json::Value),
) {
    let native = row.native_trust_ir.as_mut().unwrap();
    let bundle_artifact = &native.artifacts[0];
    let old_digest = bundle_artifact.digest.as_ref().unwrap().value.clone();
    let original = bundle_artifact.materialization.as_ref().unwrap();
    let mut input: serde_json::Value =
        serde_json::from_slice(&original.decoded_bytes().unwrap()).unwrap();
    mutate(&mut input["payload"]["bundle"]);
    digest::canonicalize_json_in_place(&mut input);
    let bytes = serde_json::to_vec(&input).unwrap();
    let changed_digest = digest::lowercase_hex(&Sha256::digest(&bytes));
    for artifact in &mut native.artifacts {
        if artifact.digest.as_ref().unwrap().value == old_digest {
            let original = artifact.materialization.as_ref().unwrap();
            artifact.materialization = TransportArtifactMaterialization::from_exact_bytes(
                &bytes,
                original.proof_binding_id.clone(),
                original.referenced_artifacts.clone(),
            );
            artifact.digest.as_mut().unwrap().value = changed_digest.clone();
        }
        artifact.uri =
            Some(artifact.uri.as_ref().unwrap().replacen(&old_digest, &changed_digest, 1));
        for reference in &mut artifact.materialization.as_mut().unwrap().referenced_artifacts {
            if reference.digest.value == old_digest {
                reference.digest.value = changed_digest.clone();
            }
        }
    }
    assert!(
        native_trust_ir_artifact_shape_is_publishable(native),
        "the independently rehashed native artifact graph must still be structurally well formed"
    );
}

fn decoded_native_bundle(
    row: &TransportObligationResult,
) -> trust_ir::request::NativeVerificationBundle {
    let native = row.native_trust_ir.as_ref().unwrap();
    let materialization = native.artifacts[0].materialization.as_ref().unwrap();
    let envelope: serde_json::Value =
        serde_json::from_slice(&materialization.decoded_bytes().unwrap()).unwrap();
    trust_ir::request::transport::rehydrate_native_bundle_transport_payload(&envelope["payload"])
        .unwrap()
}

#[test]
fn independently_rehashed_native_body_must_match_its_recorded_module_digest() {
    let original = actual();
    assert_eq!(defect(&original, None), None);
    let original_bundle = decoded_native_bundle(&original);
    assert_eq!(original_bundle.module.stable_digest(), original_bundle.trust_ir_module_digest);
    let mut row = original.clone();
    rewrite_native_bundle(&mut row, |bundle| {
        let instruction = &mut bundle["module"]["functions"][0]["blocks"][0]["body"][0]["inst"];
        assert_eq!(*instruction, serde_json::json!({"Const": {"ty": "U32", "value": {"Int": 0}}}));
        *instruction = serde_json::json!({"Const": {"ty": "U32", "value": {"Int": 1}}});
    });
    let changed = decoded_native_bundle(&row);
    assert!(changed.module.wire_image_refusals().is_empty());
    assert_eq!(row.proof_evidence, original.proof_evidence, "the certificate is unchanged");
    assert_eq!(changed.trust_ir_module_digest, original_bundle.trust_ir_module_digest);
    assert_ne!(changed.module.stable_digest(), changed.trust_ir_module_digest);
    // Bundle identity intentionally hashes its recorded module digest. A
    // publication reader must independently bind that digest to the body.
    assert_eq!(changed.stable_digest(), original_bundle.stable_digest());
    assert_eq!(
        defect(&row, None).as_deref(),
        Some("modern body-WP native module differs from its recorded digest")
    );
}

#[test]
fn independently_rehashed_native_module_without_wire_identity_refuses() {
    let original = actual();
    assert_eq!(defect(&original, None), None);
    let original_bundle = decoded_native_bundle(&original);
    let mut row = original.clone();
    rewrite_native_bundle(&mut row, |bundle| {
        let ty =
            &mut bundle["module"]["functions"][0]["blocks"][0]["body"][0]["inst"]["Const"]["ty"];
        assert_eq!(*ty, "U32");
        *ty = "Error".into();
    });
    let changed = decoded_native_bundle(&row);
    assert!(!changed.module.wire_image_refusals().is_empty());
    assert_eq!(row.proof_evidence, original.proof_evidence, "the certificate is unchanged");
    assert_eq!(changed.stable_digest(), original_bundle.stable_digest());
    assert_eq!(
        defect(&row, None).as_deref(),
        Some("modern body-WP native module has no wire identity")
    );
}

#[test]
fn duplicate_mixed_and_extraneous_artifacts_refuse() {
    for mutation in 0..3 {
        let mut row = actual();
        let extra = match mutation {
            0 => row.proof_evidence.as_ref().unwrap().artifacts[0].clone(),
            1 => row.native_trust_ir.as_ref().unwrap().artifacts[0].clone(),
            _ => TransportEvidenceArtifact {
                kind: "SolverTranscript".into(),
                uri: None,
                digest: None,
                materialization: None,
                artifact_id: None,
                format: None,
                metadata: None,
            },
        };
        row.proof_evidence.as_mut().unwrap().artifacts.push(extra);
        assert!(defect(&row, None).is_some(), "mutation {mutation}");
    }
}

#[test]
fn stronger_or_different_grades_are_not_modern_body_evidence() {
    for assurance in [
        AssuranceLevel::Certified,
        AssuranceLevel::Trusted,
        AssuranceLevel::SmtBacked,
        AssuranceLevel::Unchecked,
    ] {
        let mut row = actual();
        let proof = row.proof_evidence.as_mut().unwrap();
        proof.strength.as_mut().unwrap().assurance = assurance.clone();
        proof.evidence.as_mut().unwrap().assurance = assurance;
        assert!(defect(&row, None).is_some());
    }
    let mut row = actual();
    row.proof_evidence.as_mut().unwrap().evidence.as_mut().unwrap().assurance =
        AssuranceLevel::Sound;
    assert_eq!(
        defect(&row, None),
        None,
        "legacy spelling of the same Sound rung is canonicalized later"
    );
}

#[test]
fn path_backed_certificate_requires_a_trusted_root_and_preserves_bytes() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().canonicalize().unwrap();
    let mut row = actual();
    let artifact = &mut row.proof_evidence.as_mut().unwrap().artifacts[0];
    let materialization = artifact.materialization.as_ref().unwrap();
    let bytes = materialization.decoded_bytes().unwrap();
    let relative = format!(
        "{}/sha256/{}",
        TRANSPORT_ARTIFACT_STORE_DIRECTORY,
        artifact.digest.as_ref().unwrap().value
    );
    std::fs::create_dir_all(root.join(TRANSPORT_ARTIFACT_STORE_DIRECTORY).join("sha256")).unwrap();
    std::fs::write(root.join(&relative), &bytes).unwrap();
    artifact.materialization =
        Some(materialization.clone().with_materialized_path(relative).unwrap());
    assert!(defect(&row, None).is_some());
    assert_eq!(defect(&row, Some(&root)), None);
    assert_eq!(
        row.proof_evidence.as_ref().unwrap().artifacts[0]
            .materialization
            .as_ref()
            .unwrap()
            .decoded_bytes_at_root(
                row.proof_evidence.as_ref().unwrap().artifacts[0].digest.as_ref().unwrap(),
                &root
            )
            .unwrap(),
        bytes
    );
}

#[test]
fn mismatched_native_identity_and_native_bytes_refuse() {
    for mutation in 0..5 {
        let mut row = actual();
        let native = row.native_trust_ir.as_mut().unwrap();
        match mutation {
            0 => native.native_id = Some("trust_ir-native-trust-wp-request-3-proof-1".into()),
            1 => native.request_id = Some("4".into()),
            2 => native.suite = "trust-mc".into(),
            3 => native.present = false,
            _ => native.artifacts[0]
                .materialization
                .as_mut()
                .unwrap()
                .encoded_bytes
                .replace_range(0..2, "00"),
        }
        assert!(defect(&row, None).is_some(), "mutation {mutation}");
    }
}
