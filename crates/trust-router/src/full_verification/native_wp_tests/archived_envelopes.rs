//! Current untrusted test envelopes over unchanged archived bodies and claims.
//! Original compiler bytes keep their old handshake and remain refused.

use trust_ir::NativeVerificationBundleError;

use super::*;

pub(super) fn assert_archived_schema8_input(original: &NativeVerificationBundle) {
    // A later synchronized handshake needs its own reviewed test derivation.
    assert_eq!(NativeVerificationBundle::SCHEMA_VERSION, 9);
    assert_eq!(original.schema_version, 8);
    assert_eq!(original.serialization.schema_version, 8);
    assert_eq!(
        original.validate(),
        Err(vec![
            NativeVerificationBundleError::UnsupportedSchemaVersion(8),
            NativeVerificationBundleError::UnsupportedSerializationSchemaVersion(8),
        ])
    );
    assert_eq!(original.module.stable_digest(), original.trust_ir_module_digest);
    assert!(original.evidence_bundles.is_empty());
    assert!(original.lineage.nodes.iter().all(|node| node.certificates.is_empty()));
}

pub(super) fn derived_current_native_input(text: &str) -> NativeVerificationBundle {
    let original: NativeVerificationBundle = serde_json::from_str(text).unwrap();
    assert_archived_schema8_input(&original);
    // This authors test data; it does not run a compiler or mint source authority.
    // The current constructor supplies only the two synchronized headers.
    let current = NativeVerificationBundle::new(
        original.producer.clone(),
        original.input.clone(),
        original.trust_ir_module_digest,
        original.module.clone(),
        original.lineage.clone(),
    );
    let mut derived = original.clone();
    derived.schema_version = current.schema_version;
    derived.serialization.schema_version = current.serialization.schema_version;
    derived.validate().unwrap();
    assert_ne!(derived.stable_digest(), original.stable_digest());
    let mut restored = derived.clone();
    restored.schema_version = 8;
    restored.serialization.schema_version = 8;
    assert_eq!(restored, original);

    let document = serde_json::to_value(&restored).unwrap();
    let mut expected: serde_json::Value = serde_json::from_str(text).unwrap();
    // Current canonical serde emits the previously omitted empty collection.
    let layouts = expected["module"]
        .as_object_mut()
        .unwrap()
        .entry("closure_layouts")
        .or_insert_with(|| serde_json::json!([]));
    assert_eq!(layouts, &serde_json::json!([]));
    assert_eq!(document, expected, "a non-header archived field changed");
    derived
}

#[test]
fn derived_envelope_retains_old_refusal_and_every_archived_field() {
    let text = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/current_self_use/signed_min_magnitude/native.json"
    ));
    derived_current_native_input(text).validate().unwrap();
}

#[test]
fn derivation_refuses_other_invalid_or_unrecognized_archived_data() {
    let text = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/current_self_use/signed_min_magnitude/native.json"
    ));
    let original: serde_json::Value = serde_json::from_str(text).unwrap();
    for mutation in ["schema", "policy", "unknown"] {
        let mut document = original.clone();
        match mutation {
            "schema" => document["schema_version"] = 7.into(),
            "policy" => document["serialization"]["canonical_order"] = false.into(),
            "unknown" => document["unrecognized_capture_field"] = true.into(),
            _ => unreachable!(),
        }
        assert!(
            std::panic::catch_unwind(|| { derived_current_native_input(&document.to_string()) })
                .is_err(),
            "derivation accepted {mutation}"
        );
    }
}
