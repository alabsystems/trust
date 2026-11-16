use std::collections::BTreeMap;

use super::*;

fn objects(capture: &VerifierInputCapture) -> BTreeMap<String, Vec<u8>> {
    [&capture.public, &capture.requested, &capture.native]
        .into_iter()
        .map(|file| (file.filename.clone(), file.bytes.clone()))
        .collect()
}

fn restore(
    capture: &VerifierInputCapture,
    objects: &BTreeMap<String, Vec<u8>>,
) -> Result<CapturedVerifierInputs, String> {
    decode_verifier_input_pair(&capture.record.filename, &capture.record.bytes, |name| {
        objects.get(name).cloned().ok_or_else(|| format!("missing {name}"))
    })
}

#[test]
fn paired_capture_roundtrips_exact_native_dispatch_and_replays() {
    for negate in [false, true] {
        let (public, native) = fixture(negate);
        let capture = encode_verifier_input_pair(&public, &public.obligations, &native).unwrap();
        let loaded = restore(&capture, &objects(&capture)).unwrap();
        assert_eq!(loaded.public, public);
        assert_eq!(loaded.requested, public.obligations);
        assert_eq!(
            serde_json::to_value(&loaded.native).unwrap(),
            serde_json::to_value(&native).unwrap()
        );
        let live = FullVerificationEngine::with_required_native_engines_timeout_ms(5_000)
            .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                &loaded.public,
                &loaded.requested,
                &loaded.native,
                &VerifierExecutionContext::new("replay-exact-capture"),
            );
        assert_eq!(live.result().summary.proved, usize::from(!negate));
        assert_eq!(live.checked_native_wp_proofs().len(), usize::from(!negate));
    }
}

#[test]
fn paired_capture_deduplicates_large_public_and_native_objects_across_subsets() {
    let (public, native) = fixture(false);
    let a = encode_verifier_input_pair(&public, &public.obligations, &native).unwrap();
    let b = encode_verifier_input_pair(&public, &[], &native).unwrap();
    assert_eq!(a.public, b.public);
    assert_eq!(a.native, b.native);
    assert_ne!(a.requested.filename, b.requested.filename);
    assert_ne!(a.record.filename, b.record.filename);
    let repeated = encode_verifier_input_pair(&public, &public.obligations, &native).unwrap();
    assert_eq!(a, repeated);
}

#[test]
fn paired_capture_refuses_changed_missing_or_substituted_object_bytes() {
    let (public, native) = fixture(false);
    let capture = encode_verifier_input_pair(&public, &public.obligations, &native).unwrap();
    for name in [&capture.public.filename, &capture.requested.filename, &capture.native.filename] {
        let mut changed = objects(&capture);
        changed.get_mut(name).unwrap().push(b' ');
        assert!(restore(&capture, &changed).is_err());
        changed.remove(name);
        assert!(restore(&capture, &changed).is_err());
    }
    let mut changed = objects(&capture);
    changed.insert(capture.public.filename.clone(), capture.requested.bytes.clone());
    assert!(restore(&capture, &changed).is_err());
}

#[test]
fn paired_capture_refuses_record_tampering_and_path_injection() {
    let (public, native) = fixture(false);
    let original = encode_verifier_input_pair(&public, &public.obligations, &native).unwrap();
    let mut capture = original.clone();
    capture.record.bytes.push(b' ');
    assert!(restore(&capture, &objects(&capture)).is_err());
    let mut capture = original.clone();
    capture.record.filename = "../pair.json".into();
    assert!(restore(&capture, &objects(&capture)).is_err());
    for field in ["schema", "public", "oversized"] {
        let mut value: serde_json::Value = serde_json::from_slice(&original.record.bytes).unwrap();
        if field == "schema" {
            value[field] = "unknown".into();
        } else if field == "oversized" {
            value["public"]["bytes"] = (128u64 * 1024 * 1024 + 1).into();
        } else {
            value[field]["sha256"] = "../../outside".into();
        }
        let bytes = trust_types::canonical_json_bytes(&value).unwrap();
        let filename =
            format!("trust-verifier-input-pair-{}.json", trust_types::stable_sha256_hex(&bytes));
        assert!(
            decode_verifier_input_pair(&filename, &bytes, |_| panic!(
                "invalid reference must not be read"
            ))
            .is_err()
        );
    }
}

#[test]
fn paired_capture_preserves_rejected_request_instead_of_silently_repairing_it() {
    let (public, native) = fixture(false);
    let mut requested = public.obligations.clone();
    requested[0].description.push_str(" changed");
    assert!(public.validate_requested_obligations(&requested).is_err());
    let capture = encode_verifier_input_pair(&public, &requested, &native).unwrap();
    let loaded = restore(&capture, &objects(&capture)).unwrap();
    assert_eq!(loaded.requested, requested);
    assert!(loaded.public.validate_requested_obligations(&loaded.requested).is_err());
}

#[test]
fn fully_rehashed_capture_does_not_authorize_a_different_public_claim() {
    let (mut public, native) = fixture(false);
    public.obligations[0].source.line = Some(200);
    let capture = encode_verifier_input_pair(&public, &public.obligations, &native).unwrap();
    let loaded = restore(&capture, &objects(&capture)).unwrap();
    let live = engine(EvidenceStatus::Unknown)
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            &loaded.public,
            &loaded.requested,
            &loaded.native,
            &VerifierExecutionContext::new("rehashed-capture-is-not-authority"),
        );
    assert_eq!(live.result().summary.proved, 0);
    assert!(live.checked_native_wp_proofs().is_empty());
}
