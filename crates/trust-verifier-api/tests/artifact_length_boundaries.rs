//! Public length and shape boundaries of proof-artifact materializations.
//!
//! Every malformed length, truncation, trailing byte and single-byte change of a
//! bound evidence envelope must be refused by both the verifier API predicates
//! and the transport topology check, before and after a JSON round trip, and
//! must never panic. Malformed transport hex (odd length, invalid or uppercase
//! digits, wrong declared length, foreign encoding, dual channel) must be
//! refused by decoding, digest matching and rooted decoding alike.
//!
//! Originally an untracked audit (2026-10-20) in the `perf/verifier-artifact-witness`
//! worktree; kept as a regression test when that worktree was retired.

use trust_types::digest::stable_sha256_hex;
use trust_types::{
    TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX, TransportArtifactDigest,
    TransportArtifactMaterialization, TransportEvidenceArtifact,
    transport_proof_artifact_topology_defect,
};
use trust_verifier_api::*;

const OWNER: &str = "length-audit-owner";
const BINDING: &str = "length-audit-binding";

fn assert_bound_case(bytes: Vec<u8>, accepted: bool, label: &str) {
    let checked = std::panic::catch_unwind(|| {
        let api = EvidenceArtifactMaterialization::new(bytes.clone(), BINDING, vec![]);
        if bytes.is_empty() {
            assert!(api.is_none());
            return;
        }
        let api = api.expect("bounded nonempty raw materialization");
        assert_eq!(
            api.bound_payload_bytes(EvidenceArtifactKind::ProofCertificate, OWNER).is_some(),
            accepted,
            "API payload {label}"
        );
        let roundtrip: EvidenceArtifactMaterialization =
            serde_json::from_slice(&serde_json::to_vec(&api).unwrap()).unwrap();
        let hash = stable_sha256_hex(&bytes);
        for materialization in [api, roundtrip] {
            let proof = ObligationEvidence {
                evidence_id: "length-audit-evidence".into(),
                obligation_id: OWNER.into(),
                engine: EngineManifest::new("length-audit", "0.1.0", EngineKind::Deductive),
                status: EvidenceStatus::Proved,
                decline: None,
                proof_strength: Some(ProofStrength::deductive()),
                artifacts: vec![EvidenceArtifact {
                    kind: EvidenceArtifactKind::ProofCertificate,
                    uri: format!("artifact://audit/{hash}"),
                    hash: ArtifactHash { algorithm: "sha256".into(), value: hash.clone() },
                    materialization: Some(materialization),
                }],
                counterexample: None,
                publication: EvidencePublicationMetadata::default(),
                diagnostics: vec![],
            };
            assert_eq!(proof.satisfies_proof_artifact_policy(), accepted, "API policy {label}");
        }
        let transport =
            TransportArtifactMaterialization::from_exact_bytes(&bytes, BINDING, vec![]).unwrap();
        assert_eq!(transport.decoded_bytes().unwrap(), bytes);
        let roundtrip: TransportArtifactMaterialization =
            serde_json::from_slice(&serde_json::to_vec(&transport).unwrap()).unwrap();
        for materialization in [transport, roundtrip] {
            let artifact = TransportEvidenceArtifact {
                kind: "ProofCertificate".into(),
                format: None,
                artifact_id: None,
                digest: Some(TransportArtifactDigest {
                    algorithm: "sha256".into(),
                    value: hash.clone(),
                }),
                uri: Some(format!(
                    "{TRUST_VC_NATIVE_TRUST_IR_PROOF_CERTIFICATE_URI_PREFIX}{hash}.json"
                )),
                materialization: Some(materialization),
                metadata: None,
            };
            assert_eq!(
                transport_proof_artifact_topology_defect("trust-vc", &[artifact], Some(OWNER))
                    .is_none(),
                accepted,
                "transport topology {label}"
            );
        }
    });
    assert!(checked.is_ok(), "public malformed input panicked: {label}");
}

#[test]
fn public_binding_construction_and_serde_refuse_malformed_lengths() {
    let (materialization, _) = EvidenceArtifactMaterialization::new_bound(
        EvidenceArtifactKind::ProofCertificate,
        b"exact boundary-control payload",
        BINDING,
        OWNER,
        vec![],
    )
    .unwrap();
    let bytes = materialization.bytes().to_vec();
    let mut cursor = EVIDENCE_ARTIFACT_BINDING_ENVELOPE_SCHEMA.len() + 1;
    let mut offsets = vec![];
    for _ in 0..3 {
        offsets.push(cursor);
        let len = u32::from_be_bytes(bytes[cursor..cursor + 4].try_into().unwrap()) as usize;
        cursor += 4 + len;
    }
    let references_offset = cursor;
    cursor += 4;
    let payload_offset = cursor;
    let payload_len = u64::from_be_bytes(bytes[cursor..cursor + 8].try_into().unwrap());
    assert_bound_case(bytes.clone(), true, "exact valid envelope");
    let mut controls = 1;
    for end in 0..bytes.len() {
        assert_bound_case(bytes[..end].to_vec(), false, &format!("truncated-at-{end}"));
        controls += 1;
    }
    for offset in offsets.into_iter().chain([references_offset]) {
        for len in [0, 1, u32::MAX] {
            let mut changed = bytes.clone();
            changed[offset..offset + 4].copy_from_slice(&len.to_be_bytes());
            let accepted = changed == bytes;
            assert_bound_case(changed, accepted, &format!("field-{offset}-length-{len}"));
            controls += 1;
        }
    }
    for len in [
        0,
        payload_len - 1,
        payload_len,
        payload_len + 1,
        MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES as u64,
        MAX_EVIDENCE_ARTIFACT_MATERIALIZATION_BYTES as u64 + 1,
        u64::MAX,
    ] {
        let mut changed = bytes.clone();
        changed[payload_offset..payload_offset + 8].copy_from_slice(&len.to_be_bytes());
        assert_bound_case(changed, len == payload_len, &format!("declared-payload-{len}"));
        controls += 1;
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert_bound_case(trailing, false, "trailing byte");
    controls += 1;
    for offset in 0..bytes.len() {
        let mut changed = bytes.clone();
        changed[offset] ^= 1;
        assert_bound_case(changed, offset >= payload_offset + 8, &format!("single-byte-{offset}"));
        controls += 1;
    }
    println!(
        "binding-public-controls={controls}, both API and transport predicates, construction and JSON roundtrip"
    );
}

#[test]
fn public_transport_hex_lengths_refuse_invalid_shapes() {
    let original =
        TransportArtifactMaterialization::from_exact_bytes(&[0, 0x12, 0xab, 0xff], BINDING, vec![])
            .unwrap();
    let digest = TransportArtifactDigest {
        algorithm: "sha256".into(),
        value: stable_sha256_hex(&[0, 0x12, 0xab, 0xff]),
    };
    let root = std::path::Path::new("/unused-for-inline-materialization");
    assert!(original.matches_sha256_digest(&digest));
    assert!(original.decoded_bytes_at_root(&digest, root).is_ok());
    let mut cases = vec![];
    for len in [
        0,
        1,
        3,
        5,
        trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES as u64,
        trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES as u64 + 1,
        u64::MAX,
    ] {
        let mut value = original.clone();
        value.byte_len = len;
        cases.push((format!("byte-len-{len}"), value));
    }
    for encoded in ["0012abf", "0012abff0", "0012abFG", "0012abFF", "0012abé", "zzzzzzzz", ""] {
        let mut value = original.clone();
        value.encoded_bytes = encoded.into();
        cases.push((format!("hex-{encoded:?}"), value));
    }
    let mut value = original.clone();
    value.encoding = "base64".into();
    cases.push(("encoding".into(), value));
    let mut value = original.clone();
    value.materialized_path = Some("../outside".into());
    cases.push(("dual-channel".into(), value));
    for (label, value) in &cases {
        let checked = std::panic::catch_unwind(|| {
            assert!(value.decoded_bytes().is_err(), "decode {label}");
            assert!(!value.matches_sha256_digest(&digest), "hash {label}");
            assert!(value.decoded_bytes_at_root(&digest, root).is_err(), "root decode {label}");
            if let Ok(back) = serde_json::from_slice::<TransportArtifactMaterialization>(
                &serde_json::to_vec(value).unwrap(),
            ) {
                assert!(back.decoded_bytes().is_err(), "JSON decode {label}");
                assert!(!back.matches_sha256_digest(&digest), "JSON hash {label}");
            }
        });
        assert!(checked.is_ok(), "malformed public hex panicked: {label}");
    }
    for len in [1, trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES] {
        let bytes = vec![0x5a; len];
        let value =
            TransportArtifactMaterialization::from_exact_bytes(&bytes, BINDING, vec![]).unwrap();
        let digest = TransportArtifactDigest {
            algorithm: "sha256".into(),
            value: stable_sha256_hex(&bytes),
        };
        assert_eq!(value.decoded_bytes().unwrap(), bytes);
        assert!(value.matches_sha256_digest(&digest));
    }
    println!("transport-hex-public-refusals={}, valid-boundaries=1-byte-and-16-MiB", cases.len());
}
