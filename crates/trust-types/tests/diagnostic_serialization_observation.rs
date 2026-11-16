//! Bounded observational probe; no verification authority is constructed.
use std::io::{self, Write};

use serde::Serialize;
use sha2::{Digest, Sha256};
use trust_types::{
    FunctionTransportResult, MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES, Outcome,
    TRANSPORT_DIAGNOSTIC_CODE, TRANSPORT_PREFIX, TransportArtifactDigest,
    TransportArtifactMaterialization, TransportEvidenceArtifact, TransportMessage,
    TransportObligationResult, TransportProofEvidence, TransportProofStatus,
    parse_transport_payload,
};

#[derive(Default)]
struct Count(u64);
impl Write for Count {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.0 = self.0.checked_add(bytes.len() as u64).expect("bounded observation counter");
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
fn encoded_len(value: &impl Serialize) -> u64 {
    let mut count = Count::default();
    serde_json::to_writer(&mut count, value).expect("serialize observation");
    count.0
}

// Mirrors the SERIALIZED shape at compiler/rustc_errors/src/json.rs, not its
// renderer. The rendered string below is an explicitly measured lower-bound
// model; the separate compiler observation checks the real renderer.
#[derive(Serialize)]
struct Diagnostic<'a> {
    #[serde(rename = "$message_type")]
    message_type: &'static str,
    message: &'a str,
    code: Code,
    level: &'static str,
    spans: [(); 0],
    children: [(); 0],
    rendered: Option<&'a str>,
}
#[derive(Serialize)]
struct Code {
    code: &'static str,
    explanation: Option<&'static str>,
}

fn message(bytes_per_artifact: usize) -> TransportMessage {
    let artifacts = [0x41u8, 0x42u8]
        .into_iter()
        .map(|byte| {
            let bytes = vec![byte; bytes_per_artifact];
            let digest = format!("{:x}", Sha256::digest(&bytes));
            TransportEvidenceArtifact {
                kind: "solver_transcript".into(),
                format: None,
                artifact_id: None,
                digest: Some(TransportArtifactDigest { algorithm: "sha256".into(), value: digest }),
                uri: Some("observation://unknown-evidence".into()),
                materialization: Some(
                    TransportArtifactMaterialization::from_exact_bytes(&bytes, "binding-1", vec![])
                        .expect("existing per-artifact cap accepts exact bytes"),
                ),
                metadata: None,
            }
        })
        .collect();
    TransportMessage::FunctionResult(FunctionTransportResult {
        function: "diagnostic_size_observation::unknown".into(),
        package_name: None,
        crate_name: None,
        primary_package: false,
        verification_session: String::new(),
        runtime_checks: None,
        modeled_facts: vec![],
        stable_ids: vec![],
        transport_budget: None,
        source_sha256: None,
        expanded_function_identity: None,
        results: vec![TransportObligationResult {
            obligation_id: None,
            claim_digest_sha256: None,
            original_vc_snapshot: None,
            kind: "observation".into(),
            typed_kind: None,
            description: "serialization observation; no proof claim".into(),
            location: None,
            outcome: Outcome::Unknown,
            solver: "none".into(),
            time_ms: 0,
            counterexample: None,
            counterexample_model: None,
            reason: None,
            design_mandate: false,
            gap_class: None,
            native_trust_ir: None,
            proof_evidence: Some(TransportProofEvidence {
                suite: "observation".into(),
                backend: "none".into(),
                request_id: None,
                proof_id: None,
                native_id: None,
                status: TransportProofStatus::Unknown,
                strength: None,
                evidence: None,
                artifacts,
                diagnostics: vec![],
            }),
            monitor: None,
            assumes: vec![],
            grade: None,
        }],
        proved: 0,
        failed: 0,
        unknown: 1,
        timed_out: 0,
        skipped: 0,
        runtime_checked: 0,
        cached: 0,
        total: 1,
    })
}

#[test]
fn observe_materialization_encoding_and_diagnostic_duplication() {
    const LINE_CAP: u64 = 128 * 1024 * 1024;
    const FUNCTION_RAW_MATERIALIZATION_CAP: u64 = 32 * 1024 * 1024;
    for bytes_per_artifact in [64 * 1024, MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES] {
        let msg = message(bytes_per_artifact);
        let TransportMessage::FunctionResult(function) = &msg else { unreachable!() };
        let artifacts = &function.results[0].proof_evidence.as_ref().unwrap().artifacts;
        let raw_bytes: u64 =
            artifacts.iter().map(|a| a.materialization.as_ref().unwrap().byte_len).sum();
        assert!(raw_bytes <= FUNCTION_RAW_MATERIALIZATION_CAP);
        let hex_field_bytes: u64 = artifacts
            .iter()
            .map(|a| encoded_len(&a.materialization.as_ref().unwrap().encoded_bytes))
            .sum();
        let json = serde_json::to_string(&msg).expect("actual current transport serializer");
        let parsed =
            parse_transport_payload(&json).expect("actual current bounded transport decoder");
        let TransportMessage::FunctionResult(parsed) = parsed else { unreachable!() };
        assert_eq!(parsed.results.len(), 1);
        assert_eq!(parsed.unknown, 1);
        assert_eq!(parsed.proved, 0);
        assert_eq!(parsed.results[0].outcome, Outcome::Unknown);
        assert!(parsed.results[0].grade.is_none());
        assert!(parsed.results == function.results, "every original field survives");
        drop(parsed);
        let payload = format!("{TRANSPORT_PREFIX}{json}");
        let rendered_lower_bound = format!("note: {payload}\n\n");
        let mut diagnostic = Diagnostic {
            message_type: "diagnostic",
            message: &payload,
            code: Code { code: TRANSPORT_DIAGNOSTIC_CODE, explanation: None },
            level: "note",
            spans: [],
            children: [],
            rendered: Some(&rendered_lower_bound),
        };
        let duplicated_line_bytes = encoded_len(&diagnostic) + 1;
        diagnostic.rendered = Some("note: structured verification results are in message\n\n");
        let compact_rendered_line_bytes = encoded_len(&diagnostic) + 1;
        if bytes_per_artifact == MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES {
            assert_eq!(raw_bytes, FUNCTION_RAW_MATERIALIZATION_CAP);
            assert!((json.len() as u64) < LINE_CAP);
            assert!(duplicated_line_bytes > LINE_CAP);
            assert!(compact_rendered_line_bytes < LINE_CAP);
        }
        println!(
            "OBSERVATION:{}",
            serde_json::json!({
                "raw_materialization_bytes":raw_bytes, "artifacts":artifacts.len(), "rows":1,
                "unknown":1, "proved":0, "authority_grade":null,
                "hex_field_encoded_bytes":hex_field_bytes, "function_json_bytes":json.len(),
                "diagnostic_line_with_minimal_rendered_copy_bytes":duplicated_line_bytes,
                "diagnostic_line_with_compact_rendered_string_bytes":compact_rendered_line_bytes,
                "line_cap":LINE_CAP, "rendered_is_lower_bound_model":true,
                "compact_rendered_remains_a_string":true,
                "actual_current_transport_types":true,
            })
        );
    }
}
