use super::*;
use clean_auto::bridge::ay_contract::deserialize_term;
use clean_kernel::Expr;
use std::sync::atomic::{AtomicU64, Ordering};
use trust_certify::calculus_row::{hints, test_support};

struct FixtureDir(PathBuf);

impl Drop for FixtureDir {
    fn drop(&mut self) { let _ = std::fs::remove_dir_all(&self.0); }
}

fn private_dir(path: &Path) {
    let mut builder = std::fs::DirBuilder::new();
    #[cfg(unix)]
    { use std::os::unix::fs::DirBuilderExt; builder.mode(0o700); }
    builder.create(path).unwrap();
}

fn checked() -> (FixtureDir, CheckedPresentation, CalculusRowClaim) {
    // Existing test-only stand-in family, through the ACTUAL fenced
    // checker/replay API. This tests capsule mechanics, not SemR, the
    // production base/pin, a compiler-produced module or row eligibility.
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let root = std::env::temp_dir().join(format!(
        "trust-vf5-model-transport-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed),
    ));
    private_dir(&root);
    let owner = FixtureDir(root);
    let store = owner.0.join("kernel-proof-artifacts-v2");
    private_dir(&store);
    let incoming = store.join("incoming");
    private_dir(&incoming);
    let claim = CalculusRowClaim {
        artifact: vec![1], fid: 0, symbol: b"model-transport-control".to_vec(),
    };
    let bytes = hints::encode(&claim.artifact, &Expr::nat_lit(0), &Expr::nat_lit(0)).unwrap();
    std::fs::write(incoming.join(hints::filename(&claim.artifact)), bytes).unwrap();
    let session = hints::Vf5HintSession::new(test_support::pinned_toy(true), &owner.0).unwrap();
    let token = session.replay(&claim, None).unwrap();
    (owner, token, claim)
}

fn row() -> TransportObligationResult {
    TransportObligationResult {
        obligation_id: Some("transport-control-data:0".into()),
        claim_digest_sha256: Some("a".repeat(64)), kind: "divzero".into(),
        original_vc_snapshot: None, typed_kind: Some(Box::new(VcKind::DivisionByZero)),
        description: "original transport DATA only".into(), location: None,
        outcome: Outcome::Unknown, solver: "original-producer".into(), time_ms: 17,
        counterexample: None, counterexample_model: None, reason: None,
        design_mandate: false, gap_class: None, native_trust_ir: None,
        proof_evidence: None, monitor: None, assumes: Vec::new(), grade: None,
    }
}

fn capsule(row: &TransportObligationResult) -> (Vec<u8>, serde_json::Value) {
    let proof = row.proof_evidence.as_ref().unwrap();
    let artifact = &proof.artifacts[0];
    let bytes = artifact.materialization.as_ref().unwrap().decoded_bytes().unwrap();
    assert_eq!(artifact.digest.as_ref().unwrap().value, hex(&Sha256::digest(&bytes)));
    let value = serde_json::from_slice(&bytes).unwrap();
    (bytes, value)
}

#[test]
fn actual_checked_token_capsule_retains_exact_math_binding_and_original_evidence() {
    let (_directory, token, claim) = checked();
    let mut first = row();
    first.proof_evidence = Some(TransportProofEvidence {
        suite: "original-data".into(), backend: "original-data".into(),
        request_id: Some("retained-request".into()), proof_id: None, native_id: None,
        status: TransportProofStatus::Unknown, strength: None, evidence: None,
        artifacts: Vec::new(), diagnostics: Vec::new(),
    });
    first.native_trust_ir = Some(TransportNativeTrustIrEvidence {
        suite: "original-data".into(), backend: "original-data".into(),
        request_id: Some("retained-native-request".into()), native_id: None,
        present: false, artifacts: Vec::new(), diagnostics: Vec::new(),
    });
    let original = vec![first, row()];
    let before = original.clone();
    let patches = prepare(&token, &claim, &original, &[0], || true).unwrap().into_rows();
    assert_eq!(original, before, "no Original mutation during fallible conversion");
    assert_eq!(patches.len(), 1);
    let (index, patched) = &patches[0];
    assert_eq!(*index, 0);
    let (_, value) = capsule(patched);
    assert_eq!(value["schema"], CAPSULE_SCHEMA);
    assert_eq!(value["artifact_sha256"], hex(&token.artifact_sha256()));
    assert_eq!(value["fid"], token.fid());
    assert_eq!(value["symbol"], serde_json::to_value(token.symbol()).unwrap());
    assert_eq!(value["environment_sha256"], hex(&token.environment_sha256()));
    assert_eq!(value["statement_sha256"], hex(&token.statement_sha256()));
    assert_eq!(value["original_evidence"], serde_json::to_value(&original[0].proof_evidence).unwrap());
    for (name, exact) in [("goal", token.goal()), ("proof", token.proof()),
                          ("annotation", token.annotation()), ("certificates", token.certificates())] {
        let bytes: Vec<u8> = serde_json::from_value(value[name].clone()).unwrap();
        assert_eq!(&deserialize_term(&bytes).unwrap(), exact);
    }
    assert_eq!(patched.native_trust_ir, original[0].native_trust_ir);
    assert_eq!(patched.monitor, original[0].monitor);
    assert_eq!(patched.time_ms, original[0].time_ms);
    assert_eq!(patched.obligation_id, original[0].obligation_id);
    assert_eq!(patched.claim_digest_sha256, original[0].claim_digest_sha256);
    assert_eq!(patched.typed_kind, original[0].typed_kind);
    assert_eq!(patched.description, original[0].description);
    assert_eq!(patched.assumes, original[0].assumes);
    assert_eq!(patched.outcome, Outcome::Proved);
    let grade = patched.grade.as_ref().unwrap();
    grade.admitted().unwrap();
    assert_eq!(grade.encoding, GradeEncoding::ProvenCalculus);
    assert_eq!(grade.discharge, GradeDischarge::KernelReferenceChecked);
    assert_eq!(grade.premises, CALCULUS_ROW_PREMISES);
    assert_eq!(patched.proof_evidence.as_ref().unwrap().strength, Some(ProofStrength::constructive()));
    assert!(trust_certify::calculus_row::calculus_row_certificate_for(&claim.symbol).is_none());
}

#[test]
fn changed_artifact_function_or_symbol_and_invalid_indices_refuse_without_mutation() {
    let (_directory, token, claim) = checked();
    let original = vec![row()];
    for changed in [
        CalculusRowClaim { artifact: vec![2], ..claim.clone() },
        CalculusRowClaim { fid: 1, ..claim.clone() },
        CalculusRowClaim { symbol: b"different-symbol".to_vec(), ..claim.clone() },
    ] {
        assert!(prepare(&token, &changed, &original, &[0], || true).is_none());
    }
    for indices in [vec![], vec![0, 0], vec![1], vec![0, 1]] {
        assert!(prepare(&token, &claim, &original, &indices, || true).is_none());
    }
    assert_eq!(original, vec![row()]);
}

#[test]
fn failures_timeouts_holds_and_assumptions_do_not_become_model_proofs() {
    let (_directory, token, claim) = checked();
    for outcome in [Outcome::Failed, Outcome::Timeout, Outcome::Canceled, Outcome::Skipped,
                    Outcome::Unsupported, Outcome::Rejected] {
        let mut bad = row(); bad.outcome = outcome;
        assert!(prepare(&token, &claim, &[bad], &[0], || true).is_none());
    }
    for reason in [TRUST_HELD_ASSERT_REFUTATION_REASON.to_string(),
                   format!("{}original held DATA", trust_vcgen::GENERIC_REFUTATION_HELD_PREFIX),
                   StopCause::WallBackstop.stamp("original stopped DATA")] {
        let mut bad = row(); bad.reason = Some(reason);
        assert!(prepare(&token, &claim, &[bad], &[0], || true).is_none());
    }
    let mut assumed = row(); assumed.assumes.push("original premise DATA".into());
    assert!(prepare(&token, &claim, &[assumed], &[0], || true).is_none());
    let mut failed = row(); failed.outcome = Outcome::Failed;
    let mut held = row(); held.reason = Some(TRUST_HELD_ASSERT_REFUTATION_REASON.into());
    for noncandidate in [failed, held] {
        assert!(prepare(&token, &claim, &[row(), noncandidate], &[0], || true).is_none());
    }
}

#[test]
fn stopped_conversion_never_returns_a_partial_patch_or_changes_original() {
    let (_directory, token, claim) = checked();
    let original = vec![row(), row()];
    let mut complete_checks = 0;
    assert!(prepare(&token, &claim, &original, &[0, 1], || {
        complete_checks += 1; true
    }).is_some());
    for stop_at in [1, 5, complete_checks / 2, complete_checks] {
        let mut calls = 0;
        assert!(prepare(&token, &claim, &original, &[0, 1], || {
            calls += 1; calls < stop_at
        }).is_none(), "stop checkpoint {stop_at}");
        assert_eq!(original, vec![row(), row()]);
    }
}

#[test]
fn capsule_writer_bounds_before_growth_and_checks_final_stop() {
    let mut current = || true;
    let mut writer = BoundedBytes::new(4, &mut current).unwrap();
    writer.write_all(b"1234").unwrap();
    assert!(writer.write_all(b"5").is_err());
    assert_eq!(writer.finish().unwrap(), b"1234");
    let mut calls = 0;
    let mut final_stop = || { calls += 1; calls < 2 };
    let mut writer = BoundedBytes::new(4, &mut final_stop).unwrap();
    writer.write_all(b"1234").unwrap();
    assert!(writer.finish().is_none());
}

#[test]
fn oversized_original_evidence_is_refused_without_dropping_its_provenance() {
    let (_directory, token, claim) = checked();
    let mut original = row();
    original.proof_evidence = Some(TransportProofEvidence {
        suite: "original-data".into(), backend: "original-data".into(),
        request_id: Some("x".repeat(trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES)),
        proof_id: None, native_id: None, status: TransportProofStatus::Unknown,
        strength: None, evidence: None, artifacts: Vec::new(), diagnostics: Vec::new(),
    });
    let original = vec![original];
    assert!(prepare(&token, &claim, &original, &[0], || true).is_none());
    assert_eq!(original[0].outcome, Outcome::Unknown);
    assert_eq!(original[0].proof_evidence.as_ref().unwrap().request_id.as_ref().unwrap().len(),
               trust_types::MAX_TRANSPORT_ARTIFACT_MATERIALIZATION_BYTES);
}
