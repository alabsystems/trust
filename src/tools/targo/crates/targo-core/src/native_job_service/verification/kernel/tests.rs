//! Real kernel mathematics, not native Root/SDK/source-authority fixtures.
use super::*;
use std::{
    fs::File,
    process::{Child, Command, Stdio},
    time::Duration,
};
use trust_certify::proof_artifacts::ReplayKind;
use trust_proof_session::ProofArtifactStore;
use trust_types::{Formula, OriginalVcSnapshot, Sort, SourceSpan, TransportMessage, VcKind};

fn current_vc() -> VerificationCondition {
    let x = || Formula::Var("native-current-x".into(), Sort::Int);
    VerificationCondition {
        kind: VcKind::Assertion {
            message: "native provider current math".into(),
        },
        function: "native_crate::f".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}
fn captured_function(vc: &VerificationCondition) -> FunctionTransportResult {
    let TransportMessage::FunctionResult(mut function) =
        super::super::census::tests::messages().remove(0)
    else {
        unreachable!()
    };
    let claim = trust_types::original_vc_snapshot::exact_vc_claim_digest_sha256(
        vc,
        true,
        Some("aarch64-apple-darwin"),
    )
    .unwrap();
    let original = &mut function.results[0];
    original.outcome = Outcome::Proved;
    original.obligation_id = Some("current-native-row".into());
    original.claim_digest_sha256 = Some(claim.clone());
    original.typed_kind = Some(Box::new(vc.kind.clone()));
    original.original_vc_snapshot = OriginalVcSnapshot::capture(
        vc,
        true,
        "aarch64-apple-darwin",
        "current-native-row",
        &claim,
    )
    .map(Box::new);
    assert!(original.original_vc_snapshot.is_some());
    function.proved = 1;
    function.unknown = 0;
    function
}
fn row(function: &FunctionTransportResult) -> Row {
    let original = &function.results[0];
    Row {
        function: function.function.clone(),
        obligation: original.obligation_id.clone(),
        claim: original.claim_digest_sha256.clone(),
        _replay_entered: false,
        proof: None,
        identity: None,
        vc: None,
        stop: None,
        failure: None,
    }
}

struct OwnedChild(Option<Child>);
impl Drop for OwnedChild {
    fn drop(&mut self) {
        if let Some(mut child) = self.0.take() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

#[test]
fn native_math_hints_receive_fresh_kernel_checks_without_a_native_node_grant() {
    let home = tempfile::tempdir().unwrap();
    let session = VerificationSession::create().unwrap();
    let proof = trust_certify::proof_artifacts::certify_vc_with_artifacts(
        &current_vc(),
        session.artifact_root(),
    );
    assert!(
        proof.is_some(),
        "actual current mathematics must produce its hint"
    );
    let store = ProofArtifactStore::open(home.path()).unwrap();
    assert_eq!(store.publish_session(session.artifact_root()).unwrap(), 1);
    let stdout_path = home.path().join("stdout");
    let stderr_path = home.path().join("stderr");
    let child = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "native_job_service::verification::kernel::tests::fresh_kernel_component_child",
            "--nocapture",
        ])
        .env("TRUST_NATIVE_VERIFY_MATH_TEST", home.path())
        .stdout(Stdio::from(File::create(&stdout_path).unwrap()))
        .stderr(Stdio::from(File::create(&stderr_path).unwrap()))
        .spawn()
        .unwrap();
    let mut owned = OwnedChild(Some(child));
    let until = Instant::now() + Duration::from_secs(90);
    let status = loop {
        if let Some(status) = owned.0.as_mut().unwrap().try_wait().unwrap() {
            break status;
        }
        assert!(
            Instant::now() < until,
            "fresh mathematical actor exceeded its bounded watchdog"
        );
        std::thread::sleep(Duration::from_millis(5));
    };
    owned.0.take();
    let stdout = std::fs::read_to_string(stdout_path).unwrap();
    let stderr = std::fs::read_to_string(stderr_path).unwrap();
    assert!(
        status.success(),
        "actual fresh actor: {status}\n{stdout}\n{stderr}"
    );
    assert!(stdout.contains("1 passed; 0 failed"), "{stdout}");
    assert_eq!(
        stdout
            .matches("NATIVE_CURRENT_KERNEL_COMPONENT_COMPLETE")
            .count(),
        1,
        "{stdout}"
    );
}

#[test]
fn fresh_kernel_component_child() {
    let gctx = crate::util::GlobalContext::default().unwrap();
    let Some(home) = gctx.get_env_os("TRUST_NATIVE_VERIFY_MATH_TEST") else {
        return;
    };
    let session = VerificationSession::create()
        .unwrap()
        .with_proof_store(Some(std::path::Path::new(home)));
    let until = Instant::now() + Duration::from_secs(30);
    let current = current_vc();
    let function = captured_function(&current);
    let mut first = row(&function);
    replay_current_row(&function, &function.results[0], &session, until, &mut first).unwrap();
    let proof = first.proof.as_ref().unwrap();
    let audit = proof.audit().unwrap();
    assert_eq!(audit.kind(), ReplayKind::CurrentKernelRecheck);
    assert!(audit.matches(&current, proof.evidence()));

    let mut rebound = current.clone();
    rebound.location.line_start += 1;
    rebound.location.line_end += 1;
    let second_function = captured_function(&rebound);
    let mut second = row(&second_function);
    replay_current_row(
        &second_function,
        &second_function.results[0],
        &session,
        until,
        &mut second,
    )
    .unwrap();
    let second_proof = second.proof.as_ref().unwrap();
    assert!(
        second_proof
            .audit()
            .unwrap()
            .matches(&rebound, second_proof.evidence())
    );
    assert!(
        !second_proof
            .audit()
            .unwrap()
            .matches(&current, second_proof.evidence())
    );
    assert_ne!(
        first.identity, second.identity,
        "complete current VC location is not donated"
    );

    let mut changed = current.clone();
    changed.formula = Formula::Bool(true);
    let changed_function = captured_function(&changed);
    let mut rejected = row(&changed_function);
    assert!(
        replay_current_row(
            &changed_function,
            &changed_function.results[0],
            &session,
            until,
            &mut rejected
        )
        .is_err()
    );
    assert!(
        rejected.proof.is_none(),
        "old correct proof cannot prove changed current mathematics"
    );
    let mut unknown = function.clone();
    unknown.results[0].outcome = Outcome::Unknown;
    let mut rejected = row(&unknown);
    assert!(
        replay_current_row(
            &unknown,
            &unknown.results[0],
            &session,
            until,
            &mut rejected
        )
        .is_err()
    );
    assert!(rejected.proof.is_none());
    let mut foreign = function.clone();
    foreign.results[0].claim_digest_sha256 = Some("0".repeat(64));
    let mut rejected = row(&foreign);
    assert!(
        replay_current_row(
            &foreign,
            &foreign.results[0],
            &session,
            until,
            &mut rejected
        )
        .is_err()
    );
    assert!(
        rejected.proof.is_none(),
        "self-inconsistent claim cannot borrow a valid proof"
    );
    let mut rejected = row(&function);
    assert!(
        replay_current_row(
            &function,
            &function.results[0],
            &session,
            Instant::now(),
            &mut rejected
        )
        .is_err()
    );
    assert!(rejected.proof.is_none());
    let mut messages = super::super::census::tests::messages();
    messages[0] = TransportMessage::FunctionResult(function.clone());
    let TransportMessage::CrateSummary(terminal) = &mut messages[2] else {
        unreachable!()
    };
    terminal.functions_verified = 1;
    terminal.total_proved = 1;
    terminal.total_unknown = 0;
    let encoded = messages
        .iter()
        .map(|message| {
            format!(
                "{}{}\n",
                trust_types::TRANSPORT_PREFIX,
                serde_json::to_string(message).unwrap()
            )
        })
        .collect::<String>();
    let mut census = super::super::census::parse(
        encoded.as_bytes(),
        &super::super::census::Scope {
            package: "native-pkg",
            krate: "native_crate",
            primary: true,
            session: "fresh-session",
        },
    )
    .unwrap();
    let mut checked = CheckedRows {
        rows: vec![first],
        input_failures: vec![],
    };
    assert_eq!(
        checked.observed_work(),
        (1, 1, Some((1, 0))),
        "only actual API entry and this fresh actor's retained proof/audit are counted"
    );
    checked.require_complete(&census).unwrap();
    census.functions[0].results[0].claim_digest_sha256 = Some("f".repeat(64));
    assert!(
        checked.require_complete(&census).is_err(),
        "actual proof owner cannot be reattached to changed captured current rows"
    );
    census.functions[0].results[0].claim_digest_sha256 =
        function.results[0].claim_digest_sha256.clone();
    checked.require_complete(&census).unwrap();

    // A real failed session namespace bookend must keep its original native
    // error and the exact actual proof owner. Restoring the name cannot turn
    // this failed completed observation into a favorable current result.
    let original = session.artifact_root().to_owned();
    let moved_parent = tempfile::tempdir().unwrap();
    let moved = moved_parent.path().join("retained-session");
    std::fs::rename(&original, &moved).unwrap();
    checked.record_session_bookend(&session);
    assert_eq!(checked.input_failures.len(), 1);
    let original_error = checked.input_failures[0]
        .downcast_ref::<std::io::Error>()
        .expect("retain the actual session native IO error");
    assert_eq!(original_error.kind(), std::io::ErrorKind::NotFound);
    let errno = original_error
        .raw_os_error()
        .expect("native errno remains available");
    std::fs::rename(&moved, &original).unwrap();
    assert_eq!(
        checked.input_failures[0]
            .downcast_ref::<std::io::Error>()
            .unwrap()
            .raw_os_error(),
        Some(errno)
    );
    assert!(checked.require_complete(&census).is_err());
    let proof = checked.rows[0].proof.as_ref().unwrap();
    assert!(proof.audit().unwrap().matches(&current, proof.evidence()));
    println!("NATIVE_CURRENT_KERNEL_COMPONENT_COMPLETE");
}
