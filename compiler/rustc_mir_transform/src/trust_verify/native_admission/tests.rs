use super::*;

fn binding() -> NativeAdmissionBinding {
    NativeAdmissionBinding {
        run_digest: "a".repeat(64),
        unit_digest: "b".repeat(64),
        semantics_digest: "c".repeat(64),
        role: "primary".into(),
        target: "native".into(),
    }
}

fn body(name: &str) -> NativeAdmissionBody {
    NativeAdmissionBody { function: name.into(), body_digest: "d".repeat(64) }
}

#[test]
fn custom_target_binding_uses_owned_launch_path_when_rustdoc_path_is_absent() {
    let mut options = rustc_session::config::Options::default();
    options.unstable_opts.trust_verify_session = Some("session".into());
    options.unstable_opts.trust_admission_run_digest = Some(run_digest("session"));
    options.unstable_opts.trust_admission_unit_digest = Some("b".repeat(64));
    options.unstable_opts.trust_admission_semantics_digest = Some("c".repeat(64));
    options.unstable_opts.trust_admission_unit_role = Some("primary".into());
    let path = "/owned/targets/日本語 directory/custom.json";
    options.unstable_opts.trust_admission_compile_target = Some(path.into());
    // TargetTuple decoding deliberately discards the rustdoc-only path.
    options.target_triple = rustc_target::spec::TargetTuple::TargetJson {
        path_for_rustdoc: std::path::PathBuf::new(),
        tuple: "custom".into(),
        contents: "{}".into(),
    };
    assert_eq!(session_binding(&options).unwrap().target, path);
    options.unstable_opts.trust_admission_compile_target = None;
    assert!(session_binding(&options).is_none());
    options.unstable_opts.trust_admission_compile_target = Some(path.into());
    options.target_triple = rustc_target::spec::TargetTuple::from_tuple("aarch64-apple-darwin");
    assert!(session_binding(&options).is_none(), "built-in target mismatch must not bind");
}

#[test]
fn oversized_producer_census_emits_only_bounded_explicit_incompleteness() {
    let body = NativeAdmissionBody {
        function: "x".repeat(MAX_CENSUS_TRANSPORT_BYTES),
        body_digest: "d".repeat(64),
    };
    let mut ledger = Ledger::default();
    let index = ledger.begin(&binding(), body.clone(), "request").unwrap();
    ledger.finish(index, false);
    let oversized = NativeAdmissionCensus {
        transport_type: None,
        schema: SCHEMA.into(),
        binding: binding(),
        package_name: "demo".into(),
        crate_name: "demo".into(),
        bodies: vec![body],
        auxiliary_bodies: vec![],
        attempts: ledger.attempts,
        complete: true,
        problems: vec![],
    };
    assert!(oversized.validate().is_ok());
    assert!(bounded_census_json(&oversized).is_err());
    let json = census_transport_json(oversized).unwrap();
    assert!(json.len() < MAX_CENSUS_TRANSPORT_BYTES);
    let trust_types::TransportMessage::NativeAdmissionCensus(omitted) =
        trust_types::parse_transport_payload(&json).unwrap()
    else {
        unreachable!()
    };
    omitted.validate().unwrap();
    assert!(!omitted.complete);
    assert!(omitted.problems[0].contains("producer payload bound"));
    assert!(omitted.bodies.is_empty() && omitted.attempts.is_empty());
}

#[test]
fn nested_and_retried_scopes_keep_their_own_terminal_slot() {
    let mut ledger = Ledger::default();
    let outer = ledger.begin(&binding(), body("outer"), "request").unwrap();
    let inner = ledger.begin(&binding(), body("inner"), "request").unwrap();
    ledger.finish(inner, false);
    assert!(!ledger.attempts[outer].terminal);
    let retry = ledger.begin(&binding(), body("outer"), "request").unwrap();
    assert_eq!(ledger.attempts[retry].attempt, 2);
    ledger.finish(retry, true);
    ledger.finish(outer, false);
    assert!(ledger.attempts[outer].terminal);
    assert!(ledger.attempts[inner].terminal);
    assert!(!ledger.attempts[retry].terminal, "unwinding is not completion");
}

#[test]
fn concurrent_begins_never_reuse_an_attempt_or_terminal_slot() {
    let ledger = Arc::new(Mutex::new(Ledger::default()));
    let workers: Vec<_> = (0..4)
        .map(|_| {
            let ledger = ledger.clone();
            std::thread::spawn(move || {
                let index =
                    ledger.lock().unwrap().begin(&binding(), body("same"), "request").unwrap();
                ledger.lock().unwrap().finish(index, false);
            })
        })
        .collect();
    for worker in workers {
        worker.join().unwrap();
    }
    let state = ledger.lock().unwrap();
    assert_eq!(state.attempts.iter().map(|r| r.attempt).collect::<Vec<_>>(), vec![1, 2, 3, 4]);
    assert!(state.attempts.iter().all(|r| r.terminal));
}

#[test]
fn exhausted_sequence_is_incomplete_without_wrapping_or_reusing_an_attempt() {
    let mut ledger = Ledger::default();
    ledger.last_attempt_by_body.insert(body("exhausted"), u64::MAX);
    assert_eq!(ledger.begin(&binding(), body("exhausted"), "request"), None);
    assert!(ledger.attempts.is_empty());
    assert_eq!(ledger.last_attempt_by_body[&body("exhausted")], u64::MAX);
    assert_eq!(ledger.problems.len(), 1);
    let other = ledger.begin(&binding(), body("other"), "request").unwrap();
    assert_eq!(ledger.attempts[other].attempt, 1);
}
