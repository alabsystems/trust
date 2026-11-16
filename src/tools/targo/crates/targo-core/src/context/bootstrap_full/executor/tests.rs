use super::*;

#[test]
fn query_target_budget_only_restricts_the_original_owner_deadline() {
    let before = Instant::now();
    let original = before + Duration::from_secs(120);
    assert_eq!(target_deadline(original, None).unwrap(), original);
    let query = target_deadline(original, Some(Duration::from_secs(30))).unwrap();
    assert!(query >= before + Duration::from_secs(30));
    assert!(query <= Instant::now() + Duration::from_secs(30));
    let short_original = Instant::now() + Duration::from_secs(2);
    assert_eq!(
        target_deadline(short_original, Some(Duration::from_secs(30))).unwrap(),
        short_original
    );
    assert!(target_deadline(before - Duration::from_secs(1), None).is_err());
    assert!(
        target_deadline(
            before - Duration::from_secs(1),
            Some(Duration::from_secs(30))
        )
        .is_err()
    );
}

#[test]
fn a_retired_failed_compiler_never_becomes_a_successful_cargo_stream() {
    // Output is DATA, not a native retirement token or admission fixture.
    let process = ProcessBuilder::new("trustc");
    for status in [
        ExitStatus::from_raw(17 << 8),
        ExitStatus::from_raw(libc::SIGTERM),
    ] {
        let error = completed_stream(
            &process,
            Output {
                status,
                stdout: b"actual stdout prefix\n".to_vec(),
                stderr: b"error: controlled compiler failure\n".to_vec(),
            },
        )
        .unwrap_err();
        let failure = error.downcast_ref::<cargo_util::ProcessError>().unwrap();
        assert_eq!(failure.code, status.code());
        assert!(
            error
                .to_string()
                .contains("process didn't exit successfully")
        );
    }
    let output = completed_stream(
        &process,
        Output {
            status: ExitStatus::from_raw(0),
            stdout: b"compiler output\n".to_vec(),
            stderr: Vec::new(),
        },
    )
    .unwrap();
    assert_eq!(output.stdout, b"compiler output\n");
}
