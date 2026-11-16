//! Real-pipe component controls, not an Aterm/SDK admission qualification.
use super::*;
use std::io::Write as _;
use std::process::{Command, Stdio};

const ACTOR: &str = "TARGO_TEST_NATIVE_COMPILER_CAPTURE_ACTOR";
fn limits() -> StreamingOutputLimits {
    StreamingOutputLimits::new(4096, 4096)
        .with_timeout(Duration::from_secs(10))
        .with_child_exit_cleanup()
}
#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "binary pipe actor reads its parent's actual environment before a Cargo context exists"
)]
fn native_binary_pipe_actor() {
    if std::env::var_os(ACTOR).is_none() {
        return;
    }
    std::io::stdout()
        .write_all(b"actual\0binary\xff-tail")
        .unwrap();
    std::io::stderr()
        .write_all(b"actual-stderr\0without-newline")
        .unwrap();
    std::process::exit(7);
}
#[test]
fn real_failed_child_keeps_binary_tails_physical_eof_and_nonzero_status() {
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "resource_v3::executor::capture::tests::native_binary_pipe_actor",
            "--nocapture",
        ])
        .env(ACTOR, "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdout = Stream::new();
    let mut stderr = Stream::new();
    let mut eof = [false; 2];
    let read = cargo_util::read2_controlled_with_eof(
        child.stdout.take().unwrap(),
        child.stderr.take().unwrap(),
        Some(Instant::now() + Duration::from_secs(10)),
        &mut |is_out, bytes, _| {
            accept(
                if is_out { &mut stdout } else { &mut stderr },
                None,
                is_out,
                bytes,
                limits(),
            )
            .unwrap();
            Read2Action::Continue
        },
        &mut || Ok(Read2Control::Continue),
        &mut eof,
    );
    assert!(matches!(read, Ok(Read2Action::Continue)));
    assert_eq!(eof, [true, true]);
    assert!(stdout.bytes.ends_with(b"actual\0binary\xff-tail"));
    assert_eq!(stderr.bytes, b"actual-stderr\0without-newline");
    assert_eq!(child.wait().unwrap().code(), Some(7));
    assert_eq!(end(eof[0], &read), CaptureStreamEnd::Eof);
    assert_eq!(
        end(false, &Ok(Read2Action::Continue)),
        CaptureStreamEnd::LeaderExitDrained
    );
    assert_eq!(
        end(false, &Ok(Read2Action::Stop)),
        CaptureStreamEnd::Incomplete
    );
}
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn original_durable_prefix_precedes_line_stream_or_writer_failure() {
    use crate::ops::cargo_test::workload::evidence::tests::native::Fixture;
    for (line, stream, writer) in [(4, 4096, 4096), (4096, 4, 4096), (4096, 4096, 4)] {
        let directory = tempfile::tempdir().unwrap();
        let fixture = Fixture::at(directory.path());
        let evidence = fixture.action(writer);
        let mut retained = Stream::new();
        let actual = b"prefix\0\xff-tail";
        let mut read = actual.to_vec();
        assert!(
            accept(
                &mut retained,
                Some(&evidence),
                true,
                &mut read,
                StreamingOutputLimits::new(line, stream)
            )
            .is_err()
        );
        assert!(read.is_empty());
        assert_eq!(retained.bytes, &actual[..actual.len().min(stream)]);
        assert_eq!(
            fixture.raw("stdout"),
            &actual[..actual.len().min(writer as usize)]
        );
        assert_eq!(evidence.stdout.received(), actual.len() as u64);
        assert_eq!(
            evidence.stdout.persisted(),
            actual.len().min(writer as usize) as u64
        );
        // No synthetic final callback duplicates any already-retained bytes.
        let _ = accept(
            &mut retained,
            Some(&evidence),
            true,
            &mut Vec::new(),
            StreamingOutputLimits::new(line, stream),
        );
        assert_eq!(evidence.stdout.received(), actual.len() as u64);
    }
}
#[test]
fn original_terminal_preserves_failure_cause_runtime_and_unknown_absence() {
    let observed = observation(
        &Status::Finished {
            outcome: Outcome::Exit(7),
            cause: CompletionCause::Cancelled,
            runtime_ns: 23,
        },
        Some([9; 16]),
    )
    .unwrap();
    assert_eq!(observed.native_member_attempt, Some([9; 16]));
    assert_eq!(observed.target_runtime, Some(Duration::from_nanos(23)));
    assert_eq!(observed.cause, Some(CaptureCompletionCause::Cancelled));
    assert!(observed.retirement_confirmed);
    assert!(
        observation(
            &Status::Refused {
                reason: "closed before GO".into()
            },
            None
        )
        .is_none()
    );
    assert!(
        observation(
            &Status::Unknown {
                reason: "transport lost".into(),
                started: None
            },
            None
        )
        .is_none()
    );
}

// These are untrusted observation DATA. They exercise the production query
// projection without constructing an SDK, CPU, native child or Ready owner.
fn completed_data() -> CapturedProcess {
    CapturedProcess {
        started: true,
        status: Some(ExitStatus::from_raw(0)),
        stdout: b"actual\0binary\xff-query".to_vec(),
        stderr: b"diagnostic\0tail".to_vec(),
        stdout_end: CaptureStreamEnd::Eof,
        stderr_end: CaptureStreamEnd::Eof,
        ..CapturedProcess::default()
    }
}

#[test]
fn query_projection_rejects_exit_zero_without_complete_error_free_capture() {
    for missing in 0..11 {
        let mut captured = completed_data();
        match missing {
            0 => captured.started = false,
            1 => captured.status = None,
            2 => captured.status = Some(ExitStatus::from_raw(7 * 256)),
            3 => captured.stdout_end = CaptureStreamEnd::LeaderExitDrained,
            4 => captured.stderr_end = CaptureStreamEnd::LeaderExitDrained,
            5 => captured.stdout_end = CaptureStreamEnd::Incomplete,
            6 => captured.stdout_truncated = true,
            7 => captured.stderr_truncated = true,
            8 => captured.failure = Some(anyhow::anyhow!("original helper/evidence failed")),
            9 => captured.read_error = Some("original pipe read failed".into()),
            10 => captured.cleanup_error = Some("original native cleanup failed".into()),
            _ => unreachable!(),
        }
        let stdout = captured.stdout.clone();
        let stderr = captured.stderr.clone();
        assert!(query_output(&mut captured, None).is_err(), "case {missing}");
        assert!(
            query_output(&mut captured, None).is_err(),
            "failure remained case {missing}"
        );
        assert_eq!(
            captured.stdout, stdout,
            "failed binary prefix case {missing}"
        );
        assert_eq!(
            captured.stderr, stderr,
            "failed binary prefix case {missing}"
        );
    }
}

#[test]
fn query_projection_preserves_complete_binary_data_without_text_callbacks() {
    let mut captured = completed_data();
    let output = query_output(&mut captured, None).unwrap();
    assert!(output.status.success());
    assert_eq!(output.stdout, b"actual\0binary\xff-query");
    assert_eq!(output.stderr, b"diagnostic\0tail");
    assert!(captured.stdout.is_empty());
    assert!(captured.stderr.is_empty());
}
