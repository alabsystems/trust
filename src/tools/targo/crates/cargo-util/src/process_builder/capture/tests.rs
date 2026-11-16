// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::super::tests::{CHILD_EXIT_TEST_LOCK, STREAMING_CHILD_MARKER, streaming_child_command};
use super::super::{
    ProcessBuilder, StreamingChildExit, StreamingSignals, configure_streaming_child,
};
use super::*;
use crate::read2::Read2Action;
use std::io;
use std::io::Write as _;
use std::os::fd::{FromRawFd, IntoRawFd, OwnedFd};
use std::os::unix::process::ExitStatusExt;
use std::process::{ChildStdout, Stdio};
use std::time::{Duration, Instant};

/// Test-only selected owner with one actual native child as its backing. This
/// is not an Aterm admission fixture: production owners remain unsupported
/// until they explicitly implement their retained transport.
struct NativeCaptureOwner {
    calls: std::sync::atomic::AtomicUsize,
    measured: std::sync::atomic::AtomicBool,
    fail_after_capture: bool,
}

impl crate::ProcessExecutor for NativeCaptureOwner {
    fn supports_structured_capture(&self) -> bool {
        true
    }
    fn capture(
        &self,
        process: &ProcessBuilder,
        limits: StreamingOutputLimits,
        capture_rusage: bool,
    ) -> (crate::ExecStats, CapturedProcess) {
        use std::sync::atomic::Ordering;
        self.calls.fetch_add(1, Ordering::SeqCst);
        self.measured.store(capture_rusage, Ordering::SeqCst);
        assert!(limits.child_exit_cleanup);
        assert!(limits.line_bytes() > 0 && limits.stream_bytes() > 0);
        // This explicit fixture owner selects the maintained native lifecycle
        // once. Clearing its own test route is not a production retry/fallback.
        let mut backing = process.clone();
        backing.executor = None;
        let (stats, mut captured) = backing.exec_with_capture_and_stats(limits, capture_rusage);
        if self.fail_after_capture {
            captured.failure = Some(anyhow!("selected owner failed after actual capture"));
        }
        (stats, captured)
    }
    fn status(&self, _: &ProcessBuilder) -> io::Result<ExitStatus> {
        panic!("structured capture retried through status")
    }
    fn output(&self, _: &ProcessBuilder) -> io::Result<std::process::Output> {
        panic!("structured capture retried through output")
    }
    fn streaming(
        &self,
        _: &ProcessBuilder,
        _: &mut dyn FnMut(&str) -> Result<()>,
        _: &mut dyn FnMut(&str) -> Result<()>,
        _: bool,
        _: Option<StreamingOutputLimits>,
        _: bool,
    ) -> (crate::ExecStats, Result<std::process::Output>) {
        panic!("structured capture retried through streaming")
    }
}

fn native_capture_owner(fail_after_capture: bool) -> std::sync::Arc<NativeCaptureOwner> {
    std::sync::Arc::new(NativeCaptureOwner {
        calls: std::sync::atomic::AtomicUsize::new(0),
        measured: std::sync::atomic::AtomicBool::new(false),
        fail_after_capture,
    })
}

#[test]
fn selected_capture_owner_keeps_actual_failed_binary_bytes_status_and_error() {
    use std::sync::atomic::Ordering;
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    for fail_after_capture in [false, true] {
        let owner = native_capture_owner(fail_after_capture);
        let mut process = streaming_child_command("capture-failure");
        process
            .process_executor(owner.clone())
            .retry_with_argfile(true);
        let (stats, captured) = process.exec_with_capture_and_stats(limits(), true);
        assert_eq!(owner.calls.load(Ordering::SeqCst), 1);
        assert!(owner.measured.load(Ordering::SeqCst));
        assert!(captured.started && captured.complete() && !captured.succeeded());
        assert_eq!(captured.status.unwrap().code(), Some(7));
        assert!(captured.stdout.ends_with(b"raw\0\xff-final-tail"));
        assert_eq!(captured.stderr, b"stderr-evidence-tail\0");
        assert!(captured.read_error.is_none() && captured.cleanup_error.is_none());
        assert!(
            stats.cpu_times.is_some() && stats.peak_rss.is_some(),
            "{stats:?}"
        );
        if fail_after_capture {
            assert_eq!(
                captured.failure.unwrap().to_string(),
                "selected owner failed after actual capture"
            );
        }
    }
}

#[test]
fn selected_capture_owner_keeps_same_wait_accounting_when_output_is_rejected() {
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let owner = native_capture_owner(false);
    let mut process = streaming_child_command("aggregate-stdout");
    process.process_executor(owner);
    let (stats, captured) = process.exec_with_capture_and_stats(
        StreamingOutputLimits::new(1024, 4096).with_child_exit_cleanup(),
        true,
    );
    assert!(captured.started && captured.status.is_some() && !captured.succeeded());
    assert_eq!(captured.stdout.len(), 4096);
    assert!(captured.stdout_truncated && captured.read_error.is_some());
    assert!(
        stats.cpu_times.is_some() && stats.peak_rss.is_some(),
        "{stats:?}"
    );
}

#[test]
fn selected_capture_owner_keeps_actual_rejected_prefix_and_incomplete_streams() {
    use std::sync::atomic::Ordering;
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let owner = native_capture_owner(false);
    let mut process = streaming_child_command("aggregate-stdout");
    process.process_executor(owner.clone());
    let captured =
        process.exec_with_capture(StreamingOutputLimits::new(1024, 4096).with_child_exit_cleanup());
    assert_eq!(owner.calls.load(Ordering::SeqCst), 1);
    assert!(!owner.measured.load(Ordering::SeqCst));
    assert_eq!(captured.stdout.len(), 4096);
    assert!(captured.stdout_truncated && !captured.complete() && !captured.succeeded());
    assert!(captured.status.is_some() && captured.cleanup_error.is_none());
    assert!(
        captured
            .read_error
            .unwrap()
            .contains("4096-byte aggregate safety limit")
    );
    assert_eq!(captured.limits.unwrap().stream_bytes(), 4096);
}

#[test]
fn selected_capture_owner_is_not_delivered_invalid_or_confined_work() {
    use std::sync::atomic::Ordering;
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let owner = native_capture_owner(false);
    let mut process = streaming_child_command("capture-success");
    process.process_executor(owner.clone());
    for invalid in [
        StreamingOutputLimits::new(1, 1),
        StreamingOutputLimits::new(0, 1).with_child_exit_cleanup(),
        limits().with_timeout(Duration::ZERO),
    ] {
        let captured = process.exec_with_capture(invalid);
        assert!(!captured.started && captured.status.is_none());
        assert!(captured.failure.is_some() && captured.limits.is_none());
    }
    process.action_sandbox = Some(crate::ActionSandbox::new());
    let captured = process.exec_with_capture(limits());
    assert!(!captured.started && captured.status.is_none());
    assert!(
        captured
            .failure
            .unwrap()
            .to_string()
            .contains("confined action")
    );
    assert_eq!(owner.calls.load(Ordering::SeqCst), 0);
}

fn limits() -> StreamingOutputLimits {
    StreamingOutputLimits::new(1024, 16 * 1024).with_child_exit_cleanup()
}

#[test]
fn controlled_reader_retains_physical_eof_separately_from_retired_scope_flush() {
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let (reader, writer) = io::pipe().unwrap();
    let held_writer = writer.try_clone().unwrap();
    let mut child = streaming_child_command("capture-success")
        .build_command()
        .stdout(Stdio::from(writer))
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // Only this known native child writes; the parent deliberately keeps a
    // writer open after its actual wait. There is no resource-admission claim.
    let reader = unsafe { OwnedFd::from_raw_fd(reader.into_raw_fd()) };
    let stderr = child.stderr.take().unwrap();
    let mut physical_eof = [true; 2]; // The reader must clear stale caller data.
    let mut final_callbacks = [false; 2];
    let mut bytes = [Vec::new(), Vec::new()];
    let result = crate::read2_controlled_with_eof(
        ChildStdout::from(reader),
        stderr,
        Some(Instant::now() + Duration::from_secs(60)),
        &mut |out, data, final_line| {
            let index = usize::from(!out);
            bytes[index].extend_from_slice(data);
            data.clear();
            final_callbacks[index] |= final_line;
            Read2Action::Continue
        },
        &mut || {
            Ok(if child.try_wait()?.is_some() {
                crate::Read2Control::Drain
            } else {
                crate::Read2Control::Continue
            })
        },
        &mut physical_eof,
    );
    assert_eq!(result.unwrap(), Read2Action::Continue);
    assert_eq!(physical_eof, [false, true]);
    assert_eq!(final_callbacks, [true, true]);
    assert!(bytes[0].ends_with(b"raw\0\xff-final-tail"));
    assert_eq!(bytes[1], b"stderr-evidence-tail\0");
    assert!(child.wait().unwrap().success());
    drop(held_writer);
}

#[test]
fn owner_observations_never_replace_byte_completion_or_general_exit_semantics() {
    let mut captured = CapturedProcess {
        started: true,
        status: Some(ExitStatus::from_raw(0)),
        stdout_end: CaptureStreamEnd::Eof,
        stderr_end: CaptureStreamEnd::Eof,
        ..CapturedProcess::default()
    };
    assert!(captured.succeeded());
    captured.owner_observation = Some(CaptureOwnerObservation {
        native_member_attempt: None,
        target_runtime: Some(Duration::ZERO),
        cause: Some(CaptureCompletionCause::Cancelled),
        retirement_confirmed: false,
    });
    // Workload eligibility separately checks the actual cause and retirement.
    assert!(captured.succeeded());
    captured.stdout_end = CaptureStreamEnd::LeaderExitDrained;
    captured
        .owner_observation
        .as_mut()
        .unwrap()
        .retirement_confirmed = true;
    assert!(!captured.complete() && !captured.succeeded());
}

#[test]
fn raw_capture_split_tail_newline_and_eof_keep_each_byte_once() {
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let directory = tempfile::tempdir().unwrap();
    let address = directory.path().join("ack.sock");
    let listener = std::os::unix::net::UnixListener::bind(&address).unwrap();
    let mut process = streaming_child_command("capture-split");
    process.env(STREAMING_CHILD_MARKER, &address);
    let mut captured = CapturedProcess::default();
    // The child writes its second chunk only after this callback proves the
    // first chunk reached the actual reader. No scheduling delay is assumed.
    let (_, result) = process.exec_with_streaming_impl(
        &mut |line| {
            if line == "prefix-first" {
                listener.accept()?.0.write_all(&[1])?;
            }
            Ok(())
        },
        &mut |_| Ok(()),
        false,
        Some(limits().with_timeout(Duration::from_secs(60))),
        false,
        Some(&mut captured),
    );
    assert!(result.is_ok(), "{result:?}; {captured:?}");
    assert!(captured.succeeded(), "{captured:?}");
    let expected = b"prefix-first\npartial\0\xff-finished\nlast\0\xfe";
    assert!(captured.stdout.ends_with(expected), "{:?}", captured.stdout);
    assert_eq!(
        captured
            .stdout
            .windows(b"prefix-first".len())
            .filter(|part| *part == b"prefix-first")
            .count(),
        1
    );
    assert!(captured.stderr.is_empty());
}

#[test]
fn raw_capture_preserves_binary_tails_nonzero_and_signal_status_without_diagnostic_copies() {
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    for (role, code, signal) in [
        ("capture-success", Some(0), None),
        ("capture-failure", Some(7), None),
        ("capture-signal", None, Some(libc::SIGKILL)),
    ] {
        let captured = streaming_child_command(role).exec_with_capture(limits());
        assert!(captured.started && captured.complete(), "{captured:?}");
        assert!(captured.stdout.ends_with(b"raw\0\xff-final-tail"));
        assert_eq!(captured.stderr, b"stderr-evidence-tail\0");
        assert_eq!(captured.status.unwrap().code(), code);
        assert_eq!(captured.status.unwrap().signal(), signal);
        assert_eq!(captured.succeeded(), code == Some(0));
        assert!(captured.read_error.is_none() && captured.cleanup_error.is_none());
        if let Some(error) = &captured.failure {
            assert!(!format!("{error:#}").contains("stderr-evidence-tail"));
        }
    }
}

#[test]
fn raw_capture_keeps_rejected_lines_and_clips_aggregate_prefix_at_applied_bound() {
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let line = streaming_child_command("oversized-stderr").exec_with_capture(limits());
    assert_eq!(line.stderr, vec![b'e'; 1025]);
    assert!(!line.complete() && !line.succeeded());
    assert!(
        line.read_error
            .as_ref()
            .unwrap()
            .contains("1024-byte safety limit")
    );
    assert!(line.status.is_some() && line.cleanup_error.is_none());
    let aggregate = streaming_child_command("aggregate-stdout")
        .exec_with_capture(StreamingOutputLimits::new(1024, 4096).with_child_exit_cleanup());
    assert_eq!(aggregate.stdout.len(), 4096);
    assert!(aggregate.stdout_truncated && !aggregate.complete() && !aggregate.succeeded());
    assert!(
        aggregate
            .read_error
            .as_ref()
            .unwrap()
            .contains("4096-byte aggregate safety limit")
    );
    assert_eq!(aggregate.limits.unwrap().stream_bytes(), 4096);
    assert!(aggregate.status.is_some() && aggregate.cleanup_error.is_none());
}

#[test]
fn raw_capture_timeout_retains_unterminated_bytes_and_reaped_status() {
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    for role in ["capture-timeout", "closed-pipes-hang"] {
        let captured = streaming_child_command(role)
            .exec_with_capture(limits().with_timeout(Duration::from_secs(2)));
        assert!(captured.started && captured.status.is_some() && !captured.succeeded());
        assert!(captured.read_error.as_ref().unwrap().contains("timeout"));
        assert!(captured.cleanup_error.is_none(), "{captured:?}");
        if role == "capture-timeout" {
            assert!(captured.stdout.ends_with(b"raw\0\xff-final-tail"));
            assert_eq!(captured.stderr, b"stderr-evidence-tail\0");
            assert!(!captured.complete());
        } else {
            assert!(
                captured.complete(),
                "physical EOF alone cannot imply success"
            );
        }
        assert!(!format!("{:#}", captured.failure.unwrap()).contains("never executed"));
    }
}

#[test]
fn raw_capture_preflight_and_spawn_refusals_do_not_invent_execution() {
    let process = ProcessBuilder::new("/nonexistent-capture-fixture-must-not-execute");
    let invalid = process.exec_with_capture(StreamingOutputLimits::new(1, 1));
    assert!(!invalid.started && invalid.status.is_none() && invalid.limits.is_none());
    assert!(
        invalid
            .failure
            .unwrap()
            .to_string()
            .contains("requires child-exit cleanup")
    );
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let missing = process.exec_with_capture(limits());
    assert!(!missing.started && missing.status.is_none() && !missing.complete());
    assert!(missing.stdout.is_empty() && missing.stderr.is_empty());
    assert!(missing.failure.is_some() && missing.limits.is_some());
}

#[test]
fn raw_capture_parent_held_writer_is_owner_drained_and_cleanup_error_keeps_status() {
    let _lease = CHILD_EXIT_TEST_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let mut signals = StreamingSignals::install(true).unwrap();
    let (reader, writer) = io::pipe().unwrap();
    let held_writer = writer.try_clone().unwrap();
    let mut command = streaming_child_command("capture-success").build_command();
    configure_streaming_child(&mut command, true);
    let mut child = command
        .stdout(Stdio::from(writer))
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // SAFETY: ownership is transferred from this pipe reader, exactly once.
    let reader = unsafe { OwnedFd::from_raw_fd(reader.into_raw_fd()) };
    let stderr = child.stderr.take().unwrap();
    let mut owner = StreamingChildExit::start(&mut child, true, None, None)
        .unwrap()
        .unwrap();
    let mut bytes = Vec::new();
    let read = owner
        .read(
            ChildStdout::from(reader),
            stderr,
            Some(Instant::now() + Duration::from_secs(60)),
            &mut |stdout, data, _| {
                if stdout {
                    bytes.extend_from_slice(data);
                }
                data.clear();
                Read2Action::Continue
            },
        )
        .unwrap();
    assert!(matches!(read, Read2Action::Continue));
    assert!(bytes.ends_with(b"raw\0\xff-final-tail"));
    assert_eq!(
        owner.stream_ends,
        [CaptureStreamEnd::LeaderExitDrained, CaptureStreamEnd::Eof]
    );
    // Exercise a cleanup failure after a real WNOWAIT observation, before its
    // final real reap. The status must survive the distinct cleanup error.
    owner.observed.as_mut().unwrap().error = Some(io::Error::other("injected cleanup failure"));
    assert!(
        owner
            .finish(false)
            .unwrap_err()
            .to_string()
            .contains("injected cleanup failure")
    );
    let captured = CapturedProcess {
        started: true,
        status: owner.reaped_status,
        stdout_end: owner.stream_ends[0],
        stderr_end: owner.stream_ends[1],
        ..CapturedProcess::default()
    };
    assert!(captured.status.unwrap().success());
    assert!(!captured.complete() && !captured.succeeded());
    drop(owner);
    drop(held_writer);
    signals.as_mut().unwrap().restore().unwrap();
}
