use super::*;
use std::sync::atomic::{AtomicUsize, Ordering};

// Real process/pipe controls for status owners that already captured a child.
// These supply no hosted execution authority and execute no compiler fixture.
#[cfg(unix)]
#[test]
fn captured_status_actor() {
    let Ok(mode) = std::env::var("TRUST_CARGO_CAPTURED_STATUS_ACTOR") else {
        return;
    };
    let success = mode == "success";
    let code = if success { "0" } else { "7" };
    let script = format!(
        "printf 'status-out\\000\\377tail'; printf 'status-err\\000\\376tail' >&2; exit {code}"
    );
    if mode == "capture-failure" {
        let mut child = ProcessBuilder::new("/bin/sh");
        child.args(&["-c", &script]);
        let capture = child
            .exec_with_capture(StreamingOutputLimits::new(1024, 4096).with_child_exit_cleanup());
        assert!(capture.started && capture.complete());
        assert_eq!(capture.status.unwrap().code(), Some(7));
        let failure = capture
            .failure
            .as_ref()
            .expect("actual failed child")
            .to_string();
        let process = ProcessBuilder::new("/not-executed-captured-status");
        let error = process
            .report_captured_completion(capture, "missing original exit")
            .unwrap_err();
        assert_eq!(error.to_string(), failure);
        eprintln!("original-capture-failure-preserved");
        std::process::exit(0);
    }
    let output = std::process::Command::new("/bin/sh")
        .args(["-c", &script])
        .output()
        .unwrap();
    let mut process = ProcessBuilder::new("/not-executed-captured-status");
    match mode.as_str() {
        "inherit" | "success" | "broken-stdout" => {
            process.stderr(crate::Stdio::Inherit);
        }
        "null" => {
            process
                .stdout(crate::Stdio::Null)
                .stderr(crate::Stdio::Null);
        }
        "piped" => {
            process
                .stdout(crate::Stdio::Piped)
                .stderr(crate::Stdio::Piped);
        }
        "mixed" => {
            process
                .stdout(crate::Stdio::Null)
                .stderr(crate::Stdio::Inherit);
        }
        _ => panic!("unknown status actor mode"),
    }
    if mode == "broken-stdout" {
        use std::io::Write;
        use std::os::fd::AsRawFd;
        use std::os::unix::net::UnixStream;

        std::io::stdout().flush().unwrap();
        let (writer, reader) = UnixStream::pair().unwrap();
        drop(reader);
        // Only this isolated actor's own stdout is replaced, after the real
        // child exited. A closed peer makes delivery fail with a real EPIPE.
        assert_eq!(
            unsafe { libc::dup2(writer.as_raw_fd(), libc::STDOUT_FILENO) },
            1
        );
        let error = process.report_captured_status(output).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
        let report = error.get_ref().unwrap().to_string();
        assert!(report.contains("exit status: 7"), "{report}");
        assert!(std::error::Error::source(error.get_ref().unwrap()).is_some());
        eprintln!("original-status-and-first-io-error-preserved");
        std::process::exit(0);
    }
    let status = process.report_captured_status(output).unwrap();
    std::process::exit(status.code().unwrap());
}

#[cfg(unix)]
fn status_actor(mode: &str) -> Output {
    std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "process_executor::tests::captured_status_actor",
            "--nocapture",
        ])
        .env("TRUST_CARGO_CAPTURED_STATUS_ACTOR", mode)
        .output()
        .unwrap()
}

#[cfg(unix)]
fn has_bytes(haystack: &[u8], needle: &[u8]) -> bool {
    haystack.windows(needle.len()).any(|bytes| bytes == needle)
}

#[cfg(unix)]
#[test]
fn captured_status_preserves_raw_inherited_streams_and_both_exit_kinds() {
    for (mode, code) in [("inherit", 7), ("success", 0)] {
        let output = status_actor(mode);
        assert_eq!(output.status.code(), Some(code));
        assert!(has_bytes(&output.stdout, b"status-out\0\xfftail"));
        assert!(has_bytes(&output.stderr, b"status-err\0\xfetail"));
    }
}

#[cfg(unix)]
#[test]
fn captured_status_keeps_null_and_piped_streams_private() {
    for mode in ["null", "piped"] {
        let output = status_actor(mode);
        assert_eq!(output.status.code(), Some(7));
        assert!(!has_bytes(&output.stdout, b"status-out\0\xfftail"));
        assert!(!has_bytes(&output.stderr, b"status-err\0\xfetail"));
    }
}

#[cfg(unix)]
#[test]
fn captured_status_honors_each_stream_selection_independently() {
    let output = status_actor("mixed");
    assert_eq!(output.status.code(), Some(7));
    assert!(!has_bytes(&output.stdout, b"status-out\0\xfftail"));
    assert!(has_bytes(&output.stderr, b"status-err\0\xfetail"));
}

#[cfg(unix)]
#[test]
fn captured_failure_reports_both_streams_and_keeps_the_original_failure() {
    let output = status_actor("capture-failure");
    assert!(output.status.success(), "{output:?}");
    assert!(has_bytes(&output.stdout, b"status-out\0\xfftail"));
    assert!(has_bytes(&output.stderr, b"status-err\0\xfetail"));
    assert!(has_bytes(
        &output.stderr,
        b"original-capture-failure-preserved"
    ));
}

#[cfg(unix)]
#[test]
fn failed_stdout_delivery_still_reports_stderr_and_the_original_exit() {
    let output = status_actor("broken-stdout");
    assert!(output.status.success(), "{output:?}");
    assert!(!has_bytes(&output.stdout, b"status-out\0\xfftail"));
    assert!(has_bytes(&output.stderr, b"status-err\0\xfetail"));
    assert!(has_bytes(
        &output.stderr,
        b"original-status-and-first-io-error-preserved"
    ));
}
struct RefusingOwner(AtomicUsize);
impl ProcessExecutor for RefusingOwner {
    fn status(&self, _: &ProcessBuilder) -> io::Result<ExitStatus> {
        self.0.fetch_add(1, Ordering::Relaxed);
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "original execution owner refusal",
        ))
    }
    fn output(&self, _: &ProcessBuilder) -> io::Result<Output> {
        self.0.fetch_add(1, Ordering::Relaxed);
        Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "original execution owner refusal",
        ))
    }
    fn streaming(
        &self,
        _: &ProcessBuilder,
        _: &mut dyn FnMut(&str) -> Result<()>,
        _: &mut dyn FnMut(&str) -> Result<()>,
        _: bool,
        _: Option<StreamingOutputLimits>,
        _: bool,
    ) -> (ExecStats, Result<Output>) {
        self.0.fetch_add(1, Ordering::Relaxed);
        (
            ExecStats::default(),
            Err(anyhow::anyhow!("original execution owner refusal")),
        )
    }
}
#[test]
fn owned_routes_never_retry_locally_or_replace_their_root_on_failure() {
    let owner = Arc::new(RefusingOwner(AtomicUsize::new(0)));
    let mut process = ProcessBuilder::new("/nonexistent-must-not-execute-owned-route");
    process
        .process_executor(owner.clone())
        .retry_with_argfile(true);
    assert!(
        format!("{:#}", process.status().unwrap_err()).contains("original execution owner refusal")
    );
    assert!(
        format!("{:#}", process.output().unwrap_err()).contains("original execution owner refusal")
    );
    let (_, result) = process.exec_with_streaming(&mut |_| Ok(()), &mut |_| Ok(()), true, false);
    assert!(format!("{:#}", result.unwrap_err()).contains("original execution owner refusal"));
    assert!(
        format!("{:#}", process.exec_replace().unwrap_err()).contains("owned hosted execution")
    );
    assert!(
        format!("{:#}", process.exec_replace_supervised().unwrap_err())
            .contains("owned hosted execution")
    );
    assert_eq!(owner.0.load(Ordering::Relaxed), 3);
}

#[test]
fn structured_capture_refuses_unsupported_owner_before_delivery() {
    let owner = Arc::new(RefusingOwner(AtomicUsize::new(0)));
    let mut process = ProcessBuilder::new("/nonexistent-structured-capture-must-not-execute");
    process.process_executor(owner.clone());
    let captured =
        process.exec_with_capture(StreamingOutputLimits::new(1024, 4096).with_child_exit_cleanup());
    assert!(!captured.started && captured.status.is_none() && !captured.complete());
    assert!(
        captured
            .failure
            .unwrap()
            .to_string()
            .contains("does not support structured capture")
    );
    assert_eq!(owner.0.load(Ordering::Relaxed), 0);
}
