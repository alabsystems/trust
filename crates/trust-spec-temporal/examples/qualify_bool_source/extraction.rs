// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Compiler output evidence through the maintained native process owner.
//! This does not bound compiler memory, disk writes or the IR artifact read.

use std::error::Error;
use std::path::Path;

use cargo_util::{CaptureStreamEnd, CapturedProcess, ProcessBuilder, StreamingOutputLimits};

use super::{EXTRACTION_FLAGS, failure, reuse};

// Match Targo's compiler stream policy, including its machine-scaled aggregate
// floor. Identity queries have a different small-output policy. A live compiler
// has no default timeout; child-exit cleanup is not a runtime deadline.
fn compiler_limits() -> StreamingOutputLimits {
    StreamingOutputLimits::new(128 * 1024 * 1024, 512 * 1024 * 1024).with_child_exit_cleanup()
}

fn compiler_command(executable: &Path, output: &Path) -> ProcessBuilder {
    let mut process = ProcessBuilder::new(executable);
    process.cwd(output).args(EXTRACTION_FLAGS).arg("--out-dir").arg(output).arg("source.rs");
    // No stdin payload: the maintained owner supplies null stdin. Its normal
    // scheduling hygiene removes unchecked jobserver handoff, never restores it.
    process
}

pub(super) fn run(executable: &Path, output: &Path) -> Result<(), Box<dyn Error>> {
    execute(&compiler_command(executable, output), output, compiler_limits())
}

fn execute(
    process: &ProcessBuilder,
    output: &Path,
    limits: StreamingOutputLimits,
) -> Result<(), Box<dyn Error>> {
    let captured = process.exec_with_capture(limits);
    retain_and_admit(captured, output, limits)
}

fn stream_end(end: &CaptureStreamEnd) -> &'static str {
    match end {
        CaptureStreamEnd::Incomplete => "incomplete",
        CaptureStreamEnd::Eof => "eof",
        CaptureStreamEnd::LeaderExitDrained => "leader-exit-drained",
    }
}

fn retain_and_admit(
    captured: CapturedProcess,
    output: &Path,
    requested: StreamingOutputLimits,
) -> Result<(), Box<dyn Error>> {
    // These are the actual retained bytes, never UTF-8 callbacks or a rendering
    // of ProcessError. Save them on ordinary exit and capture/cleanup failure.
    reuse::write_new(&output.join("compiler.stdout"), &captured.stdout)?;
    reuse::write_new(&output.join("compiler.stderr"), &captured.stderr)?;
    let allowed = captured.started
        && captured.succeeded()
        && captured.read_error.is_none()
        && captured.cleanup_error.is_none();
    #[cfg(unix)]
    let signal = {
        use std::os::unix::process::ExitStatusExt as _;
        captured.status.and_then(|status| status.signal())
    };
    #[cfg(not(unix))]
    let signal: Option<i32> = None;
    let milliseconds =
        |duration: std::time::Duration| u64::try_from(duration.as_millis()).unwrap_or(u64::MAX);
    let record = serde_json::json!({
        "schema": "trust.source-compiler-execution/v1",
        "started": captured.started,
        "status_available": captured.status.is_some(),
        "status_success": captured.status.map(|status| status.success()),
        "exit_code": captured.status.and_then(|status| status.code()),
        "signal": signal,
        "stdout_end": stream_end(&captured.stdout_end),
        "stderr_end": stream_end(&captured.stderr_end),
        "stdout_truncated": captured.stdout_truncated,
        "stderr_truncated": captured.stderr_truncated,
        "capture_complete": captured.complete(),
        "execution_admitted": allowed,
        "failure": captured.failure.as_ref().map(|error| error.to_string()),
        "read_error": captured.read_error,
        "cleanup_error": captured.cleanup_error,
        "stdout_bytes": captured.stdout.len(),
        "stderr_bytes": captured.stderr.len(),
        "requested_line_bytes": requested.line_bytes(),
        "requested_stream_floor_bytes": requested.stream_bytes(),
        "requested_timeout_ms": requested.runtime_timeout().map(milliseconds),
        "actual_line_bytes": captured.limits.map(|limits| limits.line_bytes()),
        "actual_stream_bytes": captured.limits.map(|limits| limits.stream_bytes()),
        "actual_timeout_ms": captured.limits.and_then(|limits| limits.runtime_timeout()).map(milliseconds),
        "scope": "owned output capture; no compiler memory, disk, IR-file or loaded-runtime bound",
    });
    reuse::write_new(
        &output.join("compiler-execution.json"),
        &serde_json::to_vec_pretty(&record)?,
    )?;
    if !allowed {
        return Err(failure(format!("source compiler failed; see {}", output.display())));
    }
    Ok(())
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
#[path = "extraction/tests.rs"]
mod tests;
