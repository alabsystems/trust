// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::{ExitStatus, StreamingOutputLimits};
use anyhow::{Result, anyhow};
use std::time::Duration;

/// An observed owning lifecycle cause, separate from the process exit status.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CaptureCompletionCause {
    Exited,
    Timeout,
    Cancelled,
    ResourceLimit,
    /// The native owner lost execution or custody integrity.
    HostFault,
}

/// Optional actual native-owner observations. These fields neither admit work
/// nor authenticate an executable, and cannot reconstruct a live owner.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CaptureOwnerObservation {
    /// Original native member attempt observed by this execution owner. None
    /// for local/legacy routes. This equality data grants no execution, output
    /// eligibility, proof or authority to reconstruct a registered member.
    pub native_member_attempt: Option<[u8; 16]>,
    /// Actual target GO through its kernel exit, excluding later scope cleanup.
    /// Never substitute elapsed helper/orchestrator time for an unavailable value.
    pub target_runtime: Option<Duration>,
    pub cause: Option<CaptureCompletionCause>,
    /// Positive completion of the original scope AND retained helper transport.
    /// A reported terminal followed by transport loss leaves this false.
    pub retirement_confirmed: bool,
}

/// Trust: how the reader ended, distinct from process exit or proof success.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CaptureStreamEnd {
    /// No EOF was established, including refusal before launch.
    #[default]
    Incomplete,
    /// The reader observed physical EOF.
    Eof,
    /// The owner drained available bytes after leader retirement; writers may
    /// still hold the pipe. This is not complete capture, even at exit zero.
    LeaderExitDrained,
}

/// Trust: owned process observations, never a saved semantic verdict.
///
/// Status is unavailable when custody/wait could not establish it; absence does
/// not mean that execution never occurred. `started` records successful local
/// spawn or actual native target Started; helper spawn alone does not set it.
/// Cleanup failures remain distinct from the primary read failure.
#[derive(Debug, Default)]
pub struct CapturedProcess {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub started: bool,
    pub status: Option<ExitStatus>,
    pub stdout_end: CaptureStreamEnd,
    pub stderr_end: CaptureStreamEnd,
    pub stdout_truncated: bool,
    pub stderr_truncated: bool,
    pub failure: Option<anyhow::Error>,
    pub read_error: Option<String>,
    pub cleanup_error: Option<String>,
    /// Actual native lifecycle only, independent of physical pipe EOF and
    /// optional owning-wait metrics. Unobserved facts remain absent.
    pub owner_observation: Option<CaptureOwnerObservation>,
    /// Limits resolved once, if that point was reached. A refused launch can
    /// still have a resolved policy; these fields do not establish execution.
    pub limits: Option<StreamingOutputLimits>,
}

impl CapturedProcess {
    /// Both pipes reached physical EOF and every observed byte was retained.
    pub fn complete(&self) -> bool {
        self.stdout_end == CaptureStreamEnd::Eof
            && self.stderr_end == CaptureStreamEnd::Eof
            && !self.stdout_truncated
            && !self.stderr_truncated
    }

    /// Complete capture and a successful observed exit without owner errors.
    pub fn succeeded(&self) -> bool {
        self.started
            && self.complete()
            && self.status.is_some_and(|status| status.success())
            && self.failure.is_none()
            && self.read_error.is_none()
            && self.cleanup_error.is_none()
    }

    pub(super) fn ended(&mut self, stdout: bool, end: CaptureStreamEnd) {
        if stdout {
            self.stdout_end = end
        } else {
            self.stderr_end = end
        }
    }

    pub(super) fn retain(&mut self, stdout: bool, bytes: &[u8]) -> Result<()> {
        let maximum = self
            .limits
            .expect("raw capture requires resolved limits")
            .stream_bytes();
        let (output, truncated) = if stdout {
            (&mut self.stdout, &mut self.stdout_truncated)
        } else {
            (&mut self.stderr, &mut self.stderr_truncated)
        };
        let keep = bytes.len().min(maximum.saturating_sub(output.len()));
        *truncated |= keep != bytes.len();
        if let Err(error) = output.try_reserve_exact(keep) {
            *truncated = true;
            return Err(anyhow!(
                "could not retain bounded raw process output: {error}"
            ));
        }
        output.extend_from_slice(&bytes[..keep]);
        Ok(())
    }
}

#[cfg(all(test, any(target_os = "linux", target_os = "macos")))]
mod tests;
