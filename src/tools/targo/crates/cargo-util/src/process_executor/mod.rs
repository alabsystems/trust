//! An explicit maintained execution owner for hosted processes. This interface
//! carries no admission authority; the owner must validate its actual context.
use crate::{CapturedProcess, ExecStats, ProcessBuilder, StreamingOutputLimits};
use anyhow::Result;
use std::io;
use std::process::{ExitStatus, Output};
use std::sync::{Arc, OnceLock};

/// Execution belongs to one real owner. Errors never fall back to local spawn
/// or an argument-file retry, since delivery may already have occurred.
pub trait ProcessExecutor: Send + Sync {
    /// Transport support only, never admission or proof authority. Unsupported
    /// owners retain the original before-delivery structured-capture refusal.
    fn supports_structured_capture(&self) -> bool {
        false
    }
    /// The selected owner alone retains the original child/transport through
    /// failed reads, cancellation, terminal observation and actual retirement.
    /// The builder supplies the once-resolved validated finite policy. Raw
    /// stream ends and measured stats must remain unknown when unobserved.
    fn capture(
        &self,
        _process: &ProcessBuilder,
        _limits: StreamingOutputLimits,
        _capture_rusage: bool,
    ) -> (ExecStats, CapturedProcess) {
        (
            ExecStats::default(),
            CapturedProcess {
                failure: Some(anyhow::anyhow!(
                    "execution owner does not support structured capture"
                )),
                ..CapturedProcess::default()
            },
        )
    }
    fn status(&self, process: &ProcessBuilder) -> io::Result<ExitStatus>;
    fn output(&self, process: &ProcessBuilder) -> io::Result<Output>;
    fn streaming(
        &self,
        process: &ProcessBuilder,
        on_stdout: &mut dyn FnMut(&str) -> Result<()>,
        on_stderr: &mut dyn FnMut(&str) -> Result<()>,
        capture: bool,
        limits: Option<StreamingOutputLimits>,
        capture_rusage: bool,
    ) -> (ExecStats, Result<Output>);
}
static DEFAULT: OnceLock<Arc<dyn ProcessExecutor>> = OnceLock::new();
/// Install the mandatory native execution owner before project subprocesses.
/// There is no reset or fallback to local execution after installation.
pub fn install_process_executor(executor: Arc<dyn ProcessExecutor>) -> io::Result<()> {
    DEFAULT.set(executor).map_err(|_| {
        io::Error::new(
            io::ErrorKind::AlreadyExists,
            "process execution owner already installed",
        )
    })
}
pub(crate) fn default_executor() -> Option<Arc<dyn ProcessExecutor>> {
    DEFAULT.get().cloned()
}

/// Borrow the SAME already installed mandatory dispatcher before constructing
/// a hosted context. This never installs/replaces an owner or grants native
/// admission, source/cache/SDK meaning, containment or settlement authority.
/// An absent dispatcher stays absent; callers must not fall back to local spawn.
pub fn installed_process_executor() -> Option<Arc<dyn ProcessExecutor>> {
    default_executor()
}

#[cfg(test)]
mod tests;
