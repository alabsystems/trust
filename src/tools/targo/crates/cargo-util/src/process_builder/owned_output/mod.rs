//! Opt-in synchronous capture retaining the real child through every error.
use super::{ProcessBuilder, ProcessError, close_tempfile_and_log_error, debug_force_argfile};
use anyhow::{Context as _, Result};
use std::fs::File;
use std::io::{self, Read, Seek, Write};
use std::process::{Child, Command, Output, Stdio};

impl ProcessBuilder {
    /// Capture a synchronous query without consuming Child before terminal.
    /// Existing hosted execution and argument-file policy remain authoritative.
    /// This opts in only the query owner; ordinary unit execution is unchanged.
    pub fn output_owned(&self) -> Result<Output> {
        self.owned_output()
            .with_context(|| ProcessError::could_not_execute(self))
    }

    fn owned_output(&self) -> io::Result<Output> {
        if let Some(executor) = self.executor() {
            if self.action_sandbox.is_some() {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "hosted executor cannot bypass a confined action",
                ));
            }
            // Delivery belongs to this executor; errors never try local spawn.
            return executor.output(self);
        }
        if !debug_force_argfile(self.retry_with_argfile) {
            match capture(self.build_command(), self.stdin.as_deref()) {
                Err(CaptureError::BeforeStart(error)) if self.should_retry_with_argfile(&error) => {
                }
                result => return result.map_err(CaptureError::into_io),
            }
        }
        let (command, argfile) = self.build_command_with_argfile()?;
        let result = capture(command, self.stdin.as_deref()).map_err(CaptureError::into_io);
        close_tempfile_and_log_error(argfile);
        result
    }
}

// Retained before the scheduler borrow is released, including during unwind.
struct Running(Child);
impl Drop for Running {
    fn drop(&mut self) {
        if !matches!(self.0.try_wait(), Ok(Some(_))) {
            let _ = self.0.kill();
            if self.0.wait().is_err() {
                // A future implicit borrower cannot run with unknown custody.
                std::process::abort();
            }
        }
    }
}

enum CaptureError {
    BeforeStart(io::Error),
    AfterStart(io::Error),
}
impl CaptureError {
    fn into_io(self) -> io::Error {
        match self {
            Self::BeforeStart(error) | Self::AfterStart(error) => error,
        }
    }
}

fn capture(mut command: Command, stdin: Option<&[u8]>) -> Result<Output, CaptureError> {
    // Private seekable captures avoid pipe deadlock and keep Child available
    // on every write/wait/read error. No detached capture workers are created.
    let (mut stdout, mut stderr, mut running) = (|| -> io::Result<_> {
        let directory = tempfile::env::temp_dir();
        let stdout = capture_file_in(&directory)?;
        let stderr = capture_file_in(&directory)?;
        command
            .stdout(stdout.try_clone()?)
            .stderr(stderr.try_clone()?);
        command.stdin(if stdin.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        });
        Ok((stdout, stderr, Running(command.spawn()?)))
    })()
    .map_err(CaptureError::BeforeStart)?;
    let result = (|| -> io::Result<_> {
        if let Some(bytes) = stdin {
            running
                .0
                .stdin
                .take()
                .ok_or_else(|| io::Error::other("query stdin missing"))?
                .write_all(bytes)?;
        }
        let status = running.0.wait()?;
        let stdout = contents(&mut stdout)?;
        let stderr = contents(&mut stderr)?;
        Ok(Output {
            status,
            stdout,
            stderr,
        })
    })();
    drop(running); // also owns the child before returning an I/O error
    result.map_err(CaptureError::AfterStart)
}

// Trust (RL-64): a capture file that cannot be made names the folder that
// refused it. With an inherited scheduler and a TMPDIR that refuses writes,
// the whole cause under "could not execute process ... (never executed)" was
// a bare `Permission denied (os error 13)`. The kind is kept for callers.
fn capture_file_in(directory: &std::path::Path) -> io::Result<File> {
    tempfile::tempfile_in(directory).map_err(|error| {
        io::Error::new(
            error.kind(),
            format!(
                "could not create an output capture file in {}: {error}",
                directory.display()
            ),
        )
    })
}

fn contents(file: &mut File) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    file.rewind()?;
    file.read_to_end(&mut bytes)?;
    Ok(bytes)
}

#[cfg(all(test, unix))]
mod tests;
