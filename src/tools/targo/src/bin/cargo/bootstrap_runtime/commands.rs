//! Trust: regular Cargo command results from the SAME original Root library.
//! No local child, new admission or artifact/native retirement is issued here.
use std::collections::BTreeMap;
use std::io::{self, Write};
use std::os::unix::process::ExitStatusExt as _;
use std::process::{Command, ExitStatus, Output};
use std::sync::{Arc, Mutex};

use bootstrap::engine::{OriginalBootstrapCompilation, OriginalCommand, OriginalCommandExecutor};
use cargo_util::EnvironmentInputs;
use cargo_util_terminal::Shell;
use targo::context::bootstrap_full::BootstrapFull;

const CAPTURE_LIMIT: usize = 128 * 1024 * 1024;

/// The constructor requires the real consuming native/Rust transition. Program
/// paths, environment, library status and decoded observations cannot create it.
pub(super) struct Commands {
    full: Arc<BootstrapFull>,
}
impl Commands {
    pub(super) fn new(full: Arc<BootstrapFull>) -> io::Result<Self> {
        full.check_current()?;
        Ok(Self { full })
    }
}
impl OriginalCommandExecutor for Commands {
    fn original(&self) -> &Arc<OriginalBootstrapCompilation> {
        self.full.original()
    }
    fn output(
        &self,
        projection: &OriginalCommand<'_>,
        stdout: bool,
        stderr: bool,
    ) -> io::Result<Output> {
        self.full.check_current()?;
        let command = projection.command();
        if command.get_program() != self.original().control_targo()?.as_os_str() {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "this command requires its actual seed or produced-program issuer; the control library cannot impersonate it",
            ));
        }
        // std::Command inherits the environment/cwd at execution time, not
        // when it was built or during a previous dependency-input phase.
        // These are selection DATA only; the actual Full owner checks them.
        let ambient = EnvironmentInputs::capture().map_err(io::Error::other)?;
        let environment =
            projected_environment(&ambient, command, projection.environment_cleared())?;
        let ambient_directory = std::env::current_dir()?;
        let directory = command
            .get_current_dir()
            .map_or(ambient_directory.clone(), |selected| {
                if selected.is_absolute() {
                    selected.to_owned()
                } else {
                    ambient_directory.join(selected)
                }
            });
        let directory = directory.canonicalize()?;
        let captured_stdout = Capture::new();
        let captured_stderr = Capture::new();
        let out: Box<dyn Write + Send + Sync> = if stdout {
            Box::new(captured_stdout.clone())
        } else {
            Box::new(io::stdout())
        };
        let err: Box<dyn Write + Send + Sync> = if stderr {
            Box::new(captured_stderr.clone())
        } else {
            Box::new(io::stderr())
        };
        let mut context = self
            .full
            .context(Shell::from_writes(out, err), environment)
            .map_err(io::Error::other)?;
        self.full
            .reload_context_directory(&mut context, &directory)
            .map_err(io::Error::other)?;
        let arguments = command
            .get_args()
            .map(ToOwned::to_owned)
            .collect::<Vec<_>>();
        let result =
            super::super::cli::original_full(&mut context, &arguments, Arc::clone(&self.full));
        let code = match result {
            Ok(()) => 0,
            Err(error) => report(error, &context)?,
        };
        if !(0..=255).contains(&code) {
            return Err(io::Error::other(
                "Cargo library returned an invalid command exit code",
            ));
        }
        self.full.check_current()?;
        drop(context);
        // This ordinary library result is not a Child, native completion,
        // source retirement, emitted-artifact witness or returned CPU credit.
        Ok(Output {
            status: ExitStatus::from_raw(code << 8),
            stdout: captured_stdout.into_bytes()?,
            stderr: captured_stderr.into_bytes()?,
        })
    }
}

fn projected_environment(
    ambient: &EnvironmentInputs,
    command: &Command,
    cleared: bool,
) -> io::Result<EnvironmentInputs> {
    let mut values = if cleared {
        BTreeMap::new()
    } else {
        ambient
            .iter()
            .map(|(name, value)| (name.to_owned(), value.to_owned()))
            .collect()
    };
    for (name, value) in command.get_envs() {
        match value {
            Some(value) => {
                values.insert(name.to_owned(), value.to_owned());
            }
            None => {
                values.remove(name);
            }
        }
    }
    EnvironmentInputs::from_variables(values).map_err(io::Error::other)
}

fn report(error: targo::util::CliError, context: &targo::util::GlobalContext) -> io::Result<i32> {
    // Keep canonical Clap diagnostics in this command's real output streams;
    // Error::print would write the Root process's global streams instead.
    if let Some(clap) = error
        .error
        .as_ref()
        .and_then(|error| error.downcast_ref::<clap::Error>())
    {
        let mut shell = context.shell();
        if clap.use_stderr() {
            write!(shell.err(), "{}", clap.render())?;
        } else {
            write!(shell.out(), "{}", clap.render())?;
        }
        return Ok(if clap.use_stderr() { 1 } else { 0 });
    }
    Ok(targo::report_cli_error(error, &mut context.shell()))
}

#[derive(Clone)]
struct Capture(Arc<Mutex<Captured>>);
struct Captured {
    bytes: Vec<u8>,
    failed: bool,
    limit: usize,
}
impl Capture {
    fn new() -> Self {
        Self(Arc::new(Mutex::new(Captured {
            bytes: Vec::new(),
            failed: false,
            limit: CAPTURE_LIMIT,
        })))
    }
    fn into_bytes(self) -> io::Result<Vec<u8>> {
        let captured = Arc::try_unwrap(self.0)
            .map_err(|_| io::Error::other("Cargo output still has live library writers"))?
            .into_inner()
            .map_err(|_| io::Error::other("Cargo output writer was poisoned"))?;
        if captured.failed {
            return Err(io::Error::other(
                "Cargo library output exceeded its finite capture bound",
            ));
        }
        Ok(captured.bytes)
    }
}
impl Write for Capture {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let mut captured = self
            .0
            .lock()
            .map_err(|_| io::Error::other("Cargo output poisoned"))?;
        if captured.failed || bytes.len() > captured.limit.saturating_sub(captured.bytes.len()) {
            captured.failed = true;
            return Err(io::Error::other(
                "Cargo library output exceeds its finite capture bound",
            ));
        }
        if let Err(error) = captured.bytes.try_reserve(bytes.len()) {
            captured.failed = true;
            return Err(io::Error::other(error));
        }
        captured.bytes.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_command_environment_edits_preserve_clear_and_remove_semantics() {
        let ambient = EnvironmentInputs::from_variables([
            ("KEEP".into(), "ambient".into()),
            ("REMOVE".into(), "ambient".into()),
        ])
        .unwrap();
        let mut command = Command::new("/selected-program");
        command.env_remove("REMOVE").env("EXPLICIT", "selected");
        let inherited = projected_environment(&ambient, &command, false).unwrap();
        let inherited = inherited.iter().collect::<BTreeMap<_, _>>();
        assert_eq!(inherited.len(), 2);
        assert_eq!(inherited[std::ffi::OsStr::new("KEEP")], "ambient");
        assert_eq!(inherited[std::ffi::OsStr::new("EXPLICIT")], "selected");
        command.env_clear().env("EXPLICIT", "selected");
        let cleared = projected_environment(&ambient, &command, true).unwrap();
        let cleared = cleared.iter().collect::<BTreeMap<_, _>>();
        assert_eq!(cleared.len(), 1);
        assert_eq!(cleared[std::ffi::OsStr::new("EXPLICIT")], "selected");
    }

    #[test]
    fn actual_capture_retains_bytes_and_rejects_live_writer_completion() {
        let mut captured = Capture::new();
        captured.write_all(b"actual\0output\n").unwrap();
        let live = captured.clone();
        assert!(captured.into_bytes().is_err());
        assert_eq!(live.into_bytes().unwrap(), b"actual\0output\n");
    }

    #[test]
    fn capture_refusal_is_sticky_and_never_returns_a_truncated_success() {
        let mut captured = Capture::new();
        captured.0.lock().unwrap().limit = 3;
        captured.write_all(b"abc").unwrap();
        assert!(captured.write_all(b"z").is_err());
        assert!(captured.write(b"").is_err());
        assert!(captured.into_bytes().is_err());
    }
}
