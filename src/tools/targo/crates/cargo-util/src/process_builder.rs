use crate::process_error::ProcessError;
use crate::read2::{Read2Action, read2_interruptible};

use anyhow::{Context, Result, anyhow, bail};
use jobserver::Client;
use shell_escape::escape;
use tempfile::NamedTempFile;

use std::collections::BTreeMap;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::io::{self, Write};
use std::iter::once;
#[cfg(unix)]
use std::os::fd::{AsRawFd as _, OwnedFd};
use std::path::Path;
use std::process::{Child, Command, ExitStatus, Output, Stdio};
#[cfg(unix)]
use std::sync::Arc;
use std::time::{Duration, Instant};

/// Trust: finite buffering policy for untrusted child stdout and stderr.
///
/// Upstream reads a child's output until the pipe closes, which is fine when
/// the child is trusted and fatal when it is not: a compiler, proc macro, or
/// build script can emit an unbounded newline-free stream and exhaust the
/// parent's memory before any consumer inspects a single line.
///
/// The ordinary Cargo streaming API remains unbounded for compatibility. A
/// caller handling authenticated or otherwise adversarial output can opt into
/// this policy with [`ProcessBuilder::exec_with_streaming_limits`]. Each stream
/// gets an independent aggregate budget; `max_line_bytes` also bounds the
/// unterminated partial line retained while waiting for a newline.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StreamingOutputLimits {
    max_line_bytes: usize,
    max_stream_bytes: usize,
    timeout: Option<Duration>,
}

impl StreamingOutputLimits {
    pub const fn new(max_line_bytes: usize, max_stream_bytes: usize) -> Self {
        Self {
            max_line_bytes,
            max_stream_bytes,
            timeout: None,
        }
    }

    /// Adds a finite elapsed-time budget for spawning, reading, and waiting
    /// for the child. The timeout uses a monotonic clock.
    pub const fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    fn validate(self) -> Result<()> {
        if self.max_line_bytes == 0 {
            bail!("streaming output line limit must be greater than zero");
        }
        if self.max_stream_bytes == 0 {
            bail!("streaming output aggregate limit must be greater than zero");
        }
        if self.timeout == Some(Duration::ZERO) {
            bail!("streaming process timeout must be greater than zero");
        }
        Ok(())
    }
}

/// A builder object for an external process, similar to [`std::process::Command`].
#[derive(Clone, Debug)]
pub struct ProcessBuilder {
    /// The program to execute.
    program: OsString,
    /// Best-effort replacement for arg0
    arg0: Option<OsString>,
    /// A list of arguments to pass to the program.
    args: Vec<OsString>,
    /// Any environment variables that should be set for the program.
    env: BTreeMap<String, Option<OsString>>,
    /// The directory to run the program from.
    cwd: Option<OsString>,
    /// A list of wrappers that wrap the original program when calling
    /// [`ProcessBuilder::wrapped`]. The last one is the outermost one.
    wrappers: Vec<OsString>,
    /// The `make` jobserver. See the [jobserver crate] for
    /// more information.
    ///
    /// [jobserver crate]: https://docs.rs/jobserver/
    jobserver: Option<Client>,
    /// `true` to include environment variable in display.
    display_env_vars: bool,
    /// `true` to retry with an argfile if hitting "command line too big" error.
    /// See [`ProcessBuilder::retry_with_argfile`] for more information.
    retry_with_argfile: bool,
    /// Data to write to stdin.
    stdin: Option<Vec<u8>>,
    /// Descriptors whose `FD_CLOEXEC` bit is cleared only in this command's
    /// post-fork child. The parent and unrelated children retain CLOEXEC.
    #[cfg(unix)]
    inherited_fds: Vec<Arc<OwnedFd>>,
    /// CLOEXEC descriptors retained through fork so they can back a
    /// builder-scoped capability, but never inherited across exec.
    #[cfg(unix)]
    exec_guard_fds: Vec<Arc<OwnedFd>>,
}

impl fmt::Display for ProcessBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`")?;

        if self.display_env_vars {
            for (key, val) in self.env.iter() {
                if let Some(val) = val {
                    let val = escape(val.to_string_lossy());
                    if cfg!(windows) {
                        write!(f, "set {}={}&& ", key, val)?;
                    } else {
                        write!(f, "{}={} ", key, val)?;
                    }
                }
            }
        }

        write!(f, "{}", self.get_program().to_string_lossy())?;

        for arg in self.get_args() {
            write!(f, " {}", escape(arg.to_string_lossy()))?;
        }

        write!(f, "`")
    }
}

impl ProcessBuilder {
    /// Creates a new [`ProcessBuilder`] with the given executable path.
    pub fn new<T: AsRef<OsStr>>(cmd: T) -> ProcessBuilder {
        ProcessBuilder {
            program: cmd.as_ref().to_os_string(),
            arg0: None,
            args: Vec::new(),
            cwd: None,
            env: BTreeMap::new(),
            wrappers: Vec::new(),
            jobserver: None,
            display_env_vars: false,
            retry_with_argfile: false,
            stdin: None,
            #[cfg(unix)]
            inherited_fds: Vec::new(),
            #[cfg(unix)]
            exec_guard_fds: Vec::new(),
        }
    }

    /// Trust: pass a CLOEXEC descriptor to this process only.
    ///
    /// Upstream has no way to give exactly one child a descriptor: clearing
    /// CLOEXEC in the parent hands it to every subsequent child as well. A
    /// capability that authenticates one specific handoff has to be narrower
    /// than that, so the bit is cleared after fork and before exec, only for
    /// commands cloned from this builder.
    #[cfg(unix)]
    pub fn inherit_fd_for_exec(&mut self, fd: Arc<OwnedFd>) -> io::Result<&mut ProcessBuilder> {
        let raw_fd = fd.as_raw_fd();
        if raw_fd < 3 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "inherited process descriptor must not alias stdin/stdout/stderr",
            ));
        }
        let flags = unsafe { libc::fcntl(raw_fd, libc::F_GETFD) };
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        if flags & libc::FD_CLOEXEC == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "inherited process descriptor must be CLOEXEC in the parent",
            ));
        }
        if self
            .inherited_fds
            .iter()
            .chain(&self.exec_guard_fds)
            .any(|existing| existing.as_raw_fd() == raw_fd)
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "process descriptor was registered more than once",
            ));
        }
        self.inherited_fds.push(fd);
        Ok(self)
    }

    /// Trust: keep a CLOEXEC descriptor live until this command crosses exec.
    ///
    /// Unlike [`Self::inherit_fd_for_exec`], this never clears CLOEXEC. It is
    /// useful for retaining the peer of a child-only socket capability without
    /// exposing that authoritative endpoint to the child image.
    #[cfg(unix)]
    pub fn hold_fd_through_exec(&mut self, fd: Arc<OwnedFd>) -> io::Result<&mut ProcessBuilder> {
        let raw_fd = fd.as_raw_fd();
        if raw_fd < 3 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "exec guard descriptor must not alias stdin/stdout/stderr",
            ));
        }
        let flags = unsafe { libc::fcntl(raw_fd, libc::F_GETFD) };
        if flags < 0 {
            return Err(io::Error::last_os_error());
        }
        if flags & libc::FD_CLOEXEC == 0 {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "exec guard descriptor must be CLOEXEC",
            ));
        }
        if self
            .exec_guard_fds
            .iter()
            .chain(&self.inherited_fds)
            .any(|existing| existing.as_raw_fd() == raw_fd)
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "process descriptor was registered more than once",
            ));
        }
        self.exec_guard_fds.push(fd);
        Ok(self)
    }

    /// (chainable) Sets the executable for the process.
    pub fn program<T: AsRef<OsStr>>(&mut self, program: T) -> &mut ProcessBuilder {
        self.program = program.as_ref().to_os_string();
        self
    }

    /// (chainable) Overrides `arg0` for this program.
    pub fn arg0<T: AsRef<OsStr>>(&mut self, arg: T) -> &mut ProcessBuilder {
        self.arg0 = Some(arg.as_ref().to_os_string());
        self
    }

    /// (chainable) Adds `arg` to the args list.
    pub fn arg<T: AsRef<OsStr>>(&mut self, arg: T) -> &mut ProcessBuilder {
        self.args.push(arg.as_ref().to_os_string());
        self
    }

    /// (chainable) Adds multiple `args` to the args list.
    pub fn args<T: AsRef<OsStr>>(&mut self, args: &[T]) -> &mut ProcessBuilder {
        self.args
            .extend(args.iter().map(|t| t.as_ref().to_os_string()));
        self
    }

    /// (chainable) Replaces the args list with the given `args`.
    pub fn args_replace<T: AsRef<OsStr>>(&mut self, args: &[T]) -> &mut ProcessBuilder {
        if let Some(program) = self.wrappers.pop() {
            // User intend to replace all args, so we
            // - use the outermost wrapper as the main program, and
            // - cleanup other inner wrappers.
            self.program = program;
            self.wrappers = Vec::new();
        }
        self.args = args.iter().map(|t| t.as_ref().to_os_string()).collect();
        self
    }

    /// (chainable) Sets the current working directory of the process.
    pub fn cwd<T: AsRef<OsStr>>(&mut self, path: T) -> &mut ProcessBuilder {
        self.cwd = Some(path.as_ref().to_os_string());
        self
    }

    /// (chainable) Sets an environment variable for the process.
    pub fn env<T: AsRef<OsStr>>(&mut self, key: &str, val: T) -> &mut ProcessBuilder {
        self.env
            .insert(key.to_string(), Some(val.as_ref().to_os_string()));
        self
    }

    /// (chainable) Unsets an environment variable for the process.
    pub fn env_remove(&mut self, key: &str) -> &mut ProcessBuilder {
        self.env.insert(key.to_string(), None);
        self
    }

    /// Trust: clears an explicit set/unset operation for an environment
    /// variable.
    ///
    /// This differs from [`ProcessBuilder::env_remove`]: the child resumes
    /// inheriting the variable instead of receiving an unset operation. It is
    /// useful when replacing every case variant of a variable on platforms
    /// whose environment namespace is case-insensitive.
    pub fn env_clear_override(&mut self, key: &str) -> &mut ProcessBuilder {
        self.env.remove(key);
        self
    }

    /// Gets the executable name.
    pub fn get_program(&self) -> &OsString {
        self.wrappers.last().unwrap_or(&self.program)
    }

    /// Gets the program arg0.
    pub fn get_arg0(&self) -> Option<&OsStr> {
        self.arg0.as_deref()
    }

    /// Gets the program arguments.
    pub fn get_args(&self) -> impl Iterator<Item = &OsString> {
        self.wrappers
            .iter()
            .rev()
            .chain(once(&self.program))
            .chain(self.args.iter())
            .skip(1) // Skip the main `program
    }

    /// Gets the current working directory for the process.
    pub fn get_cwd(&self) -> Option<&Path> {
        self.cwd.as_ref().map(Path::new)
    }

    /// Gets an environment variable as the process will see it (will inherit from environment
    /// unless explicitly unset).
    pub fn get_env(&self, var: &str) -> Option<OsString> {
        self.env
            .get(var)
            .cloned()
            .or_else(|| Some(env::var_os(var)))
            .and_then(|s| s)
    }

    /// Gets all environment variables explicitly set or unset for the process (not inherited
    /// vars).
    pub fn get_envs(&self) -> &BTreeMap<String, Option<OsString>> {
        &self.env
    }

    /// Trust: returns the complete environment this builder will present to
    /// its child, including the jobserver overlay applied at spawn time.
    ///
    /// Unlike [`Self::get_envs`], this materializes inherited variables.
    /// Authenticating a child's environment requires the environment it will
    /// actually see, and upstream's view omits everything inherited — which is
    /// most of it.
    #[cfg(unix)]
    pub fn get_effective_envs(&self) -> io::Result<BTreeMap<OsString, OsString>> {
        let mut effective = BTreeMap::new();
        for (name, value) in env::vars_os() {
            if effective.insert(name, value).is_some() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "process environment contains a duplicate variable name",
                ));
            }
        }
        for (name, value) in &self.env {
            match value {
                Some(value) => {
                    effective.insert(name.into(), value.clone());
                }
                None => {
                    effective.remove(OsStr::new(name));
                }
            }
        }
        if let Some(jobserver) = &self.jobserver {
            // Trust: `Client::configure` is the authoritative source for the
            // spawn-time jobserver environment. Apply its overlay after the
            // builder's explicit environment, matching `build_command`, or this
            // view disagrees with the child's in exactly the variables that
            // grant it resources.
            let mut probe = Command::new("__cargo_effective_env_probe__");
            jobserver.configure(&mut probe);
            for (name, value) in probe.get_envs() {
                match value {
                    Some(value) => {
                        effective.insert(name.to_os_string(), value.to_os_string());
                    }
                    None => {
                        effective.remove(name);
                    }
                }
            }
        }
        Ok(effective)
    }

    /// Sets the `make` jobserver. See the [jobserver crate][jobserver_docs] for
    /// more information.
    ///
    /// [jobserver_docs]: https://docs.rs/jobserver/latest/jobserver/
    pub fn inherit_jobserver(&mut self, jobserver: &Client) -> &mut Self {
        self.jobserver = Some(jobserver.clone());
        self
    }

    /// Trust: remove inherited jobserver authority from a command that will be
    /// launched by a platform-specific authenticated executor instead of
    /// [`Command`].
    ///
    /// The normal spawn path arranges both the environment and descriptor
    /// inheritance inside `jobserver::Client::configure`. An authenticated
    /// executor that deliberately closes every non-stdio descriptor must not
    /// leave a `CARGO_MAKEFLAGS` capability string naming descriptors it did
    /// not transfer. Test binaries do not need build-scheduler authority.
    pub fn clear_jobserver(&mut self) -> &mut Self {
        self.jobserver = None;
        self
    }

    /// Enables environment variable display.
    pub fn display_env_vars(&mut self) -> &mut Self {
        self.display_env_vars = true;
        self
    }

    /// Enables retrying with an argfile if hitting "command line too big" error
    ///
    /// This is primarily for the `@path` arg of rustc and rustdoc, which treat
    /// each line as an command-line argument, so `LF` and `CRLF` bytes are not
    /// valid as an argument for argfile at this moment.
    /// For example, `RUSTDOCFLAGS="--crate-version foo\nbar" cargo doc` is
    /// valid when invoking from command-line but not from argfile.
    ///
    /// To sum up, the limitations of the argfile are:
    ///
    /// - Must be valid UTF-8 encoded.
    /// - Must not contain any newlines in each argument.
    ///
    /// Ref:
    ///
    /// - <https://doc.rust-lang.org/rustdoc/command-line-arguments.html#path-load-command-line-flags-from-a-path>
    /// - <https://doc.rust-lang.org/rustc/command-line-arguments.html#path-load-command-line-flags-from-a-path>
    pub fn retry_with_argfile(&mut self, enabled: bool) -> &mut Self {
        self.retry_with_argfile = enabled;
        self
    }

    /// Sets a value that will be written to stdin of the process on launch.
    pub fn stdin<T: Into<Vec<u8>>>(&mut self, stdin: T) -> &mut Self {
        self.stdin = Some(stdin.into());
        self
    }

    fn should_retry_with_argfile(&self, err: &io::Error) -> bool {
        self.retry_with_argfile && imp::command_line_too_big(err)
    }

    /// Like [`Command::status`] but with a better error message.
    pub fn status(&self) -> Result<ExitStatus> {
        self._status()
            .with_context(|| ProcessError::could_not_execute(self))
    }

    fn _status(&self) -> io::Result<ExitStatus> {
        if !debug_force_argfile(self.retry_with_argfile) {
            let mut cmd = self.build_command();
            match cmd.spawn() {
                Err(ref e) if self.should_retry_with_argfile(e) => {}
                Err(e) => return Err(e),
                Ok(mut child) => return child.wait(),
            }
        }
        let (mut cmd, argfile) = self.build_command_with_argfile()?;
        let status = cmd.spawn()?.wait();
        close_tempfile_and_log_error(argfile);
        status
    }

    /// Runs the process, waiting for completion, and mapping non-success exit codes to an error.
    pub fn exec(&self) -> Result<()> {
        let exit = self.status()?;
        if exit.success() {
            Ok(())
        } else {
            Err(ProcessError::new(
                &format!("process didn't exit successfully: {}", self),
                Some(exit),
                None,
            )
            .into())
        }
    }

    /// Replaces the current process with the target process.
    ///
    /// On Unix, this executes the process using the Unix syscall `execvp`, which will block
    /// this process, and will only return if there is an error.
    ///
    /// On Windows this isn't technically possible. Instead we emulate it to the best of our
    /// ability. One aspect we fix here is that we specify a handler for the Ctrl-C handler.
    /// In doing so (and by effectively ignoring it) we should emulate proxying Ctrl-C
    /// handling to the application at hand, which will either terminate or handle it itself.
    /// According to Microsoft's documentation at
    /// <https://docs.microsoft.com/en-us/windows/console/ctrl-c-and-ctrl-break-signals>.
    /// the Ctrl-C signal is sent to all processes attached to a terminal, which should
    /// include our child process. If the child terminates then we'll reap them in Cargo
    /// pretty quickly, and if the child handles the signal then we won't terminate
    /// (and we shouldn't!) until the process itself later exits.
    pub fn exec_replace(&self) -> Result<()> {
        imp::exec_replace(self)
    }

    /// Runs the target while retaining this process as a transparent Linux
    /// supervisor.
    ///
    /// This is for callers that own in-process state which must outlive the
    /// launched program and therefore cannot use [`Self::exec_replace`].
    /// Common process-control and termination signals are forwarded through a
    /// pidfd, and this process exits with the child's exact numeric status or
    /// terminating signal. Only spawn or supervision setup failures return.
    #[cfg(target_os = "linux")]
    pub fn exec_replace_supervised(&self) -> Result<()> {
        imp::exec_replace_supervised(self)
    }

    /// Like [`Command::output`] but with a better error message.
    pub fn output(&self) -> Result<Output> {
        self._output()
            .with_context(|| ProcessError::could_not_execute(self))
    }

    fn _output(&self) -> io::Result<Output> {
        if !debug_force_argfile(self.retry_with_argfile) {
            let mut cmd = self.build_command();
            match piped(&mut cmd, self.stdin.is_some()).spawn() {
                Err(ref e) if self.should_retry_with_argfile(e) => {}
                Err(e) => return Err(e),
                Ok(mut child) => {
                    if let Some(stdin) = &self.stdin {
                        child.stdin.take().unwrap().write_all(stdin)?;
                    }
                    return child.wait_with_output();
                }
            }
        }
        let (mut cmd, argfile) = self.build_command_with_argfile()?;
        let mut child = piped(&mut cmd, self.stdin.is_some()).spawn()?;
        if let Some(stdin) = &self.stdin {
            child.stdin.take().unwrap().write_all(stdin)?;
        }
        let output = child.wait_with_output();
        close_tempfile_and_log_error(argfile);
        output
    }

    /// Executes the process, returning the stdio output, or an error if non-zero exit status.
    pub fn exec_with_output(&self) -> Result<Output> {
        let output = self.output()?;
        if output.status.success() {
            Ok(output)
        } else {
            Err(ProcessError::new(
                &format!("process didn't exit successfully: {}", self),
                Some(output.status),
                Some(&output),
            )
            .into())
        }
    }

    /// Executes a command, passing each line of stdout and stderr to the supplied callbacks, which
    /// can mutate the string data.
    ///
    /// If any invocations of these function return an error, it will be propagated.
    ///
    /// If `capture_output` is true, then all the output will also be buffered
    /// and stored in the returned `Output` object. If it is false, no caching
    /// is done, and the callbacks are solely responsible for handling the
    /// output.
    pub fn exec_with_streaming(
        &self,
        on_stdout_line: &mut dyn FnMut(&str) -> Result<()>,
        on_stderr_line: &mut dyn FnMut(&str) -> Result<()>,
        capture_output: bool,
    ) -> Result<Output> {
        self.exec_with_streaming_impl(on_stdout_line, on_stderr_line, capture_output, None)
    }

    /// Trust: executes a command with finite per-line and per-stream output
    /// budgets, and does not outlive the output it has already rejected.
    ///
    /// Unlike [`ProcessBuilder::exec_with_streaming`], this creates an isolated
    /// child process group on Unix. A callback rejection, read failure, limit
    /// violation, or configured timeout stops both pipe readers immediately,
    /// terminates the group, and reaps the direct child before returning. This
    /// prevents an untrusted child (or a descendant holding one of its pipes
    /// open) from retaining Cargo's lifetime after its output has already been
    /// rejected.
    pub fn exec_with_streaming_limits(
        &self,
        on_stdout_line: &mut dyn FnMut(&str) -> Result<()>,
        on_stderr_line: &mut dyn FnMut(&str) -> Result<()>,
        capture_output: bool,
        limits: StreamingOutputLimits,
    ) -> Result<Output> {
        limits.validate()?;
        self.exec_with_streaming_impl(on_stdout_line, on_stderr_line, capture_output, Some(limits))
    }

    fn exec_with_streaming_impl(
        &self,
        on_stdout_line: &mut dyn FnMut(&str) -> Result<()>,
        on_stderr_line: &mut dyn FnMut(&str) -> Result<()>,
        capture_output: bool,
        limits: Option<StreamingOutputLimits>,
    ) -> Result<Output> {
        let deadline = limits
            .and_then(|limits| limits.timeout)
            .map(|timeout| {
                Instant::now().checked_add(timeout).ok_or_else(|| {
                    anyhow!(
                        "streaming process timeout cannot be represented by the monotonic clock"
                    )
                })
            })
            .transpose()?;

        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let mut callback_error = None;
        let mut stdout_pos = 0;
        let mut stderr_pos = 0;
        let mut stdout_bytes = 0_usize;
        let mut stderr_bytes = 0_usize;

        let spawn = |mut cmd| {
            configure_streaming_child(&mut cmd, limits.is_some());
            if !debug_force_argfile(self.retry_with_argfile) {
                match piped(&mut cmd, false).spawn() {
                    Err(ref e) if self.should_retry_with_argfile(e) => {}
                    Err(e) => return Err(e),
                    Ok(child) => return Ok((child, None)),
                }
            }
            let (mut cmd, argfile) = self.build_command_with_argfile()?;
            configure_streaming_child(&mut cmd, limits.is_some());
            Ok((piped(&mut cmd, false).spawn()?, Some(argfile)))
        };

        let status = (|| {
            let cmd = self.build_command();
            let (mut child, argfile) = spawn(cmd)?;
            let out = child.stdout.take().unwrap();
            let err = child.stderr.take().unwrap();
            let read_result = read2_interruptible(out, err, deadline, &mut |is_out, data, eof| {
                if callback_error.is_some() {
                    return Read2Action::Stop;
                }

                let pos = if is_out {
                    &mut stdout_pos
                } else {
                    &mut stderr_pos
                };
                let stream_bytes = if is_out {
                    &mut stdout_bytes
                } else {
                    &mut stderr_bytes
                };
                let stream_name = if is_out { "stdout" } else { "stderr" };

                let Some(new_bytes) = data.len().checked_sub(*pos) else {
                    callback_error = Some(anyhow!(
                        "internal streaming {stream_name} buffer position moved past its data"
                    ));
                    return Read2Action::Stop;
                };
                if let Some(limits) = limits {
                    let Some(total) = stream_bytes.checked_add(new_bytes) else {
                        callback_error = Some(anyhow!(
                            "streaming {stream_name} byte count overflowed its aggregate safety limit"
                        ));
                        return Read2Action::Stop;
                    };
                    if total > limits.max_stream_bytes {
                        callback_error = Some(anyhow!(
                            "streaming {stream_name} exceeds the {}-byte aggregate safety limit",
                            limits.max_stream_bytes
                        ));
                        return Read2Action::Stop;
                    }
                    *stream_bytes = total;
                }

                let idx = if eof {
                    data.len()
                } else {
                    match data[*pos..].iter().rposition(|b| *b == b'\n') {
                        Some(i) => *pos + i + 1,
                        None => {
                            *pos = data.len();
                            if let Some(limits) = limits
                                && data.len() > limits.max_line_bytes
                            {
                                callback_error = Some(anyhow!(
                                    "streaming {stream_name} line exceeds the {}-byte safety limit",
                                    limits.max_line_bytes
                                ));
                                return Read2Action::Stop;
                            }
                            return Read2Action::Continue;
                        }
                    }
                };

                let new_lines = &data[..idx];
                if let Some(limits) = limits
                    && let Some(line_bytes) = oversized_line_bytes(new_lines, limits.max_line_bytes)
                {
                    callback_error = Some(anyhow!(
                        "streaming {stream_name} line contains {line_bytes} bytes, exceeding the {}-byte safety limit",
                        limits.max_line_bytes
                    ));
                    return Read2Action::Stop;
                }
                if let Some(limits) = limits
                    && data.len() - idx > limits.max_line_bytes
                {
                    callback_error = Some(anyhow!(
                        "streaming {stream_name} line exceeds the {}-byte safety limit",
                        limits.max_line_bytes
                    ));
                    return Read2Action::Stop;
                }

                for line in String::from_utf8_lossy(new_lines).lines() {
                    let callback_result = if is_out {
                        on_stdout_line(line)
                    } else {
                        on_stderr_line(line)
                    };
                    if let Err(e) = callback_result {
                        callback_error = Some(e);
                        return Read2Action::Stop;
                    }
                }

                if capture_output {
                    let dst = if is_out { &mut stdout } else { &mut stderr };
                    if limits.is_some()
                        && let Err(error) = dst.try_reserve_exact(new_lines.len())
                    {
                        callback_error = Some(anyhow!(
                            "could not retain bounded streaming {stream_name}: {error}"
                        ));
                        return Read2Action::Stop;
                    }
                    dst.extend(new_lines);
                }

                data.drain(..idx);
                // Trust: `stream_bytes` already includes every byte currently
                // in `data`, including an unterminated tail retained for the next
                // callback. Keep the cursor at the retained length after the
                // completed prefix is drained so that the next read counts
                // only newly appended bytes.
                *pos = data.len();
                Read2Action::Continue
            });

            let status = match read_result {
                Ok(Read2Action::Continue) => {
                    wait_for_streaming_child(&mut child, deadline, limits.is_some())
                        .map_err(anyhow::Error::from)
                }
                Ok(Read2Action::Stop) => terminate_and_reap(&mut child, limits.is_some())
                    .map_err(anyhow::Error::from)
                    .with_context(|| {
                        let rejection = callback_error
                            .as_ref()
                            .map(ToString::to_string)
                            .unwrap_or_else(|| "stream reader interruption".to_string());
                        format!("failed to terminate child after rejecting output: {rejection}")
                    }),
                Err(read_error) => terminate_and_reap(&mut child, limits.is_some())
                    .map_err(anyhow::Error::from)
                    .with_context(|| {
                        format!(
                            "failed to terminate child after streaming read failed: {read_error}"
                        )
                    })
                    .and_then(|_| Err(read_error.into())),
            };
            if let Some(argfile) = argfile {
                close_tempfile_and_log_error(argfile);
            }
            status
        })()
        .with_context(|| ProcessError::could_not_execute(self))?;
        let output = Output {
            status,
            stdout,
            stderr,
        };

        {
            let to_print = if capture_output { Some(&output) } else { None };
            if let Some(e) = callback_error {
                let cx = ProcessError::new(
                    &format!("failed to parse process output: {}", self),
                    Some(output.status),
                    to_print,
                );
                bail!(anyhow::Error::new(cx).context(e));
            } else if !output.status.success() {
                bail!(ProcessError::new(
                    &format!("process didn't exit successfully: {}", self),
                    Some(output.status),
                    to_print,
                ));
            }
        }

        Ok(output)
    }

    /// Builds the command with an `@<path>` argfile that contains all the
    /// arguments. This is primarily served for rustc/rustdoc command family.
    fn build_command_with_argfile(&self) -> io::Result<(Command, NamedTempFile)> {
        use std::io::Write as _;

        let mut tmp = tempfile::Builder::new()
            .prefix("cargo-argfile.")
            .tempfile()?;

        let mut arg = OsString::from("@");
        arg.push(tmp.path());
        let mut cmd = self.build_command_without_args();
        cmd.arg(arg);
        tracing::debug!("created argfile at {} for {self}", tmp.path().display());

        let cap = self.get_args().map(|arg| arg.len() + 1).sum::<usize>();
        let mut buf = Vec::with_capacity(cap);
        for arg in &self.args {
            let arg = arg.to_str().ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::Other,
                    format!(
                        "argument for argfile contains invalid UTF-8 characters: `{}`",
                        arg.to_string_lossy()
                    ),
                )
            })?;
            if arg.contains('\n') {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!("argument for argfile contains newlines: `{arg}`"),
                ));
            }
            writeln!(buf, "{arg}")?;
        }
        tmp.write_all(&mut buf)?;
        Ok((cmd, tmp))
    }

    /// Builds a command from `ProcessBuilder` for everything but not `args`.
    fn build_command_without_args(&self) -> Command {
        let mut command = {
            let mut iter = self.wrappers.iter().rev().chain(once(&self.program));
            let mut cmd = Command::new(iter.next().expect("at least one `program` exists"));
            cmd.args(iter);
            cmd
        };
        #[cfg(unix)]
        if let Some(arg0) = self.get_arg0() {
            use std::os::unix::process::CommandExt as _;
            command.arg0(arg0);
        }
        #[cfg(unix)]
        // Trust: the only moment a per-child descriptor can be granted is
        // between fork and exec — before it, the parent would be handing the
        // capability to every future child; after it, the child is already
        // running.
        if !self.inherited_fds.is_empty() || !self.exec_guard_fds.is_empty() {
            use std::os::unix::process::CommandExt as _;

            let inherited_fds = self.inherited_fds.clone();
            let exec_guard_fds = self.exec_guard_fds.clone();
            unsafe {
                command.pre_exec(move || {
                    // Trust: capturing the guard descriptors in the command
                    // keeps the parent-side capability endpoints live through fork. They
                    // retain CLOEXEC and therefore disappear from the child
                    // image. Do not otherwise touch them in the post-fork path.
                    let _ = &exec_guard_fds;
                    for fd in &inherited_fds {
                        let fd = fd.as_raw_fd();
                        let flags = libc::fcntl(fd, libc::F_GETFD);
                        if flags < 0 {
                            return Err(io::Error::last_os_error());
                        }
                        if libc::fcntl(fd, libc::F_SETFD, flags & !libc::FD_CLOEXEC) < 0 {
                            return Err(io::Error::last_os_error());
                        }
                    }
                    Ok(())
                });
            }
        }
        if let Some(cwd) = self.get_cwd() {
            command.current_dir(cwd);
        }
        for (k, v) in &self.env {
            match *v {
                Some(ref v) => {
                    command.env(k, v);
                }
                None => {
                    command.env_remove(k);
                }
            }
        }
        if let Some(ref c) = self.jobserver {
            c.configure(&mut command);
        }
        command
    }

    /// Converts `ProcessBuilder` into a `std::process::Command`, and handles
    /// the jobserver, if present.
    ///
    /// Note that this method doesn't take argfile fallback into account. The
    /// caller should handle it by themselves.
    pub fn build_command(&self) -> Command {
        let mut command = self.build_command_without_args();
        for arg in &self.args {
            command.arg(arg);
        }
        command
    }

    /// Wraps an existing command with the provided wrapper, if it is present and valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use cargo_util::ProcessBuilder;
    /// // Running this would execute `rustc`
    /// let cmd = ProcessBuilder::new("rustc");
    ///
    /// // Running this will execute `sccache rustc`
    /// let cmd = cmd.wrapped(Some("sccache"));
    /// ```
    pub fn wrapped(mut self, wrapper: Option<impl AsRef<OsStr>>) -> Self {
        if let Some(wrapper) = wrapper.as_ref() {
            let wrapper = wrapper.as_ref();
            if !wrapper.is_empty() {
                self.wrappers.push(wrapper.to_os_string());
            }
        }
        self
    }
}

fn oversized_line_bytes(bytes: &[u8], max_line_bytes: usize) -> Option<usize> {
    let mut line_start = 0;
    for (index, byte) in bytes.iter().enumerate() {
        if *byte == b'\n' {
            let line_bytes = index - line_start;
            if line_bytes > max_line_bytes {
                return Some(line_bytes);
            }
            line_start = index + 1;
        }
    }
    let trailing_bytes = bytes.len() - line_start;
    (trailing_bytes > max_line_bytes).then_some(trailing_bytes)
}

/// Trust: an isolated process group is what makes a rejection enforceable — a
/// child that spawned descendants holding its pipes cannot otherwise be stopped
/// without also killing unrelated work.
fn configure_streaming_child(command: &mut Command, isolated_process_group: bool) {
    #[cfg(unix)]
    if isolated_process_group {
        use std::os::unix::process::CommandExt as _;
        command.process_group(0);
    }

    #[cfg(not(unix))]
    let _ = (command, isolated_process_group);
}

fn terminate_and_reap(child: &mut Child, isolated_process_group: bool) -> io::Result<ExitStatus> {
    let mut termination_error = None;

    #[cfg(not(unix))]
    let _ = isolated_process_group;

    #[cfg(unix)]
    if isolated_process_group {
        let child_pid = libc::c_int::try_from(child.id()).map_err(|_| {
            io::Error::other(format!("child pid {} does not fit in c_int", child.id()))
        })?;
        // The bounded streaming path creates the child as its own process-group
        // leader, so a negative PID reaches descendants that inherited either
        // output pipe. The unreaped leader keeps this PID from being reused
        // during the signal operation.
        if unsafe { libc::kill(-child_pid, libc::SIGKILL) } == -1 {
            let error = io::Error::last_os_error();
            if error.raw_os_error() != Some(libc::ESRCH) {
                termination_error = Some(error);
            }
        }
    }

    if let Err(error) = child.kill()
        && error.kind() != io::ErrorKind::InvalidInput
        && error.raw_os_error() != Some(libc_esrch())
        && termination_error.is_none()
    {
        termination_error = Some(error);
    }

    let status = child.wait()?;
    if let Some(error) = termination_error {
        return Err(error);
    }
    Ok(status)
}

fn wait_for_streaming_child(
    child: &mut Child,
    deadline: Option<Instant>,
    isolated_process_group: bool,
) -> io::Result<ExitStatus> {
    let Some(deadline) = deadline else {
        return child.wait();
    };

    loop {
        if let Some(status) = child.try_wait()? {
            if Instant::now() < deadline {
                return Ok(status);
            }
            let timeout = io::Error::new(
                io::ErrorKind::TimedOut,
                "streaming process exceeded its wall-clock timeout",
            );
            return match terminate_and_reap(child, isolated_process_group) {
                Ok(_) => Err(timeout),
                Err(cleanup) => Err(io::Error::other(format!(
                    "{timeout}; additionally failed to clean up timed-out process group: {cleanup}"
                ))),
            };
        }
        let Some(remaining) = deadline.checked_duration_since(Instant::now()) else {
            let timeout = io::Error::new(
                io::ErrorKind::TimedOut,
                "streaming process exceeded its wall-clock timeout",
            );
            return match terminate_and_reap(child, isolated_process_group) {
                Ok(_) => Err(timeout),
                Err(cleanup) => Err(io::Error::other(format!(
                    "{timeout}; additionally failed to terminate timed-out child: {cleanup}"
                ))),
            };
        };
        std::thread::sleep(remaining.min(Duration::from_millis(10)));
    }
}

#[cfg(unix)]
const fn libc_esrch() -> i32 {
    libc::ESRCH
}

#[cfg(not(unix))]
const fn libc_esrch() -> i32 {
    // Windows does not expose an errno-style ESRCH through Child::kill.
    i32::MIN
}

/// Forces the command to use `@path` argfile.
///
/// You should set `__CARGO_TEST_FORCE_ARGFILE` to enable this.
fn debug_force_argfile(retry_enabled: bool) -> bool {
    cfg!(debug_assertions) && env::var("__CARGO_TEST_FORCE_ARGFILE").is_ok() && retry_enabled
}

/// Creates new pipes for stderr, stdout, and optionally stdin.
fn piped(cmd: &mut Command, pipe_stdin: bool) -> &mut Command {
    cmd.stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .stdin(if pipe_stdin {
            Stdio::piped()
        } else {
            Stdio::null()
        })
}

fn close_tempfile_and_log_error(file: NamedTempFile) {
    file.close().unwrap_or_else(|e| {
        tracing::warn!("failed to close temporary file: {e}");
    });
}

#[cfg(unix)]
mod imp {
    use super::{ProcessBuilder, ProcessError, close_tempfile_and_log_error, debug_force_argfile};
    #[cfg(target_os = "linux")]
    use anyhow::Context as _;
    use anyhow::Result;
    use std::io;
    #[cfg(target_os = "linux")]
    use std::mem::MaybeUninit;
    #[cfg(target_os = "linux")]
    use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
    use std::os::unix::process::CommandExt;
    #[cfg(target_os = "linux")]
    use std::os::unix::process::ExitStatusExt as _;
    #[cfg(target_os = "linux")]
    use std::process::{Child, Command, ExitStatus};
    #[cfg(target_os = "linux")]
    use std::sync::atomic::{AtomicBool, AtomicI32, AtomicU32, Ordering};

    #[cfg(target_os = "linux")]
    const FORWARDED_SIGNALS: &[libc::c_int] = &[
        libc::SIGHUP,
        libc::SIGINT,
        libc::SIGQUIT,
        libc::SIGUSR1,
        libc::SIGUSR2,
        libc::SIGALRM,
        libc::SIGTERM,
    ];
    #[cfg(target_os = "linux")]
    static SUPERVISED_EXEC_ACTIVE: AtomicBool = AtomicBool::new(false);
    #[cfg(target_os = "linux")]
    static SUPERVISED_CHILD_PIDFD: AtomicI32 = AtomicI32::new(-1);
    #[cfg(target_os = "linux")]
    static PENDING_SUPERVISED_SIGNALS: AtomicU32 = AtomicU32::new(0);

    #[cfg(target_os = "linux")]
    const fn supervised_signal_bit(signal: libc::c_int) -> u32 {
        if signal > 0 && signal < u32::BITS as libc::c_int {
            1_u32 << signal
        } else {
            0
        }
    }

    #[cfg(target_os = "linux")]
    unsafe extern "C" fn forward_supervised_exec_signal(signal: libc::c_int) {
        let bit = supervised_signal_bit(signal);
        if bit == 0 {
            return;
        }
        PENDING_SUPERVISED_SIGNALS.fetch_or(bit, Ordering::SeqCst);
        let pidfd = SUPERVISED_CHILD_PIDFD.load(Ordering::SeqCst);
        if pidfd >= 0 && PENDING_SUPERVISED_SIGNALS.fetch_and(!bit, Ordering::SeqCst) & bit != 0 {
            // SAFETY: the signal handler performs only lock-free atomics, raw
            // TLS errno access, and one raw system call; it restores errno
            // before returning. Once published, the descriptor remains open
            // through process exit (and is deliberately leaked on a returnable
            // error) so an already-running handler cannot observe fd reuse.
            unsafe {
                let saved_errno = *libc::__errno_location();
                libc::syscall(
                    libc::SYS_pidfd_send_signal,
                    pidfd,
                    signal,
                    std::ptr::null::<libc::siginfo_t>(),
                    0_u32,
                );
                *libc::__errno_location() = saved_errno;
            }
        }
    }

    #[cfg(target_os = "linux")]
    struct SupervisedSignalHandlers {
        previous: Vec<(libc::c_int, libc::sigaction)>,
        child_pidfd: Option<OwnedFd>,
        restored: bool,
    }

    #[cfg(target_os = "linux")]
    impl SupervisedSignalHandlers {
        fn install() -> io::Result<Self> {
            if SUPERVISED_EXEC_ACTIVE
                .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
                .is_err()
            {
                return Err(io::Error::other(
                    "a supervised exec replacement is already active",
                ));
            }
            SUPERVISED_CHILD_PIDFD.store(-1, Ordering::SeqCst);
            PENDING_SUPERVISED_SIGNALS.store(0, Ordering::SeqCst);

            let mut handlers = Self {
                previous: Vec::with_capacity(FORWARDED_SIGNALS.len()),
                child_pidfd: None,
                restored: false,
            };
            for &signal in FORWARDED_SIGNALS {
                // SAFETY: zero is a valid initial representation for sigaction;
                // sigemptyset initializes its mask before installation.
                let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
                action.sa_sigaction = forward_supervised_exec_signal as *const () as usize;
                action.sa_flags = libc::SA_RESTART;
                // SAFETY: action owns a valid sigset_t output buffer.
                if unsafe { libc::sigemptyset(&mut action.sa_mask) } != 0 {
                    let error = io::Error::last_os_error();
                    handlers.restore_best_effort();
                    return Err(error);
                }
                let mut previous = MaybeUninit::<libc::sigaction>::uninit();
                // SAFETY: both pointers name correctly sized sigaction
                // structures for this process.
                if unsafe { libc::sigaction(signal, &action, previous.as_mut_ptr()) } != 0 {
                    let error = io::Error::last_os_error();
                    handlers.restore_best_effort();
                    return Err(error);
                }
                // SAFETY: successful sigaction initialized the old action.
                handlers
                    .previous
                    .push((signal, unsafe { previous.assume_init() }));
            }
            Ok(handlers)
        }

        fn publish_child(&mut self, pidfd: OwnedFd) {
            let descriptor = pidfd.as_raw_fd();
            self.child_pidfd = Some(pidfd);
            SUPERVISED_CHILD_PIDFD.store(descriptor, Ordering::SeqCst);
            let pending = PENDING_SUPERVISED_SIGNALS.swap(0, Ordering::SeqCst);
            for &signal in FORWARDED_SIGNALS {
                if pending & supervised_signal_bit(signal) != 0 {
                    // SAFETY: pidfd remains owned by the caller throughout
                    // supervision, and pidfd_send_signal binds delivery to the
                    // captured child rather than a reusable numeric PID.
                    unsafe {
                        libc::syscall(
                            libc::SYS_pidfd_send_signal,
                            descriptor,
                            signal,
                            std::ptr::null::<libc::siginfo_t>(),
                            0_u32,
                        );
                    }
                }
            }
        }

        fn child_ignored_signals(&self) -> u32 {
            self.previous
                .iter()
                .filter(|(_, action)| action.sa_sigaction == libc::SIG_IGN)
                .fold(0, |signals, (signal, _)| {
                    signals | supervised_signal_bit(*signal)
                })
        }

        fn restore(&mut self) -> io::Result<()> {
            if self.restored {
                return Ok(());
            }
            let mut first_error = None;
            for (signal, action) in self.previous.iter().rev() {
                // SAFETY: action is the exact initialized disposition returned
                // by the matching successful sigaction installation.
                if unsafe { libc::sigaction(*signal, action, std::ptr::null_mut()) } != 0
                    && first_error.is_none()
                {
                    first_error = Some(io::Error::last_os_error());
                }
            }
            self.restored = true;
            SUPERVISED_CHILD_PIDFD.store(-1, Ordering::SeqCst);
            SUPERVISED_EXEC_ACTIVE.store(false, Ordering::SeqCst);
            if let Some(error) = first_error {
                Err(error)
            } else {
                Ok(())
            }
        }

        fn restore_best_effort(&mut self) {
            let _ = self.restore();
        }
    }

    #[cfg(target_os = "linux")]
    impl Drop for SupervisedSignalHandlers {
        fn drop(&mut self) {
            self.restore_best_effort();
            if let Some(pidfd) = self.child_pidfd.take() {
                // A signal handler which loaded this raw descriptor before
                // restoration may still be running on another thread. There
                // is no async-signal-safe join protocol here, so preserving the
                // process-bound pidfd until process exit is safer than closing
                // it into the descriptor-reuse race.
                std::mem::forget(pidfd);
            }
        }
    }

    #[cfg(target_os = "linux")]
    fn prepare_supervised_child(
        command: &mut Command,
        parent_pid: libc::pid_t,
        ignored_signals: u32,
    ) {
        // SAFETY: after fork the callback performs only async-signal-safe raw
        // syscalls, reads copied integers/static data, and constructs an
        // io::Error from thread-local errno if setup fails.
        unsafe {
            command.pre_exec(move || {
                // PR_SET_PDEATHSIG prevents an abrupt parent death, including
                // uncatchable SIGKILL, from orphaning the launched program.
                // Rechecking getppid after prctl closes the race in which the
                // parent died just before setup. SIGSTOP does not kill the
                // parent and is intentionally left to ordinary process-group
                // job control rather than claimed as a closed death gap.
                if libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL) != 0 {
                    return Err(io::Error::last_os_error());
                }
                if libc::getppid() != parent_pid {
                    libc::_exit(128 + libc::SIGKILL);
                }
                for &signal in FORWARDED_SIGNALS {
                    let mut action: libc::sigaction = std::mem::zeroed();
                    action.sa_sigaction = if ignored_signals & supervised_signal_bit(signal) != 0 {
                        libc::SIG_IGN
                    } else {
                        libc::SIG_DFL
                    };
                    if libc::sigemptyset(&mut action.sa_mask) != 0
                        || libc::sigaction(signal, &action, std::ptr::null_mut()) != 0
                    {
                        return Err(io::Error::last_os_error());
                    }
                }
                Ok(())
            });
        }
    }

    #[cfg(target_os = "linux")]
    fn open_child_pidfd(child: &Child) -> io::Result<OwnedFd> {
        let pid = libc::pid_t::try_from(child.id())
            .map_err(|_| io::Error::other("child pid does not fit Linux pid_t"))?;
        // SAFETY: pidfd_open takes the copied PID and zero flags. The returned
        // descriptor is checked before ownership is constructed.
        let descriptor = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0_u32) };
        if descriptor < 0 {
            return Err(io::Error::last_os_error());
        }
        let descriptor = libc::c_int::try_from(descriptor)
            .map_err(|_| io::Error::other("pidfd descriptor does not fit c_int"))?;
        // SAFETY: successful pidfd_open returned one new owned descriptor.
        Ok(unsafe { OwnedFd::from_raw_fd(descriptor) })
    }

    #[cfg(target_os = "linux")]
    fn spawn_supervised(
        process_builder: &ProcessBuilder,
        parent_pid: libc::pid_t,
        ignored_signals: u32,
    ) -> io::Result<(Child, Option<tempfile::NamedTempFile>)> {
        if debug_force_argfile(process_builder.retry_with_argfile) {
            let (mut command, argfile) = process_builder.build_command_with_argfile()?;
            prepare_supervised_child(&mut command, parent_pid, ignored_signals);
            return command.spawn().map(|child| (child, Some(argfile)));
        }

        let mut command = process_builder.build_command();
        prepare_supervised_child(&mut command, parent_pid, ignored_signals);
        match command.spawn() {
            Ok(child) => Ok((child, None)),
            Err(error) if process_builder.should_retry_with_argfile(&error) => {
                let (mut command, argfile) = process_builder.build_command_with_argfile()?;
                prepare_supervised_child(&mut command, parent_pid, ignored_signals);
                command.spawn().map(|child| (child, Some(argfile)))
            }
            Err(error) => Err(error),
        }
    }

    #[cfg(target_os = "linux")]
    fn exit_like_supervised_child(status: ExitStatus) -> ! {
        if let Some(code) = status.code() {
            std::process::exit(code);
        }
        if let Some(signal) = status.signal() {
            // SAFETY: this process is deliberately recreating exec-replacement
            // semantics. Defaulting, unblocking, and delivering the child's
            // terminating signal makes observers see the same wait status.
            unsafe {
                let mut action: libc::sigaction = std::mem::zeroed();
                action.sa_sigaction = libc::SIG_DFL;
                libc::sigemptyset(&mut action.sa_mask);
                libc::sigaction(signal, &action, std::ptr::null_mut());
                let mut mask: libc::sigset_t = std::mem::zeroed();
                libc::sigemptyset(&mut mask);
                libc::sigaddset(&mut mask, signal);
                libc::pthread_sigmask(libc::SIG_UNBLOCK, &mask, std::ptr::null_mut());
                libc::kill(libc::getpid(), signal);
                libc::_exit(128 + signal);
            }
        }
        std::process::exit(101);
    }

    pub fn exec_replace(process_builder: &ProcessBuilder) -> Result<()> {
        let mut error;
        let mut file = None;
        if debug_force_argfile(process_builder.retry_with_argfile) {
            let (mut command, argfile) = process_builder.build_command_with_argfile()?;
            file = Some(argfile);
            error = command.exec()
        } else {
            let mut command = process_builder.build_command();
            error = command.exec();
            if process_builder.should_retry_with_argfile(&error) {
                let (mut command, argfile) = process_builder.build_command_with_argfile()?;
                file = Some(argfile);
                error = command.exec()
            }
        }
        if let Some(file) = file {
            close_tempfile_and_log_error(file);
        }

        Err(anyhow::Error::from(error).context(ProcessError::new(
            &format!("could not execute process {}", process_builder),
            None,
            None,
        )))
    }

    #[cfg(target_os = "linux")]
    pub fn exec_replace_supervised(process_builder: &ProcessBuilder) -> Result<()> {
        let mut handlers = SupervisedSignalHandlers::install()
            .map_err(anyhow::Error::from)
            .context("failed to install supervised exec signal forwarding")?;
        let parent_pid = libc::pid_t::try_from(std::process::id())
            .map_err(|_| anyhow::anyhow!("supervisor pid does not fit Linux pid_t"))?;
        let ignored_signals = handlers.child_ignored_signals();
        let (mut child, argfile) = spawn_supervised(process_builder, parent_pid, ignored_signals)
            .map_err(|error| {
            anyhow::Error::from(error).context(ProcessError::new(
                &format!("could not execute process {}", process_builder),
                None,
                None,
            ))
        })?;
        let pidfd = match open_child_pidfd(&child) {
            Ok(pidfd) => pidfd,
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(anyhow::Error::from(error)
                    .context("failed to bind supervised exec replacement to a Linux pidfd"));
            }
        };
        handlers.publish_child(pidfd);
        let status = match child.wait() {
            Ok(status) => status,
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                let restore = handlers
                    .restore()
                    .context("failed to restore signal dispositions after wait failure");
                std::mem::forget(handlers);
                restore?;
                return Err(anyhow::Error::from(error).context(ProcessError::new(
                    &format!("could not wait for process {}", process_builder),
                    None,
                    None,
                )));
            }
        };
        if let Some(argfile) = argfile {
            close_tempfile_and_log_error(argfile);
        }
        // Keep the handlers and pidfd live through the non-returning status
        // recreation below. Restoring dispositions cannot synchronize with a
        // handler already running on the broker thread, while process exit
        // itself closes every descriptor without any reuse window.
        std::mem::forget(handlers);
        exit_like_supervised_child(status)
    }

    pub fn command_line_too_big(err: &io::Error) -> bool {
        err.raw_os_error() == Some(libc::E2BIG)
    }
}

#[cfg(windows)]
mod imp {
    use super::{ProcessBuilder, ProcessError};
    use anyhow::Result;
    use std::io;
    use windows_sys::Win32::Foundation::{FALSE, TRUE};
    use windows_sys::Win32::System::Console::SetConsoleCtrlHandler;
    use windows_sys::core::BOOL;

    unsafe extern "system" fn ctrlc_handler(_: u32) -> BOOL {
        // Do nothing; let the child process handle it.
        TRUE
    }

    pub fn exec_replace(process_builder: &ProcessBuilder) -> Result<()> {
        unsafe {
            if SetConsoleCtrlHandler(Some(ctrlc_handler), TRUE) == FALSE {
                return Err(ProcessError::new("Could not set Ctrl-C handler.", None, None).into());
            }
        }

        // Just execute the process as normal.
        process_builder.exec()
    }

    pub fn command_line_too_big(err: &io::Error) -> bool {
        use windows_sys::Win32::Foundation::ERROR_FILENAME_EXCED_RANGE;
        err.raw_os_error() == Some(ERROR_FILENAME_EXCED_RANGE as i32)
    }
}

// Trust: pins the bounded-streaming and descriptor-scoping behavior above.
// These spawn real children because the properties under test — a limit
// stopping an unbounded writer, a timeout reaping a wedged process group, a
// descriptor being absent from the child image — only exist at the process
// boundary.
#[cfg(test)]
mod tests {
    use super::{ProcessBuilder, StreamingOutputLimits};
    use anyhow::bail;
    use std::fs;
    use std::io::{self, Write as _};
    use std::process::{Command, Stdio};
    use std::thread;
    use std::time::{Duration, Instant};

    const STREAMING_CHILD_ROLE: &str = "__CARGO_UTIL_STREAMING_CHILD_ROLE";
    const STREAMING_CHILD_MARKER: &str = "__CARGO_UTIL_STREAMING_CHILD_MARKER";
    #[cfg(unix)]
    const INHERITED_FD_TEST_ENV: &str = "__CARGO_UTIL_INHERITED_FD_TEST";

    fn streaming_child_command(role: &str) -> ProcessBuilder {
        let mut cmd = ProcessBuilder::new(std::env::current_exe().unwrap());
        cmd.args(&[
            "--exact",
            "process_builder::tests::streaming_child_helper",
            "--nocapture",
        ])
        .env(STREAMING_CHILD_ROLE, role);
        cmd
    }

    fn small_streaming_limits() -> StreamingOutputLimits {
        StreamingOutputLimits::new(1024, 16 * 1024)
    }

    fn assert_fast_failure(started: Instant) {
        assert!(
            started.elapsed() < Duration::from_secs(5),
            "bounded streaming rejection did not terminate the child promptly: {:?}",
            started.elapsed()
        );
    }

    #[test]
    fn streaming_child_helper() {
        let Ok(role) = std::env::var(STREAMING_CHILD_ROLE) else {
            return;
        };
        match role.as_str() {
            #[cfg(unix)]
            "inherited-fd-open" | "inherited-fd-closed" => {
                let fd = std::env::var(INHERITED_FD_TEST_ENV)
                    .unwrap()
                    .parse::<libc::c_int>()
                    .unwrap();
                let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
                if role == "inherited-fd-open" {
                    assert!(flags >= 0, "selected child did not inherit its descriptor");
                } else {
                    assert_eq!(
                        flags, -1,
                        "an unrelated child inherited a builder-scoped descriptor"
                    );
                }
            }
            "oversized-stdout" => {
                let mut stdout = io::stdout().lock();
                stdout.write_all(&vec![b'o'; 1025]).unwrap();
                stdout.flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "oversized-stderr" => {
                let mut stderr = io::stderr().lock();
                stderr.write_all(&vec![b'e'; 1025]).unwrap();
                stderr.flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "aggregate-stdout" => {
                let mut stdout = io::stdout().lock();
                for _ in 0..4096 {
                    stdout.write_all(b"bounded-line\n").unwrap();
                }
                stdout.flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "burst-later-rejection" => {
                let mut stderr = io::stderr().lock();
                stderr.write_all(b"first\nreject-later\ntrailing").unwrap();
                stderr.flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "split-partial" => {
                let mut stderr = io::stderr().lock();
                stderr.write_all(b"complete\npartial").unwrap();
                stderr.flush().unwrap();
                thread::sleep(Duration::from_millis(500));
                stderr.write_all(b"more\n").unwrap();
                stderr.flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "silent-hang" => loop {
                thread::park_timeout(Duration::from_secs(60));
            },
            "closed-pipes-hang" => {
                #[cfg(unix)]
                unsafe {
                    libc::close(libc::STDOUT_FILENO);
                    libc::close(libc::STDERR_FILENO);
                }
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "timeout-parent" => {
                #[cfg(unix)]
                {
                    let marker = std::env::var_os(STREAMING_CHILD_MARKER).unwrap();
                    Command::new(std::env::current_exe().unwrap())
                        .args([
                            "--exact",
                            "process_builder::tests::streaming_child_helper",
                            "--nocapture",
                        ])
                        .env(STREAMING_CHILD_ROLE, "timeout-descendant")
                        .env(STREAMING_CHILD_MARKER, marker)
                        .stdout(Stdio::inherit())
                        .stderr(Stdio::inherit())
                        .spawn()
                        .unwrap();
                }
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "timeout-descendant" => {
                thread::sleep(Duration::from_secs(2));
                fs::write(
                    std::env::var_os(STREAMING_CHILD_MARKER).unwrap(),
                    "survived",
                )
                .unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "callback-parent" => {
                #[cfg(unix)]
                {
                    let marker = std::env::var_os(STREAMING_CHILD_MARKER).unwrap();
                    Command::new(std::env::current_exe().unwrap())
                        .args([
                            "--exact",
                            "process_builder::tests::streaming_child_helper",
                            "--nocapture",
                        ])
                        .env(STREAMING_CHILD_ROLE, "callback-descendant")
                        .env(STREAMING_CHILD_MARKER, marker)
                        .stdout(Stdio::inherit())
                        .stderr(Stdio::inherit())
                        .spawn()
                        .unwrap();
                }
                println!("reject-now");
                io::stdout().flush().unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            "callback-descendant" => {
                thread::sleep(Duration::from_millis(750));
                fs::write(
                    std::env::var_os(STREAMING_CHILD_MARKER).unwrap(),
                    "survived",
                )
                .unwrap();
                loop {
                    thread::park_timeout(Duration::from_secs(60));
                }
            }
            role => panic!("unknown streaming child role `{role}`"),
        }
    }

    #[test]
    fn bounded_streaming_rejects_oversized_newline_free_stdout() {
        let cmd = streaming_child_command("oversized-stdout");
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits(),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(
            error.contains("streaming stdout line exceeds the 1024-byte safety limit"),
            "{error}"
        );
    }

    #[test]
    fn bounded_streaming_rejects_oversized_newline_free_stderr() {
        let cmd = streaming_child_command("oversized-stderr");
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits(),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(
            error.contains("streaming stderr line exceeds the 1024-byte safety limit"),
            "{error}"
        );
    }

    #[test]
    fn bounded_streaming_rejects_aggregate_output() {
        let cmd = streaming_child_command("aggregate-stdout");
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                true,
                StreamingOutputLimits::new(1024, 4096),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(
            error.contains("streaming stdout exceeds the 4096-byte aggregate safety limit"),
            "{error}"
        );
    }

    #[test]
    fn bounded_streaming_times_out_a_silent_hung_child() {
        let cmd = streaming_child_command("silent-hang");
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits().with_timeout(Duration::from_millis(200)),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(error.contains("wall-clock timeout"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn bounded_streaming_times_out_after_a_child_closes_its_pipes() {
        let cmd = streaming_child_command("closed-pipes-hang");
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits().with_timeout(Duration::from_millis(200)),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(error.contains("wall-clock timeout"), "{error}");
    }

    #[cfg(unix)]
    #[test]
    fn bounded_streaming_timeout_kills_the_child_process_group() {
        let temp = tempfile::tempdir().unwrap();
        let marker = temp.path().join("timeout-descendant-survived");
        let mut cmd = streaming_child_command("timeout-parent");
        cmd.env(STREAMING_CHILD_MARKER, &marker);
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                false,
                small_streaming_limits().with_timeout(Duration::from_millis(200)),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(error.contains("wall-clock timeout"), "{error}");

        thread::sleep(Duration::from_millis(2200));
        assert!(
            !marker.exists(),
            "a descendant survived the timed-out child's isolated process group"
        );
    }

    #[test]
    fn bounded_streaming_rejects_a_later_complete_line_from_one_read() {
        let cmd = streaming_child_command("burst-later-rejection");
        let started = Instant::now();
        let mut visited = Vec::new();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |line| {
                    visited.push(line.to_owned());
                    if line == "reject-later" {
                        bail!("deliberate later-line rejection");
                    }
                    Ok(())
                },
                false,
                small_streaming_limits(),
            )
            .unwrap_err();
        assert_fast_failure(started);
        assert_eq!(visited, ["first", "reject-later"]);
        let error = format!("{error:#}");
        assert!(error.contains("deliberate later-line rejection"), "{error}");
    }

    #[test]
    fn retained_partial_line_bytes_are_not_counted_twice() {
        let cmd = streaming_child_command("split-partial");
        let started = Instant::now();
        let mut visited = Vec::new();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |line| {
                    visited.push(line.to_owned());
                    if line == "partialmore" {
                        bail!("deliberate joined-line rejection");
                    }
                    Ok(())
                },
                false,
                StreamingOutputLimits::new(1024, 21),
            )
            .unwrap_err();
        assert_fast_failure(started);
        assert_eq!(visited, ["complete", "partialmore"]);
        let error = format!("{error:#}");
        assert!(
            error.contains("deliberate joined-line rejection"),
            "{error}"
        );
        assert!(!error.contains("aggregate safety limit"), "{error}");
    }

    #[test]
    fn callback_rejection_kills_hanging_child_process_group() {
        let temp = tempfile::tempdir().unwrap();
        let marker = temp.path().join("descendant-survived");
        let mut cmd = streaming_child_command("callback-parent");
        cmd.env(STREAMING_CHILD_MARKER, &marker);
        let started = Instant::now();
        let error = cmd
            .exec_with_streaming_limits(
                &mut |line| {
                    if line == "reject-now" {
                        bail!("deliberate callback rejection");
                    }
                    Ok(())
                },
                &mut |_| Ok(()),
                false,
                small_streaming_limits(),
            )
            .unwrap_err();
        assert_fast_failure(started);
        let error = format!("{error:#}");
        assert!(error.contains("deliberate callback rejection"), "{error}");

        #[cfg(unix)]
        {
            thread::sleep(Duration::from_secs(1));
            assert!(
                !marker.exists(),
                "a descendant holding the child's output pipes survived callback rejection"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn inherited_fd_is_scoped_to_the_selected_process_builder() {
        use std::os::fd::{AsRawFd as _, OwnedFd};
        use std::os::unix::net::UnixStream;
        use std::sync::Arc;

        let (_peer, inherited) = UnixStream::pair().unwrap();
        let inherited: OwnedFd = inherited.into();
        let inherited = Arc::new(inherited);
        let fd = inherited.as_raw_fd();
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        assert!(flags >= 0);
        assert_ne!(flags & libc::FD_CLOEXEC, 0);

        let mut selected = streaming_child_command("inherited-fd-open");
        selected
            .env(INHERITED_FD_TEST_ENV, fd.to_string())
            .inherit_fd_for_exec(Arc::clone(&inherited))
            .unwrap();
        selected.exec().unwrap();

        let mut unrelated = streaming_child_command("inherited-fd-closed");
        unrelated.env(INHERITED_FD_TEST_ENV, fd.to_string());
        unrelated.exec().unwrap();

        let parent_flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        assert!(parent_flags >= 0);
        assert_ne!(parent_flags & libc::FD_CLOEXEC, 0);
    }

    #[test]
    fn argfile_build_succeeds() {
        let mut cmd = ProcessBuilder::new("echo");
        cmd.args(["foo", "bar"].as_slice());
        let (cmd, argfile) = cmd.build_command_with_argfile().unwrap();

        assert_eq!(cmd.get_program(), "echo");
        let cmd_args: Vec<_> = cmd.get_args().map(|s| s.to_str().unwrap()).collect();
        assert_eq!(cmd_args.len(), 1);
        assert!(cmd_args[0].starts_with("@"));
        assert!(cmd_args[0].contains("cargo-argfile."));

        let buf = fs::read_to_string(argfile.path()).unwrap();
        assert_eq!(buf, "foo\nbar\n");
    }

    #[test]
    fn argfile_build_fails_if_arg_contains_newline() {
        let mut cmd = ProcessBuilder::new("echo");
        cmd.arg("foo\n");
        let err = cmd.build_command_with_argfile().unwrap_err();
        assert_eq!(
            err.to_string(),
            "argument for argfile contains newlines: `foo\n`"
        );
    }

    #[test]
    fn argfile_build_fails_if_arg_contains_invalid_utf8() {
        let mut cmd = ProcessBuilder::new("echo");

        #[cfg(windows)]
        let invalid_arg = {
            use std::os::windows::prelude::*;
            std::ffi::OsString::from_wide(&[0x0066, 0x006f, 0xD800, 0x006f])
        };

        #[cfg(unix)]
        let invalid_arg = {
            use std::os::unix::ffi::OsStrExt;
            std::ffi::OsStr::from_bytes(&[0x66, 0x6f, 0x80, 0x6f]).to_os_string()
        };

        cmd.arg(invalid_arg);
        let err = cmd.build_command_with_argfile().unwrap_err();
        assert_eq!(
            err.to_string(),
            "argument for argfile contains invalid UTF-8 characters: `fo�o`"
        );
    }
}
