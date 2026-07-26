//! This module is explictly not `mod`ed as it's shared across multiple crates
//! like bootstrap and compiletest via `#[path]` moduled declarations.
//! It's important to keep this file isolated from the rest of build_helper so it can be compiled
//! without build_helper.

// Roughly match the `std::process::Command` API
#![allow(dead_code, unreachable_pub)]

use std::ffi::{OsStr, OsString};
use std::io::Write;
use std::path::Path;
use std::process::{Command, CommandEnvs};

use tempfile::NamedTempFile;

/// A wrapper around [`Command`] that adds support for arg files.
/// This is useful as we have some commands that can get very long and at times
/// hit the OS limit (usually Windows)
///
/// This implementation is based off the `ProcessBuilder` implementation in Cargo
/// but simplified.
///
/// NOTE: In most scenarios we want to avoid arg files as it makes debugging more complicated
///       so we try to avoid it if the command is not close to the OS limit.
#[derive(Debug)]
pub struct ArgFileCommand {
    command: Command,
    args: Vec<OsString>,
    force_argfile: bool,
    argfile_prefix_args: usize,
}

impl ArgFileCommand {
    pub fn new<S: AsRef<OsStr>>(program: S) -> Self {
        let command = Command::new(program);
        Self { command, args: Vec::new(), force_argfile: false, argfile_prefix_args: 0 }
    }
    pub fn arg<S: AsRef<OsStr>>(&mut self, arg: S) -> &mut Self {
        self.args.push(arg.as_ref().to_os_string());
        self
    }

    pub fn args<I, S>(&mut self, args: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        self.args.extend(args.into_iter().map(|s| s.as_ref().to_os_string()));
        self
    }

    /// Returns the complete argument vector so a shim can enforce policy at
    /// the final process boundary, after all authored and environment-derived
    /// options have been assembled.
    pub fn args_mut(&mut self) -> &mut Vec<OsString> {
        &mut self.args
    }

    /// Force a fresh response-file boundary even for short commands. Shims use
    /// this after inspecting an inbound response file so a nested literal
    /// `@file` is expanded exactly once by the real compiler, not once again
    /// merely because the shim forwarded it as explicit argv.
    pub fn force_argfile(&mut self, force: bool) -> &mut Self {
        self.force_argfile = force;
        self
    }

    /// Keep this many leading arguments outside any response file. Wrapper
    /// protocols use an explicit compiler path as argv[1], which the wrapper
    /// must see before the compiler's response-file argument.
    pub fn argfile_prefix_args(&mut self, count: usize) -> &mut Self {
        self.argfile_prefix_args = count;
        self
    }

    pub fn env<K, V>(&mut self, key: K, val: V) -> &mut Self
    where
        K: AsRef<OsStr>,
        V: AsRef<OsStr>,
    {
        self.command.env(key, val);
        self
    }

    pub fn get_envs(&self) -> CommandEnvs<'_> {
        self.command.get_envs()
    }

    pub fn env_remove<K: AsRef<OsStr>>(&mut self, key: K) -> &mut Self {
        self.command.env_remove(key);
        self
    }

    pub fn current_dir<P: AsRef<Path>>(&mut self, dir: P) -> &mut Self {
        self.command.current_dir(dir);
        self
    }

    pub fn stdin(&mut self, stdin: std::process::Stdio) -> &mut Self {
        self.command.stdin(stdin);
        self
    }

    pub fn build(mut self) -> std::io::Result<(Command, Option<NamedTempFile>)> {
        // On Windows there is a hard limit of ~32KB, so we cut off at 30KB to
        // give some buffer just incase.
        #[cfg(windows)]
        let threshold: usize = 30 * 1024;
        // On unix the limit is defined by ARG_MAX. If its not explicitly set we set it to 1MB
        // which is fairly large but lower than the ~2MB that it defaults to on most systems.
        #[cfg(unix)]
        let threshold: usize =
            std::env::var("ARG_MAX").ok().and_then(|v| v.parse().ok()).unwrap_or(1024 * 1024);

        let total_arg_len: usize = self.args.iter().map(|a| a.len() + 1).sum();
        if !self.force_argfile && total_arg_len <= threshold {
            self.command.args(self.args);
            return Ok((self.command, None));
        }

        let mut tmp = tempfile::Builder::new().prefix("bootstrap-argfile.").tempfile()?;

        if self.argfile_prefix_args > self.args.len() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "argfile prefix exceeds argument count",
            ));
        }
        let (prefix_args, response_args) = self.args.split_at(self.argfile_prefix_args);
        self.command.args(prefix_args);
        let args = response_args
            .iter()
            .map(|arg| {
                arg.to_str().ok_or_else(|| {
                    std::io::Error::other(format!(
                        "argument for argfile contains invalid UTF-8 characters: `{}`",
                        arg.to_string_lossy()
                    ))
                })
            })
            .collect::<std::io::Result<Vec<_>>>()?;
        let mut arg = OsString::from("@");
        let mut buf = Vec::with_capacity(total_arg_len);
        if args.iter().any(|arg| arg.contains('\n')) {
            // Line argfiles cannot represent embedded newlines. Rustc's shell
            // argfile dialect can, and is parsed by the same shlex version the
            // bootstrap shim used for its immutable inspection snapshot.
            let encoded = shlex::try_join(args.iter().copied()).map_err(|err| {
                std::io::Error::other(format!("cannot quote compiler args: {err}"))
            })?;
            tmp.write_all(encoded.as_bytes())?;
            self.command.arg("-Zshell-argfiles");
            arg.push("shell:");
        } else {
            for arg in args {
                writeln!(buf, "{arg}")?;
            }
            tmp.write_all(&buf)?;
        }
        arg.push(tmp.path());
        self.command.arg(arg);
        tmp.flush()?;

        Ok((self.command, Some(tmp)))
    }
}
