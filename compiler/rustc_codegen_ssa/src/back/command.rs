//! A thin wrapper around `Command` in the standard library which allows us to
//! read the arguments that are built up.

use std::ffi::{OsStr, OsString};
use std::process::{self, Output};
use std::{fmt, io, mem};

// Trust: invocation-owned observations are consumed only after the owning wait.
use rustc_session::{Session, tool_inputs::Attempt};
use rustc_target::spec::LldFlavor;

#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "command/native.rs"]
mod native;
// Trust: same original Fixed compiler primary, separate from cooperative v3.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[path = "command/bootstrap_fixed.rs"]
mod bootstrap_fixed;

pub(crate) enum LinkChild {
    // Trust: retain the live window alongside the child that owns its wait.
    Local {
        child: process::Child,
        attempt: Option<Attempt>,
    },
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    Native(native::Child),
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    BootstrapFixed(bootstrap_fixed::Child),
}

#[derive(Clone)]
pub(crate) struct Command {
    program: Program,
    args: Vec<OsString>,
    env: Vec<(OsString, OsString)>,
    env_remove: Vec<OsString>,
    env_clear: bool,
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    resources: Option<rustc_data_structures::jobserver::ChildResources>,
}

#[derive(Clone)]
enum Program {
    Normal(OsString),
    CmdBatScript(OsString),
    Lld(OsString, LldFlavor),
}

impl Command {
    pub(crate) fn new<P: AsRef<OsStr>>(program: P) -> Command {
        Command::_new(Program::Normal(program.as_ref().to_owned()))
    }

    pub(crate) fn bat_script<P: AsRef<OsStr>>(program: P) -> Command {
        Command::_new(Program::CmdBatScript(program.as_ref().to_owned()))
    }

    pub(crate) fn lld<P: AsRef<OsStr>>(program: P, flavor: LldFlavor) -> Command {
        Command::_new(Program::Lld(program.as_ref().to_owned(), flavor))
    }

    fn _new(program: Program) -> Command {
        Command {
            program,
            args: Vec::new(),
            env: Vec::new(),
            env_remove: Vec::new(),
            env_clear: false,
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            resources: None,
        }
    }

    pub(crate) fn arg<P: AsRef<OsStr>>(&mut self, arg: P) -> &mut Command {
        self._arg(arg.as_ref());
        self
    }

    pub(crate) fn args<I>(&mut self, args: I) -> &mut Command
    where
        I: IntoIterator<Item: AsRef<OsStr>>,
    {
        for arg in args {
            self._arg(arg.as_ref());
        }
        self
    }

    fn _arg(&mut self, arg: &OsStr) {
        self.args.push(arg.to_owned());
    }

    pub(crate) fn env<K, V>(&mut self, key: K, value: V) -> &mut Command
    where
        K: AsRef<OsStr>,
        V: AsRef<OsStr>,
    {
        self._env(key.as_ref(), value.as_ref());
        self
    }

    fn _env(&mut self, key: &OsStr, value: &OsStr) {
        self.env.push((key.to_owned(), value.to_owned()));
    }

    pub(crate) fn env_remove<K>(&mut self, key: K) -> &mut Command
    where
        K: AsRef<OsStr>,
    {
        self._env_remove(key.as_ref());
        self
    }

    pub(crate) fn env_clear(&mut self) -> &mut Command {
        self.env_clear = true;
        self
    }

    fn _env_remove(&mut self, key: &OsStr) {
        self.env_remove.push(key.to_owned());
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub(crate) fn set_resources(
        &mut self,
        resources: Option<rustc_data_structures::jobserver::ChildResources>,
    ) {
        self.resources = resources;
    }

    fn check_local_execution(&self) -> io::Result<()> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if rustc_data_structures::jobserver::native_v3_context().is_some()
            || rustc_data_structures::jobserver::bootstrap_fixed_context().is_some()
        {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "native v3 external compiler phases require a retained hosted execution loan",
            ));
        }
        Ok(())
    }

    // Trust: linker attempts, including response-file retries, share this path.
    pub(crate) fn spawn_linker(&self, sess: &Session) -> io::Result<LinkChild> {
        self.spawn_linker_inner(sess, false)
    }

    fn spawn_linker_inner(&self, sess: &Session, null_stdin: bool) -> io::Result<LinkChild> {
        // Trust: this backend path follows the actual codegen join. No local fallback.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(context) = rustc_data_structures::jobserver::bootstrap_fixed_context() {
            sess.tool_inputs_unavailable();
            return bootstrap_fixed::Child::spawn(self, context).map(LinkChild::BootstrapFixed);
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(context) = rustc_data_structures::jobserver::native_v3_context() {
            // Trust: a hosted transport has a different lookup and security context.
            sess.tool_inputs_unavailable();
            return native::Child::spawn(self, context).map(LinkChild::Native);
        }
        self.check_local_execution()?;
        let mut command = self.command();
        command.stdout(process::Stdio::piped()).stderr(process::Stdio::piped());
        if null_stdin {
            command.stdin(process::Stdio::null());
        }
        let attempt = self.observe_linker(sess, &command);
        match command.spawn() {
            Ok(child) => Ok(LinkChild::Local { child, attempt }),
            Err(error) => {
                // Trust: a failed spawn can cause a later command retry. Preserve
                // that lookup attempt too; observation failure never masks it.
                if let Some(attempt) = attempt {
                    sess.finish_tool_inputs(attempt);
                }
                Err(error)
            }
        }
    }

    fn observe_linker(&self, sess: &Session, command: &process::Command) -> Option<Attempt> {
        if !sess.tool_inputs_requested() {
            return None;
        }
        let inherited_path = std::env::var_os("PATH");
        let Ok(cwd) = std::env::current_dir()
            .map(|cwd| command.get_current_dir().map_or(cwd.clone(), |path| cwd.join(path)))
        else {
            sess.tool_inputs_unavailable();
            return None;
        };
        let child_path = self.final_child_path(command, inherited_path.as_deref());
        Some(sess.begin_tool_inputs(
            command.get_program(),
            &cwd,
            child_path.as_deref(),
            sess.tool_inputs_parent_path(),
        ))
    }

    // Trust: inspect the fully constructed std Command, after all localization,
    // removals and resource configuration. env_clear is not exposed by std.
    fn final_child_path(
        &self,
        command: &process::Command,
        parent_path: Option<&OsStr>,
    ) -> Option<OsString> {
        let mut path = if self.env_clear { None } else { parent_path.map(OsStr::to_owned) };
        for (key, value) in command.get_envs() {
            if key == OsStr::new("PATH") {
                path = value.map(OsStr::to_owned);
            }
        }
        path
    }

    // Trust: preserve std::Command::output's null stdin for the response-file
    // fallback, while using the same actual-launch observation and owning wait.
    pub(crate) fn linker_output(&self, sess: &Session) -> io::Result<Output> {
        let child = self.spawn_linker_inner(sess, true)?;
        self.wait_with_output(sess, child)
    }

    pub(crate) fn output(&mut self) -> io::Result<Output> {
        // Trust: generic output is not a separately joined linker boundary.
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if rustc_data_structures::jobserver::bootstrap_fixed_context().is_some() {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "private Fixed compiler external phase requires its post-join paired linker path",
            ));
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(context) = rustc_data_structures::jobserver::native_v3_context() {
            return native::Child::spawn(self, context)?.output();
        }
        self.check_local_execution()?;
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(resources) = &self.resources {
            let child = self
                .command()
                .stdin(process::Stdio::null())
                .stdout(process::Stdio::piped())
                .stderr(process::Stdio::piped())
                .spawn()?;
            return resources.wait_with_output(child);
        }
        self.command().output()
    }

    pub(crate) fn wait_with_output(&self, sess: &Session, child: LinkChild) -> io::Result<Output> {
        let (child, attempt) = match child {
            LinkChild::Local { child, attempt } => (child, attempt),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            LinkChild::Native(child) => return child.output(),
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            LinkChild::BootstrapFixed(child) => return child.output(),
        };
        // Trust: even an unsuccessful linker exit has a completed owning wait.
        // An I/O wait error cannot establish completion and withholds the unit.
        let output = self.wait_local(child);
        if let Some(attempt) = attempt {
            if output.is_err() {
                sess.tool_inputs_unavailable();
            }
            sess.finish_tool_inputs(attempt);
        }
        output
    }

    fn wait_local(&self, child: process::Child) -> io::Result<Output> {
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(resources) = &self.resources {
            return resources.wait_with_output(child);
        }
        child.wait_with_output()
    }

    pub(crate) fn command(&self) -> process::Command {
        let mut ret = match self.program {
            Program::Normal(ref p) => process::Command::new(p),
            Program::CmdBatScript(ref p) => {
                let mut c = process::Command::new("cmd");
                c.arg("/c").arg(p);
                c
            }
            Program::Lld(ref p, flavor) => {
                let mut c = process::Command::new(p);
                c.arg("-flavor").arg(flavor.desc());
                c
            }
        };
        ret.args(&self.args);
        ret.envs(self.env.clone());
        for k in &self.env_remove {
            ret.env_remove(k);
        }
        if self.env_clear {
            ret.env_clear();
        }
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        if let Some(resources) = &self.resources {
            resources.configure(&mut ret);
        }
        ret
    }

    // extensions

    pub(crate) fn get_args(&self) -> &[OsString] {
        &self.args
    }

    pub(crate) fn take_args(&mut self) -> Vec<OsString> {
        mem::take(&mut self.args)
    }

    /// Returns a `true` if we're pretty sure that this'll blow OS spawn limits,
    /// or `false` if we should attempt to spawn and see what the OS says.
    pub(crate) fn very_likely_to_exceed_some_spawn_limit(&self) -> bool {
        #[cfg(not(any(windows, unix)))]
        {
            return false;
        }

        // On Unix the limits can be gargantuan anyway so we're pretty
        // unlikely to hit them, but might still exceed it.
        // We consult ARG_MAX here to get an estimate.
        #[cfg(unix)]
        {
            let ptr_size = mem::size_of::<usize>();
            // arg + \0 + pointer
            let args_size = self.args.iter().fold(0usize, |acc, a| {
                let arg = a.as_encoded_bytes().len();
                let nul = 1;
                acc.saturating_add(arg).saturating_add(nul).saturating_add(ptr_size)
            });
            // key + `=` + value + \0 + pointer
            let envs_size = self.env.iter().fold(0usize, |acc, (k, v)| {
                let k = k.as_encoded_bytes().len();
                let eq = 1;
                let v = v.as_encoded_bytes().len();
                let nul = 1;
                acc.saturating_add(k)
                    .saturating_add(eq)
                    .saturating_add(v)
                    .saturating_add(nul)
                    .saturating_add(ptr_size)
            });
            let arg_max = match unsafe { libc::sysconf(libc::_SC_ARG_MAX) } {
                -1 => return false, // Go to OS anyway.
                max => max as usize,
            };
            return args_size.saturating_add(envs_size) > arg_max;
        }

        // Ok so on Windows to spawn a process is 32,768 characters in its
        // command line [1]. Unfortunately we don't actually have access to that
        // as it's calculated just before spawning. Instead we perform a
        // poor-man's guess as to how long our command line will be. We're
        // assuming here that we don't have to escape every character...
        //
        // Turns out though that `cmd.exe` has even smaller limits, 8192
        // characters [2]. Linkers can often be batch scripts (for example
        // Emscripten, Gecko's current build system) which means that we're
        // running through batch scripts. These linkers often just forward
        // arguments elsewhere (and maybe tack on more), so if we blow 8192
        // bytes we'll typically cause them to blow as well.
        //
        // Basically as a result just perform an inflated estimate of what our
        // command line will look like and test if it's > 8192 (we actually
        // test against 6k to artificially inflate our estimate). If all else
        // fails we'll fall back to the normal unix logic of testing the OS
        // error code if we fail to spawn and automatically re-spawning the
        // linker with smaller arguments.
        //
        // [1]: https://docs.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-createprocessa
        // [2]: https://devblogs.microsoft.com/oldnewthing/?p=41553
        #[cfg(windows)]
        {
            let estimated_command_line_len = self
                .args
                .iter()
                .fold(0usize, |acc, a| acc.saturating_add(a.as_encoded_bytes().len()));
            return estimated_command_line_len > 1024 * 6;
        }
    }
}

impl fmt::Debug for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.command().fmt(f)
    }
}

// Trust: tool-input tests, in the sibling `command/tests.rs` as tidy's unit_tests
// layout requires. They exercise extraction from the actual std Command; they neither
// mutate process environment nor replace a linker with a fabricated tool role.
#[cfg(test)]
mod tests;
