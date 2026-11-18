//! Continue an actual fixed ancestor without a second machine reservation.
//! The ancestor remains the original group and descendant-retirement owner.

use std::time::{Duration, Instant};

use trust_resource_provenance::program::HeldSystemCommand;

use super::*;
use crate::trust_repo_lock::management::exec::native;

#[cfg(test)]
thread_local! {
    static REPLACE_OUTPUT_BEFORE_GO: std::cell::RefCell<Option<(PathBuf, PathBuf)>> = const { std::cell::RefCell::new(None) };
}
#[cfg(test)]
pub(super) fn replace_output_before_go(path: PathBuf, retained: PathBuf) {
    REPLACE_OUTPUT_BEFORE_GO.with(|fault| *fault.borrow_mut() = Some((path, retained)));
}

/// One nested command retaining the same original fixed and GNU descriptions.
/// This owner cannot create a new group, pool, worktree lock or exclusive fence.
pub struct PreparedNestedFixedCommand {
    original: InheritedFixedClaim,
    scheduler: jobserver_utils::Jobserver,
    command: Command,
    deadline: Instant,
    image: HeldSystemCommand,
    directory: Option<MemberDirectory>,
    execution_start: Option<group::execution_start::ExecutionStart>,
}

/// Direct-child wait inside the ancestor's existing original group. Direct
/// exit is not a claim that all descendants have retired; the outer owner
/// continues to retain its complete original admission for that purpose.
#[must_use = "retain the original fixed and GNU owners through the actual child wait"]
pub struct RunningNestedFixedCommand {
    original: Option<InheritedFixedClaim>,
    _scheduler: jobserver_utils::Jobserver,
    image: HeldSystemCommand,
    child: native::Child,
    directory: Option<MemberDirectory>,
}

impl InheritedFixedClaim {
    /// Retain an actual original continuation and its existing GNU server.
    /// No token is acquired, released or manufactured. The caller must wait
    /// rather than concurrently consume the same implicit GNU continuation.
    ///
    /// # Safety
    ///
    /// The native coordinator must supply the SAME original GNU transport
    /// belonging to this actual fixed ancestor, never a replacement/new pool.
    /// Caller work must be serially paused while the child uses its implicit
    /// continuation. The actual outer group owner must remain alive through
    /// descendant retirement. The command supplies only argv/environment
    /// changes and uses the original cwd/console stdio; arbitrary pre_exec,
    /// env_clear and stdio/cwd redirection are not supported by this launcher.
    pub unsafe fn prepare_nested_command(
        self,
        command: Command,
        scheduler: jobserver_utils::Jobserver,
        budget: NonZeroU32,
        worktree: Option<&Path>,
        exclusive: bool,
        deadline: Instant,
    ) -> io::Result<PreparedNestedFixedCommand> {
        self.prepare_nested_at(command, scheduler, budget, worktree, exclusive, deadline, None)
    }

    /// Continue within a Root-issued output member, using its actual opened
    /// directory for child fchdir. This does not reinterpret V1's missing
    /// worktree or grant source, SDK, CPU or exclusive authority.
    ///
    /// # Safety
    /// The same original-GNU, serial continuation, outer-group retirement and
    /// restricted-command contract of `prepare_nested_command` applies.
    pub unsafe fn prepare_nested_output_command(
        self,
        command: Command,
        scheduler: jobserver_utils::Jobserver,
        budget: NonZeroU32,
        directory: MemberDirectory,
        exclusive: bool,
        deadline: Instant,
    ) -> io::Result<PreparedNestedFixedCommand> {
        self.prepare_nested_at(
            command,
            scheduler,
            budget,
            None,
            exclusive,
            deadline,
            Some(directory),
        )
    }

    fn prepare_nested_at(
        self,
        mut command: Command,
        mut scheduler: jobserver_utils::Jobserver,
        budget: NonZeroU32,
        worktree: Option<&Path>,
        exclusive: bool,
        deadline: Instant,
        directory: Option<MemberDirectory>,
    ) -> io::Result<PreparedNestedFixedCommand> {
        match &directory {
            Some(directory) => self.check_output_nested(budget, directory, exclusive)?,
            None => self.check_nested(budget, worktree, exclusive)?,
        }
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        let loader = |name: &OsStr| {
            name.as_bytes().starts_with(b"DYLD_") || name.as_bytes().starts_with(b"LD_")
        };
        // Match the native launcher's inherited-plus-explicit environment.
        // A caller can remove a loader input; no present override is accepted.
        if std::env::vars_os().any(|(name, _)| {
            loader(&name) && !command.get_envs().any(|(key, value)| key == name && value.is_none())
        }) || command.get_envs().any(|(name, value)| value.is_some() && loader(name))
        {
            return Err(invalid("nested command refuses loader overrides"));
        }
        let image = HeldSystemCommand::open(Path::new(command.get_program()), deadline)?;
        if command.get_envs().any(|(name, _)| {
            name == FIXED_HANDOFF_ENV || name == jobserver_utils::FIXED_CLAIM_HANDOFF_ENV
        }) {
            return Err(invalid("nested command overrides its original fixed handoff"));
        }
        scheduler.enable_descendant_handoff()?;
        scheduler.configure_make(&mut command);
        command.env("CARGO_BUILD_JOBS", budget.get().to_string());
        command.env(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV, self.descendant_advertisement()?);
        command.env(FIXED_HANDOFF_ENV, "requires-live-ancestor-v1");
        self.check_current()?;
        if Instant::now() >= deadline {
            return Err(io::ErrorKind::TimedOut.into());
        }
        Ok(PreparedNestedFixedCommand {
            original: self,
            scheduler,
            command,
            deadline,
            image,
            directory,
            execution_start: None,
        })
    }
}

impl PreparedNestedFixedCommand {
    /// Observe this actual V2 suboperation's loaded-to-GO transition without
    /// creating another Root, group, output member or resource reservation.
    /// V1 remains unchanged. The same original fixed/GNU rights fund the child.
    pub fn with_execution_start(mut self, pipe: group::ExecutionStartPipe) -> io::Result<Self> {
        if self.execution_start.is_some() {
            return Err(invalid("nested execution observer was already supplied"));
        }
        if !self.original.has_original_output_member()? {
            return Err(invalid(
                "nested execution observation requires the original V2 output member",
            ));
        }
        let original_gnu = self.scheduler.retain_transport_descriptors()?;
        self.execution_start = Some(group::execution_start::ExecutionStart::capture(
            pipe,
            self.original
                .maintenance_originals()?
                .iter()
                .map(AsRawFd::as_raw_fd)
                .chain(original_gnu.iter().map(AsRawFd::as_raw_fd)),
        )?);
        self.original.check_current()?;
        Ok(self)
    }

    /// Launch once inside the existing process group. Only the outer original
    /// owner forwards group signals or establishes descendant retirement.
    pub fn spawn(self) -> io::Result<RunningNestedFixedCommand> {
        self.original.check_current()?;
        self.image.validate(self.deadline)?;
        let child = match &self.directory {
            Some(directory) => {
                self.original.check_output_directory(directory)?;
                native::Child::spawn_output_member_suspended(
                    &self.command,
                    &self.scheduler,
                    directory.original(),
                    self.deadline,
                )?
            }
            None => native::Child::spawn_suspended(&self.command, &self.scheduler, self.deadline)?,
        };
        let mut owner = RunningNestedFixedCommand {
            original: Some(self.original),
            _scheduler: self.scheduler,
            image: self.image,
            child,
            directory: self.directory,
        };
        let identity = owner.child.stopped_identity(self.deadline)?;
        owner.image.validate_loaded(identity, self.deadline)?;
        #[cfg(test)]
        REPLACE_OUTPUT_BEFORE_GO.with(|fault| -> io::Result<()> {
            if let Some((path, retained)) = fault.borrow_mut().take() {
                fs::rename(&path, retained)?;
                fs::create_dir(&path)?;
            }
            Ok(())
        })?;
        owner.original.as_ref().expect("original nested admission").check_current()?;
        if let Some(directory) = &owner.directory {
            owner
                .original
                .as_ref()
                .expect("same original admission")
                .check_output_directory(directory)?;
        }
        if let Some(observer) = self.execution_start {
            observer.notify(identity.pid, self.deadline)?;
        }
        owner.child.resume(identity, self.deadline)?;
        Ok(owner)
    }
}

impl RunningNestedFixedCommand {
    /// Wait for this actual child with the same original admission retained.
    pub fn wait(&mut self) -> io::Result<ExitStatus> {
        self.original.as_ref().expect("live original nested admission").check_current()?;
        if let Some(directory) = &self.directory {
            self.original
                .as_ref()
                .expect("same original admission")
                .check_output_directory(directory)?;
        }
        let status = self.child.wait()?;
        self.original.as_ref().expect("live original nested admission").check_current()?;
        if let Some(directory) = &self.directory {
            self.original
                .as_ref()
                .expect("same original admission")
                .check_output_directory(directory)?;
        }
        self.image.validate(
            Instant::now()
                .checked_add(Duration::from_secs(30))
                .ok_or_else(|| invalid("nested input deadline overflow"))?,
        )?;
        Ok(status)
    }

    /// Cancel only this owned direct child, never the ancestor's group.
    pub fn cancel(&mut self) -> io::Result<ExitStatus> {
        if let Some(status) = self.child.try_wait()? {
            return Ok(status);
        }
        if let Err(error) = self.child.kill() {
            return match self.child.try_wait()? {
                Some(status) => Ok(status),
                None => Err(error),
            };
        }
        self.child.wait()
    }
}

impl Drop for RunningNestedFixedCommand {
    fn drop(&mut self) {
        if let Err(error) = self.cancel() {
            if let Some(original) = self.original.take() {
                std::mem::forget(original);
            }
            let _ = writeln!(
                io::stderr().lock(),
                "nested direct-child retirement unknown; original admission retained: {error}"
            );
        }
    }
}
