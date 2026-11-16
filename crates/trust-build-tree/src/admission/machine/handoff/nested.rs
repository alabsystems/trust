//! Continue an actual fixed ancestor without a second machine reservation.
//! The ancestor remains the original group and descendant-retirement owner.

use std::time::{Duration, Instant};

use trust_resource_provenance::program::HeldSystemCommand;

use super::*;
use crate::trust_repo_lock::management::exec::native;

/// One nested command retaining the same original fixed and GNU descriptions.
/// This owner cannot create a new group, pool, worktree lock or exclusive fence.
pub struct PreparedNestedFixedCommand {
    original: InheritedFixedClaim,
    scheduler: jobserver_utils::Jobserver,
    command: Command,
    deadline: Instant,
    image: HeldSystemCommand,
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
        mut command: Command,
        mut scheduler: jobserver_utils::Jobserver,
        budget: NonZeroU32,
        worktree: Option<&Path>,
        exclusive: bool,
        deadline: Instant,
    ) -> io::Result<PreparedNestedFixedCommand> {
        self.check_nested(budget, worktree, exclusive)?;
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
        Ok(PreparedNestedFixedCommand { original: self, scheduler, command, deadline, image })
    }
}

impl PreparedNestedFixedCommand {
    /// Launch once inside the existing process group. Only the outer original
    /// owner forwards group signals or establishes descendant retirement.
    pub fn spawn(self) -> io::Result<RunningNestedFixedCommand> {
        self.original.check_current()?;
        self.image.validate(self.deadline)?;
        let child = native::Child::spawn_suspended(&self.command, &self.scheduler, self.deadline)?;
        let mut owner = RunningNestedFixedCommand {
            original: Some(self.original),
            _scheduler: self.scheduler,
            image: self.image,
            child,
        };
        let identity = owner.child.stopped_identity(self.deadline)?;
        owner.image.validate_loaded(identity, self.deadline)?;
        owner.original.as_ref().expect("original nested admission").check_current()?;
        owner.child.resume(identity, self.deadline)?;
        Ok(owner)
    }
}

impl RunningNestedFixedCommand {
    /// Wait for this actual child with the same original admission retained.
    pub fn wait(&mut self) -> io::Result<ExitStatus> {
        self.original.as_ref().expect("live original nested admission").check_current()?;
        let status = self.child.wait()?;
        self.original.as_ref().expect("live original nested admission").check_current()?;
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
