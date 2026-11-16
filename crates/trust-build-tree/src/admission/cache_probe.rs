//! Closed cache-health version probes using the SAME original fixed/GNU job.
//! A version exit is observation only. Only actual native no-fork confinement
//! and the original child's owning wait can permit the next local operation.

use std::ffi::{OsStr, OsString};
use std::fs::File;
use std::io::{self, Read as _, Write as _};
use std::os::fd::{AsFd, AsRawFd};
use std::os::unix::net::UnixStream;
use std::os::unix::process::ExitStatusExt as _;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use jobserver_utils::Jobserver;
use trust_resource_provenance::process::{self, Identity};
use trust_resource_provenance::program::{HeldProgram, HeldSystemCommand, ProgramObservation};
use trust_sha2::{Digest as _, Sha256};

use super::{InheritedFixedClaim, invalid};
use crate::trust_output_lock::OutputLock;
use crate::trust_repo_lock::management::exec::native;
use crate::trust_repo_lock::management::{Lease, MaintenanceBinding, MaintenanceLease};

mod inputs;
mod prelude;
pub use prelude::private_entry;
const POLL: Duration = Duration::from_millis(5);
const MAX_PROBE: Duration = Duration::from_secs(60);

fn check_output(output: &OutputLock, root: &Path) -> io::Result<()> {
    let actual = output.original_root()?;
    if actual == root || !actual.starts_with(root) {
        return Err(invalid("cache output is not inside the SAME original repository"));
    }
    output.check_root(actual)
}

/// Health observation, not a reusable native execution or SDK capability.
#[derive(Debug, serde_derive::Serialize)]
pub struct Observation {
    stage: u32,
    pub complete: bool,
    pub detail: String,
    pub compiler: PathBuf,
    pub raw_status: Option<i32>,
    pub libstd_files: usize,
    #[serde(skip)]
    original: Option<ProgramObservation>,
    #[serde(skip)]
    std: Vec<inputs::StdInput>,
    #[serde(skip)]
    kept: Option<KeptProgram>,
    #[serde(skip)]
    seed_absence: Option<inputs::AbsentCompilers>,
}
impl Observation {
    pub fn stage(&self) -> u32 {
        self.stage
    }
}

struct KeptProgram(Arc<HeldProgram>);
impl std::fmt::Debug for KeptProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("RetainedProgram").field(self.0.observation()).finish()
    }
}

/// One-use proof minted only by this actual private probe's native no-launch
/// result, or no-fork/session-leader + owning reap + EOF + group-absence path.
/// It is intentionally neither constructible nor exported to public callers.
pub(crate) struct NativeClosed {
    binding: MaintenanceBinding,
    _status: Option<std::process::ExitStatus>,
}
impl NativeClosed {
    pub(crate) fn matches(&self, original: &MaintenanceBinding) -> bool {
        self.binding.same(original)
    }
}
#[derive(Debug)]
struct ProbeFailure {
    observed: Option<std::process::ExitStatus>,
    error: io::Error,
}
impl std::fmt::Display for ProbeFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "native cache probe failed; actual observed status {:?}: {}",
            self.observed, self.error
        )
    }
}
impl std::error::Error for ProbeFailure {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

struct Resources {
    original: InheritedFixedClaim,
    scheduler: Jobserver,
    lease: Option<Lease>,
    maintenance: Option<MaintenanceLease>,
    failed: Option<Box<dyn std::error::Error>>,
    output: OutputLock,
    root: PathBuf,
    worktree: PathBuf,
    self_image: HeldSystemCommand,
}
struct Contained {
    initial: Identity,
}
struct Running {
    child: native::Child,
    program: Arc<HeldProgram>,
    control: UnixStream,
    initial: Option<Identity>,
    confined: Option<Contained>,
    target_started: bool,
    exec_requested: bool,
    ack: bool,
    observed_status: Option<std::process::ExitStatus>,
}
impl Running {
    fn control_closed(&mut self) -> io::Result<bool> {
        let mut byte = [0];
        match self.control.read(&mut byte) {
            Ok(0) => Ok(true),
            Ok(_) => Err(invalid("unexpected bytes after original cache prelude acknowledgement")),
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => Ok(false),
            Err(error) if error.kind() == io::ErrorKind::Interrupted => Ok(false),
            Err(error) => Err(error),
        }
    }
}

/// Actual original Manager/output/fixed/GNU owners. No constructor accepts
/// counts, token text, a path identity or a saved version/status as ownership.
#[must_use = "retain original owners through every native probe and cleanup"]
pub struct Owner {
    resources: Option<Resources>,
    running: Option<Running>,
}
impl Owner {
    /// # Safety
    /// The original native CLI must pass the SAME captured GNU transport for
    /// this inherited fixed claim. Its original executable must dispatch this
    /// module's private_entry at FIRST main entry, before imports, callbacks,
    /// file operations or threads. The caller is serially paused during each
    /// probe. The outer RunningFixedGroup retains the original root, while
    /// this owner separately retains its exact no-fork maintenance subgroup
    /// through native closure. No new scheduler, CPU pool or lease is acquired.
    pub unsafe fn new(
        original: InheritedFixedClaim,
        scheduler: Jobserver,
        lease: Lease,
        output: OutputLock,
        root: PathBuf,
        worktree: PathBuf,
    ) -> io::Result<Self> {
        if lease.is_borrowed() {
            return Err(invalid(
                "whole-tree cleanup requires the original independent Manager lease",
            ));
        }
        original.check_nested(original.budget()?, Some(&worktree), false)?;
        lease.check_root(&root)?;
        check_output(&output, &root)?;
        for (name, _) in std::env::vars_os() {
            if prelude::loader(&name) {
                return Err(invalid("whole-tree probe refuses ambient loader overrides"));
            }
        }
        let deadline = deadline()?;
        let self_image = HeldSystemCommand::open(&std::env::current_exe()?, deadline)?;
        self_image.validate_loaded(process::read_identity(std::process::id())?, deadline)?;
        Ok(Self {
            resources: Some(Resources {
                original,
                scheduler,
                lease: Some(lease),
                maintenance: None,
                failed: None,
                output,
                root,
                worktree,
                self_image,
            }),
            running: None,
        })
    }
    pub fn guards(&self) -> io::Result<(&Lease, &OutputLock)> {
        if self.running.is_some() {
            return Err(invalid("native cache probe closure remains unresolved"));
        }
        let resources =
            self.resources.as_ref().ok_or_else(|| invalid("cache owner unavailable"))?;
        resources.original.check_nested(
            resources.original.budget()?,
            Some(&resources.worktree),
            false,
        )?;
        if resources.maintenance.is_some() || resources.failed.is_some() {
            return Err(invalid("cache maintenance source custody remains withheld"));
        }
        let lease =
            resources.lease.as_ref().ok_or_else(|| invalid("cache source custody unavailable"))?;
        lease.check_root(&resources.root)?;
        check_output(&resources.output, &resources.root)?;
        Ok((lease, &resources.output))
    }
    /// Observe the SAME retained controller image/closure. This is used only
    /// to refuse a selection that would unlink an input required by subsequent
    /// probes; it cannot construct execution, exclusion or an SDK keeper.
    pub fn controller_inputs(&self) -> io::Result<&ProgramObservation> {
        self.guards()?;
        let resources = self.resources.as_ref().expect("checked original owner");
        let until = deadline()?;
        resources.self_image.validate_loaded(process::read_identity(std::process::id())?, until)?;
        Ok(resources.self_image.observation())
    }

    /// The only executable form is build/HOST/stage{1,2}/bin/trustc --version.
    /// The compiler stays stopped until its actual loaded held closure and
    /// kernel no-fork policy have been independently checked by this owner.
    pub fn sysroot(
        &mut self,
        host: &OsStr,
        stage: u32,
        original: Option<&Observation>,
    ) -> io::Result<Observation> {
        self.guards()?;
        if !matches!(stage, 1 | 2)
            || Path::new(host).components().count() != 1
            || !matches!(Path::new(host).components().next(), Some(Component::Normal(_)))
        {
            return Err(invalid("closed version probe requires host and stage1/stage2"));
        }
        self.probe(host, stage, original)
    }

    /// Explicit tools-before-compiler profile. Positive actual absence of BOTH
    /// later stages is required on both sides of the SAME contained stage0
    /// probe. A present, broken, symlinked or unknown stage is never fallback.
    pub fn seed_tools(
        &mut self,
        host: &OsStr,
        original: Option<&Observation>,
    ) -> io::Result<Observation> {
        self.guards()?;
        if Path::new(host).components().count() != 1
            || !matches!(Path::new(host).components().next(), Some(Component::Normal(_)))
        {
            return Err(invalid("seed-tools probe requires one original host name"));
        }
        let resources = self.resources.as_ref().expect("checked original owner");
        if let Some(prior) = original {
            if prior.stage != 0 {
                return Err(invalid("seed-tools postcheck requires its original seed observation"));
            }
            prior
                .seed_absence
                .as_ref()
                .ok_or_else(|| invalid("seed-tools original absence owner unavailable"))?
                .check(&resources.output)?;
        }
        let absence = inputs::AbsentCompilers::capture(&resources.output, host)?;
        let mut observed = self.probe(host, 0, original)?;
        absence.check(&self.resources.as_ref().expect("same original owner").output)?;
        observed.seed_absence = Some(absence);
        Ok(observed)
    }

    fn probe(
        &mut self,
        host: &OsStr,
        stage: u32,
        original: Option<&Observation>,
    ) -> io::Result<Observation> {
        self.guards()?;
        let until = deadline()?;
        let resources = self.resources.as_ref().expect("checked original owner");
        let relative = Path::new(host).join(format!("stage{stage}"));
        let root = resources.output.original_root()?.join(&relative);
        let compiler = root.join("bin/trustc");
        let mut observation = Observation {
            stage,
            complete: false,
            detail: String::new(),
            compiler: compiler.clone(),
            raw_status: None,
            libstd_files: 0,
            original: None,
            std: Vec::new(),
            kept: None,
            seed_absence: None,
        };
        let capture = inputs::capture(&resources.output, &relative, host, until);
        let (held, std) = match capture {
            Ok(Some(value)) => value,
            Ok(None) => {
                observation.detail = "incomplete: original stage/bin/trustc is absent".into();
                return Ok(observation);
            }
            Err(error) => return Err(error),
        };
        if let Some(prior) = original {
            if prior.stage != stage
                || prior.compiler != compiler
                || prior.original.as_ref() != Some(held.observation())
            {
                return Err(invalid(
                    "post-cleanup compiler differs from original preflight input observation",
                ));
            }
            prior
                .kept
                .as_ref()
                .ok_or_else(|| invalid("original compiler keeper unavailable"))?
                .0
                .validate(until)?;
            inputs::recheck_std(&prior.std, until)?;
        }
        observation.libstd_files = std.len();
        observation.original = Some(held.observation().clone());
        observation.kept = Some(KeptProgram(Arc::clone(&held)));
        observation.std = std;
        let mut command = std::process::Command::new(resources.self_image.program());
        let (parent, child) = UnixStream::pair()?;
        parent.set_nonblocking(true)?;
        command.arg(prelude::ENTRY).arg(format!("--control-fd={}", child.as_raw_fd()));
        resources.scheduler.configure_make(&mut command);
        command.env("CARGO_BUILD_JOBS", "1");
        let plan = prelude::Plan::new(&held)?;
        self.begin_maintenance()?;
        let resources = self.resources.as_ref().expect("same original resources");
        let mut originals = resources.original.maintenance_originals()?;
        // SAFETY: the private same-image prelude and selected compiler receive
        // close-only duplicates. Parent originals are retained throughout the
        // actual private subgroup and its closure/restore transaction.
        let output_originals = unsafe { resources.output.original_descriptions()? };
        originals.extend([output_originals.directory(), output_originals.lock()]);
        let launched = match native::Child::spawn_version_prelude(
            &command,
            &resources.scheduler,
            child.as_fd(),
            &originals,
            until,
        ) {
            Ok(child) => child,
            Err(native::VersionSpawnError::NotSpawned(error)) => {
                // This variant can only originate before OS creation or from
                // the native failed-spawn result, never from a status/EOF.
                let proof = NativeClosed { binding: self.binding()?, _status: None };
                self.restore(proof)?;
                return Err(error);
            }
            Err(native::VersionSpawnError::Unresolved(error)) => return Err(error),
        };
        // Install the actual wait/control/input owner immediately after spawn.
        // Even an expired deadline or failed first observation must retain it;
        // an absent observation is never replaced with an invented identity.
        self.running = Some(Running {
            child: launched,
            program: held,
            control: parent,
            initial: None,
            confined: None,
            target_started: false,
            exec_requested: false,
            ack: false,
            observed_status: None,
        });
        drop(child);
        let result = (|| {
            let running = self.running.as_mut().expect("same original child");
            let initial = running.child.stopped_identity(until)?;
            self.resources
                .as_ref()
                .expect("same original controller")
                .self_image
                .validate_loaded(initial, until)?;
            running.initial = Some(initial);
            prelude::send_plan(&mut running.control, &plan, until)?;
            running.child.resume(initial, until)?;
            self.finish_probe(until)
        })();
        let (status, closure_error) = match result {
            Ok(status) => (status, None),
            Err(error) => {
                let observed = self.cancel_confined();
                let closed = self.closed().map_err(|close| {
                    io::Error::other(ProbeFailure {
                        observed: self.running.as_ref().and_then(|r| r.observed_status),
                        error: io::Error::other(format!("{error}; closure check: {close}")),
                    })
                })?;
                if self.running.as_ref().is_some_and(|running| running.observed_status.is_some())
                    && closed
                {
                    (
                        observed
                            .or_else(|| self.running.as_ref().and_then(|r| r.observed_status))
                            .expect("actual owning wait"),
                        Some(error),
                    )
                } else {
                    return Err(io::Error::other(ProbeFailure {
                        observed: observed
                            .or_else(|| self.running.as_ref().and_then(|r| r.observed_status)),
                        error,
                    }));
                }
            }
        };
        let proof = NativeClosed { binding: self.binding()?, _status: Some(status) };
        self.restore(proof)
            .map_err(|error| io::Error::other(ProbeFailure { observed: Some(status), error }))?;
        let completed = self.running.take().expect("same contained terminal");
        let target_started = completed.target_started;
        let held = completed.program;
        observation.raw_status = Some(status.into_raw());
        let checked =
            held.validate(until).and_then(|()| inputs::recheck_std(&observation.std, until));
        observation.complete = closure_error.is_none()
            && target_started
            && status.success()
            && checked.is_ok()
            && !observation.std.is_empty();
        observation.detail = if let Some(error) = closure_error {
            format!("closed version failed after actual status {status}: {error}")
        } else if let Err(error) = checked {
            format!("closed version input recheck failed: {error}")
        } else if !target_started {
            format!("incomplete: child closed before checked compiler GO; actual status {status}")
        } else if observation.std.is_empty() {
            format!("incomplete: original libstd catalog is empty; actual version status {status}")
        } else {
            format!(
                "{}: actual contained trustc --version status {status}; {} original libstd files",
                if observation.complete { "complete health observation" } else { "incomplete" },
                observation.std.len()
            )
        };
        self.guards()?;
        Ok(observation)
    }
    fn finish_probe(&mut self, until: Instant) -> io::Result<std::process::ExitStatus> {
        loop {
            let running = self.running.as_mut().expect("original running probe");
            let initial =
                running.initial.ok_or_else(|| invalid("original probe identity unavailable"))?;
            let current = process::read_identity(running.child.id());
            if let Ok(current) = current {
                if current.birth != initial.birth || current.unique_id != initial.unique_id {
                    return Err(invalid("version probe original process changed"));
                }
                if prelude::no_fork(current.pid)? {
                    prelude::no_escape(current)?;
                    running.confined = Some(Contained { initial });
                }
            }
            if !running.ack {
                let mut byte = [0];
                match running.control.read(&mut byte) {
                    Ok(1) if byte == [prelude::ACK] => running.ack = true,
                    Ok(_) => {
                        return Err(invalid(
                            "cache version prelude closed without exact acknowledgement",
                        ));
                    }
                    Err(error)
                        if matches!(
                            error.kind(),
                            io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                        ) => {}
                    Err(error) => return Err(error),
                }
            }
            if running.ack && running.confined.is_some() && !running.exec_requested {
                match running.control.write(&[prelude::EXEC]) {
                    Ok(1) => running.exec_requested = true,
                    Ok(_) => return Err(invalid("cache version exec request was not delivered")),
                    Err(error)
                        if matches!(
                            error.kind(),
                            io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                        ) => {}
                    Err(error) => return Err(error),
                }
            }
            if running.exec_requested && !running.target_started {
                if let Some(target) = running.child.version_exec_stop(initial, until)? {
                    if !prelude::no_fork(target.pid)?
                        || running.confined.as_ref().is_none_or(|scope| scope.initial != initial)
                    {
                        return Err(invalid(
                            "version target has no actual original no-fork confinement",
                        ));
                    }
                    running.program.validate_loaded(target, until)?;
                    prelude::no_escape(target)?;
                    running.child.resume_version_target(initial, target, until)?;
                    running.target_started = true;
                }
            }
            if let Some(status) = running.child.try_wait()? {
                running.observed_status = Some(status);
                if running.confined.is_none() {
                    return Err(invalid("version child reaped without native no-fork closure"));
                }
                if running.control_closed()? && running.child.version_group_gone()? {
                    return Ok(status);
                }
            }
            if Instant::now() >= until {
                // Owning cancellation is allowed; no status/clock can stand in
                // for confinement. Unknown closure keeps every actual owner.
                running.child.kill()?;
                let cleanup = Instant::now() + Duration::from_secs(5);
                loop {
                    if let Some(status) = running.child.try_wait()? {
                        running.observed_status = Some(status);
                        if running.confined.is_some()
                            && running.control_closed()?
                            && running.child.version_group_gone()?
                        {
                            return Err(io::ErrorKind::TimedOut.into());
                        }
                        return Err(invalid(
                            "timed-out version probe has unresolved descendant closure",
                        ));
                    }
                    if Instant::now() >= cleanup {
                        return Err(invalid("version probe owning reap remains unresolved"));
                    }
                    std::thread::sleep(POLL);
                }
            }
            std::thread::sleep(POLL);
        }
    }
    fn closed(&mut self) -> io::Result<bool> {
        let running =
            self.running.as_mut().ok_or_else(|| invalid("maintenance wait owner missing"))?;
        Ok((running.confined.is_some() || running.child.version_unstarted()?)
            && running.observed_status.is_some()
            && running.control_closed()?
            && running.child.version_group_gone()?)
    }
    fn cancel_confined(&mut self) -> Option<std::process::ExitStatus> {
        let running = self.running.as_mut()?;
        if running.confined.is_none() && !matches!(running.child.version_unstarted(), Ok(true)) {
            return running.observed_status;
        }
        if running.child.kill().is_err() {
            return running.observed_status;
        }
        let until = Instant::now() + Duration::from_secs(5);
        loop {
            match running.child.try_wait() {
                Ok(Some(status)) => {
                    running.observed_status = Some(status);
                    return Some(status);
                }
                Err(_) => return running.observed_status,
                Ok(None) => {}
            }
            if Instant::now() >= until {
                return running.observed_status;
            }
            std::thread::sleep(POLL);
        }
    }
    fn begin_maintenance(&mut self) -> io::Result<()> {
        let resources = self.resources.as_mut().expect("original resources");
        let lease =
            resources.lease.take().ok_or_else(|| invalid("original cache lease unavailable"))?;
        match MaintenanceLease::begin(lease) {
            Ok(held) => {
                resources.maintenance = Some(held);
                Ok(())
            }
            Err(held) => {
                let error = io::Error::other(held.to_string());
                resources.failed = Some(Box::new(held));
                Err(error)
            }
        }
    }
    fn binding(&self) -> io::Result<MaintenanceBinding> {
        let held = self
            .resources
            .as_ref()
            .and_then(|r| r.maintenance.as_ref())
            .ok_or_else(|| invalid("same withheld maintenance owner unavailable"))?;
        held.check_current()?;
        Ok(held.binding())
    }
    fn restore(&mut self, proof: NativeClosed) -> io::Result<()> {
        let resources = self.resources.as_mut().expect("same original resources");
        let held = resources
            .maintenance
            .take()
            .ok_or_else(|| invalid("same withheld maintenance owner unavailable"))?;
        match held.restore(proof) {
            Ok(lease) => {
                resources.lease = Some(lease);
                Ok(())
            }
            Err(held) => {
                let error = io::Error::other(held.to_string());
                resources.failed = Some(Box::new(held));
                Err(error)
            }
        }
    }
}
fn deadline() -> io::Result<Instant> {
    Instant::now().checked_add(MAX_PROBE).ok_or_else(|| invalid("version probe deadline overflow"))
}

impl Drop for Owner {
    fn drop(&mut self) {
        if self.running.is_none()
            && self.resources.as_ref().is_none_or(|r| r.maintenance.is_none() && r.failed.is_none())
        {
            return;
        }
        // A missing containment/reap fact never releases source/output/fixed
        // ownership. Durable withholding also survives producer death; failure
        // retains the original guarded transition rather than falling back.
        if let Some(mut running) = self.running.take() {
            // Signal only our still-owned unreaped child. An unobserved/failed
            // closure remains debt even when this cancellation succeeds.
            let _ = running.child.kill();
            std::mem::forget(running);
        }
        if let Some(mut resources) = self.resources.take() {
            if let Some(lease) = resources.lease.take() {
                match lease.into_withheld() {
                    Ok(owner) => std::mem::forget(owner),
                    Err(original) => std::mem::forget(original),
                }
            }
            std::mem::forget(resources);
        }
        let _ = writeln!(
            io::stderr().lock(),
            "native cache probe unresolved; actual original owners retained"
        );
    }
}

#[cfg(test)]
mod tests;
