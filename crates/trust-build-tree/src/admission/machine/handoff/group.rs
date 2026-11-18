//! Own one isolated original process group under the same original fixed claim.
//! The unreaped direct child anchors group identity while signals can be sent.
//! Other waiters must not reap this owner's child. Escaped sessions/groups and
//! arbitrary descendant closure require the separate native workload protocol.

use std::time::{Duration, Instant};

use super::*;
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
use crate::trust_repo_lock::management::exec::native;
use crate::trust_repo_lock::management::process;

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[path = "group/execution_start.rs"]
pub(super) mod execution_start;
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
pub use execution_start::ExecutionStartPipe;

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
struct NativeGroupInputs {
    image: NativeGroupImage,
    _scheduler: jobserver_utils::Jobserver,
    // The original supervisor serves SAME rights across unaware std execs.
    // No descriptor parser or endpoint is manufactured by an App descendant.
    _fixed_courier: jobserver_utils::FixedClaimHandoff,
    completion: Option<Result<(), (io::ErrorKind, String)>>,
}

/// Different original-input owners; neither variant supplies resource admission.
#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
enum NativeGroupImage {
    System(trust_resource_provenance::program::HeldSystemCommand),
    Produced(trust_resource_provenance::program::produced::HeldProducedExecution),
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
impl NativeGroupImage {
    fn program(&self) -> &Path {
        match self {
            Self::System(image) => image.program(),
            Self::Produced(image) => image.program(),
        }
    }
    fn validate(&self, deadline: Instant) -> io::Result<()> {
        match self {
            Self::System(image) => image.validate(deadline),
            Self::Produced(image) => image.validate(deadline),
        }
    }
    fn validate_loaded(
        &self,
        child: trust_resource_provenance::process::Identity,
        deadline: Instant,
    ) -> io::Result<()> {
        match self {
            Self::System(image) => image.validate_loaded(child, deadline),
            Self::Produced(image) => image.validate_loaded(child, deadline),
        }
    }
    fn check_environment(&self, command: &Command) -> io::Result<()> {
        use std::collections::BTreeMap;
        use std::os::unix::ffi::OsStrExt;
        let loader = |name: &OsStr| {
            name.as_bytes().starts_with(b"DYLD_") || name.as_bytes().starts_with(b"LD_")
        };
        let mut actual: BTreeMap<OsString, OsString> =
            std::env::vars_os().filter(|(name, _)| loader(name)).collect();
        for (name, value) in command.get_envs().filter(|(name, _)| loader(name)) {
            if let Some(value) = value {
                actual.insert(name.to_owned(), value.to_owned());
            } else {
                actual.remove(name);
            }
        }
        match self {
            Self::System(_) if !actual.is_empty() => {
                Err(invalid("native group refuses loader overrides"))
            }
            Self::System(_) => Ok(()),
            Self::Produced(image) => {
                if &actual != image.environment() {
                    return Err(invalid(
                        "produced native group differs from its original runtime environment",
                    ));
                }
                Ok(())
            }
        }
    }
}

#[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
impl NativeGroupInputs {
    fn completed(&mut self) -> io::Result<()> {
        let result = self.completion.get_or_insert_with(|| {
            self.image
                .validate(Instant::now() + ORIGINAL_TRANSACTION_WAIT)
                .map_err(|error| (error.kind(), error.to_string()))
        });
        match result {
            Ok(()) => Ok(()),
            Err((kind, message)) => Err(io::Error::new(*kind, message.clone())),
        }
    }
}

enum GroupChild {
    Standard(Child),
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    Native(native::Child),
}

impl GroupChild {
    fn id(&self) -> u32 {
        match self {
            Self::Standard(child) => child.id(),
            #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
            Self::Native(child) => child.id(),
        }
    }
    fn wait(&mut self) -> io::Result<ExitStatus> {
        match self {
            Self::Standard(child) => child.wait(),
            #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
            Self::Native(child) => child.wait(),
        }
    }
    fn take_stdout(&mut self) -> Option<std::process::ChildStdout> {
        match self {
            Self::Standard(child) => child.stdout.take(),
            #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
            Self::Native(_) => None,
        }
    }
    fn take_stderr(&mut self) -> Option<std::process::ChildStderr> {
        match self {
            Self::Standard(child) => child.stderr.take(),
            #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
            Self::Native(_) => None,
        }
    }
}

#[path = "group/relay.rs"]
mod relay;
use relay::SignalRelay;

const POLL: Duration = Duration::from_millis(10);
const CANCEL_WAIT: Duration = Duration::from_secs(5);

#[cfg(all(test, feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[derive(Clone, Copy, PartialEq, Eq)]
enum PreGoExit {
    BeforeIdentity,
    BeforeResume,
}

#[cfg(all(test, feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
thread_local! {
    static PRE_GO_EXIT: std::cell::Cell<Option<PreGoExit>> = const { std::cell::Cell::new(None) };
}

/// Signals the owning launcher can forward to its actual isolated group.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FixedCommandSignal {
    Interrupt,
    Terminate,
    Hangup,
}

impl FixedCommandSignal {
    fn raw(self) -> libc::c_int {
        match self {
            Self::Interrupt => libc::SIGINT,
            Self::Terminate => libc::SIGTERM,
            Self::Hangup => libc::SIGHUP,
        }
    }
}

/// Actual original-group owner. No PID, saved status or process census can
/// construct it. Keep it through the owning wait, group retirement and IO drain.
#[must_use = "retain original group and resource custody through actual retirement"]
pub struct RunningFixedGroup {
    claim: Option<FixedClaim>,
    _packet: File,
    child: Option<GroupChild>,
    group: libc::pid_t,
    status: Option<ExitStatus>,
    retired: bool,
    absence_error: Option<io::Error>,
    relay: Option<SignalRelay>,
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    native_inputs: Option<NativeGroupInputs>,
}

impl PreparedFixedCommand {
    #[cfg(all(test, feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    pub(super) unsafe fn spawn_loaded_output_fixture(
        self,
        image: trust_resource_provenance::program::HeldSystemCommand,
        scheduler: jobserver_utils::Jobserver,
        deadline: Instant,
    ) -> io::Result<RunningFixedGroup> {
        // SAFETY: only the isolated real-FD output fixture calls this private
        // test entry; its exact inherited-console/original-GNU contract holds.
        unsafe {
            self.spawn_loaded_group_checked(
                NativeGroupImage::System(image),
                scheduler,
                None,
                deadline,
                None,
            )
        }
    }
    /// Start the admitted orchestrator at its actual stopped-image GO boundary.
    /// The observer is lifecycle DATA only and never reaches the child. The
    /// same group owner retains CPU/GNU/image custody through real retirement.
    ///
    /// # Safety
    /// The caller supplies the SAME original GNU server, with its implicit
    /// continuation serially paused. The command uses inherited cwd/console
    /// stdio and environment plus explicit edits; no caller pre_exec, env_clear,
    /// arg0 or stdio/cwd redirection is supported. Only this preparation's own
    /// original-descriptor pre_exec is replaced by native inheritance actions.
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    pub unsafe fn spawn_loaded_group_with_signal_forwarding_before(
        self,
        image: trust_resource_provenance::program::HeldSystemCommand,
        scheduler: jobserver_utils::Jobserver,
        execution_start: Option<ExecutionStartPipe>,
        deadline: Instant,
    ) -> io::Result<RunningFixedGroup> {
        // SAFETY: the unchanged public caller contract applies to this exact
        // original system image and the same command/scheduler.
        unsafe {
            self.spawn_loaded_program_before(
                NativeGroupImage::System(image),
                scheduler,
                execution_start,
                deadline,
            )
        }
    }

    /// Execute a genuinely retained produced artifact under the same fixed
    /// claim. Its original output/SDK/runtime owners survive group retirement;
    /// path/hash observations cannot construct this input. Loader edits must
    /// equal that owner's complete retained startup environment.
    ///
    /// # Safety
    /// The caller must satisfy the same serial original-GNU and command-field
    /// contract as `spawn_loaded_group_with_signal_forwarding_before`, and must
    /// have positively retired every compiler writer before capturing `image`.
    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    pub unsafe fn spawn_loaded_produced_group_with_signal_forwarding_before(
        self,
        image: trust_resource_provenance::program::produced::HeldProducedExecution,
        scheduler: jobserver_utils::Jobserver,
        execution_start: Option<ExecutionStartPipe>,
        deadline: Instant,
    ) -> io::Result<RunningFixedGroup> {
        // SAFETY: the caller retains the actual produced-input owner and
        // satisfies the same original command and GNU continuation contract.
        unsafe {
            self.spawn_loaded_program_before(
                NativeGroupImage::Produced(image),
                scheduler,
                execution_start,
                deadline,
            )
        }
    }

    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    unsafe fn spawn_loaded_program_before(
        self,
        image: NativeGroupImage,
        scheduler: jobserver_utils::Jobserver,
        execution_start: Option<ExecutionStartPipe>,
        deadline: Instant,
    ) -> io::Result<RunningFixedGroup> {
        let deadline = deadline.min(Instant::now() + ORIGINAL_TRANSACTION_WAIT);
        let relay = SignalRelay::install()?;
        let interrupt = || {
            if relay.take().is_empty() {
                Ok(())
            } else {
                Err(io::Error::new(io::ErrorKind::Interrupted, "interrupted before native GO"))
            }
        };
        interrupt()?;
        match self.claim.observe_native_room_before(deadline, interrupt)? {
            LegacyFixedRoom::Fits { .. } => {}
            room => {
                return Err(io::Error::new(
                    io::ErrorKind::WouldBlock,
                    format!("native fixed group prelaunch refused: {room:?}"),
                ));
            }
        }
        // SAFETY: the same caller contract above applies; no command field is
        // changed after the ordinary actual-room check.
        unsafe {
            self.spawn_loaded_group_checked(
                image,
                scheduler,
                execution_start,
                deadline,
                Some(relay),
            )
        }
    }

    #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    unsafe fn spawn_loaded_group_checked(
        mut self,
        image: NativeGroupImage,
        scheduler: jobserver_utils::Jobserver,
        execution_start: Option<ExecutionStartPipe>,
        deadline: Instant,
        relay: Option<SignalRelay>,
    ) -> io::Result<RunningFixedGroup> {
        use std::os::fd::AsRawFd;
        self.claim.check_current()?;
        if self.command.get_program() != image.program().as_os_str() {
            return Err(invalid("native group differs from the same held image"));
        }
        image.check_environment(&self.command)?;
        let original_gnu = scheduler.retain_transport_descriptors()?;
        let execution_start = execution_start
            .map(|pipe| {
                execution_start::ExecutionStart::capture(
                    pipe,
                    self.original_descriptors
                        .iter()
                        .copied()
                        .chain(original_gnu.iter().map(AsRawFd::as_raw_fd)),
                )
            })
            .transpose()?;
        if let Some(quiet) = self.quiet.as_mut() {
            quiet.check(&self.claim)?;
        }
        image.validate(deadline)?;
        let mut originals = original_entries(&self.claim)?
            .iter()
            .map(|entry| {
                trust_build_cpu::duplicate_descriptor(OsStr::new(&entry.descriptor.to_string()))
                    .map(Into::into)
            })
            .collect::<io::Result<Vec<std::os::fd::OwnedFd>>>()?;
        let output = self.claim.output.as_ref().map(output_member::Issued::wire).transpose()?;
        if let Some(output) = &output {
            for fd in output.descriptors() {
                originals.push(
                    trust_build_cpu::duplicate_descriptor(OsStr::new(&fd.to_string()))?.into(),
                );
            }
        }
        let packet = self.packet.try_clone()?.into();
        let courier = if output.is_some() {
            jobserver_utils::FixedClaimHandoff::new_with_output_member(packet, originals)?
        } else {
            jobserver_utils::FixedClaimHandoff::new(packet, originals)?
        };
        self.command.env(jobserver_utils::FIXED_CLAIM_HANDOFF_ENV, courier.advertisement());
        self.command.env(FIXED_HANDOFF_ENV, "requires-live-ancestor-v1");
        self.claim.check_current()?;
        let child = native::Child::spawn_group_suspended(
            &self.command,
            &scheduler,
            &self.original_descriptors,
            deadline,
        )?;
        let group = child.id() as libc::pid_t;
        // Install the actual child/group owner before any fallible observation:
        // every error below kills the still-stopped group and retires it using
        // the same existing bounded cancellation, never TERM-only waiting.
        let mut owner = RunningFixedGroup {
            claim: Some(self.claim),
            _packet: self.packet,
            child: Some(GroupChild::Native(child)),
            group,
            status: None,
            retired: false,
            absence_error: None,
            relay,
            native_inputs: Some(NativeGroupInputs {
                image,
                _scheduler: scheduler,
                _fixed_courier: courier,
                completion: None,
            }),
        };
        #[cfg(test)]
        owner.fixture_exit_before_go(PreGoExit::BeforeIdentity, deadline)?;
        let identity = match owner.child_mut() {
            GroupChild::Native(child) => child.stopped_group_identity(deadline)?,
            GroupChild::Standard(_) => unreachable!("native child installed above"),
        };
        owner
            .native_inputs
            .as_ref()
            .expect("same original native inputs")
            .image
            .validate_loaded(identity, deadline)?;
        owner.claim.as_ref().expect("same original claim").check_current()?;
        if owner.relay.as_ref().is_some_and(|relay| !relay.take().is_empty()) {
            return Err(io::Error::new(io::ErrorKind::Interrupted, "interrupted before native GO"));
        }
        if let Some(observer) = execution_start {
            observer.notify(identity.pid, deadline)?;
        }
        #[cfg(test)]
        owner.fixture_exit_before_go(PreGoExit::BeforeResume, deadline)?;
        match owner.child_mut() {
            GroupChild::Native(child) => child.resume_group(identity, deadline)?,
            GroupChild::Standard(_) => unreachable!("same original native child"),
        }
        owner.claim.as_mut().expect("same original claim").release_prelaunch_admission();
        Ok(owner)
    }

    /// Launch in a new session and original process group, retaining the same
    /// complete fixed resource claim. No existing group can be named or joined.
    pub fn spawn_group(self) -> io::Result<RunningFixedGroup> {
        match self
            .claim
            .observe_native_room_before(Instant::now() + ORIGINAL_TRANSACTION_WAIT, || Ok(()))?
        {
            LegacyFixedRoom::Fits { .. } => self.spawn_group_checked(),
            room => Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                format!("native fixed group prelaunch refused: {room:?}"),
            )),
        }
    }

    /// A standalone launcher's scoped INT/TERM/HUP relay. Only one relay can
    /// be live in this process; existing application handlers are not replaced.
    pub fn spawn_group_with_signal_forwarding(self) -> io::Result<RunningFixedGroup> {
        self.spawn_group_with_signal_forwarding_before(Instant::now() + ORIGINAL_TRANSACTION_WAIT)
    }

    /// Retain the same unlaunched claim through transient manifest contention.
    /// The existing metadata bound and caller's remaining queue deadline both
    /// apply. Unknown or over-capacity observations never authorize a launch.
    pub fn spawn_group_with_signal_forwarding_before(
        self,
        deadline: Instant,
    ) -> io::Result<RunningFixedGroup> {
        let relay = SignalRelay::install()?;
        let interrupt = || {
            if relay.take().is_empty() {
                Ok(())
            } else {
                Err(io::Error::new(
                    io::ErrorKind::Interrupted,
                    "interrupted before original group launch",
                ))
            }
        };
        interrupt()?;
        match self.claim.observe_native_room_before(
            deadline.min(Instant::now() + ORIGINAL_TRANSACTION_WAIT),
            interrupt,
        )? {
            LegacyFixedRoom::Fits { .. } => self.spawn_with_relay_checked(relay),
            room => Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                format!("native fixed group prelaunch refused: {room:?}"),
            )),
        }
    }

    #[cfg(test)]
    fn spawn_with_forwarder_checked(self) -> io::Result<RunningFixedGroup> {
        let relay = SignalRelay::install()?;
        self.spawn_with_relay_checked(relay)
    }

    fn spawn_with_relay_checked(self, relay: SignalRelay) -> io::Result<RunningFixedGroup> {
        if !relay.take().is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "interrupted before original group launch",
            ));
        }
        let mut group = self.spawn_group_checked()?;
        group.relay = Some(relay);
        Ok(group)
    }

    pub(super) fn spawn_group_checked(mut self) -> io::Result<RunningFixedGroup> {
        let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
        // SAFETY: observe the current complete disposition before any child
        // delivery. Autoreaping/custom waiters cannot anchor this owner.
        if unsafe { libc::sigaction(libc::SIGCHLD, std::ptr::null(), &mut action) } != 0 {
            return Err(io::Error::last_os_error());
        }
        if action.sa_sigaction != libc::SIG_DFL || action.sa_flags & libc::SA_NOCLDWAIT != 0 {
            return Err(invalid(
                "native original group requires default waitable SIGCHLD handling",
            ));
        }
        // SAFETY: setsid is async-signal-safe. It runs after the earlier
        // original-descriptor setup and fails spawn if isolation is refused.
        unsafe {
            self.command.pre_exec(|| {
                if libc::setsid() < 0 { Err(io::Error::last_os_error()) } else { Ok(()) }
            });
        }
        let spawned = self.launch_checked()?;
        // Unix child IDs are positive pid_t values returned by the kernel.
        let group = spawned.child.id() as libc::pid_t;
        if group <= 0 {
            // Do not release room or signal a numeric group on an impossible
            // identity. Preserve the actual original claim for process lifetime.
            std::mem::forget(spawned.claim);
            return Err(invalid("native child process group is not a positive pid_t"));
        }
        Ok(RunningFixedGroup {
            claim: Some(spawned.claim),
            _packet: spawned.packet,
            child: Some(GroupChild::Standard(spawned.child)),
            group,
            status: None,
            retired: false,
            absence_error: None,
            relay: None,
            #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
            native_inputs: None,
        })
    }
}

impl RunningFixedGroup {
    #[cfg(all(test, feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
    fn fixture_exit_before_go(&mut self, point: PreGoExit, deadline: Instant) -> io::Result<()> {
        let kill = PRE_GO_EXIT.with(|fault| {
            if fault.get() == Some(point) {
                fault.set(None);
                true
            } else {
                false
            }
        });
        if kill {
            match self.child_mut() {
                GroupChild::Native(child) => child.kill()?,
                GroupChild::Standard(_) => unreachable!("native-only fixture point"),
            }
            while !self.leader_exited()? {
                if Instant::now() >= deadline {
                    return Err(io::ErrorKind::TimedOut.into());
                }
                std::thread::sleep(POLL);
            }
        }
        Ok(())
    }

    fn child(&self) -> &GroupChild {
        self.child.as_ref().expect("original group child retained through retirement")
    }

    fn child_mut(&mut self) -> &mut GroupChild {
        self.child.as_mut().expect("original group child retained through retirement")
    }

    pub fn id(&self) -> u32 {
        self.child().id()
    }

    pub fn take_stdout(&mut self) -> Option<std::process::ChildStdout> {
        self.child_mut().take_stdout()
    }

    pub fn take_stderr(&mut self) -> Option<std::process::ChildStderr> {
        self.child_mut().take_stderr()
    }

    /// Forward only while the actual child remains this owner's unreaped group
    /// anchor. A stolen wait or already-reaped leader never authorizes a signal.
    pub fn forward_signal(&mut self, signal: FixedCommandSignal) -> io::Result<()> {
        self.signal(signal.raw())
    }

    fn signal(&mut self, signal: libc::c_int) -> io::Result<()> {
        if self.retired {
            return Ok(());
        }
        if self.status.is_some() {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "original group anchor was already reaped; no group signal sent",
            ));
        }
        let _ = self.leader_exited()?;
        // SAFETY: this owner created this isolated group with setsid; its
        // direct child remains unreaped. No caller-supplied PID selects it.
        if unsafe { libc::kill(-self.group, signal) } == 0 {
            Ok(())
        } else {
            let error = io::Error::last_os_error();
            #[cfg(test)]
            eprintln!("original group {} actual signal {signal}: {error}", self.group);
            Err(error)
        }
    }

    fn leader_exited(&self) -> io::Result<bool> {
        loop {
            let mut info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
            // SAFETY: initialized writable siginfo; WNOWAIT preserves the
            // original child anchor and WNOHANG does not wait on other jobs.
            let result = unsafe {
                libc::waitid(
                    libc::P_PID,
                    self.child().id() as libc::id_t,
                    info.as_mut_ptr(),
                    libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
                )
            };
            if result == 0 {
                // SAFETY: success initialized siginfo, including the no-event
                // zero PID. No exit status is fabricated from the observation.
                let info = unsafe { info.assume_init() };
                // SAFETY: successful waitid initialized this siginfo observation.
                let observed = unsafe { info.si_pid() };
                return if observed == 0 {
                    Ok(false)
                } else if observed == self.group {
                    // A reported child is not necessarily terminal. In
                    // particular, Darwin can report the initial exec stop;
                    // never enter a blocking owning wait for that event.
                    match info.si_code {
                        libc::CLD_EXITED | libc::CLD_KILLED | libc::CLD_DUMPED => Ok(true),
                        libc::CLD_STOPPED | libc::CLD_CONTINUED | libc::CLD_TRAPPED => Ok(false),
                        _ => Err(invalid("unknown original child wait event")),
                    }
                } else {
                    Err(invalid("owning wait observed another child"))
                };
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                #[cfg(test)]
                eprintln!("original group {} actual waitid: {error}", self.group);
                return Err(error);
            }
        }
    }

    fn group_gone(&mut self) -> io::Result<bool> {
        debug_assert!(self.status.is_some(), "absence follows the original owning reap");
        // Signal zero is observation only. After reap, no numeric group signal
        // is permitted. Permission denial is not positive absence: retain both
        // the SAME claim and actual error while bounded cancellation polls.
        let result = absence_probe(self.group);
        match result {
            Ok(()) => Ok(false),
            Err(error) if error.raw_os_error() == Some(libc::ESRCH) => {
                self.absence_error = None;
                Ok(true)
            }
            Err(error) if error.raw_os_error() == Some(libc::EPERM) => {
                self.absence_error = Some(error);
                Ok(false)
            }
            Err(error) => Err(error),
        }
    }

    fn poll_retirement(&mut self) -> io::Result<Option<ExitStatus>> {
        if self.retired {
            return Ok(self.status);
        }
        if self.status.is_none() {
            if !self.leader_exited()? {
                return Ok(None);
            }
            let members = process::group_pids(self.child().id()).inspect_err(|error| {
                #[cfg(test)]
                eprintln!("original group {} actual proc_listpids: {error}", self.group);
                #[cfg(not(test))]
                let _ = error;
            })?;
            if members.iter().any(|pid| *pid != self.child().id()) {
                return Ok(None);
            }
            self.status = Some(self.child_mut().wait().inspect_err(|error| {
                #[cfg(test)]
                eprintln!("original group {} actual owning wait: {error}", self.group);
                #[cfg(not(test))]
                let _ = error;
            })?);
        }
        // Enumeration can race a final fork/exit. Releasing capacity requires
        // the actual post-reap kernel absence probe, not that earlier census.
        if self.group_gone()? {
            self.retired = true;
            Ok(self.status)
        } else {
            Ok(None)
        }
    }

    /// The direct child's status is returned only after original group absence.
    /// This does not settle a descendant that escaped into another group/session.
    pub fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
        self.claim.as_ref().expect("live original group claim").check_current()?;
        let signals = self.relay.as_ref().map(SignalRelay::take).unwrap_or_default();
        for signal in signals {
            if let Err(error) = self.forward_signal(signal) {
                return match self.poll_retirement()? {
                    Some(status) => self.completed_terminal(Some(status)),
                    None => Err(error),
                };
            }
        }
        let terminal = self.poll_retirement()?;
        self.completed_terminal(terminal)
    }

    fn completed_terminal(
        &mut self,
        terminal: Option<ExitStatus>,
    ) -> io::Result<Option<ExitStatus>> {
        #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
        if terminal.is_some() {
            if let Some(inputs) = self.native_inputs.as_mut() {
                inputs.completed()?;
            }
        }
        Ok(terminal)
    }

    pub fn wait(&mut self) -> io::Result<ExitStatus> {
        loop {
            if let Some(status) = self.try_wait()? {
                return Ok(status);
            }
            std::thread::sleep(POLL);
        }
    }

    /// Cancel this original group and retain resources through actual group
    /// retirement. Record/path validation cannot prevent owned cancellation.
    pub fn cancel(&mut self) -> io::Result<ExitStatus> {
        if self.retired {
            return Ok(self.status.expect("retired original group status"));
        }
        if let Some(status) = self.poll_retirement()? {
            return Ok(status);
        }
        if self.status.is_none() {
            if let Err(error) = self.signal(libc::SIGKILL) {
                return match self.poll_retirement()? {
                    Some(status) => Ok(status),
                    None => Err(error),
                };
            }
        }
        let deadline = Instant::now() + CANCEL_WAIT;
        loop {
            if let Some(status) = self.poll_retirement()? {
                return Ok(status);
            }
            if Instant::now() >= deadline {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    match self.absence_error.take() {
                        Some(error) => format!(
                            "original group retirement unknown; native absence observation: {error}"
                        ),
                        None => "original group retirement unknown".to_owned(),
                    },
                ));
            }
            std::thread::sleep(POLL);
        }
    }
}

fn absence_probe(group: libc::pid_t) -> io::Result<()> {
    #[cfg(test)]
    if ABSENCE_FAULT.with(|fault| match fault.get() {
        Some((expected, remaining)) if expected == group && remaining > 0 => {
            fault.set(Some((expected, remaining - 1)));
            true
        }
        _ => false,
    }) {
        return Err(io::Error::from_raw_os_error(libc::EPERM));
    }
    // SAFETY: read-only existence probe; never a post-reap delivery signal.
    if unsafe { libc::kill(-group, 0) } == 0 { Ok(()) } else { Err(io::Error::last_os_error()) }
}

#[cfg(test)]
thread_local! {
    static ABSENCE_FAULT: std::cell::Cell<Option<(libc::pid_t, usize)>> = const { std::cell::Cell::new(None) };
}

impl Drop for RunningFixedGroup {
    fn drop(&mut self) {
        if let Err(error) = self.cancel() {
            if let Some(claim) = self.claim.take() {
                std::mem::forget(claim);
            }
            // Native direct-child Drop intentionally waits indefinitely on an
            // unknown owning wait. The GROUP owner already applied its bounded
            // kill/retirement protocol; retain that actual child too instead of
            // starting a second unbounded wait after its terminal refusal.
            if let Some(child) = self.child.take() {
                std::mem::forget(child);
            }
            #[cfg(all(feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
            if let Some(inputs) = self.native_inputs.take() {
                std::mem::forget(inputs);
            }
            let _ = writeln!(
                io::stderr().lock(),
                "native original group retirement unknown; actual resources retained: {error}"
            );
        }
    }
}

#[cfg(test)]
#[path = "group/tests.rs"]
pub(super) mod tests;

#[cfg(all(test, feature = "native-exec", target_os = "macos", target_arch = "aarch64"))]
#[path = "group/loaded_tests.rs"]
pub(super) mod loaded_tests;
