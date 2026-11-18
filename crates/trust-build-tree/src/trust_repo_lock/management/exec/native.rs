//! One direct child's original stopped launch and owning wait. Ordinary exec
//! retains its original group. The private cache-maintenance profile alone
//! creates its owned session leader, retaining the same actual resource FDs.
//! No resource claim, generic pre-exec callback or reconstructed Child is used.

use std::collections::BTreeMap;
use std::ffi::{CString, OsString};
use std::io;
use std::os::fd::AsRawFd as _;
use std::os::unix::ffi::OsStrExt as _;
use std::os::unix::process::ExitStatusExt as _;
use std::process::{Command, ExitStatus};
use std::time::{Duration, Instant};

use jobserver_utils::Jobserver;
use trust_resource_provenance::process::{self, Identity};

unsafe extern "C" {
    // Public Darwin spawn.h extension. Same-number dup2 does not override
    // FD_CLOEXEC under CLOEXEC_DEFAULT; original inheritance must be explicit.
    fn posix_spawn_file_actions_addinherit_np(
        actions: *mut libc::posix_spawn_file_actions_t,
        fd: libc::c_int,
    ) -> libc::c_int;
    fn posix_spawn_file_actions_addfchdir_np(
        actions: *mut libc::posix_spawn_file_actions_t,
        directory: libc::c_int,
    ) -> libc::c_int;
}

fn check(code: libc::c_int) -> io::Result<()> {
    if code == 0 { Ok(()) } else { Err(io::Error::from_raw_os_error(code)) }
}

fn time(deadline: Instant) -> io::Result<()> {
    if Instant::now() >= deadline { Err(io::ErrorKind::TimedOut.into()) } else { Ok(()) }
}

fn cstring(value: &std::ffi::OsStr) -> io::Result<CString> {
    CString::new(value.as_bytes()).map_err(|_| io::ErrorKind::InvalidInput.into())
}

struct Objects {
    actions: libc::posix_spawn_file_actions_t,
    attributes: libc::posix_spawnattr_t,
}

impl Objects {
    fn new() -> io::Result<Self> {
        let mut actions = std::mem::MaybeUninit::uninit();
        let mut attributes = std::mem::MaybeUninit::uninit();
        // SAFETY: the initializers write their opaque objects once.
        unsafe {
            check(libc::posix_spawn_file_actions_init(actions.as_mut_ptr()))?;
            if let Err(error) = check(libc::posix_spawnattr_init(attributes.as_mut_ptr())) {
                libc::posix_spawn_file_actions_destroy(actions.as_mut_ptr());
                return Err(error);
            }
            Ok(Self { actions: actions.assume_init(), attributes: attributes.assume_init() })
        }
    }

    fn inherit(&mut self, fd: libc::c_int) -> io::Result<()> {
        // SAFETY: initialized exclusive actions. Explicit Darwin inheritance
        // keeps this original without changing the parent's descriptor flags.
        unsafe { check(posix_spawn_file_actions_addinherit_np(&mut self.actions, fd)) }
    }
}

impl Drop for Objects {
    fn drop(&mut self) {
        // SAFETY: both objects were initialized and remain exclusively owned.
        unsafe {
            libc::posix_spawn_file_actions_destroy(&mut self.actions);
            libc::posix_spawnattr_destroy(&mut self.attributes);
        }
    }
}

#[cfg(test)]
std::thread_local! {
    static EXPIRE_VERSION_OBSERVATION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static EXPIRE_VERSION_GO: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static VERSION_EXPIRY_REACHED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
#[cfg(test)]
fn expire_after_native_observation(enabled: bool, deadline: Instant) {
    if enabled {
        VERSION_EXPIRY_REACHED.set(true);
        while Instant::now() < deadline {
            std::thread::sleep(
                Duration::from_millis(1).min(deadline.saturating_duration_since(Instant::now())),
            );
        }
    }
}

/// A private original posix_spawn child. It is never built from a caller PID.
/// This is the sole wait owner; stop/image observations never invent a terminal.
pub(crate) enum VersionSpawnError {
    NotSpawned(io::Error),
    Unresolved(io::Error),
}

pub(crate) struct Child {
    pid: libc::pid_t,
    owner: u32,
    status: Option<ExitStatus>,
    resumed: bool,
    version_group: bool,
}

#[derive(Clone, Copy)]
enum Launch {
    Ordinary,
    Version,
    Group,
    OutputDirectory(libc::c_int),
}

#[derive(Clone, Copy)]
enum TerminalObservation {
    OwningWait,
    PreserveGroupAnchor,
}

impl Child {
    /// Only the native ordinary/nested builders call this: inherited console
    /// stdio, exact argv/environment and no arbitrary std::Command pre_exec.
    pub(crate) fn spawn_suspended(
        command: &Command,
        scheduler: &Jobserver,
        deadline: Instant,
    ) -> io::Result<Self> {
        Self::spawn_with_originals(command, scheduler, &[], Launch::Ordinary, deadline, &mut false)
    }

    /// The fixed continuation retains this actual member directory through
    /// the child wait. No pathname or ambient cwd substitutes for fchdir.
    pub(crate) fn spawn_output_member_suspended(
        command: &Command,
        scheduler: &Jobserver,
        directory: std::os::fd::BorrowedFd<'_>,
        deadline: Instant,
    ) -> io::Result<Self> {
        Self::spawn_with_originals(
            command,
            scheduler,
            &[],
            Launch::OutputDirectory(directory.as_raw_fd()),
            deadline,
            &mut false,
        )
    }

    /// The fixed-group owner retains the actual stopped child before any
    /// fallible observation, then owns group cancellation and the sole wait.
    pub(crate) fn spawn_group_suspended(
        command: &Command,
        scheduler: &Jobserver,
        originals: &[i32],
        deadline: Instant,
    ) -> io::Result<Self> {
        Self::spawn_with_originals(
            command,
            scheduler,
            originals,
            Launch::Group,
            deadline,
            &mut false,
        )
    }

    /// Closed cache-version prelude only. The extra descriptor is its actual
    /// original controller socket, not a caller-selected resource/grant. Probe
    /// stdout joins original stderr so the owning CLI's JSON stdout stays clean.
    pub(crate) fn spawn_version_prelude(
        command: &Command,
        scheduler: &Jobserver,
        control: std::os::fd::BorrowedFd<'_>,
        originals: &[std::os::fd::BorrowedFd<'_>],
        deadline: Instant,
    ) -> Result<Self, VersionSpawnError> {
        let originals = std::iter::once(control.as_raw_fd())
            .chain(originals.iter().map(|fd| fd.as_raw_fd()))
            .collect::<Vec<_>>();
        let mut launched = false;
        Self::spawn_with_originals(
            command,
            scheduler,
            &originals,
            Launch::Version,
            deadline,
            &mut launched,
        )
        .map_err(|error| {
            if launched {
                VersionSpawnError::Unresolved(error)
            } else {
                VersionSpawnError::NotSpawned(error)
            }
        })
    }

    fn spawn_with_originals(
        command: &Command,
        scheduler: &Jobserver,
        extra: &[i32],
        launch: Launch,
        deadline: Instant,
        launched: &mut bool,
    ) -> io::Result<Self> {
        time(deadline)?;
        if command.get_current_dir().is_some() {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "native exec uses original cwd",
            ));
        }
        let mut disposition = unsafe { std::mem::zeroed::<libc::sigaction>() };
        // SAFETY: observe SIGCHLD without changing any disposition.
        if unsafe { libc::sigaction(libc::SIGCHLD, std::ptr::null(), &mut disposition) } != 0 {
            return Err(io::Error::last_os_error());
        }
        if disposition.sa_sigaction != libc::SIG_DFL
            || disposition.sa_flags & libc::SA_NOCLDWAIT != 0
        {
            return Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "native exec requires its original waitable child",
            ));
        }
        let path = cstring(command.get_program())?;
        let mut args = vec![path.clone()];
        args.extend(command.get_args().map(cstring).collect::<io::Result<Vec<_>>>()?);
        let mut environment: BTreeMap<OsString, OsString> = std::env::vars_os().collect();
        for (name, value) in command.get_envs() {
            match value {
                Some(value) => {
                    environment.insert(name.to_owned(), value.to_owned());
                }
                None => {
                    environment.remove(name);
                }
            }
        }
        let environment = environment
            .into_iter()
            .map(|(name, value)| {
                let mut bytes = name.as_bytes().to_vec();
                bytes.push(b'=');
                bytes.extend_from_slice(value.as_bytes());
                CString::new(bytes).map_err(|_| io::ErrorKind::InvalidInput.into())
            })
            .collect::<io::Result<Vec<_>>>()?;
        let pointers = |values: &[CString]| {
            values
                .iter()
                .map(|s| s.as_ptr().cast_mut())
                .chain(std::iter::once(std::ptr::null_mut()))
                .collect::<Vec<_>>()
        };
        let argv = pointers(&args);
        let envp = pointers(&environment);
        let mut objects = Objects::new()?;
        for fd in 0..3 {
            objects.inherit(fd)?;
        }
        if let Launch::OutputDirectory(directory) = launch {
            if directory < 3 {
                return Err(io::ErrorKind::InvalidInput.into());
            }
            objects.inherit(directory)?;
            // SAFETY: initialized private actions and the same actual held
            // directory. Only the new child changes cwd, before selected exec.
            unsafe {
                check(posix_spawn_file_actions_addfchdir_np(&mut objects.actions, directory))?;
            }
        }
        for fd in extra {
            if *fd < 3 {
                return Err(io::ErrorKind::InvalidInput.into());
            }
            objects.inherit(*fd)?;
        }
        if matches!(launch, Launch::Version) {
            // SAFETY: exclusive initialized actions; neither parent FD nor OFD
            // is changed. No generic stdio/pre_exec callback is admitted.
            unsafe {
                check(libc::posix_spawn_file_actions_adddup2(&mut objects.actions, 2, 1))?;
            }
        }
        if let Some(originals) = scheduler.pipe_descriptors() {
            for original in originals {
                if original.as_raw_fd() < 3 {
                    return Err(io::ErrorKind::InvalidInput.into());
                }
                objects.inherit(original.as_raw_fd())?;
            }
        }
        let mut defaults = unsafe { std::mem::zeroed::<libc::sigset_t>() };
        // SAFETY: writable initialized local signal set, then initialized
        // attributes. Ordinary execution retains the actual outer group;
        // private cache maintenance alone requests its owned session leader.
        unsafe {
            if libc::sigemptyset(&mut defaults) != 0
                || libc::sigaddset(&mut defaults, libc::SIGPIPE) != 0
            {
                return Err(io::Error::last_os_error());
            }
            check(libc::posix_spawnattr_setsigdefault(&mut objects.attributes, &defaults))?;
            check(libc::posix_spawnattr_setflags(
                &mut objects.attributes,
                (libc::POSIX_SPAWN_START_SUSPENDED
                    | libc::POSIX_SPAWN_CLOEXEC_DEFAULT
                    | libc::POSIX_SPAWN_SETSIGDEF
                    // Darwin's public spawn.h POSIX_SPAWN_SETSID. Only the
                    // private maintenance owner supports this new subgroup.
                    | if matches!(launch, Launch::Version | Launch::Group) { 0x0400 } else { 0 })
                    as libc::c_short,
            ))?;
        }
        time(deadline)?;
        let mut pid = 0;
        // SAFETY: complete NUL-terminated vectors/objects outlive this call.
        // No pathname/PATH fallback and no code in the target can run yet.
        check(unsafe {
            libc::posix_spawn(
                &mut pid,
                path.as_ptr(),
                &objects.actions,
                &objects.attributes,
                argv.as_ptr(),
                envp.as_ptr(),
            )
        })?;
        *launched = true;
        if pid <= 0 {
            return Err(io::Error::other("native spawn returned no original child"));
        }
        let child = Self {
            pid,
            owner: std::process::id(),
            status: None,
            resumed: false,
            version_group: matches!(launch, Launch::Version),
        };
        // The cache probe immediately installs this original Child in its
        // retaining owner. A post-spawn deadline error must not lose that
        // ownership or enter the ordinary Child Drop wait on this path.
        if matches!(launch, Launch::Ordinary) {
            time(deadline)?;
        }
        Ok(child)
    }

    fn custody(&self) -> io::Result<()> {
        if self.owner == std::process::id() {
            Ok(())
        } else {
            Err(io::Error::new(io::ErrorKind::PermissionDenied, "forked child owner"))
        }
    }

    pub(crate) fn stopped_identity(&mut self, deadline: Instant) -> io::Result<Identity> {
        self.stopped_identity_with(deadline, TerminalObservation::OwningWait)
    }

    pub(crate) fn stopped_group_identity(&mut self, deadline: Instant) -> io::Result<Identity> {
        self.stopped_identity_with(deadline, TerminalObservation::PreserveGroupAnchor)
    }

    fn stopped_identity_with(
        &mut self,
        deadline: Instant,
        observation: TerminalObservation,
    ) -> io::Result<Identity> {
        self.custody()?;
        if self.resumed {
            return Err(io::Error::other("original child is not awaiting GO"));
        }
        let terminal = match observation {
            TerminalObservation::OwningWait => self.try_wait()?.is_some(),
            TerminalObservation::PreserveGroupAnchor => self.group_terminal_pending(deadline)?,
        };
        if terminal {
            return Err(io::Error::other("original child is not awaiting GO"));
        }
        time(deadline)?;
        let identity = process::read_identity(self.pid as u32)?;
        let mut info = std::mem::MaybeUninit::<libc::proc_bsdinfo>::uninit();
        let size = std::mem::size_of::<libc::proc_bsdinfo>() as libc::c_int;
        // SAFETY: exact public BSD-info buffer for this original unreaped child.
        let count = unsafe {
            libc::proc_pidinfo(self.pid, libc::PROC_PIDTBSDINFO, 0, info.as_mut_ptr().cast(), size)
        };
        super::super::process::proc_info_count(
            count,
            size,
            "incomplete native stopped-child observation",
        )?;
        let info = unsafe { info.assume_init() };
        if info.pbi_pid != self.pid as u32
            || info.pbi_status != libc::SSTOP
            || process::read_identity(self.pid as u32)? != identity
        {
            return Err(io::Error::other("original loaded child is not stopped"));
        }
        time(deadline)?;
        Ok(identity)
    }

    pub(crate) fn resume(&mut self, identity: Identity, deadline: Instant) -> io::Result<()> {
        self.resume_with(identity, deadline, TerminalObservation::OwningWait)
    }

    pub(crate) fn resume_group(&mut self, identity: Identity, deadline: Instant) -> io::Result<()> {
        self.resume_with(identity, deadline, TerminalObservation::PreserveGroupAnchor)
    }

    fn resume_with(
        &mut self,
        identity: Identity,
        deadline: Instant,
        observation: TerminalObservation,
    ) -> io::Result<()> {
        if self.stopped_identity_with(deadline, observation)? != identity {
            return Err(io::Error::other("original stopped child changed before GO"));
        }
        time(deadline)?;
        // SAFETY: our original unreaped child, never a caller-selected PID.
        if unsafe { libc::kill(self.pid, libc::SIGCONT) } != 0 {
            return Err(io::Error::last_os_error());
        }
        self.resumed = true;
        Ok(())
    }

    fn group_terminal_pending(&self, deadline: Instant) -> io::Result<bool> {
        self.custody()?;
        if self.status.is_some() {
            return Err(io::Error::other("original group anchor was already reaped"));
        }
        loop {
            time(deadline)?;
            let mut info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
            // SAFETY: observe only this actual original child. WNOWAIT keeps
            // its terminal anchor for the group owner's sole owning wait.
            let result = unsafe {
                libc::waitid(
                    libc::P_PID,
                    self.pid as libc::id_t,
                    info.as_mut_ptr(),
                    libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
                )
            };
            if result == 0 {
                // SAFETY: successful waitid initialized the observation.
                let info = unsafe { info.assume_init() };
                // SAFETY: successful waitid initialized this siginfo observation.
                let observed = unsafe { info.si_pid() };
                return if observed == 0 {
                    Ok(false)
                } else if observed == self.pid {
                    // Preserve the actual stopped anchor: a nonterminal
                    // exec-stop event is not an owning-wait permission.
                    match info.si_code {
                        libc::CLD_EXITED | libc::CLD_KILLED | libc::CLD_DUMPED => Ok(true),
                        libc::CLD_STOPPED | libc::CLD_CONTINUED | libc::CLD_TRAPPED => Ok(false),
                        _ => Err(io::Error::other("unknown original group child wait event")),
                    }
                } else {
                    Err(io::Error::other("group observation named another child"))
                };
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        }
    }

    pub(crate) fn id(&self) -> u32 {
        self.pid as u32
    }

    /// Observe an actual second exec stop without reaping the original child.
    /// Only its new exec version may differ from the retained initial identity.
    pub(crate) fn version_exec_stop(
        &self,
        initial: Identity,
        deadline: Instant,
    ) -> io::Result<Option<Identity>> {
        self.custody()?;
        time(deadline)?;
        if !self.resumed || self.status.is_some() {
            return Err(io::Error::other("version prelude has no original unreaped execution"));
        }
        let identity = process::read_identity(self.id())?;
        if identity.pid != initial.pid
            || identity.birth != initial.birth
            || identity.unique_id != initial.unique_id
            || identity.parent != initial.parent
            || identity.parent_unique_id != initial.parent_unique_id
        {
            return Err(io::Error::other("version prelude changed original process identity"));
        }
        let mut info = std::mem::MaybeUninit::<libc::proc_bsdinfo>::uninit();
        let size = std::mem::size_of::<libc::proc_bsdinfo>() as libc::c_int;
        let count = unsafe {
            libc::proc_pidinfo(self.pid, libc::PROC_PIDTBSDINFO, 0, info.as_mut_ptr().cast(), size)
        };
        super::super::process::proc_info_count(
            count,
            size,
            "incomplete native version-exec observation",
        )?;
        let info = unsafe { info.assume_init() };
        if info.pbi_pid != self.id() || process::read_identity(self.id())? != identity {
            return Err(io::Error::other("version exec stop changed during observation"));
        }
        #[cfg(test)]
        expire_after_native_observation(EXPIRE_VERSION_OBSERVATION.get(), deadline);
        time(deadline)?;
        if info.pbi_status != libc::SSTOP || identity.exec_version == initial.exec_version {
            return Ok(None);
        }
        Ok(Some(identity))
    }

    /// The closed cache-probe owner alone calls this after independently
    /// checking the same stopped compiler image AND native no-fork policy.
    pub(crate) fn resume_version_target(
        &mut self,
        initial: Identity,
        target: Identity,
        deadline: Instant,
    ) -> io::Result<()> {
        if self.version_exec_stop(initial, deadline)? != Some(target) {
            return Err(io::Error::other("original version target lost its second stop"));
        }
        #[cfg(test)]
        expire_after_native_observation(EXPIRE_VERSION_GO.get(), deadline);
        time(deadline)?;
        if unsafe { libc::kill(self.pid, libc::SIGCONT) } != 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(())
    }

    pub(crate) fn version_unstarted(&self) -> io::Result<bool> {
        self.custody()?;
        Ok(self.version_group && !self.resumed)
    }

    /// Positive kernel absence only after this SAME original session leader's
    /// owning reap. The private no-fork/session-leader proof is additionally
    /// required by cache_probe; a numeric empty group never constructs it.
    pub(crate) fn version_group_gone(&self) -> io::Result<bool> {
        self.custody()?;
        if !self.version_group || self.status.is_none() {
            return Err(io::Error::other("maintenance group has no original owning reap"));
        }
        if unsafe { libc::kill(-self.pid, 0) } == 0 {
            return Ok(false);
        }
        let error = io::Error::last_os_error();
        if error.raw_os_error() == Some(libc::ESRCH) { Ok(true) } else { Err(error) }
    }

    pub(crate) fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
        self.reap(libc::WNOHANG)
    }

    pub(crate) fn wait(&mut self) -> io::Result<ExitStatus> {
        self.reap(0)?.ok_or_else(|| io::Error::other("owning wait returned no terminal"))
    }

    fn reap(&mut self, flags: libc::c_int) -> io::Result<Option<ExitStatus>> {
        self.custody()?;
        if self.status.is_some() {
            return Ok(self.status);
        }
        loop {
            let mut raw = 0;
            // SAFETY: writable status and exactly this owner's original child.
            let got = unsafe { libc::waitpid(self.pid, &mut raw, flags) };
            if got == self.pid {
                if !libc::WIFEXITED(raw) && !libc::WIFSIGNALED(raw) {
                    return Err(io::Error::other("owning wait returned no terminal"));
                }
                self.status = Some(ExitStatus::from_raw(raw));
                return Ok(self.status);
            }
            if got == 0 {
                return Ok(None);
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        }
    }

    pub(crate) fn kill(&mut self) -> io::Result<()> {
        self.custody()?;
        if self.status.is_some() {
            return Ok(());
        }
        // SAFETY: the original child stays unreaped while this owner signals it.
        if unsafe { libc::kill(self.pid, libc::SIGKILL) } == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }
}

impl Drop for Child {
    fn drop(&mut self) {
        if self.owner != std::process::id() {
            return;
        }
        while self.status.is_none() {
            let _ = self.kill();
            if self.wait().is_err() {
                // Do not turn an unknown/stolen wait into a completed owner.
                std::thread::sleep(Duration::from_millis(100));
            }
        }
    }
}

#[cfg(test)]
mod tests;
