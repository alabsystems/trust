//! Own one isolated original process group under the same original fixed claim.
//! The unreaped direct child anchors group identity while signals can be sent.
//! Other waiters must not reap this owner's child. Escaped sessions/groups and
//! arbitrary descendant closure require the separate native workload protocol.

use std::time::{Duration, Instant};

use super::*;
use crate::trust_repo_lock::management::process;

#[path = "group/relay.rs"]
mod relay;
use relay::SignalRelay;

const POLL: Duration = Duration::from_millis(10);
const CANCEL_WAIT: Duration = Duration::from_secs(5);

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
    child: Child,
    group: libc::pid_t,
    status: Option<ExitStatus>,
    retired: bool,
    absence_error: Option<io::Error>,
    relay: Option<SignalRelay>,
}

impl PreparedFixedCommand {
    /// Launch in a new session and original process group, retaining the same
    /// complete fixed resource claim. No existing group can be named or joined.
    pub fn spawn_group(self) -> io::Result<RunningFixedGroup> {
        match self.claim.observe_native_room()? {
            LegacyFixedRoom::Fits { .. } => self.spawn_group_checked(),
            _ => Err(io::ErrorKind::WouldBlock.into()),
        }
    }

    /// A standalone launcher's scoped INT/TERM/HUP relay. Only one relay can
    /// be live in this process; existing application handlers are not replaced.
    pub fn spawn_group_with_signal_forwarding(self) -> io::Result<RunningFixedGroup> {
        match self.claim.observe_native_room()? {
            LegacyFixedRoom::Fits { .. } => self.spawn_with_forwarder_checked(),
            _ => Err(io::ErrorKind::WouldBlock.into()),
        }
    }

    fn spawn_with_forwarder_checked(self) -> io::Result<RunningFixedGroup> {
        let relay = SignalRelay::install()?;
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
            child: spawned.child,
            group,
            status: None,
            retired: false,
            absence_error: None,
            relay: None,
        })
    }
}

impl RunningFixedGroup {
    pub fn id(&self) -> u32 {
        self.child.id()
    }

    pub fn take_stdout(&mut self) -> Option<std::process::ChildStdout> {
        self.child.stdout.take()
    }

    pub fn take_stderr(&mut self) -> Option<std::process::ChildStderr> {
        self.child.stderr.take()
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
                    self.child.id() as libc::id_t,
                    info.as_mut_ptr(),
                    libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
                )
            };
            if result == 0 {
                // SAFETY: success initialized siginfo, including the no-event
                // zero PID. No exit status is fabricated from the observation.
                let observed = unsafe { info.assume_init().si_pid() };
                return if observed == 0 {
                    Ok(false)
                } else if observed == self.group {
                    Ok(true)
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
            let members = process::group_pids(self.child.id()).inspect_err(|error| {
                #[cfg(test)]
                eprintln!("original group {} actual proc_listpids: {error}", self.group);
                #[cfg(not(test))]
                let _ = error;
            })?;
            if members.iter().any(|pid| *pid != self.child.id()) {
                return Ok(None);
            }
            self.status = Some(self.child.wait().inspect_err(|error| {
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
                    Some(status) => Ok(Some(status)),
                    None => Err(error),
                };
            }
        }
        self.poll_retirement()
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
            let _ = writeln!(
                io::stderr().lock(),
                "native original group retirement unknown; actual resources retained: {error}"
            );
        }
    }
}

#[cfg(test)]
#[path = "group/tests.rs"]
mod tests;
