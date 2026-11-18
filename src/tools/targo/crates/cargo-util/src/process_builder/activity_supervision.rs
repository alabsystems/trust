//! Narrowing policy inside the existing unreaped-child owner. This observer
//! never signals, reaps, admits work, or treats process counters as a grant.

use super::ChildSupervision;
use std::io;
use std::time::{Duration, Instant};
use trust_resource_provenance::process::{Identity, TreeActivity, TreeActivityObservation};

pub(super) enum ActivityPoll {
    Active,
    Exited(Option<io::Error>),
}

pub(super) struct ActivitySupervision {
    pid: u32,
    original: Option<Identity>,
    policy: ChildSupervision,
    previous: Option<TreeActivity>,
    last_progress: Instant,
    next_sample: Instant,
}

impl ActivitySupervision {
    pub(super) fn new(pid: u32, policy: ChildSupervision) -> Self {
        let now = Instant::now();
        Self {
            pid,
            original: None,
            policy,
            previous: None,
            last_progress: now,
            next_sample: now,
        }
    }

    pub(super) fn output(&mut self) {
        self.last_progress = Instant::now();
    }

    pub(super) fn poll(&mut self) -> io::Result<ActivityPoll> {
        let now = Instant::now();
        if now < self.next_sample {
            return Ok(ActivityPoll::Active);
        }
        self.next_sample = now + Duration::from_millis(100);
        let sample = read_activity(self.pid, self.original, now + Duration::from_millis(100));
        match sample {
            Ok(TreeActivityObservation::Exited) => return Ok(ActivityPoll::Exited(None)),
            Ok(TreeActivityObservation::OriginalUnavailable(error)) => {
                return Ok(ActivityPoll::Exited(Some(error)));
            }
            Ok(TreeActivityObservation::Active(sample)) => {
                let observed_at = Instant::now();
                self.original = Some(sample.original());
                if self
                    .policy
                    .resident_bytes
                    .is_some_and(|limit| sample.resident_bytes() > limit.get())
                {
                    return Err(io::Error::other(
                        "streaming child process tree exceeds its sampled resident-byte ceiling",
                    ));
                }
                if self
                    .previous
                    .as_ref()
                    .is_none_or(|previous| sample.advanced_since(previous))
                {
                    self.last_progress = observed_at;
                }
                self.previous = Some(sample);
                if observed_at.duration_since(self.last_progress) >= self.policy.inactivity {
                    return Err(io::Error::new(
                        io::ErrorKind::TimedOut,
                        "streaming child process tree exceeded its output/CPU/I/O inactivity window",
                    ));
                }
            }
            Err(error) => {
                // Only the sampler's typed natural-population cause retries,
                // within the original one-sample deadline. Permission and
                // integrity failures never become idle/zero or new allowance.
                return Err(io::Error::new(
                    error.kind(),
                    format!("streaming child activity observation unavailable: {error}"),
                ));
            }
        }
        Ok(ActivityPoll::Active)
    }
}

fn read_activity(
    pid: u32,
    original: Option<Identity>,
    deadline: Instant,
) -> io::Result<TreeActivityObservation> {
    #[cfg(test)]
    if let Some(action) = OBSERVATION_FAULT.with(|value| value.borrow().clone()) {
        match action {
            ObservationAction::Denied => return Err(io::Error::from_raw_os_error(libc::EPERM)),
            ObservationAction::Exit(release) => {
                let _ = OBSERVATION_FAULT.with(|value| value.replace(None));
                std::fs::write(release, b"release actual root")?;
                // SAFETY: the scoped fixture is called only by this original
                // StreamingChildExit owner. Its observer also uses WNOWAIT;
                // neither observer reaps before the same owner finishes.
                while !unsafe {
                    trust_resource_provenance::process::unreaped_child_exit(pid as libc::pid_t)?
                } {
                    if Instant::now() >= deadline {
                        return Err(io::Error::new(
                            io::ErrorKind::TimedOut,
                            "actual fixture root did not exit inside the original sample deadline",
                        ));
                    }
                    std::thread::sleep(Duration::from_millis(1));
                }
            }
        }
    }
    TreeActivity::read(pid, original, deadline)
}

#[cfg(test)]
thread_local! { static OBSERVATION_FAULT: std::cell::RefCell<Option<ObservationAction>> = const { std::cell::RefCell::new(None) }; }

#[cfg(test)]
#[derive(Clone)]
enum ObservationAction {
    Denied,
    Exit(std::path::PathBuf),
}

#[cfg(test)]
pub(super) struct ObservationFault {
    before: Option<ObservationAction>,
    action: ObservationAction,
    _thread: std::marker::PhantomData<*mut ()>,
}
#[cfg(test)]
impl ObservationFault {
    pub(super) fn scope() -> Self {
        Self {
            before: OBSERVATION_FAULT.with(|value| value.replace(None)),
            action: ObservationAction::Denied,
            _thread: std::marker::PhantomData,
        }
    }
    pub(super) fn exiting(release: std::path::PathBuf) -> Self {
        let mut scope = Self::scope();
        scope.action = ObservationAction::Exit(release);
        scope
    }
    pub(super) fn activate(&self) {
        let _ = OBSERVATION_FAULT.with(|value| value.replace(Some(self.action.clone())));
    }
}
#[cfg(test)]
impl Drop for ObservationFault {
    fn drop(&mut self) {
        let _ = OBSERVATION_FAULT.with(|value| value.replace(self.before.take()));
    }
}
