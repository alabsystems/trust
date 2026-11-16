//! Sampled exclusive readiness while the SAME original complete claim is held.
//! No serialized observation constructs readiness, and no process is signalled.

use std::time::{Duration, Instant};

use super::*;
use crate::trust_repo_lock::management::process;

const QUIET_FOR: Duration = Duration::from_secs(10);
const POLL: Duration = Duration::from_millis(500);
const MAX_GAP: Duration = Duration::from_secs(2);
const MAX_SAMPLE: Duration = Duration::from_secs(1);
/// The readiness census's exit-wait budget (process::CensusSettle): half the
/// sample bound, so a census that spends it all can still yield a sample
/// `observe` accepts. A longer wait would only delay the reset that an exit
/// still unfinished causes.
const EXIT_SETTLE: Duration = Duration::from_nanos(MAX_SAMPLE.as_nanos() as u64 / 2);

struct Sample {
    available: Option<u64>,
    load: f64,
    compilers: usize,
}

/// Private live state. It is always owned with its original exclusive claim;
/// a caller cannot supply a saved timestamp, memory reading or process count.
pub(super) struct QuietWindow {
    since: Option<Instant>,
    last: Option<Instant>,
    deadline: Instant,
    waiting: String,
}

impl QuietWindow {
    fn observe(
        &mut self,
        sample: io::Result<Sample>,
        start: Instant,
        end: Instant,
        cpus: NonZeroU32,
        minimum_memory: u64,
    ) -> bool {
        let problem = match sample {
            Err(error) => Some(format!("native observation unavailable: {error}")),
            Ok(sample) => {
                if sample.available.is_none_or(|bytes| bytes < minimum_memory) {
                    Some(format!(
                        "available memory {:?} below required {minimum_memory}",
                        sample.available
                    ))
                } else if !sample.load.is_finite() || sample.load < 0.0 {
                    Some(format!("invalid native load {}", sample.load))
                } else if sample.load > 0.35 * f64::from(cpus.get()) {
                    Some(format!("native load {} above 0.35 * {} CPUs", sample.load, cpus))
                } else if sample.compilers > 0 {
                    Some(format!("{} other live compiler processes", sample.compilers))
                } else {
                    None
                }
            }
        };
        let good = end < self.deadline
            && end.saturating_duration_since(start) <= MAX_SAMPLE
            && problem.is_none();
        if !good {
            self.waiting =
                problem.unwrap_or_else(|| "sample expired or exceeded its time bound".into());
            self.since = None;
            self.last = None;
            return false;
        }
        if self.last.is_none_or(|last| end.saturating_duration_since(last) > MAX_GAP) {
            self.since = Some(end);
        }
        self.last = Some(end);
        let observed = end.saturating_duration_since(self.since.expect("first quiet observation"));
        self.waiting =
            format!("continuous sampled quiet interval {observed:?} below {QUIET_FOR:?}");
        observed >= QUIET_FOR
    }

    /// Reobserve immediately before the actual spawn. Delayed preparation,
    /// unavailable readings and busy samples invalidate the quiet interval.
    pub(super) fn check(&mut self, claim: &FixedClaim) -> io::Result<()> {
        claim.check_current()?;
        if !claim.reservation.exclusive || !claim.reservation.drained {
            return Err(invalid("quiet readiness lost its original exclusive claim"));
        }
        let start = Instant::now();
        let sample = measure(claim.cpus);
        if self.observe(
            sample,
            start,
            Instant::now(),
            claim.cpus,
            claim.reservation.minimum_memory_bytes,
        ) {
            claim.check_current()
        } else {
            Err(io::Error::new(io::ErrorKind::WouldBlock, "exclusive host is not measured quiet"))
        }
    }
}

impl FixedClaim {
    /// Wait for ten seconds of sampled host quietness under this original
    /// exclusive admission/worktree/slot claim, then prepare one command.
    /// Unknown memory, load or system process observations reset the interval.
    /// The same preconditions are reobserved at spawn; no caller facts authorize it.
    pub fn prepare_exclusive_command(
        self,
        command: std::process::Command,
        timeout: Duration,
    ) -> io::Result<PreparedFixedCommand> {
        self.check_current()?;
        if !self.reservation.exclusive || !self.reservation.drained {
            return Err(invalid("quiet launch requires the original drained exclusive claim"));
        }
        let deadline = Instant::now()
            .checked_add(timeout)
            .ok_or_else(|| invalid("exclusive quiet timeout exceeds the clock bound"))?;
        let mut quiet = QuietWindow {
            since: None,
            last: None,
            deadline,
            waiting: "no completed native sample".into(),
        };
        loop {
            if Instant::now() >= deadline {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    format!(
                        "exclusive admission timed out before measured host quietness; no command started; last condition: {}",
                        quiet.waiting
                    ),
                ));
            }
            match quiet.check(&self) {
                Ok(()) => return self.prepare_with_quiet(command, Some(quiet)),
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {}
                Err(error) => return Err(error),
            }
            std::thread::sleep(POLL.min(deadline.saturating_duration_since(Instant::now())));
        }
    }
}

fn measure(cpus: NonZeroU32) -> io::Result<Sample> {
    if std::thread::available_parallelism()?.get() != cpus.get() as usize {
        return Err(invalid("exclusive CPU width differs from the measured machine"));
    }
    let available = trust_build_cpu::available_memory();
    let mut load = 0.0;
    // SAFETY: getloadavg writes at most one double to the initialized output.
    if unsafe { libc::getloadavg(&mut load, 1) } != 1 {
        return Err(io::Error::other("native host load is unavailable"));
    }
    Ok(Sample { available, load, compilers: compiler_processes()? })
}

fn compiler_processes() -> io::Result<usize> {
    let mut count = 0;
    // One exit-wait budget for the whole census (process::CensusSettle).
    let settle = process::CensusSettle::within(EXIT_SETTLE);
    for pid in process::system_pids()? {
        // A native Targo supervisor is itself named targo. Exclude only this
        // actual observer; other Targo processes, including ancestors, count.
        if pid == std::process::id() {
            continue;
        }
        let (name, zombie) = match process::readiness_name(pid) {
            Ok(observed) => observed,
            Err(error) => {
                // Enumeration races exits and Darwin denies BSD info for
                // zombies. Only a positive kernel absence/zombie observation
                // permits skipping; access denial alone never means quiet. An
                // exit in progress is waited for, within this census's budget.
                if process::census_gone(pid, &settle) {
                    continue;
                }
                if process::writer_gone(pid).map_err(|error| {
                    io::Error::new(
                        error.kind(),
                        format!("cannot confirm kernel absence/zombie for PID {pid}: {error}"),
                    )
                })? {
                    continue;
                }
                return Err(io::Error::new(
                    error.kind(),
                    format!("cannot observe system PID {pid}: {error}"),
                ));
            }
        };
        if !zombie && is_compiler(&name) {
            count += 1;
        }
    }
    Ok(count)
}

fn is_compiler(name: &std::ffi::OsStr) -> bool {
    matches!(name.as_bytes(), b"cargo" | b"targo" | b"rustc" | b"trustc")
}

#[cfg(test)]
#[path = "quiet/tests.rs"]
mod tests;
