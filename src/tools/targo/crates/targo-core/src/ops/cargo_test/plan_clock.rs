//! Trust: the clock of a test plan run.
//!
//! A run that never ends holds its caller's push, its build slot and its
//! terminal, so a plan bounds itself (`[run]` in the plan file,
//! `build.test-wall-seconds` and `build.test-stall-seconds` over it):
//!
//! * the wall bound covers the whole invocation, from the moment the plan
//!   is selected: phases, the build and the tests;
//! * the stall bound covers one running test executable: the time since it
//!   last printed a line, on either stream. A build is exempt, because a
//!   compiler prints nothing for as long as it works.
//!
//! The job queue reads the clock where it polls for a stop (`observe`). A
//! bound that ran out stops the run as a root stop does: no new work is
//! admitted, and everything the run started is killed by process group,
//! with its descendants: every test executable, and every compiler, build
//! script and linker in flight. The invocation exits 3 with a closing record
//! that names what was running (`plan_outcome::stop`).
//!
//! That a build is killed too is what makes the wall bound a bound: a build
//! script, a proc macro or a compiler that never ends would otherwise hold
//! the run past it, and past a signal to Targo. So the clock holds custody
//! of the run's children from the moment it is armed (`Clock::custody`):
//! every compiler-side child of a plan run is started in its own process
//! group under it (`compiler::exec_with_targo_streaming_policy`), and a
//! stop, or `SIGINT`, `SIGTERM`, `SIGHUP` or `SIGQUIT` to Targo, ends them
//! all, in a `[[tool]]` build as in the plan's own.
//!
//! A run may be told to hold its tests at a barrier (`--run-after <FILE>`,
//! `Barrier`): it builds, and starts no test executable until the file
//! says `run`. The time it spends with nothing left to do but wait there is
//! the caller's and is not charged to the wall bound.
//!
//! The clock belongs to the invocation, as its signal handlers do: a
//! `[[workspace]]` phase runs under the clock of the plan that started it,
//! and a queue that starts after a stop is stopped before it admits work.
//!
//! A job queue reads the clock only while it drains, and a run spends time
//! outside every queue: selecting and resolving, between phases, waiting on
//! another process's build-directory lock, and the whole of a
//! `--unit-graph-parity` check. The signal handlers only note a signal, so
//! the clock keeps a watcher of its own (`watch`): when a signal has come,
//! or the wall bound has run out, and no queue is draining, it records the
//! stop as a queue would and ends every child under custody. If no queue
//! has ended the run a short grace later, the watcher ends the invocation
//! itself: the closing record of a phase that was running, the run's
//! closing record (with JSON messages), and the stop's exit status.

use std::io::Write as _;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use super::plan_outcome::Outcome;

use super::plan::Run;
use crate::CargoResult;
use crate::util::GlobalContext;

/// The bounds of this invocation's plan, and when it began.
pub struct Clock {
    started: Instant,
    pub wall: Option<Duration>,
    pub stall: Option<Duration>,
    /// Custody of what the run starts: the invocation's signal handlers and
    /// the flag that ends every child started under it. `None` where Targo
    /// cannot own a child's process group (neither Linux nor macOS).
    custody: Option<cargo_util::StreamingProcessScope>,
    /// What holds the run's tests until a caller releases them, if the
    /// invocation named it.
    barrier: Option<Barrier>,
    /// The job queues draining now: each reads the clock itself.
    queues: AtomicUsize,
    /// The plan as the run's records spell it, and whether they are JSON:
    /// what the watcher needs to close a run it ends.
    plan: String,
    json: bool,
}

/// Held by a job queue while it drains (`Clock::queues`).
pub(crate) struct Draining(&'static Clock);

impl Drop for Draining {
    fn drop(&mut self) {
        self.0.queues.fetch_sub(1, Ordering::AcqRel);
    }
}

/// How often the watcher looks, and how long after a stop it waits for the
/// run to end on its own before it ends the invocation.
const WATCH: Duration = Duration::from_millis(50);
const GRACE: Duration = Duration::from_secs(2);

/// `--run-after <FILE>`: a file another process writes when the run's test
/// executables may start.
///
/// A caller that overlaps this run's build with work the tests depend on (a
/// push hook whose earlier lanes rebuild the compiler some tests execute)
/// starts the run at once and writes the file when that work has ended. The
/// run builds meanwhile and starts no test executable, in a `[[workspace]]`
/// phase or of its own, until the file exists:
///
/// * its content is `run` (white space aside): the tests start;
/// * any other content is the caller's stop: the run ends `interrupted`,
///   exit 2, having run no test;
/// * the process that was to write it (`--run-after-owner <PID>`) is gone
///   and the file is not there: the same;
/// * the run has waited `[run] run-after-seconds` with nothing left to do
///   but wait: it ends `out-of-time`, exit 3.
///
/// A writer must put the file in place whole (write beside it, rename).
pub struct Barrier {
    path: PathBuf,
    owner: Option<u32>,
    max: Duration,
    released: AtomicBool,
    waiting: Mutex<Waiting>,
}

/// How long the run has had nothing to do but wait at its barrier.
#[derive(Default)]
struct Waiting {
    /// When the queue last saw the run idle at the barrier.
    since: Option<Instant>,
    total: Duration,
}

impl Barrier {
    /// The barrier `path` (`--run-after`), released by `owner`
    /// (`--run-after-owner`) and waited for at most the plan's `[run]
    /// run-after-seconds`, which a plan run held at a barrier must state: a
    /// barrier nobody releases would otherwise hold the run for as long as
    /// its owner lives.
    pub fn new(run: &Run, path: PathBuf, owner: Option<&str>) -> CargoResult<Barrier> {
        let max = run.run_after_seconds.ok_or_else(|| {
            anyhow::anyhow!(
                "--run-after needs the plan's `[run] run-after-seconds`: how long the run \
                 waits for `{}` with nothing else to do before it gives up",
                path.display()
            )
        })?;
        let owner = owner
            .map(|pid| {
                pid.parse::<u32>()
                    .ok()
                    .filter(|pid| *pid != 0 && i32::try_from(*pid).is_ok())
                    .ok_or_else(|| anyhow::anyhow!("--run-after-owner `{pid}` is not a process id"))
            })
            .transpose()?;
        Ok(Barrier {
            path,
            owner,
            max: Duration::from_secs(max),
            released: AtomicBool::new(false),
            waiting: Mutex::default(),
        })
    }

    /// The tests may start.
    pub(crate) fn released(&self) -> bool {
        self.released.load(Ordering::Acquire)
    }

    /// Time the run spent with nothing to do but wait here.
    pub(crate) fn waited(&self) -> Duration {
        self.waiting.lock().unwrap().total
    }

    /// What the file says, if it is there.
    fn said(&self) -> std::io::Result<Option<String>> {
        match std::fs::read(&self.path) {
            Ok(bytes) => Ok(Some(String::from_utf8_lossy(&bytes).trim().to_owned())),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error),
        }
    }

    /// Reads the barrier once. `idle`: the run has nothing running and
    /// nothing to build, only tests the barrier holds. Returns the stop the
    /// barrier asks for, if it asks for one.
    pub(crate) fn poll(&self, now: Instant, idle: bool) -> Option<(Outcome, String)> {
        if self.released() {
            return None;
        }
        let waited = {
            let mut waiting = self.waiting.lock().unwrap();
            if let (true, Some(since)) = (idle, waiting.since) {
                waiting.total += now.saturating_duration_since(since);
            }
            waiting.since = idle.then_some(now);
            waiting.total
        };
        let path = self.path.display();
        let nothing_ran = "no test executable was started";
        let gone = |pid: u32| {
            // SAFETY: signal 0 sends nothing; it asks whether the process
            // exists.
            #[cfg(unix)]
            let gone = unsafe { libc::kill(pid as libc::pid_t, 0) } != 0
                && std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH);
            #[cfg(not(unix))]
            let gone = {
                let _ = pid;
                false
            };
            gone
        };
        let said = match self.said() {
            Ok(None) => match self.owner {
                // Written just before its writer exited: read it once more.
                Some(owner) if gone(owner) => match self.said() {
                    Ok(None) => {
                        return Some((
                            Outcome::Interrupted,
                            format!(
                                "process {owner}, which was to release the barrier `{path}`, is \
                                 gone and never did; {nothing_ran}"
                            ),
                        ));
                    }
                    again => again,
                },
                _ => Ok(None),
            },
            said => said,
        };
        match said {
            Ok(Some(text)) if text == "run" => {
                self.released.store(true, Ordering::Release);
                None
            }
            Ok(Some(text)) => Some((
                Outcome::Interrupted,
                format!("the barrier `{path}` says `{text}`, not `run`; {nothing_ran}"),
            )),
            Err(error) => Some((
                Outcome::Interrupted,
                format!("the barrier `{path}` cannot be read ({error}); {nothing_ran}"),
            )),
            Ok(None) if waited >= self.max => Some((
                Outcome::OutOfTime,
                format!(
                    "the barrier `{path}` did not appear in the {} s the run waited for it \
                     with nothing else to do (`[run] run-after-seconds`); {nothing_ran}",
                    self.max.as_secs()
                ),
            )),
            Ok(None) => None,
        }
    }
}

impl std::fmt::Debug for Clock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Clock")
            .field("wall", &self.wall)
            .field("stall", &self.stall)
            .field("custody", &self.custody.is_some())
            .field(
                "barrier",
                &self.barrier.as_ref().map(|barrier| &barrier.path),
            )
            .finish()
    }
}

static CLOCK: OnceLock<Clock> = OnceLock::new();

/// The bounds a run of `members` members has: the plan's, with the
/// configuration's over them.
pub(crate) fn bounds(
    run: &Run,
    members: usize,
    wall: Option<u64>,
    stall: Option<u64>,
) -> CargoResult<(Option<Duration>, Option<Duration>)> {
    anyhow::ensure!(wall != Some(0), "build.test-wall-seconds must be 1 or more");
    anyhow::ensure!(
        stall != Some(0),
        "build.test-stall-seconds must be 1 or more"
    );
    let per_member = run
        .wall_seconds_per_member
        .map(|seconds| seconds.saturating_mul(members.max(1) as u64));
    let planned = match (run.wall_seconds, per_member) {
        (Some(wall), Some(per_member)) => Some(wall.max(per_member)),
        (wall, per_member) => wall.or(per_member),
    };
    Ok((
        wall.or(planned).map(Duration::from_secs),
        stall.or(run.stall_seconds).map(Duration::from_secs),
    ))
}

/// Starts the invocation's clock. The first plan to be selected is the
/// invocation's; a phase's plan runs under it.
pub(crate) fn arm(
    gctx: &GlobalContext,
    run: &Run,
    members: usize,
    barrier: Option<Barrier>,
    plan: &std::path::Path,
    json: bool,
) -> CargoResult<()> {
    let config = gctx.build_config()?;
    let (wall, stall) = bounds(
        run,
        members,
        config.test_wall_seconds,
        config.test_stall_seconds,
    )?;
    if CLOCK.get().is_some() {
        return Ok(());
    }
    // From here a signal to Targo is the run's interruption, read by the
    // queue and by every child's observer, whatever phase it arrives in.
    let custody = if cfg!(any(target_os = "linux", target_os = "macos")) {
        Some(cargo_util::StreamingProcessScope::new()?)
    } else {
        None
    };
    let watched = custody.is_some();
    let _ = CLOCK.set(Clock {
        started: Instant::now(),
        wall,
        stall,
        custody,
        barrier,
        queues: AtomicUsize::new(0),
        plan: plan.to_string_lossy().into_owned(),
        json,
    });
    // The bounds are the run's contract with its caller: say them once.
    let clock = CLOCK.get().expect("armed above");
    if watched {
        std::thread::Builder::new()
            .name("targo-plan-clock".into())
            .spawn(move || watch(clock))?;
    }
    gctx.shell().status("Bounded", clock.bounds_line(members))?;
    if let Some(barrier) = &clock.barrier {
        gctx.shell().status(
            "Holding",
            format!(
                "every test executable until `{}` says `run`, for at most {} s with nothing \
                 else to do; that wait is not charged to the wall bound",
                barrier.path.display(),
                barrier.max.as_secs()
            ),
        )?;
    }
    Ok(())
}

/// The invocation's clock, if a plan started one.
pub(crate) fn armed() -> Option<&'static Clock> {
    CLOCK.get()
}

/// Ends the run when no job queue can: a signal that came, or a wall bound
/// that ran out, while none was draining. The stop is recorded as a queue
/// records it, and every child under custody is ended; a queue that starts
/// after it admits nothing, and the run then ends by the ordinary route. A
/// run still going `GRACE` later (blocked on a lock another process holds,
/// or in work that starts no queue) is ended here, with its phase's and its
/// own closing record and the stop's exit status.
fn watch(clock: &'static Clock) {
    let mut since: Option<Instant> = None;
    loop {
        std::thread::sleep(WATCH);
        if clock.queues.load(Ordering::Acquire) > 0 {
            since = None;
            continue;
        }
        let now = Instant::now();
        let due = if let Some(signal) = clock.custody().and_then(|custody| custody.signalled()) {
            Some((
                Outcome::Interrupted,
                format!("signal {signal} stopped the run; {}", clock.outside(now)),
            ))
        } else {
            clock
                .expired(now, &[])
                .map(|_| (Outcome::OutOfTime, clock.out_of_time(now)))
        };
        let Some((outcome, why)) = due else {
            since = None;
            continue;
        };
        let Some(first) = since else {
            if super::plan_outcome::stop(outcome, why.clone()) {
                eprintln!(
                    "error: Targo stopped this test plan run: {why}; every compiler, build \
                     script and test executable still running is killed, with its descendants"
                );
            } else if super::plan_outcome::stopped().is_none() {
                // The run reached its verdict before this stop came: it is
                // over, and its record and status say how.
                return;
            }
            if let Some(custody) = clock.custody() {
                custody.cancel();
            }
            since = Some(now);
            continue;
        };
        if now.saturating_duration_since(first) < GRACE {
            continue;
        }
        // Nothing ended the run: end it here.
        let Some((outcome, why)) = super::plan_outcome::stopped() else {
            return;
        };
        let stdout = std::io::stdout();
        let mut out = stdout.lock();
        if clock.json {
            super::plan_phases::abandon(&why, &mut out);
            if let Some(line) = super::plan_outcome::closing_of_stopped(&clock.plan) {
                let _ = writeln!(out, "{line}");
            }
        } else {
            super::plan_phases::abandon(&why, &mut std::io::sink());
        }
        let _ = std::io::Write::flush(&mut out);
        std::process::exit(outcome.exit_status());
    }
}

/// When a running test executable last printed a line: milliseconds since
/// the worker began to watch it, written by the worker and read by the
/// queue.
#[derive(Clone, Debug)]
pub(crate) struct Progress {
    began: Instant,
    last: Arc<AtomicU64>,
}

impl Default for Progress {
    fn default() -> Self {
        Progress {
            began: Instant::now(),
            last: Arc::default(),
        }
    }
}

impl Progress {
    /// The executable printed a line.
    pub(crate) fn touch(&self) {
        self.last
            .store(self.began.elapsed().as_millis() as u64, Ordering::Release);
    }

    /// How long ago it last printed one, or was started.
    pub(crate) fn quiet(&self, now: Instant) -> Duration {
        let last = self.began + Duration::from_millis(self.last.load(Ordering::Acquire));
        now.saturating_duration_since(last)
    }

    /// How long it has run.
    pub(crate) fn running(&self, now: Instant) -> Duration {
        now.saturating_duration_since(self.began)
    }
}

/// A running test executable, as the clock reads it.
pub(crate) struct Running<'a> {
    pub name: String,
    pub progress: Option<&'a Progress>,
}

impl Clock {
    /// Says that a job queue drains now and reads the clock itself, until
    /// the guard is dropped.
    pub(crate) fn draining(&'static self) -> Draining {
        self.queues.fetch_add(1, Ordering::AcqRel);
        Draining(self)
    }

    /// What was running when the watcher saw a stop outside every queue.
    fn outside(&self, now: Instant) -> String {
        if !self.tests_may_start() {
            return self.describe(now, &[]);
        }
        "no test executable was running (no build or test was: Targo was selecting, \
         resolving, waiting on a lock or between phases)"
            .to_owned()
    }

    /// Why the run is out of time, seen outside every queue.
    fn out_of_time(&self, now: Instant) -> String {
        format!(
            "the run's wall bound of {} s ran out; {}",
            self.wall.map_or(0, |wall| wall.as_secs()),
            self.outside(now)
        )
    }

    /// The barrier the run's tests are held at, if it has one.
    pub(crate) fn barrier(&self) -> Option<&Barrier> {
        self.barrier.as_ref()
    }

    /// No barrier holds the run's tests: it has none, or it was released.
    pub(crate) fn tests_may_start(&self) -> bool {
        self.barrier.as_ref().is_none_or(Barrier::released)
    }

    /// Custody of the run's children, where Targo can hold it.
    pub(crate) fn custody(&self) -> Option<&cargo_util::StreamingProcessScope> {
        self.custody.as_ref()
    }

    /// The bounds, as the run states them when it starts.
    fn bounds_line(&self, members: usize) -> String {
        let seconds = |bound: Option<Duration>, of: &str| match bound {
            Some(bound) => format!("{} s {of}", bound.as_secs()),
            None => format!("no bound {of}"),
        };
        format!(
            "test plan time bound: {} ({members} member{}), {}",
            seconds(self.wall, "for the whole run"),
            if members == 1 { "" } else { "s" },
            seconds(self.stall, "without a line from a running test executable")
        )
    }

    /// Why the run is out of time at `now`, if it is: the bound that ran
    /// out, and every test executable running then.
    pub(crate) fn expired(&self, now: Instant, running: &[Running<'_>]) -> Option<String> {
        self.expired_since(self.started, now, running)
    }

    fn expired_since(
        &self,
        started: Instant,
        now: Instant,
        running: &[Running<'_>],
    ) -> Option<String> {
        // The time spent only waiting at a barrier is the caller's.
        let waited = self
            .barrier
            .as_ref()
            .map_or(Duration::ZERO, Barrier::waited);
        let elapsed = now
            .saturating_duration_since(started)
            .saturating_sub(waited);
        let bound = if let Some(wall) = self.wall.filter(|wall| elapsed >= *wall) {
            format!("the run's wall bound of {} s ran out", wall.as_secs())
        } else {
            let stall = self.stall?;
            let stalled = running.iter().find(|running| {
                running
                    .progress
                    .is_some_and(|progress| progress.quiet(now) >= stall)
            })?;
            format!(
                "{} printed nothing for {} s, the bound on a test executable's silence",
                stalled.name,
                stall.as_secs()
            )
        };
        Some(format!("{bound}; {}", self.describe(now, running)))
    }

    /// What was running, for the record of a run Targo stopped.
    pub(crate) fn describe(&self, now: Instant, running: &[Running<'_>]) -> String {
        if running.is_empty() && !self.tests_may_start() {
            return "no test executable was running (the run's tests were held at its barrier)"
                .to_owned();
        }
        describe(now, running)
    }
}

/// What was running, where no barrier holds the run's tests.
fn describe(now: Instant, running: &[Running<'_>]) -> String {
    if running.is_empty() {
        return "no test executable was running (the build was)".to_owned();
    }
    let rows = running
        .iter()
        .map(|running| match running.progress {
            Some(progress) => format!(
                "{} (running {} s, last line {} s ago)",
                running.name,
                progress.running(now).as_secs(),
                progress.quiet(now).as_secs()
            ),
            None => running.name.clone(),
        })
        .collect::<Vec<_>>();
    format!("running when stopped: {}", rows.join(", "))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run(wall: Option<u64>, per_member: Option<u64>, stall: Option<u64>) -> Run {
        Run {
            wall_seconds: wall,
            wall_seconds_per_member: per_member,
            stall_seconds: stall,
            ..Run::default()
        }
    }

    #[test]
    fn the_wall_bound_is_the_larger_of_the_floor_and_the_per_member_product() {
        let seconds = |run: &Run, members| bounds(run, members, None, None).unwrap().0;
        let plan = run(Some(14400), Some(900), Some(1800));
        assert_eq!(seconds(&plan, 3), Some(Duration::from_secs(14400)));
        assert_eq!(seconds(&plan, 40), Some(Duration::from_secs(36000)));
        assert_eq!(
            seconds(&run(None, Some(900), None), 0),
            Some(Duration::from_secs(900))
        );
        assert_eq!(seconds(&run(None, None, None), 5), None);
        // The configuration's bound replaces the plan's, whichever is larger.
        assert_eq!(
            bounds(&plan, 40, Some(60), Some(5)).unwrap(),
            (Some(Duration::from_secs(60)), Some(Duration::from_secs(5)))
        );
        assert!(bounds(&plan, 1, Some(0), None).is_err());
        assert!(bounds(&plan, 1, None, Some(0)).is_err());
    }

    #[test]
    fn a_barrier_holds_until_it_says_run_and_its_idle_wait_is_not_the_runs() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("barrier");
        let plan = Run {
            run_after_seconds: Some(50),
            ..Run::default()
        };
        let barrier = || Barrier::new(&plan, path.clone(), None).unwrap();
        // A plan that does not say how long to wait is refused, and so is
        // an owner that is no process id.
        assert!(Barrier::new(&Run::default(), path.clone(), None).is_err());
        for owner in ["", "0", "-4", "x", "99999999999"] {
            assert!(
                Barrier::new(&plan, path.clone(), Some(owner)).is_err(),
                "{owner}"
            );
        }
        let started = Instant::now();
        let at = |seconds| started + Duration::from_secs(seconds);

        // While the build runs the run is not idle: nothing is refunded.
        let held = barrier();
        assert_eq!(held.poll(at(0), false), None);
        assert_eq!(held.poll(at(30), false), None);
        assert_eq!(held.waited(), Duration::ZERO);
        // Idle from 30 s: the wait counts from the first idle look.
        assert_eq!(held.poll(at(30), true), None);
        assert_eq!(held.poll(at(70), true), None);
        assert_eq!(held.waited(), Duration::from_secs(40));
        assert!(!held.released());
        // The wall bound is charged what the run did, not what it waited.
        let clock = Clock {
            started,
            wall: Some(Duration::from_secs(60)),
            stall: None,
            custody: None,
            barrier: Some(held),
            queues: AtomicUsize::new(0),
            plan: String::new(),
            json: false,
        };
        assert!(!clock.tests_may_start());
        assert_eq!(clock.expired_since(started, at(99), &[]), None);
        let late = clock.expired_since(started, at(100), &[]).unwrap();
        assert!(
            late.ends_with("(the run's tests were held at its barrier)"),
            "{late}"
        );
        // Its own bound is on the idle wait.
        let (outcome, why) = clock.barrier().unwrap().poll(at(80), true).unwrap();
        assert_eq!(outcome, Outcome::OutOfTime);
        assert!(why.contains("did not appear in the 50 s"), "{why}");

        // Any content but `run` is a stop; `run` releases, once and for all.
        std::fs::write(&path, "stop\n").unwrap();
        let (outcome, why) = barrier().poll(at(1), true).unwrap();
        assert_eq!(outcome, Outcome::Interrupted);
        assert!(
            why.contains("says `stop`, not `run`; no test executable was started"),
            "{why}"
        );
        std::fs::write(&path, " run\n").unwrap();
        let open = barrier();
        assert_eq!(open.poll(at(1), true), None);
        assert!(open.released());
        std::fs::remove_file(&path).unwrap();
        assert_eq!(open.poll(at(999), true), None);

        // An owner that is gone without writing it never will.
        let mut child = std::process::Command::new("true").spawn().unwrap();
        child.wait().unwrap();
        let orphan = Barrier::new(&plan, path.clone(), Some(&child.id().to_string())).unwrap();
        let (outcome, why) = orphan.poll(at(1), false).unwrap();
        assert_eq!(outcome, Outcome::Interrupted);
        assert!(why.contains("is gone and never did"), "{why}");
        // One that lives is waited for.
        let own = std::process::id().to_string();
        assert_eq!(
            Barrier::new(&plan, path.clone(), Some(&own))
                .unwrap()
                .poll(at(1), false),
            None
        );
    }

    #[test]
    fn a_bound_that_ran_out_names_itself_and_what_was_running() {
        let started = Instant::now();
        let clock = Clock {
            started,
            wall: Some(Duration::from_secs(100)),
            stall: Some(Duration::from_secs(10)),
            custody: None,
            barrier: None,
            queues: AtomicUsize::new(0),
            plan: String::new(),
            json: false,
        };
        assert_eq!(
            clock.bounds_line(3),
            "test plan time bound: 100 s for the whole run (3 members), 10 s without a \
             line from a running test executable"
        );
        let quiet = Progress {
            began: started,
            last: Arc::default(),
        };
        let loud = Progress {
            began: started,
            last: Arc::new(AtomicU64::new(25_000)),
        };
        let running = [
            Running {
                name: "lib of `quiet`".to_owned(),
                progress: Some(&quiet),
            },
            Running {
                name: "lib of `loud`".to_owned(),
                progress: Some(&loud),
            },
        ];
        let at = |seconds| started + Duration::from_secs(seconds);
        // Within every bound.
        assert_eq!(clock.expired_since(started, at(9), &running), None);
        // The silent one is named, the one that printed since is not blamed,
        // and both are listed as running.
        let stalled = clock.expired_since(started, at(30), &running).unwrap();
        assert!(
            stalled.starts_with("lib of `quiet` printed nothing for 10 s"),
            "{stalled}"
        );
        assert!(
            stalled.contains("lib of `loud` (running 30 s, last line 5 s ago)"),
            "{stalled}"
        );
        // A build has no test executable to stall, and the wall bound holds
        // it all the same.
        assert_eq!(clock.expired_since(started, at(99), &[]), None);
        let wall = clock.expired_since(started, at(100), &[]).unwrap();
        assert!(
            wall.starts_with("the run's wall bound of 100 s ran out"),
            "{wall}"
        );
        assert!(wall.contains("no test executable was running"), "{wall}");
    }
}
