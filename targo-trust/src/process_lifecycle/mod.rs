//! Process lifecycle: the one stop path, signals to targo-trust, and the stop
//! of its children when targo-trust itself dies.
//!
//! Determinism plan `docs/design/2026-09-29-incremental-deterministic-trust-
//! results.md`, row T5 (its first half, T5a; the trustd lease and the handoff
//! between trustd builds are T5b, with the coordinator's protocol v2), and the
//! rulings in `docs/DECISION_QUEUE.md` "T5a".
//!
//! **One stop path.** Every child this process starts into a process group of
//! its own is OWNED ([`Ownership`]) from its spawn until it is reaped, and
//! every way such a child is ended -- a signal to targo-trust, the compiler
//! backstop, a probe's bound, an error path that abandons it, the clean-up of
//! a leader's group after it exits, and targo-trust's own death -- goes
//! through [`stop_tree`] (or its batch form): one function that
//!
//! 1. enumerates the process tree under the child, the members of its
//!    process group and the members of every group a member leads FIRST,
//!    because a signalled driver's children are reparented onto init and
//!    drop out of any later tree walk;
//! 2. sends SIGTERM in a defined order: the child's own group (so a Cargo
//!    driver stops scheduling compilers at once), then each group a member
//!    leads (so a compiler's linker goes with it), in the order their
//!    leaders were found (breadth-first), then each other member alone;
//! 3. waits [`STOP_GRACE`] for every one of them to exit, polling the
//!    kernel's record (a zombie counts as exited);
//! 4. then walks again, every millisecond, and sends SIGKILL, in the same
//!    order, to whatever runs, until the tree and its groups have stayed
//!    empty for [`QUIET_ROUNDS`] rounds in a row or [`KILL_ROUNDS`] rounds
//!    have passed: one SIGKILL does not reach a process a group is making at
//!    that instant ([`KILL_ROUNDS`] has the measurements);
//! 5. records the stop and its cause ([`StopCause`], [`recorded_stops`]),
//!    with how long after the SIGTERM its SIGKILL went out.
//!
//! A process group is signalled through its id only while the stop holds its
//! leader: an unreaped child of the caller's, or a process read with the
//! start it was found with, running or exited and not yet reaped, just before
//! the signal ([`Access`]). Once a group's leader is reaped its id may be
//! handed to another process, so what is left in the group is read and
//! signalled by pid alone.
//!
//! No other signal is ever sent: SIGABRT, SIGSEGV and SIGQUIT write crash
//! reports, and a stop is not a crash. The machine-wide `trustd` is never a
//! member of a walk ([`tree::is_trust_memory_daemon`]); a private `trustd` a
//! release smoke starts is a root, and is stopped like any other owned child.
//!
//! **Signals** ([`signals`]). SIGINT, SIGTERM and SIGHUP to targo-trust stop
//! every owned child through that path, mark the run COULD NOT RUN and exit 3
//! (T7b's exit, `determinism_report::EXIT_COULD_NOT_RUN`); a second one cuts
//! the grace short and sends SIGKILL at once.
//!
//! **Parent death** ([`sentinel`]). macOS has no `PR_SET_PDEATHSIG`, and on
//! Linux it reaches only a direct child, never the compilers under a Cargo
//! driver. So targo-trust keeps one end of a socket pair whose other end is the
//! standard input of a small SENTINEL process (this executable, re-run with a
//! private subcommand), and tells it, record by record, which children it owns.
//! When targo-trust ends -- SIGKILL included -- the kernel closes its end, the
//! sentinel reads end-of-file, and it stops every child still on its list
//! through the same path. The same mechanism runs on macOS and Linux.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

pub(crate) mod sentinel;
pub(crate) mod signals;
pub(crate) mod tree;

#[cfg(unix)]
use std::collections::BTreeSet;
use std::collections::{BTreeMap, VecDeque};
use std::io;
use std::process::{Child, Command};
use std::sync::Mutex;
use std::time::Duration;
#[cfg(unix)]
use std::time::Instant;

/// How long a stopped process is given between SIGTERM and SIGKILL.
///
/// A compiler, a Cargo driver and a shell all die on SIGTERM at once; the grace
/// is paid only by a process that ignores or handles it and does not exit. Ten
/// seconds is long enough for a handler to flush and release what it holds and
/// short enough that an operator who pressed Ctrl-C is not left waiting: a
/// second Ctrl-C ends the grace at once ([`signals`]).
pub(crate) const STOP_GRACE: Duration = Duration::from_secs(10);

/// How often the grace wait re-reads whether the stopped processes are gone.
const STOP_POLL_INTERVAL: Duration = Duration::from_millis(20);

/// How many rounds the kill phase runs at most after the grace: a walk of the
/// tree and its groups, and a SIGKILL to whatever runs, a millisecond
/// ([`ROUND_NAP`]) apart. The model is aterm's gate runner (aterm
/// `8722b107c`, `crates/aterm-verify/src/exec.rs`, `group::rekill`), whose
/// measurements, all on this macOS (26.6, 18 cores, 2026-10-13), are these.
///
/// WHY A SIGKILL IS REPEATED. On macOS a group's SIGKILL reaches the members
/// the group has at that instant and not a process one of them is making: a
/// signal does not find a child until its `fork` or `posix_spawn` is nearly
/// done (xnu-12377: `killpg` looks each member up with `proc_find`, which
/// refuses a process still being made). The parent dies and the child runs
/// on. With no gate in it, one SIGKILL at a group whose leader was inside the
/// call left the child in 1,435 of 3,000 groups for a `fork`, 498 of 3,000
/// for a `posix_spawn` and 807 of 2,000 forking back to back; one more
/// SIGKILL emptied each of 11,000 such groups. This stop, killing once,
/// left a process of a tree that ignores SIGTERM and keeps forking after 116
/// of 150 stops (TRUST-KI-1014-2).
///
/// WHY NOT "UNTIL THE GROUP IS GONE". A group can read as empty while a child
/// is still on its way: a process stops answering when the thread that takes
/// the kill begins its exit, and another of its threads can be inside
/// `posix_spawn` then. Killing only while the group answered left a process
/// in 19 of 3,000 groups whose second thread was spawning. A Cargo driver, a
/// compiler and a test harness all have more than one thread. So the rule is
/// time: the tree is done with when [`QUIET_ROUNDS`] rounds in a row have
/// found nothing in it.
///
/// THE BOUND. A tree that keeps answering is walked and killed this many
/// times and no more, about a third of a second; the outcome then counts what
/// the last round still found ([`StopOutcome::left`]). A group that emptied
/// stopped answering within 30 ms of its kill at a load of 42 to 64, and no
/// group in 25,100 kills by this rule took more than 14 rounds over its quiet
/// ones.
///
/// LINUX (read, not run, by aterm's change; nothing here ran on Linux): its
/// `fork` fails when a fatal signal is pending for the parent, so a group's
/// SIGKILL needs no repeat there. The rounds run there all the same, because
/// what a group signal cannot reach (what is left in a group whose leader is
/// reaped, signalled by pid, [`Access::Read`]) is killed one process at a
/// time. Its walks read `/proc`, so a round costs more there; unmeasured.
#[cfg(unix)]
const KILL_ROUNDS: u16 = 250;

/// How many rounds in a row must find nothing running, in the tree or in any
/// group the stop reaches, before the kill phase ends: what every stop that
/// found a process running now costs, about 50 ms, even when SIGTERM ended
/// everything (one empty reading is exactly the one measured wrong). It must
/// outlast a `posix_spawn` in flight in a process that has stopped answering:
/// such groups answered again at most 1.2 ms after their kill at a load of 3
/// to 64, and 8.9 ms after it while another build was starting beside them
/// (aterm `8722b107c`, `group::QUIET_ROUNDS`, which made the same choice).
/// A stop that found nothing running when it began, and finds nothing after
/// its grace, runs one round: an exited leader's group is stopped before
/// every reap ([`StopCause::LeaderExited`]), and is almost always empty.
#[cfg(unix)]
const QUIET_ROUNDS: u16 = 40;

/// The pause between two rounds of the kill phase.
#[cfg(unix)]
const ROUND_NAP: Duration = Duration::from_millis(1);

/// Whether a group signal that succeeds says a process RUNS in the group: on
/// macOS a group down to its unreaped leader answers `EPERM` (measured 200 of
/// 200 by aterm's change), so success is a live member, and such an answer
/// keeps the kill phase going although no walk saw the process. On Linux an
/// unreaped leader answers too (read, not run), so there only the walks count.
#[cfg(unix)]
const GROUP_ANSWER_MEANS_RUNNING: bool = cfg!(target_os = "macos");

/// How many recent stops [`recorded_stops`] keeps.
const STOP_RECORD_CAPACITY: usize = 64;

/// Why a child was stopped. Every stop names one; it is recorded with the stop
/// and, for a signal, decides the run's exit (3, COULD NOT RUN).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StopCause {
    /// targo-trust received this signal (SIGINT, SIGTERM or SIGHUP).
    Signal(i32),
    /// The run's backstop ended a verified compiler process
    /// (`CompilerProcessBounds::from_backstop`).
    Backstop,
    /// A bounded child exceeded its own bound: a probe's or a benchmark
    /// command's deadline or output cap, or a pipe held open past its grace.
    Bound,
    /// targo-trust abandoned the child on an error path (a failed wait, a
    /// missing pipe, a failed readiness check).
    Error,
    /// The child's leader exited; what is left of its process group is stopped
    /// before the leader is reaped.
    LeaderExited,
    /// The owner let go of a child that was still running: an [`Ownership`]
    /// dropped before its child exited, or an owner done with a child that
    /// runs until it is stopped (a release smoke's private `trustd`).
    Released,
    /// The process that started targo-trust ended (`targo`, which runs
    /// targo-trust as its child, or whatever else did): the run stops as for a
    /// signal ([`signals`]).
    ParentEnded,
    /// targo-trust itself ended while it still owned the child, SIGKILL
    /// included: the sentinel's stop ([`sentinel`]).
    OwnerEnded,
}

impl StopCause {
    /// The cause as it is recorded and printed.
    pub(crate) fn label(self) -> String {
        match self {
            StopCause::Signal(signal) => format!("signal {}", signals::signal_name(signal)),
            StopCause::Backstop => "backstop".to_string(),
            StopCause::Bound => "bound".to_string(),
            StopCause::Error => "error".to_string(),
            StopCause::LeaderExited => "leader-exited".to_string(),
            StopCause::Released => "released".to_string(),
            StopCause::ParentEnded => "parent-ended".to_string(),
            StopCause::OwnerEnded => "owner-ended".to_string(),
        }
    }
}

/// What one stop did.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct StopOutcome {
    /// Complete only after the required quiet observations, with no failed or
    /// capped read during this stop. Default zero counters prove no quietness.
    pub(crate) observation: tree::Observation,
    /// Any positive live PID or meaningful group answer, including a process
    /// first discovered after SIGTERM. Independent of signal counters.
    pub(crate) observed_running: bool,
    /// Processes found running when the stop began (roots, the trees under
    /// them and the other members of their groups) and sent SIGTERM.
    pub(crate) terminated: usize,
    /// Processes found running when the grace ended (or was cut short), or
    /// by a later round of the kill phase, and sent SIGKILL: each once.
    pub(crate) killed: usize,
    /// The grace was cut short: a second signal to targo-trust.
    pub(crate) escalated: bool,
    /// How long after the stop's SIGTERM its first SIGKILL went out; `None`
    /// when it sent none.
    pub(crate) killed_after: Option<Duration>,
    /// Processes the last round of the kill phase still found running: 0
    /// unless the rounds ran out ([`KILL_ROUNDS`]) before the tree stayed
    /// empty.
    pub(crate) left: usize,
}

impl StopOutcome {
    fn add(&mut self, other: StopOutcome) {
        self.observation = self.observation.combine(other.observation);
        self.observed_running |= other.observed_running;
        self.terminated += other.terminated;
        self.killed += other.killed;
        self.escalated |= other.escalated;
        self.killed_after = match (self.killed_after, other.killed_after) {
            (Some(ours), Some(theirs)) => Some(ours.min(theirs)),
            (ours, theirs) => ours.or(theirs),
        };
        self.left += other.left;
    }

    /// What the stop did after its SIGTERM, in words, or `None` when it sent
    /// no SIGKILL: "SIGKILL to 2 still running 26 ms after the SIGTERM", or,
    /// when `second` (a second signal to targo-trust) cut the grace short,
    /// "SIGKILL to 2 at once on a second signal (SIGINT), 3.2 s after the
    /// SIGTERM". The time is the one measured, never the grace's length: a
    /// stop whose SIGTERM ended what it found and that then found a process
    /// the first walk missed kills it long before the grace is over.
    pub(crate) fn kill_words(&self, second: Option<i32>) -> Option<String> {
        if self.killed == 0 {
            return None;
        }
        let after =
            self.killed_after.map(spoken).unwrap_or_else(|| "an unmeasured time".to_string());
        let mut words = match second.filter(|_| self.escalated) {
            Some(signal) => format!(
                "SIGKILL to {} at once on a second signal ({}), {after} after the SIGTERM",
                self.killed,
                signals::signal_name(signal)
            ),
            None => format!("SIGKILL to {} still running {after} after the SIGTERM", self.killed),
        };
        if self.left > 0 {
            words.push_str(&format!(
                ", and found {} still running after its last repeated SIGKILL",
                self.left
            ));
        }
        Some(words)
    }
}

/// `elapsed` for a message: whole milliseconds under a second ("26 ms"),
/// tenths of a second from one ("10.0 s").
fn spoken(elapsed: Duration) -> String {
    if elapsed < Duration::from_secs(1) {
        format!("{} ms", elapsed.as_millis())
    } else {
        format!("{:.1} s", elapsed.as_secs_f64())
    }
}

/// One recorded stop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct StopRecord {
    /// The stopped root's pid.
    pub(crate) root: u32,
    pub(crate) cause: StopCause,
    pub(crate) outcome: StopOutcome,
}

static STOP_RECORDS: Mutex<VecDeque<StopRecord>> = Mutex::new(VecDeque::new());

fn record(root: u32, cause: StopCause, outcome: StopOutcome) {
    // Every exited leader's group is stopped before it is reaped, and almost
    // always nothing is left in it: that is no stop worth a record.
    if cause == StopCause::LeaderExited
        && !outcome.observed_running
        && outcome.observation == tree::Observation::Complete
    {
        return;
    }
    if let Ok(mut records) = STOP_RECORDS.lock() {
        if records.len() == STOP_RECORD_CAPACITY {
            records.pop_front();
        }
        records.push_back(StopRecord { root, cause, outcome });
    }
}

/// The most recent stops this process made, oldest first.
pub(crate) fn recorded_stops() -> Vec<StopRecord> {
    STOP_RECORDS.lock().map(|records| records.iter().copied().collect()).unwrap_or_default()
}

/// How the stop path may treat a root's pid.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RootPin {
    /// An unreaped child of this process. Its pid, and the process group it
    /// leads, cannot be reused while it stays unreaped, so both may be
    /// signalled without a check. The caller reaps it after the stop.
    OwnChild,
    /// A process this one may no longer hold unreaped (its owner may have
    /// reaped it, or it was never this process's child). It, and its group,
    /// are signalled only while the pid still names the process that started
    /// at this time ([`tree::Identity::start`]), running or exited and not yet
    /// reaped. Once no process has the pid the root is reaped: what is left of
    /// its group is read and signalled by pid, never through the group's id,
    /// which may by then be another process's ([`Access`]).
    Started(u64),
}

/// One process tree to stop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Root {
    pub(crate) pid: u32,
    pub(crate) pin: RootPin,
}

/// Put `command`'s child in a process group of its own. Every child this
/// process owns leads one: it is what lets the stop path reach the child's
/// descendants that never leave its group, and what keeps the terminal's
/// Ctrl-C from reaching it before targo-trust has decided how to stop it.
pub(crate) fn configure_own_group(command: &mut Command) {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt as _;
        command.process_group(0);
    }
    #[cfg(not(unix))]
    let _ = command;
}

/// Spawn `command` into a process group of its own and own the child.
pub(crate) fn spawn_owned(command: &mut Command) -> io::Result<(Child, Ownership)> {
    configure_own_group(command);
    let child = command.spawn()?;
    let ownership = Ownership::of(child.id());
    Ok((child, ownership))
}

/// The children this process owns: pid -> start ([`tree::Identity::start`]),
/// or `None` where the start could not be read.
static OWNED: Mutex<BTreeMap<u32, Option<u64>>> = Mutex::new(BTreeMap::new());

/// A child this process owns, from its spawn until its owner has reaped it.
///
/// While it is owned, a signal to targo-trust stops it ([`signals`]) and the
/// sentinel stops it if targo-trust dies ([`sentinel`]). Dropping the
/// ownership releases it; a child that is still RUNNING then is stopped
/// ([`StopCause::Released`]), so no owned child outlives its owner's scope.
/// Drop it only after the child is reaped (or let it stop the child).
///
/// Every owned child's scope ends in this drop before its result reaches a
/// caller (a probe's output, a benchmark command's row, a smoke's defect), so
/// the drop is where a thread stops once the run's stop has begun
/// ([`signals::hold_if_interrupted`]): what the child produced may be what the
/// stop cut short, and nothing reports on it.
#[derive(Debug)]
pub(crate) struct Ownership {
    pid: u32,
    start: Option<u64>,
}

impl Ownership {
    /// Own the child `pid`, an unreaped child of this process. A child that
    /// leads its own process group ([`configure_own_group`], every child but
    /// one) is stopped with its group; one left in this process's group (the
    /// interactive upstream-tests engine, which reads the terminal) is stopped
    /// with its tree alone, never through a group.
    ///
    /// A child spawned once a signal has begun the run's stop is stopped at
    /// once, and this call does not return: the stop owns the exit.
    pub(crate) fn of(pid: u32) -> Self {
        let start = tree::identity(pid).map(|identity| identity.start);
        if let Ok(mut owned) = OWNED.lock() {
            owned.insert(pid, start);
        }
        sentinel::note_owned(pid, start);
        if let Some(cause) = signals::interrupted() {
            let _ = stop_tree(pid, cause);
            signals::hold_if_interrupted();
        }
        Ownership { pid, start }
    }

    #[cfg(test)]
    pub(crate) fn pid(&self) -> u32 {
        self.pid
    }
}

impl Drop for Ownership {
    fn drop(&mut self) {
        // Stopped while it is still listed, so a signal's stop that begins
        // meanwhile reaches it too (and its second signal escalates both).
        if let Some(start) = self.start {
            if tree::still_running(self.pid, Some(start)) {
                let root = Root { pid: self.pid, pin: RootPin::Started(start) };
                let _ = stop_roots_recorded(
                    &[root],
                    StopCause::Released,
                    STOP_GRACE,
                    &mut signals::escalated,
                );
            }
        }
        if let Ok(mut owned) = OWNED.lock() {
            owned.remove(&self.pid);
        }
        sentinel::note_released(self.pid);
        signals::hold_if_interrupted();
    }
}

/// How many children are owned right now.
pub(crate) fn owned_count() -> usize {
    OWNED.lock().map(|owned| owned.len()).unwrap_or(0)
}

/// Every child owned right now, as roots the stop path may signal while their
/// pids still name them.
fn owned_roots() -> Vec<Root> {
    OWNED
        .lock()
        .map(|owned| {
            owned
                .iter()
                .filter_map(|(&pid, &start)| {
                    start.map(|start| Root { pid, pin: RootPin::Started(start) })
                })
                .collect()
        })
        .unwrap_or_default()
}

/// THE stop path, for one unreaped child of this process: stop the tree under
/// `pid` and its process group, SIGTERM then (after [`STOP_GRACE`]) SIGKILL,
/// and record `cause`. The caller reaps `pid` afterwards.
///
/// The error is the one the child's own group signal returned (other than "no
/// such group", and macOS's EPERM for a group in which nothing runs: see
/// [`StopPlan::signal`]), which is what the group kill this replaces returned;
/// member signals are best-effort, because a member that exits on its own is
/// the normal case.
///
/// On a target with no process walk and no identity (neither macOS nor Linux)
/// the stop cannot see whether anything is still running, so it sends SIGTERM
/// and then SIGKILL to the child's group without a grace.
///
/// A second signal to targo-trust ends this stop's grace as it ends the
/// signal's own ([`signals::escalated`]), whichever thread runs it.
pub(crate) fn stop_tree(pid: u32, cause: StopCause) -> io::Result<StopOutcome> {
    let root = Root { pid, pin: RootPin::OwnChild };
    let (result, outcome) =
        stop_roots_recorded(&[root], cause, STOP_GRACE, &mut signals::escalated);
    result.map(|()| outcome)
}

/// The running processes a stop of `pid`, an unreaped child of this process,
/// would reach: `pid` unless it has exited, the tree under it, the other
/// members of its process group, and the trees and groups of those
/// ([`stop_tree`]'s first step, which signals nothing). A bounded probe asks
/// it whether a stream still open after its leader exited is held by a
/// process of the probe's own. `None` where this platform cannot tell a
/// running process from a gone one.
pub(crate) fn running_reach(pid: u32) -> Option<Vec<u32>> {
    #[cfg(unix)]
    {
        if !StopPlan::OBSERVABLE {
            return None;
        }
        let mut plan = StopPlan::enumerate(Root { pid, pin: RootPin::OwnChild });
        let mut reach = Vec::new();
        if plan.root_start.is_some_and(|start| plan.running_pid(pid, Some(start))) {
            reach.push(pid);
        }
        for member in plan.members.clone() {
            if plan.running_pid(member.pid, Some(member.start)) {
                reach.push(member.pid);
            }
        }
        (plan.observation == tree::Observation::Complete).then_some(reach)
    }
    #[cfg(not(unix))]
    {
        let _ = pid;
        None
    }
}

/// [`stop_tree`] for a [`Child`] on every platform: the stop path on Unix, and
/// `Child::kill` where there are no process groups. Does not reap.
pub(crate) fn stop_child(child: &mut Child, cause: StopCause) -> io::Result<()> {
    #[cfg(unix)]
    {
        stop_tree(child.id(), cause).map(|_| ())
    }
    #[cfg(not(unix))]
    {
        let _ = cause;
        child.kill()
    }
}

/// Stop `roots` together (one grace for all of them) and record each under
/// `cause`: the first group-signal error, and the summed outcome.
pub(crate) fn stop_roots_recorded(
    roots: &[Root],
    cause: StopCause,
    grace: Duration,
    escalate: &mut dyn FnMut() -> bool,
) -> (io::Result<()>, StopOutcome) {
    let (result, outcomes) = stop_roots(roots, grace, escalate);
    let mut total =
        StopOutcome { observation: tree::Observation::Complete, ..StopOutcome::default() };
    for (root, outcome) in roots.iter().zip(outcomes) {
        record(root.pid, cause, outcome);
        total.add(outcome);
    }
    (result, total)
}

/// The stop itself (module docs, steps 1-4). `escalate` is polled during the
/// grace; `true` ends it at once.
#[cfg(unix)]
fn stop_roots(
    roots: &[Root],
    grace: Duration,
    escalate: &mut dyn FnMut() -> bool,
) -> (io::Result<()>, Vec<StopOutcome>) {
    let mut plans: Vec<StopPlan> = roots.iter().map(|root| StopPlan::enumerate(*root)).collect();
    let mut first_error = Ok(());
    let mut outcomes = vec![StopOutcome::default(); plans.len()];
    for (plan, outcome) in plans.iter_mut().zip(outcomes.iter_mut()) {
        outcome.terminated = plan.running();
        if let (Err(error), _) = plan.signal(libc::SIGTERM) {
            plan.observation = plan.observation.combine(tree::Observation::Unknown);
            if first_error.is_ok() {
                first_error = Err(error);
            }
        }
    }
    let started = Instant::now();
    if !StopPlan::OBSERVABLE {
        // Nothing here can read whether a process is still running, so no
        // grace can end early: SIGKILL follows at once (see `stop_tree`).
        for plan in &mut plans {
            let _ = plan.signal(libc::SIGKILL);
        }
        return (first_error, outcomes);
    }
    let mut escalated = false;
    loop {
        if plans.iter_mut().all(|plan| plan.running() == 0) {
            break;
        }
        if escalate() {
            escalated = true;
            break;
        }
        let elapsed = started.elapsed();
        if elapsed >= grace {
            break;
        }
        std::thread::sleep(STOP_POLL_INTERVAL.min(grace - elapsed));
    }
    for outcome in &mut outcomes {
        outcome.escalated = escalated;
    }
    kill_until_quiet(&mut plans, &mut outcomes, started);
    (first_error, outcomes)
}

/// The kill phase (module docs, step 4): walk every plan again and SIGKILL
/// whatever runs, a round every [`ROUND_NAP`], until [`QUIET_ROUNDS`] rounds
/// in a row have found nothing or [`KILL_ROUNDS`] rounds have passed. A plan
/// that something ran in when the grace ended, or in any round since, is sent
/// SIGKILL every round from then on (its group signals are the probe that
/// finds a process its walk cannot see yet); until then a round asks its
/// groups with signal 0, which delivers nothing. `sigterm_at` is when the
/// stop's SIGTERM went out, for [`StopOutcome::killed_after`].
#[cfg(unix)]
fn kill_until_quiet(plans: &mut [StopPlan], outcomes: &mut [StopOutcome], sigterm_at: Instant) {
    kill_until_quiet_bounded(plans, outcomes, sigterm_at, KILL_ROUNDS, QUIET_ROUNDS);
}

#[cfg(unix)]
fn kill_until_quiet_bounded(
    plans: &mut [StopPlan],
    outcomes: &mut [StopOutcome],
    sigterm_at: Instant,
    round_limit: u16,
    quiet_rounds: u16,
) {
    // A stop that found nothing running when it began needs no quiet rounds
    // unless a round finds something (`QUIET_ROUNDS`).
    let mut doubted = plans.iter().any(|plan| plan.observed_running);
    let (mut quiet, mut rounds) = (0_u16, 0_u16);
    loop {
        let mut found = false;
        for (plan, outcome) in plans.iter_mut().zip(outcomes.iter_mut()) {
            plan.rewalk();
            let running = plan.running();
            if running > 0 && !plan.killing {
                plan.killing = true;
                outcome.killed_after = Some(sigterm_at.elapsed());
            }
            let (signal_result, mut answered) =
                plan.signal(if plan.killing { libc::SIGKILL } else { 0 });
            if signal_result.is_err() {
                plan.observation = plan.observation.combine(tree::Observation::Unknown);
            }
            answered &= GROUP_ANSWER_MEANS_RUNNING;
            if answered && !plan.killing {
                // A group the walk read as empty answered: a process is in it.
                plan.killing = true;
                outcome.killed_after = Some(sigterm_at.elapsed());
                if plan.signal(libc::SIGKILL).0.is_err() {
                    plan.observation = plan.observation.combine(tree::Observation::Unknown);
                }
            }
            outcome.killed = plan.killed;
            outcome.left = running;
            outcome.observed_running = plan.observed_running;
            found |= running > 0 || answered || plan.observation != tree::Observation::Complete;
        }
        doubted |= found;
        rounds += 1;
        quiet = if found { 0 } else { quiet + 1 };
        if !doubted || quiet >= quiet_rounds || rounds >= round_limit {
            for (plan, outcome) in plans.iter().zip(outcomes.iter_mut()) {
                outcome.observation = if !found && (!doubted || quiet >= quiet_rounds) {
                    plan.observation
                } else {
                    plan.observation.combine(tree::Observation::Exhausted)
                };
            }
            break;
        }
        std::thread::sleep(ROUND_NAP);
    }
}

#[cfg(not(unix))]
fn stop_roots(
    roots: &[Root],
    _grace: Duration,
    _escalate: &mut dyn FnMut() -> bool,
) -> (io::Result<()>, Vec<StopOutcome>) {
    // No process groups and no signals: a non-Unix owner stops its child with
    // `Child::kill` ([`stop_child`]); a pid alone cannot be stopped here.
    (Ok(()), vec![StopOutcome::default(); roots.len()])
}

/// One root's tree, as enumerated before anything is signalled and walked
/// again in every round of the kill phase.
#[cfg(unix)]
struct StopPlan {
    observation: tree::Observation,
    observed_running: bool,
    root: Root,
    /// The root's start while it runs, `None` once it does not (exited, or
    /// its pid no longer names the pinned process).
    root_start: Option<u64>,
    /// The root was sent SIGKILL while it ran (counted in `killed`).
    root_killed: bool,
    /// The process groups this stop may reach, in the order found: the
    /// root's own first, then one for each member found leading a group of
    /// its own. Kept after the leader is gone: what is left in the group
    /// may still be read ([`Access::Read`]).
    groups: Vec<Group>,
    /// Every other process found running in the tree or in one of `groups`,
    /// with its start, in the order found (tree breadth-first, then group).
    /// One that no longer runs with its start is dropped by the next walk.
    members: Vec<Member>,
    /// SIGKILL goes out every round: something ran when the grace ended, or
    /// a round found it.
    killing: bool,
    /// Processes sent SIGKILL while they ran, each once.
    killed: usize,
}

/// A process the stop found running, other than its root.
#[cfg(unix)]
#[derive(Clone, Copy, Debug)]
struct Member {
    pid: u32,
    start: u64,
    /// Sent SIGKILL while it ran (counted in [`StopPlan::killed`]).
    killed: bool,
}

/// A process group the stop may reach, and the leader that makes its id the
/// stop's to use.
#[cfg(unix)]
#[derive(Clone, Copy, Debug)]
struct Group {
    /// The group's id: its leader's pid.
    id: u32,
    leader: Leader,
    /// The id was read naming a process other than the leader: the group is
    /// gone, and is never read or signalled again.
    ended: bool,
}

/// How the stop knows a group's leader.
#[cfg(unix)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Leader {
    /// An unreaped child of the caller's, held for the whole stop
    /// ([`RootPin::OwnChild`]).
    Held,
    /// The process that started at this time ([`tree::Identity::start`]).
    Started(u64),
}

/// What the stop may do with a group right now ([`Group::access`]).
///
/// THE RULE (aterm `8722b107c`, `group::Live`): a group is signalled through
/// its id only while the stop holds its leader. A group's id is its leader's
/// pid, and the number names that group only while the leader is unreaped: the
/// kernel hands out no id in use as a pid or as a group's id, and a reaped
/// leader's id goes to the next process the kernel's counter reaches (a probe
/// that aimed for one had it 2.7 ms after the reap, measured by aterm's
/// change). Holding is: an unreaped child of the caller's for the whole stop
/// ([`Leader::Held`]), or the leader read with its start, running or exited
/// and not yet reaped, just before the signal ([`Leader::Started`]). Between
/// that read and the signal the leader can still be reaped and its id taken by
/// a new group's leader: a window of two system calls that also needs the
/// kernel's pid counter at that number, the window every member's signal has.
#[cfg(unix)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Access {
    /// The leader is held: the group may be signalled through its id.
    Signal,
    /// No process has the id: the leader is reaped. A group with that id,
    /// if one is left, is still the one the stop knew, because its id is not
    /// handed to a new process while it has a member; it is READ, and what is
    /// read in it is signalled by pid, never through the group's id. (A group
    /// that emptied can have its id taken; the read before the next one sees
    /// the process that took it, and the group is then [`Access::Gone`]. What
    /// that misses is a process that took the id, made a group, put a member
    /// in it and was reaped, all between two reads a round apart.)
    Read,
    /// The id names another process: the group is not the stop's.
    Gone,
    /// The leader's identity could not be read. Never signal through its id.
    Unknown,
}

#[cfg(unix)]
impl Group {
    fn access(&mut self) -> Access {
        if self.ended {
            return Access::Gone;
        }
        let Leader::Started(start) = self.leader else { return Access::Signal };
        match tree::observe_identity(self.id) {
            Ok(Some(identity)) if identity.start == start => Access::Signal,
            Ok(Some(_)) => {
                self.ended = true;
                Access::Gone
            }
            Ok(None) => Access::Read,
            Err(_) => Access::Unknown,
        }
    }
}

#[cfg(unix)]
impl StopPlan {
    /// Whether this platform can tell a running process from a gone one.
    const OBSERVABLE: bool = cfg!(any(target_os = "macos", target_os = "linux"));

    fn read<T>(&mut self, reading: Result<T, tree::Observation>) -> Option<T> {
        match reading {
            Ok(value) => Some(value),
            Err(fault) => {
                self.observation = self.observation.combine(fault);
                None
            }
        }
    }

    fn running_pid(&mut self, pid: u32, start: Option<u64>) -> bool {
        let runs = self.read(tree::observe_running(pid, start)).unwrap_or(false);
        self.observed_running |= runs;
        runs
    }

    fn enumerate(root: Root) -> Self {
        let mut plan = StopPlan {
            observation: if Self::OBSERVABLE {
                tree::Observation::Complete
            } else {
                tree::Observation::Unknown
            },
            observed_running: false,
            root,
            root_start: None,
            root_killed: false,
            groups: vec![Group { id: root.pid, leader: Leader::Held, ended: false }],
            members: Vec::new(),
            killing: false,
            killed: 0,
        };
        plan.rewalk();
        plan
    }

    /// Re-read the root's pid before a walk or a signal. A [`RootPin::Started`]
    /// root may be reaped by its owner during the grace and its pid given to
    /// another process: from then on neither the tree under that pid nor the
    /// group with its id is the root's, and neither is walked or signalled
    /// again (its group's [`Access`]). An [`RootPin::OwnChild`] root is held
    /// unreaped by the caller, so its pid cannot change hands.
    fn refresh_root(&mut self) {
        let pid = self.root.pid;
        let (leader, start) = match self.root.pin {
            RootPin::OwnChild => (
                Leader::Held,
                self.read(tree::observe_identity(pid))
                    .flatten()
                    .filter(|identity| !identity.zombie)
                    .map(|identity| identity.start),
            ),
            RootPin::Started(start) => {
                (Leader::Started(start), self.running_pid(pid, Some(start)).then_some(start))
            }
        };
        self.groups[0].leader = leader;
        self.root_start = start;
        self.observed_running |= start.is_some();
    }

    /// Add whatever now runs under the root, under each member, and in every
    /// group the stop may read. Members already listed keep their place, so
    /// the SIGKILL order is the SIGTERM order.
    fn rewalk(&mut self) {
        self.refresh_root();
        // A member that no longer runs with its start is never signalled
        // again, and keeping it would only fill the list; nor is a group
        // whose id names another process (the root's own stays first).
        let mut retained = Vec::with_capacity(self.members.len());
        for member in std::mem::take(&mut self.members) {
            match self.read(tree::observe_running(member.pid, Some(member.start))) {
                Some(false) => {}
                // Keep an unreadable known member so a later successful read
                // can still clean it; it is never signalled without identity.
                Some(true) | None => retained.push(member),
            }
        }
        self.members = retained;
        let mut index = 0;
        self.groups.retain(|group| {
            index += 1;
            index == 1 || !group.ended
        });
        let mut walked = BTreeSet::new();
        let mut found = Vec::new();
        let root = self.root.pid;
        if self.root_start.is_some() {
            self.observation =
                self.observation.combine(tree::observe_process_tree(root, &mut found));
            walked.extend(found.iter().copied());
            for &pid in &found {
                self.admit(pid);
            }
        }
        // Each group and each member once per walk, the ones found on the way
        // included: a member orphaned onto init is no longer under the root,
        // and what a member's group holds is in no tree of ours.
        let (mut next_group, mut next_member) = (0, 0);
        while next_group < self.groups.len() || next_member < self.members.len() {
            if next_group < self.groups.len() {
                self.read_group(next_group, &mut found);
                next_group += 1;
                continue;
            }
            let Member { pid, start, .. } = self.members[next_member];
            next_member += 1;
            if !self.running_pid(pid, Some(start)) {
                continue;
            }
            if !walked.contains(&pid) {
                self.observation =
                    self.observation.combine(tree::observe_process_tree(pid, &mut found));
                walked.extend(found.iter().copied());
                for &child in &found {
                    self.admit(child);
                }
            }
            // A child leads its group only once its own `setpgid` has run,
            // which can be after the walk that found it.
            self.note_group_led_by(pid, start);
        }
    }

    /// Admit what group `index` holds now, unless its id names another
    /// process ([`Access`]).
    fn read_group(&mut self, index: usize, found: &mut Vec<u32>) {
        match self.groups[index].access() {
            Access::Gone => return,
            Access::Unknown => {
                self.observation = self.observation.combine(tree::Observation::Unknown);
                return;
            }
            _ => {}
        }
        let id = self.groups[index].id;
        self.observation = self.observation.combine(tree::observe_process_group(id, found));
        for &pid in found.iter() {
            // The leader is the root or a member already, or, in a group
            // whose leader is reaped, a newcomer that is not the stop's.
            // A group walk follows no parent edge, so it applies the tree
            // walk's exclusion itself.
            if pid != id {
                if self.read(tree::observe_daemon(pid)) == Some(false) {
                    self.admit(pid);
                }
            }
        }
    }

    fn admit(&mut self, pid: u32) {
        if pid == self.root.pid
            || pid == std::process::id()
            || self.members.iter().any(|member| member.pid == pid)
        {
            return;
        }
        if self.members.len() >= tree::MAX_PROCESS_TREE_MEMBERS {
            self.observation = self.observation.combine(tree::Observation::Exhausted);
            return;
        }
        if let Some(identity) =
            self.read(tree::observe_identity(pid)).flatten().filter(|identity| !identity.zombie)
        {
            self.observed_running = true;
            self.members.push(Member { pid, start: identity.start, killed: false });
            self.note_group_led_by(pid, identity.start);
        }
    }

    /// Track the group `pid` (which started at `start`) leads, if it leads
    /// one. A group already tracked under that id whose leader is reaped is
    /// replaced: the id has been handed out again, so the old group is gone.
    fn note_group_led_by(&mut self, pid: u32, start: u64) {
        if pid == self.root.pid || self.read(tree::observe_group_leader(pid)) != Some(true) {
            return;
        }
        let group = Group { id: pid, leader: Leader::Started(start), ended: false };
        if let Some(known) = self.groups.iter_mut().find(|known| known.id == pid) {
            if known.leader != group.leader {
                *known = group;
            }
        } else if self.groups.len() < tree::MAX_PROCESS_TREE_MEMBERS {
            // Past the bound its leader is signalled alone, as any member.
            self.groups.push(group);
        } else {
            self.observation = self.observation.combine(tree::Observation::Exhausted);
        }
    }

    /// How many of the root and its members are running now.
    fn running(&mut self) -> usize {
        let root =
            self.root_start.is_some_and(|start| self.running_pid(self.root.pid, Some(start)));
        let mut running = usize::from(root);
        for index in 0..self.members.len() {
            let member = self.members[index];
            running += usize::from(self.running_pid(member.pid, Some(member.start)));
        }
        running
    }

    /// Send `signal` (0 asks and delivers nothing) to the root's group, the
    /// root, each other group the stop holds the leader of, and every other
    /// member still running with the start it was found with, alone. A
    /// SIGKILL counts each process it reaches while it runs once
    /// ([`StopPlan::killed`]). Returns the root's group's error (other than
    /// "no such group"), which is what the group kill this replaces returned,
    /// and whether any group signal found a process.
    fn signal(&mut self, signal: libc::c_int) -> (io::Result<()>, bool) {
        self.refresh_root();
        let Ok(root) = libc::pid_t::try_from(self.root.pid) else {
            return (
                Err(io::Error::new(io::ErrorKind::InvalidInput, "pid does not fit pid_t")),
                false,
            );
        };
        if root <= 0 {
            return (Err(io::Error::new(io::ErrorKind::InvalidInput, "not a process id")), false);
        }
        let killing = signal == libc::SIGKILL;
        // Which members run, and in which group, BEFORE anything is sent: a
        // group's SIGKILL can end a member before its own turn below, and the
        // account is of what the SIGKILL reached, not of what was still there
        // to be read after it (LIFECYCLE-KILL-COUNT-1, docs/KNOWN_HAZARDS.md).
        let mut ran_in = Vec::new();
        if killing {
            for index in 0..self.members.len() {
                let member = self.members[index];
                ran_in.push(self.read(running_group_of(member.pid, member.start)).flatten());
            }
        }
        let mut reached_groups: Vec<libc::pid_t> = Vec::new();
        let mut result = Ok(());
        let mut answered = false;
        let root_access = self.groups[0].access();
        if root_access == Access::Unknown {
            self.observation = self.observation.combine(tree::Observation::Unknown);
        }
        if root_access == Access::Signal {
            match send_group(root, signal) {
                Ok(()) => {
                    answered = true;
                    reached_groups.push(root);
                }
                // No such group: nothing of it is left.
                Err(error) if error.raw_os_error() == Some(libc::ESRCH) => {}
                // macOS answers EPERM for a group down to its unreaped leader
                // ([`GROUP_ANSWER_MEANS_RUNNING`]): nothing in it runs, so
                // there is nothing to stop. EPERM reads so only where the
                // group's own listing shows no member running; a running
                // member this process may not signal keeps it an error.
                // (Before 2026-10-21 every such stop failed, and a bounded
                // probe whose stream an outsider held reported that its group
                // "could not be terminated": land-gate run 15.)
                Err(error)
                    if error.raw_os_error() == Some(libc::EPERM)
                        && !group_has_running_member(self.root.pid) => {}
                Err(error) => result = Err(error),
            }
        }
        // The root itself, which the group signal reached only if it leads its
        // group (a child spawned without `configure_own_group` does not).
        let root_signal_allowed = match self.root.pin {
            RootPin::OwnChild => true,
            RootPin::Started(start) => self.running_pid(self.root.pid, Some(start)),
        };
        if root_signal_allowed
            && self.read(tree::observe_group_leader(self.root.pid)) == Some(false)
        {
            // SAFETY: `kill` takes no pointers; `root` is pinned by `RootPin`.
            let _ = unsafe { libc::kill(root, signal) };
        }
        if killing && self.root_start.is_some() && !self.root_killed {
            self.root_killed = true;
            self.killed += 1;
        }
        let StopPlan { groups, members, killed, observation, observed_running, .. } = self;
        for group in groups.iter_mut().skip(1) {
            let access = group.access();
            if access == Access::Unknown {
                *observation = observation.combine(tree::Observation::Unknown);
            }
            if access != Access::Signal {
                continue;
            }
            let Ok(id) = libc::pid_t::try_from(group.id) else {
                *observation = observation.combine(tree::Observation::Unknown);
                continue;
            };
            // A non-positive id would mean "my own group" or "everything".
            if id > 0 {
                match send_group(id, signal) {
                    Ok(()) => {
                        answered = true;
                        reached_groups.push(id);
                    }
                    Err(error) if error.raw_os_error() == Some(libc::ESRCH) => {}
                    Err(error)
                        if error.raw_os_error() == Some(libc::EPERM)
                            && !group_has_running_member(group.id) => {}
                    Err(_) => {
                        *observation = observation.combine(tree::Observation::Unknown);
                    }
                }
            }
        }
        #[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
        if killing {
            tests::after_group_signals(members.as_slice());
        }
        for (index, member) in members.iter_mut().enumerate() {
            // Ran in a group whose SIGKILL just went out: that signal reached it,
            // whether or not it has ended by the time this loop reads it.
            let by_group = ran_in
                .get(index)
                .copied()
                .flatten()
                .is_some_and(|group| reached_groups.contains(&group));
            let mut reached = by_group;
            let running = match tree::observe_running(member.pid, Some(member.start)) {
                Ok(running) => running,
                Err(fault) => {
                    *observation = observation.combine(fault);
                    false
                }
            };
            if running {
                *observed_running = true;
                // A running leader with its start: its group's signal reached it.
                let leads_signalled = groups.iter().skip(1).any(|group| {
                    group.id == member.pid && group.leader == Leader::Started(member.start)
                });
                if !leads_signalled {
                    if let Ok(pid) = libc::pid_t::try_from(member.pid) {
                        if pid > 0 {
                            // SAFETY: `kill` takes no pointers; the member was
                            // re-read just above with the start it was found with.
                            let _ = unsafe { libc::kill(pid, signal) };
                        }
                    }
                }
                reached = true;
            }
            if killing && reached && !member.killed {
                member.killed = true;
                *killed += 1;
            }
        }
        *observed_running |= answered && GROUP_ANSWER_MEANS_RUNNING;
        (result, answered)
    }
}

/// The group `pid` runs in, when it runs with `start`; `None` when it does not
/// run (exited, a zombie, or its pid names another process) or its group
/// cannot be read.
#[cfg(unix)]
fn running_group_of(pid: u32, start: u64) -> Result<Option<libc::pid_t>, tree::Observation> {
    if !tree::observe_running(pid, Some(start))? {
        return Ok(None);
    }
    let pid =
        libc::pid_t::try_from(pid).ok().filter(|pid| *pid > 0).ok_or(tree::Observation::Unknown)?;
    // SAFETY: `getpgid` takes no pointers.
    let group = unsafe { libc::getpgid(pid) };
    if group > 0 {
        Ok(Some(group))
    } else if io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH) {
        Ok(None)
    } else {
        Err(tree::Observation::Unknown)
    }
}

/// Whether the kernel lists a member of process group `id` that runs (has not
/// exited). `true` when the group cannot be listed, which proves nothing.
#[cfg(unix)]
fn group_has_running_member(id: u32) -> bool {
    let mut members = Vec::new();
    tree::observe_process_group(id, &mut members) != tree::Observation::Complete
        || members.iter().any(|&pid| tree::observe_running(pid, None).unwrap_or(true))
}

/// `kill(-id, signal)`: did it find a process? The one place the stop
/// signals a group through its id, so every caller owes [`Access::Signal`]
/// for `id` at its call.
#[cfg(unix)]
fn send_group(id: libc::pid_t, signal: libc::c_int) -> io::Result<()> {
    #[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
    if signal == 0 && tests::positive_group_probe() {
        return Ok(());
    }
    #[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
    tests::note_group_signal(id, signal);
    // SAFETY: `kill` takes no pointers; `-id` names exactly the group whose
    // leader the caller holds ([`Access::Signal`]).
    if unsafe { libc::kill(-id, signal) } == 0 { Ok(()) } else { Err(io::Error::last_os_error()) }
}

/// Stop every child owned right now under one grace, polling `escalate`
/// (the signal path's form; [`signals`]): how many trees, and what was done.
pub(crate) fn stop_owned(
    cause: StopCause,
    escalate: &mut dyn FnMut() -> bool,
) -> (usize, StopOutcome) {
    let roots = owned_roots();
    let (_, outcome) = stop_roots_recorded(&roots, cause, STOP_GRACE, escalate);
    (roots.len(), outcome)
}

/// Start the lifecycle for this process, first thing in `main`, while the
/// process has one thread, so the descriptors this creates are close-on-exec
/// before any other thread can spawn a child that would inherit them: the
/// sentinel's socket, then the signal handlers and their stopper thread.
///
/// When this process IS a stop sentinel (`targo-trust __targo_stop_sentinel`,
/// which only targo-trust starts), it runs the sentinel and exits instead: a
/// sentinel installs nothing and owns nothing.
pub(crate) fn start() {
    if std::env::args_os().nth(1).is_some_and(|arg| arg == sentinel::SUBCOMMAND) {
        std::process::exit(sentinel::run());
    }
    sentinel::install();
    signals::install();
}

#[cfg(test)]
mod tests;
