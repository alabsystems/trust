// Unit tests for the one stop path, the ownership registry and the sentinel's
// record format, on fixtures these tests spawn. The signal handlers, the parent
// watch and the sentinel process run end to end in `tests/full_verifier_flag.rs`
// (its `process_lifecycle` module), against the real binary: a unit-test
// executable is a libtest harness, and it installs neither.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(any(target_os = "macos", target_os = "linux"))]

use std::cell::RefCell;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use super::{
    Access, Ownership, Root, RootPin, StopCause, StopOutcome, configure_own_group, recorded_stops,
    stop_roots_recorded, stop_tree, tree,
};

/// A hang detector, not a latency budget: what must happen happens long
/// before it on any host.
const HANG: Duration = Duration::from_secs(60);

thread_local! {
    /// The group signals this thread's stops sent, `(group id, signal)`,
    /// while a test records them ([`recording_group_signals`]).
    static GROUP_SIGNALS: RefCell<Option<Vec<(libc::pid_t, libc::c_int)>>> =
        const { RefCell::new(None) };
    static POSITIVE_GROUP_PROBE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(super) fn positive_group_probe() -> bool {
    POSITIVE_GROUP_PROBE.with(std::cell::Cell::get)
}

#[test]
fn an_initial_root_identity_is_live_evidence_before_any_signal_count() {
    let mut child = spawn_group("exec sleep 30", &[]);
    let plan = super::StopPlan::enumerate(Root { pid: child.id(), pin: RootPin::OwnChild });
    let observed = plan.observed_running;
    let start = plan.root_start;
    let _ = stop_tree(child.id(), StopCause::Error);
    child.wait().unwrap();
    assert!(start.is_some(), "the owned fixture was observed running");
    assert!(observed, "that positive identity must survive a later zero count");
}

#[test]
fn failed_and_capped_observations_do_not_certify_an_owned_tree_as_quiet() {
    use tree::{Observation, ReadKind, with_read_fault};
    for (kind, fault) in [
        (ReadKind::Tree, Observation::Unknown),
        (ReadKind::Identity, Observation::Unknown),
        (ReadKind::Image, Observation::Unknown),
        (ReadKind::Group, Observation::Unknown),
        (ReadKind::Group, Observation::Exhausted),
    ] {
        let dir = scratch("observation");
        let ready = dir.join("ready");
        let mut child = spawn_group("sleep 30 & printf ready > \"$1\"; wait", &[&ready]);
        await_file(&ready);
        let root = Root { pid: child.id(), pin: RootPin::OwnChild };
        let (_, outcome) = with_read_fault(kind, fault, || {
            stop_roots_recorded(&[root], StopCause::Error, Duration::ZERO, &mut || false)
        });
        // Fault injection is over before retiring anything it prevented us from
        // observing; only this test's unreaped child/group can be signalled.
        let _ = stop_tree(child.id(), StopCause::Error);
        child.wait().unwrap();
        let _ = std::fs::remove_dir_all(dir);
        assert_ne!(outcome.observation, Observation::Complete, "{kind:?}: {outcome:?}");
    }
}

#[cfg(target_os = "macos")]
#[test]
fn a_positive_group_probe_with_no_observed_pid_exhausts_without_claiming_quiet() {
    let mut child = spawn_group("exit 0", &[]);
    while !crate::bounded_process::exited_without_reaping(&mut child).unwrap() {
        std::thread::sleep(Duration::from_millis(1));
    }
    let mut plans = [super::StopPlan::enumerate(Root { pid: child.id(), pin: RootPin::OwnChild })];
    let mut outcomes = [StopOutcome::default()];
    POSITIVE_GROUP_PROBE.with(|probe| probe.set(true));
    super::kill_until_quiet_bounded(&mut plans, &mut outcomes, Instant::now(), 1, 40);
    POSITIVE_GROUP_PROBE.with(|probe| probe.set(false));
    child.wait().unwrap();
    let outcome = outcomes[0];
    assert_eq!((outcome.terminated, outcome.killed, outcome.left), (0, 0, 0));
    assert!(outcome.observed_running, "the meaningful group answer is live evidence");
    assert_eq!(outcome.observation, tree::Observation::Exhausted);
}

/// The stop's seam (`send_group`, test builds only): note a group signal.
pub(super) fn note_group_signal(group: libc::pid_t, signal: libc::c_int) {
    GROUP_SIGNALS.with(|log| {
        if let Some(log) = log.borrow_mut().as_mut() {
            log.push((group, signal));
        }
    });
}

/// Start (`true`) or end recording the group signals this thread's stops send.
fn recording_group_signals(on: bool) {
    GROUP_SIGNALS.with(|log| *log.borrow_mut() = on.then(Vec::new));
}

/// The group signals recorded on this thread so far.
fn group_signals() -> Vec<(libc::pid_t, libc::c_int)> {
    GROUP_SIGNALS.with(|log| log.borrow().clone().unwrap_or_default())
}

thread_local! {
    /// While set, this thread's SIGKILLs wait after their group signals until
    /// no member still runs ([`after_group_signals`]).
    static SETTLE_AFTER_GROUP_KILL: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The stop's seam (`StopPlan::signal`, test builds only), between a SIGKILL's
/// group signals and its member loop: when this thread asked for it, wait
/// until every member has ended. That is the order LIFECYCLE-KILL-COUNT-1's
/// red runs took by chance (the group signal ended the fake compile's `sleep`
/// before the loop read it); here it is taken every time.
pub(super) fn after_group_signals(members: &[super::Member]) {
    if !SETTLE_AFTER_GROUP_KILL.with(std::cell::Cell::get) {
        return;
    }
    let deadline = Instant::now() + HANG;
    while members.iter().any(|member| tree::still_running(member.pid, Some(member.start))) {
        assert!(Instant::now() < deadline, "a member outlived its group's SIGKILL");
        std::thread::sleep(Duration::from_millis(1));
    }
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust-lifecycle-{name}-{}-{}",
        std::process::id(),
        Instant::now().elapsed().as_nanos()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("scratch directory");
    dir
}

/// `/bin/sh -c <script> fixture <args...>` in a process group of its own.
fn spawn_group(script: &str, args: &[&Path]) -> Child {
    spawn_group_asserting_on(script, args, &[])
}

/// As [`spawn_group`], with each signal in `asserts_on` at its default action
/// in the fixture ([`default_dispositions`]).
fn spawn_group_asserting_on(
    script: &str,
    args: &[&Path],
    asserts_on: &'static [libc::c_int],
) -> Child {
    let mut command = Command::new("/bin/sh");
    command.arg("-c").arg(script).arg("fixture").args(args);
    command.stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null());
    configure_own_group(&mut command);
    default_dispositions(&mut command, asserts_on);
    hold_no_other_descriptor(&mut command);
    command.spawn().expect("spawn fixture")
}

/// Put each signal in `asserts_on` back to its default action in the process
/// `command` starts, whatever this test binary inherited.
///
/// A test that asserts on what SIGTERM does must set what SIGTERM does: a
/// launcher that ignores it hands the ignore to everything this binary
/// starts, a fixture's `exec sleep` then dies of the stop's SIGKILL instead,
/// and a shell started with SIGTERM ignored cannot even trap it. Measured
/// 2026-10-13/14 under a launcher that ignores SIGTERM: 10 of these 14 tests
/// passed and 4 failed, on main and on this branch alike. So each test names
/// the signals whose default action it asserts on and nothing else is reset;
/// the fixtures that ignore SIGTERM on purpose (`trap '' TERM`) set that
/// themselves.
///
/// Call it BEFORE [`hold_no_other_descriptor`]: hooks run in the order they
/// were added, and that one also closes the pipe through which `spawn` waits
/// for the exec, so `spawn` returns as soon as it has run. A reset added after
/// it races the caller's first signal: measured 2026-10-14 under a launcher
/// that ignores SIGTERM, `a_root_whose_pid_changes_hands_during_the_grace_is_not_signalled`
/// stopped its fixture before the reset and saw it end by the stop's SIGKILL.
fn default_dispositions(command: &mut Command, asserts_on: &'static [libc::c_int]) {
    use std::os::unix::process::CommandExt as _;
    if asserts_on.is_empty() {
        return;
    }
    // SAFETY: the closure runs between fork and exec and calls only
    // `signal`, which is async-signal-safe; `asserts_on` is static, so
    // nothing allocates.
    unsafe {
        command.pre_exec(move || {
            for &signal in asserts_on {
                if libc::signal(signal, libc::SIG_DFL) == libc::SIG_ERR {
                    return Err(std::io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }
}

/// A fixture keeps only its stdio. The harness runs tests in parallel, and a
/// pipe another test is creating is close-on-exec only after a second call
/// (`pipe` then `fcntl` on macOS): a fixture forked in between would hold that
/// test's pipe open for as long as it lives. Some fixtures here live through a
/// grace on purpose, so they close everything else before exec.
fn hold_no_other_descriptor(command: &mut Command) {
    use std::os::unix::process::CommandExt as _;
    // SAFETY: the closure runs between fork and exec and calls only `close`,
    // which is async-signal-safe; it allocates nothing.
    unsafe {
        command.pre_exec(|| {
            for fd in 3..1024 {
                libc::close(fd);
            }
            Ok(())
        });
    }
}

fn await_file(path: &Path) -> String {
    let deadline = Instant::now() + HANG;
    loop {
        if let Ok(text) = std::fs::read_to_string(path) {
            if !text.is_empty() {
                return text;
            }
        }
        assert!(Instant::now() < deadline, "{} never appeared", path.display());
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[cfg(unix)]
fn signal_of(child: &mut Child) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt as _;
    child.wait().expect("reap fixture").signal()
}

/// SIGTERM comes first and is enough for a process that honours it: the
/// fixture's TERM trap runs (it would not under SIGKILL), its background
/// child in the same group goes with it, nothing needs SIGKILL, and the stop
/// is recorded with its cause.
///
/// `ready` is written by the background member ITSELF, as a shell of its own,
/// before it becomes `sleep`: by then it has been through an exec, so it has
/// SIGTERM's default action whenever the stop arrives. A `sleep 30 &` with
/// `ready` written by the leader does not say that. `fork` copies the leader's
/// TERM handler into the child, and the shell puts the default back only on
/// its way to exec; a SIGTERM that lands in between is delivered to the child
/// and taken by the leader's handler there, and the `sleep` the child then
/// becomes never sees a signal. Measured 2026-10-13 with no Trust code: with
/// `ready` polled every 1ms that fixture left its child running after 20 of
/// 300 group SIGTERMs (2 of 300 at this file's 10ms poll), every time a child
/// already listed in the group and still a shell, which one more SIGTERM then
/// ended; the same script without the trap lost 0 of 300, a C replica saw the
/// inherited handler run in the child in all 216 of its survivors, and this
/// fixture lost 0 of 600. Here it read as "killed: 1", ten seconds later.
#[test]
fn a_stop_sends_sigterm_first_and_records_its_cause() {
    let dir = scratch("term");
    let trapped = dir.join("trapped");
    let ready = dir.join("ready");
    // Asserts on a TERM trap and on SIGTERM's default action in the sleep.
    let mut child = spawn_group_asserting_on(
        "trap 'printf term > \"$1\"; exit 0' TERM; \
         /bin/sh -c 'printf ready > \"$0\"; exec sleep 30' \"$2\" & wait",
        &[&trapped, &ready],
        &[libc::SIGTERM],
    );
    await_file(&ready);
    let outcome = stop_tree(child.id(), StopCause::Error).expect("the group signal succeeds");
    let status = child.wait().expect("reap fixture");
    let trapped_text = std::fs::read_to_string(&trapped).unwrap_or_default();
    let records = recorded_stops();
    let _ = std::fs::remove_dir_all(&dir);

    assert_eq!(trapped_text, "term", "the fixture's TERM trap must have run");
    assert!(status.success(), "the fixture exits from its trap: {status:?}");
    assert_eq!(outcome.terminated, 2, "the shell and its sleep were running: {outcome:?}");
    assert_eq!(outcome.killed, 0, "nothing ignored SIGTERM: {outcome:?}");
    assert!(
        records.iter().any(|record| record.root == child.id()
            && record.cause == StopCause::Error
            && record.outcome == outcome),
        "the stop must be recorded with its cause: {records:?}"
    );
}

/// A process that ignores SIGTERM is sent SIGKILL when the grace ends, and so
/// is its descendant (which inherited the ignore); the outcome says when.
#[test]
fn a_process_that_ignores_sigterm_is_killed_after_the_grace() {
    let dir = scratch("ignore");
    let ready = dir.join("ready");
    let mut child = spawn_group("trap '' TERM; sleep 30 & printf ready > \"$1\"; wait", &[&ready]);
    await_file(&ready);
    let started = Instant::now();
    let root = Root { pid: child.id(), pin: RootPin::OwnChild };
    let (result, outcome) =
        stop_roots_recorded(&[root], StopCause::Bound, Duration::from_millis(300), &mut || false);
    let elapsed = started.elapsed();
    let signal = signal_of(&mut child);
    let _ = std::fs::remove_dir_all(&dir);

    result.expect("the group signal succeeds");
    assert_eq!(signal, Some(libc::SIGKILL), "the shell outlived SIGTERM, so SIGKILL ended it");
    assert_eq!(
        (outcome.terminated, outcome.killed, outcome.escalated, outcome.left),
        (2, 2, false, 0),
        "{outcome:?}"
    );
    let killed_after = outcome.killed_after.expect("a SIGKILL went out");
    assert!(
        killed_after >= Duration::from_millis(300) && killed_after <= elapsed,
        "the SIGKILL follows the grace, inside the stop: {killed_after:?} of {elapsed:?}"
    );
    assert!(elapsed >= Duration::from_millis(300), "the grace must be spent first: {elapsed:?}");
}

/// The SIGKILL account counts what the SIGKILL reached, even when the group
/// signal has ended a member before the member loop reads it
/// (LIFECYCLE-KILL-COUNT-1). The seam ([`after_group_signals`]) makes that
/// order certain: the shell and its `sleep` both ignore SIGTERM, the group
/// SIGKILL ends both, and only then are the members read. Counting what was
/// still running after the signal (the code before this fix) reads
/// "SIGKILL to 1" here every time; the members are read before it now.
#[test]
fn a_member_the_group_sigkill_ended_first_is_counted() {
    let dir = scratch("kill-count");
    let ready = dir.join("ready");
    let mut child = spawn_group("trap '' TERM; sleep 30 & printf ready > \"$1\"; wait", &[&ready]);
    await_file(&ready);
    let root = Root { pid: child.id(), pin: RootPin::OwnChild };
    SETTLE_AFTER_GROUP_KILL.with(|settle| settle.set(true));
    let (result, outcome) =
        stop_roots_recorded(&[root], StopCause::Bound, Duration::from_millis(100), &mut || false);
    SETTLE_AFTER_GROUP_KILL.with(|settle| settle.set(false));
    let signal = signal_of(&mut child);
    let _ = std::fs::remove_dir_all(&dir);

    result.expect("the group signal succeeds");
    assert_eq!(signal, Some(libc::SIGKILL), "the shell outlived SIGTERM, so SIGKILL ended it");
    assert_eq!((outcome.terminated, outcome.killed, outcome.left), (2, 2, 0), "{outcome:?}");
    let words = outcome.kill_words(None).unwrap_or_default();
    assert!(words.starts_with("SIGKILL to 2 still running"), "the account names both: {words}");
}

/// The signal path's escalation: a second signal ends the grace at once.
#[test]
fn escalation_ends_the_grace_at_once() {
    let dir = scratch("escalate");
    let ready = dir.join("ready");
    let mut child = spawn_group("trap '' TERM; printf ready > \"$1\"; sleep 30", &[&ready]);
    await_file(&ready);
    let started = Instant::now();
    let root = Root { pid: child.id(), pin: RootPin::OwnChild };
    let mut polls = 0;
    let (result, outcome) = stop_roots_recorded(&[root], StopCause::Error, HANG, &mut || {
        polls += 1;
        polls > 1
    });
    let elapsed = started.elapsed();
    let signal = signal_of(&mut child);
    let _ = std::fs::remove_dir_all(&dir);

    result.expect("the group signal succeeds");
    assert!(outcome.escalated, "{outcome:?}");
    assert!(outcome.killed >= 1, "{outcome:?}");
    assert_eq!(signal, Some(libc::SIGKILL));
    assert!(elapsed < HANG, "an escalated stop must not wait out its grace: {elapsed:?}");
}

/// A root pinned by its start is never signalled once its pid names a
/// different start: that is a recycled pid, and the process is a stranger.
#[test]
fn a_pid_that_names_another_start_is_never_signalled() {
    let mut child = spawn_group("exec sleep 30", &[]);
    let start = tree::identity(child.id()).expect("a live child has an identity").start;
    let stranger = Root { pid: child.id(), pin: RootPin::Started(start.wrapping_add(1)) };
    let (result, outcome) = stop_roots_recorded(
        &[stranger],
        StopCause::Released,
        Duration::from_millis(50),
        &mut || false,
    );
    let survived = tree::still_running(child.id(), Some(start));
    let _ = stop_tree(child.id(), StopCause::Error);
    let _ = child.wait();

    result.expect("nothing was signalled, so nothing failed");
    assert_eq!(
        outcome,
        StopOutcome { observation: tree::Observation::Complete, ..StopOutcome::default() }
    );
    assert!(survived, "a process whose start differs from the pin must not be signalled");
}

/// A root another thread may reap is re-read before every signal: once its
/// pid names a different start, neither that process nor its group is
/// signalled, although the stop began while the pid was still the root's.
#[test]
fn a_root_whose_pid_changes_hands_during_the_grace_is_not_signalled() {
    // Asserts that SIGTERM, by its default action, is what ends the fixture.
    let mut child = spawn_group_asserting_on("exec sleep 30", &[], &[libc::SIGTERM]);
    let start = tree::identity(child.id()).expect("a live child has an identity").start;
    let mut plan =
        super::StopPlan::enumerate(Root { pid: child.id(), pin: RootPin::Started(start) });
    let enumerated = (plan.root_start, plan.groups[0].access());
    // The pid now names another process: the pin's start is no longer its start.
    plan.root.pin = RootPin::Started(start.wrapping_add(1));
    let (result, answered) = plan.signal(libc::SIGKILL);
    // The fixture is ended here with SIGTERM; its exit says which signal came
    // first, which a read of its state right after `kill` could not.
    let _ = stop_tree(child.id(), StopCause::Error);
    let ended_by = signal_of(&mut child);

    assert_eq!(enumerated, (Some(start), Access::Signal), "the stop began on the root itself");
    result.expect("nothing was signalled, so nothing failed");
    assert!(!answered, "no group was signalled");
    assert_eq!(
        ended_by,
        Some(libc::SIGTERM),
        "a pid that changed hands during the grace must not be signalled"
    );
}

/// The sentinel holds none of targo-trust's descriptors: one that is not
/// close-on-exec (what another thread's `pipe` is until its `fcntl`) is not
/// open in a child spawned the sentinel's way.
#[test]
fn a_child_spawned_the_sentinels_way_holds_only_its_stdio() {
    // A descriptor far above any the child opens itself, not close-on-exec
    // (`F_DUPFD` clears the flag), as a racing `pipe` leaves one.
    // SAFETY: `fcntl` on our own stderr; the duplicate is closed below.
    let stray = unsafe { libc::fcntl(libc::STDERR_FILENO, libc::F_DUPFD, 200) };
    assert!(stray >= 200, "duplicate stderr: {}", std::io::Error::last_os_error());
    let mut command = Command::new("/bin/ls");
    command.arg("/dev/fd").stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::null());
    configure_own_group(&mut command);
    super::sentinel::hold_only_stdio_for_test(&mut command);
    let output = command.output();
    // SAFETY: `stray` is the descriptor duplicated above, closed once.
    unsafe { libc::close(stray) };
    let output = output.expect("list the child's descriptors");
    let listed: Vec<i32> = String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .filter_map(|name| name.parse().ok())
        .collect();

    assert!(output.status.success(), "{output:?}");
    assert!(listed.contains(&1), "the listing is the child's own: {listed:?}");
    assert!(!listed.contains(&stray), "fd {stray} reached the child: {listed:?}");
}

/// An ownership dropped while its child still runs stops the child, so no
/// owned child outlives its owner's scope.
#[test]
fn a_released_running_child_is_stopped() {
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "exec sleep 30"]).stdin(Stdio::null());
    // Asserts that SIGTERM, by its default action, is what ends the child.
    default_dispositions(&mut command, &[libc::SIGTERM]);
    hold_no_other_descriptor(&mut command);
    let (mut child, ownership) = super::spawn_owned(&mut command).expect("spawn owned fixture");
    let pid = ownership.pid();
    assert!(super::owned_count() >= 1);
    drop(ownership);
    let signal = signal_of(&mut child);
    assert_eq!(signal, Some(libc::SIGTERM), "the release must have stopped it with SIGTERM");
    assert!(
        recorded_stops()
            .iter()
            .any(|record| record.root == pid && record.cause == StopCause::Released),
        "the release must be recorded"
    );
}

/// Every owned child's scope ends in its release, so the release is where a
/// thread holds once the run's stop has begun: whatever the child produced
/// (a benchmark row, a smoke's defect) never reaches the caller.
#[test]
fn a_release_holds_the_thread_once_the_stop_has_begun() {
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "exit 0"]).stdin(Stdio::null());
    hold_no_other_descriptor(&mut command);
    let (mut child, ownership) = super::spawn_owned(&mut command).expect("spawn owned fixture");
    let pid = ownership.pid();
    child.wait().expect("reap fixture");
    super::signals::hold_panics_here(true);
    let released = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(ownership)));
    super::signals::hold_panics_here(false);

    let held = released
        .err()
        .and_then(|payload| payload.downcast_ref::<String>().cloned())
        .is_some_and(|message| message == super::signals::HELD);
    assert!(held, "the release returned to its caller although the stop had begun");
    assert!(!super::owned_roots().iter().any(|root| root.pid == pid), "released first");
}

/// What remains of an exited leader's group is stopped before the leader is
/// reaped; an exited leader alone is no running process.
#[test]
fn an_exited_leaders_group_remainder_is_stopped() {
    let dir = scratch("remainder");
    let pid_file = dir.join("pid");
    let mut child = spawn_group("sleep 30 & printf '%s' \"$!\" > \"$1\"; exit 0", &[&pid_file]);
    let sleeper: u32 = await_file(&pid_file).parse().expect("numeric pid");
    let deadline = Instant::now() + HANG;
    while !crate::bounded_process::exited_without_reaping(&mut child).expect("poll leader") {
        assert!(Instant::now() < deadline, "the leader never exited");
        std::thread::sleep(Duration::from_millis(10));
    }
    let leader = tree::identity(child.id());
    let sleeper_start = tree::identity(sleeper).map(|identity| identity.start);
    let outcome = stop_tree(child.id(), StopCause::LeaderExited).expect("group signal");
    let _ = child.wait();
    let deadline = Instant::now() + HANG;
    while tree::still_running(sleeper, sleeper_start) && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(10));
    }
    let survived = tree::still_running(sleeper, sleeper_start);
    let _ = std::fs::remove_dir_all(&dir);

    assert!(leader.is_none_or(|leader| leader.zombie), "an exited leader is not running");
    assert_eq!(outcome.terminated, 1, "only the background sleep was running: {outcome:?}");
    assert!(!survived, "the leader's group remainder survived the stop");
}

/// A group down to its unreaped leader has nothing left to stop, and a stop
/// of it is no failure. On macOS that group's signal answers EPERM (measured
/// 200 of 200, `GROUP_ANSWER_MEANS_RUNNING`); before 2026-10-21 the stop
/// returned that EPERM as its error, and a bounded probe whose stream a
/// process outside its group held reported that its process group "could not
/// be terminated" (land-gate run 15).
#[test]
fn a_group_down_to_its_unreaped_leader_is_stopped_without_error() {
    let mut child = spawn_group("exit 0", &[]);
    let deadline = Instant::now() + HANG;
    while !crate::bounded_process::exited_without_reaping(&mut child).expect("poll leader") {
        assert!(Instant::now() < deadline, "the leader never exited");
        std::thread::sleep(Duration::from_millis(10));
    }
    let result = stop_tree(child.id(), StopCause::Bound);
    let _ = child.wait();
    let outcome = result.expect("a group with no running member is stopped without error");
    assert_eq!(
        outcome,
        StopOutcome { observation: tree::Observation::Complete, ..StopOutcome::default() },
        "nothing was running"
    );
}

/// A pipe's write end is found in the process that holds it, and not in one
/// that holds only its read end, one that holds neither, or this process once
/// it has handed its end over: what a bounded probe reads to tell a stream
/// its own descendant holds from one an outsider holds.
#[test]
fn a_pipes_write_end_is_found_only_where_it_is_held() {
    use std::os::fd::AsRawFd as _;
    let (reader, writer) = std::io::pipe().expect("pipe");
    let named = tree::pipe_writer_of(reader.as_raw_fd()).expect("the read end names its pipe");
    let spawn_holding = |stdin: Stdio, stdout: Stdio| {
        let mut command = Command::new("/bin/sh");
        command.args(["-c", "exec sleep 30"]).stdin(stdin).stdout(stdout).stderr(Stdio::null());
        configure_own_group(&mut command);
        hold_no_other_descriptor(&mut command);
        // The command, and the end it was given, go when this returns.
        command.spawn().expect("spawn fixture")
    };
    let mut writing = spawn_holding(Stdio::null(), Stdio::from(writer));
    let mut reading =
        spawn_holding(Stdio::from(reader.try_clone().expect("dup the read end")), Stdio::null());
    let mut neither = spawn_group("exec sleep 30", &[]);
    let held = |child: &Child| tree::holds_pipe_writer(child.id(), &named);
    let (by_writing, by_reading, by_neither) = (held(&writing), held(&reading), held(&neither));
    // This process also runs the other tests' threads, whose pipes open and
    // close while its table is read: a pipe closed between the listing and
    // its own read leaves the answer unknown (`None`), as it must. Only a full
    // read answers, and the first one must say the end is not held here.
    let mut by_this = None;
    for _ in 0..200 {
        by_this = tree::holds_pipe_writer(std::process::id(), &named);
        if by_this.is_some() {
            break;
        }
        std::thread::yield_now();
    }
    for child in [&mut writing, &mut reading, &mut neither] {
        let _ = stop_tree(child.id(), StopCause::Error);
        let _ = child.wait();
    }
    assert_eq!(by_writing, Some(true), "the child whose stdout is the write end holds it");
    assert_eq!(by_reading, Some(false), "a read end is not the write end");
    assert_eq!(by_neither, Some(false));
    assert_eq!(by_this, Some(false), "this process handed its write end over");
}

/// A stop of an owned child spawned into the caller's own group (a fixture
/// without `configure_own_group`) reaches the child and never this process.
#[test]
fn a_child_in_the_callers_group_is_stopped_alone() {
    let mut command = Command::new("/bin/sh");
    command.args(["-c", "exec sleep 30"]).stdin(Stdio::null());
    // Asserts that SIGTERM, by its default action, is what ends the child.
    default_dispositions(&mut command, &[libc::SIGTERM]);
    hold_no_other_descriptor(&mut command);
    let mut child = command.spawn().expect("spawn fixture in the harness's group");
    let outcome = stop_tree(child.id(), StopCause::Error).expect("no group to signal");
    let signal = signal_of(&mut child);
    assert_eq!(signal, Some(libc::SIGTERM));
    assert_eq!(outcome.terminated, 1, "{outcome:?}");
}

#[test]
fn a_live_child_has_an_identity_and_a_reaped_one_has_none_that_runs() {
    let mut child = spawn_group("exec sleep 30", &[]);
    let live = tree::identity(child.id()).expect("a live child has an identity");
    assert!(!live.zombie);
    assert!(tree::still_running(child.id(), Some(live.start)));
    assert!(!tree::still_running(child.id(), Some(live.start.wrapping_add(1))));
    let _ = stop_tree(child.id(), StopCause::Error);
    let _ = child.wait();
    assert!(!tree::still_running(child.id(), Some(live.start)));
}

#[test]
fn ownership_registers_and_releases() {
    let mut child = spawn_group("exec sleep 30", &[]);
    let pid = child.id();
    let ownership = Ownership::of(pid);
    let owned = super::owned_roots();
    let _ = stop_tree(pid, StopCause::Error);
    let _ = child.wait();
    drop(ownership);
    assert!(owned.iter().any(|root| root.pid == pid && matches!(root.pin, RootPin::Started(_))));
    assert!(!super::owned_roots().iter().any(|root| root.pid == pid));
}

/// A tree that ignores SIGTERM and keeps forking (TRUST-KI-1014-2): the root
/// shell forks `sleep 5` back to back, and in `groups` mode it first starts
/// three members that each lead a process group of their own (job control)
/// and do the same. Every process inherits the ignore. `$1` is written once
/// every forker runs; `$2` lists the members' group ids.
const FORKING_TREE: &str = "trap '' TERM; \
     if [ \"$3\" = groups ]; then \
       set -m; \
       for i in 1 2 3; do \
         /bin/sh -c 'while :; do sleep 5 & done' & printf '%s\\n' \"$!\" >> \"$2\"; \
       done; \
       set +m; \
     fi; \
     printf ready > \"$1\"; \
     while :; do sleep 5 & done";

/// The stop's grace for the `stop`th stop of a forking tree: 30 to 59 ms, as
/// in the measurement TRUST-KI-1014-2 records, so the SIGKILL lands while the
/// tree is still forking.
fn forking_grace(stop: usize) -> Duration {
    Duration::from_millis(30 + (stop as u64 * 7) % 30)
}

/// The processes running now (zombies excluded) in each of `groups`.
fn running_in_groups(groups: &[u32]) -> Vec<(u32, u64)> {
    let mut found = Vec::new();
    let mut running = Vec::new();
    for &group in groups {
        if tree::collect_process_group(group, &mut found) {
            for &pid in &found {
                if let Some(identity) = tree::identity(pid).filter(|identity| !identity.zombie) {
                    running.push((pid, identity.start));
                }
            }
        }
    }
    running
}

/// End what a forking tree left after its stop, by the means this test owns:
/// SIGKILL to the root's group, whose leader the test holds unreaped, and to
/// each process still running in a member's group, by its pid. Repeated a
/// millisecond apart until forty passes in a row have found nothing.
fn end_forking_tree(root: u32, member_groups: &[u32]) {
    let deadline = Instant::now() + HANG;
    let mut quiet = 0;
    while quiet < 40 && Instant::now() < deadline {
        let root_group = libc::pid_t::try_from(root).expect("pid fits pid_t");
        // SAFETY: `kill` takes no pointers; the group's leader is this test's
        // unreaped child, so its id cannot name anyone else's group.
        unsafe { libc::kill(-root_group, libc::SIGKILL) };
        let left = running_in_groups(member_groups);
        for &(pid, start) in &left {
            if tree::still_running(pid, Some(start)) {
                let pid = libc::pid_t::try_from(pid).expect("pid fits pid_t");
                // SAFETY: as above; `pid` ran with this start just now, in a
                // group this test's fixture made.
                unsafe { libc::kill(pid, libc::SIGKILL) };
            }
        }
        let found = !left.is_empty() || !running_in_groups(&[root]).is_empty();
        quiet = if found { 0 } else { quiet + 1 };
        std::thread::sleep(Duration::from_millis(1));
    }
}

/// One stop of a [`FORKING_TREE`] through the product's own stop path, the
/// root held unreaped by this test: how many of the tree's processes still
/// ran 100 ms after the stop returned, and what the stop reported.
fn stop_a_forking_tree(stop: usize, members_lead_groups: bool) -> (usize, StopOutcome) {
    let dir = scratch("forking");
    let ready = dir.join("ready");
    let groups = dir.join("groups");
    let mode = Path::new(if members_lead_groups { "groups" } else { "plain" });
    let mut child = spawn_group(FORKING_TREE, &[&ready, &groups, mode]);
    await_file(&ready);
    let root = Root { pid: child.id(), pin: RootPin::OwnChild };
    let (_, outcome) =
        stop_roots_recorded(&[root], StopCause::Bound, forking_grace(stop), &mut || false);
    std::thread::sleep(Duration::from_millis(100));
    let member_groups: Vec<u32> = std::fs::read_to_string(&groups)
        .unwrap_or_default()
        .lines()
        .filter_map(|line| line.trim().parse().ok())
        .collect();
    let mut all_groups = member_groups.clone();
    all_groups.push(child.id());
    let left = running_in_groups(&all_groups).len();
    end_forking_tree(child.id(), &member_groups);
    let _ = child.wait();
    let _ = std::fs::remove_dir_all(&dir);
    (left, outcome)
}

/// A stop leaves no process of a tree that ignores SIGTERM and keeps forking
/// (TRUST-KI-1014-2): its SIGKILL is repeated until the tree has stayed empty,
/// so the child a forker was making when the kill landed, which one kill
/// does not reach on macOS, is killed by a later round, in the root's group
/// and in the groups members lead. Killing once, the stop left a process of
/// such a tree after 116 of 150 stops. A few stops here; the count over
/// hundreds is the ignored stress test's below.
#[test]
fn a_stop_leaves_no_process_of_a_tree_that_ignores_sigterm_and_keeps_forking() {
    for stop in 0..3 {
        let (left, outcome) = stop_a_forking_tree(stop, true);
        assert_eq!(left, 0, "stop {stop} left a process of the tree running: {outcome:?}");
        assert_eq!(outcome.left, 0, "the rounds ended with the tree empty: {outcome:?}");
        assert!(outcome.killed > 0, "the tree ignored SIGTERM, so SIGKILL ended it: {outcome:?}");
        let killed_after = outcome.killed_after.expect("a SIGKILL went out");
        assert!(
            killed_after >= forking_grace(stop),
            "the SIGKILL followed the grace: {killed_after:?}"
        );
    }
}

/// What is left in a group a member led, once that member has exited and
/// been reaped, is found and stopped, and the group is never signalled
/// through its id from then on (its id may be another process's).
///
/// The member leads a group of its own (job control) and, once the stop's
/// grace has begun, starts a `sleep` that ignores SIGTERM in that group and
/// exits; the root shell reaps it and lives on, ignoring SIGTERM. The sleep
/// is in no tree of the stop's (its parent is gone) and not in the root's
/// group: only a read of the member's group finds it. Until 2026-10-14 the
/// stop never read that group again, and the sleep ran on.
#[test]
fn what_a_reaped_members_group_holds_is_stopped_by_pid() {
    let dir = scratch("member-group");
    let (ready, go, orphan_file, member_file) =
        (dir.join("ready"), dir.join("go"), dir.join("orphan"), dir.join("member"));
    let mut child = spawn_group(
        "trap '' TERM; set -m; \
         /bin/sh -c 'while [ ! -e \"$1\" ]; do sleep 0.01; done; \
                     sleep 30 & printf \"%s\" \"$!\" > \"$2\"; exit 0' member \"$2\" \"$3\" & \
         printf '%s' \"$!\" > \"$4\"; set +m; printf ready > \"$1\"; wait; exec sleep 30",
        &[&ready, &go, &orphan_file, &member_file],
    );
    await_file(&ready);
    let member: u32 = await_file(&member_file).parse().expect("numeric member pid");
    assert!(tree::leads_own_process_group(member), "the member leads a group of its own");
    recording_group_signals(true);
    let mut orphan = None;
    let mut signals_before_the_reap = None;
    let root = Root { pid: child.id(), pin: RootPin::OwnChild };
    let (result, outcome) =
        stop_roots_recorded(&[root], StopCause::Bound, Duration::from_millis(300), &mut || {
            if signals_before_the_reap.is_none() {
                // The grace has begun: let the member make its sleep and go,
                // and wait until the root shell has reaped it.
                std::fs::write(&go, b"go").expect("write go");
                let pid: u32 = await_file(&orphan_file).parse().expect("numeric orphan pid");
                orphan = Some((pid, tree::identity(pid).map(|identity| identity.start)));
                let deadline = Instant::now() + HANG;
                while tree::identity(member).is_some() {
                    assert!(Instant::now() < deadline, "the member was never reaped");
                    std::thread::sleep(Duration::from_millis(5));
                }
                signals_before_the_reap = Some(group_signals().len());
            }
            false
        });
    let signals = group_signals();
    recording_group_signals(false);
    let (orphan, orphan_start) = orphan.expect("the grace ran");
    let deadline = Instant::now() + Duration::from_secs(1);
    while tree::still_running(orphan, orphan_start) && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(10));
    }
    let survived = tree::still_running(orphan, orphan_start);
    if survived {
        // SAFETY: `kill` takes no pointers; the pid ran with this start just
        // now and is this test's fixture's.
        unsafe { libc::kill(libc::pid_t::try_from(orphan).expect("pid fits"), libc::SIGKILL) };
    }
    let _ = stop_tree(child.id(), StopCause::Error);
    let _ = child.wait();
    let _ = std::fs::remove_dir_all(&dir);

    result.expect("the group signal succeeds");
    assert!(!survived, "the sleep left in the reaped member's group ran on: {outcome:?}");
    assert!(outcome.killed >= 2, "the root shell and the sleep were killed: {outcome:?}");
    let member_group = libc::pid_t::try_from(member).expect("pid fits");
    let before = signals_before_the_reap.expect("the grace ran");
    assert!(
        signals[..before].contains(&(member_group, libc::SIGTERM)),
        "while the member ran, its group had the stop's SIGTERM: {signals:?}"
    );
    assert!(
        !signals[before..].iter().any(|&(group, _)| group == member_group),
        "a group whose leader was reaped was signalled through its id: {signals:?}"
    );
}

/// TRUST-KI-1014-2's measurement, kept: stop a tree that ignores SIGTERM and
/// keeps forking `TRUST_STOP_STRESS_STOPS` times (150 unless set), first with
/// every process in the root's group, then with members that lead groups of
/// their own, and count the stops after which a process of the tree still
/// ran. Before the repeated kill: a process was left after 116 of 150 stops.
#[test]
#[ignore = "stress: 300 stops of a forking tree, about a minute; run with --ignored"]
fn stress_a_stop_leaves_no_process_of_a_tree_that_ignores_sigterm_and_keeps_forking() {
    let stops: usize = std::env::var("TRUST_STOP_STRESS_STOPS")
        .ok()
        .and_then(|stops| stops.parse().ok())
        .unwrap_or(150);
    let mut lines = Vec::new();
    let mut failed = false;
    for members_lead_groups in [false, true] {
        let (mut stops_leaving, mut left_total, mut killed) = (0, 0, 0);
        let started = Instant::now();
        for stop in 0..stops {
            let (left, outcome) = stop_a_forking_tree(stop, members_lead_groups);
            if left > 0 {
                stops_leaving += 1;
                left_total += left;
            }
            killed += outcome.killed;
        }
        failed |= stops_leaving > 0;
        let line = format!(
            "{}: a process of the tree still ran 100 ms after the stop returned after {stops_leaving} \
             of {stops} stops ({left_total} processes; SIGKILL to {killed} processes; {:?})",
            if members_lead_groups { "members lead groups" } else { "one group" },
            started.elapsed()
        );
        eprintln!("{line}");
        lines.push(line);
    }
    assert!(!failed, "{lines:#?}");
}

#[test]
fn the_sentinel_reads_owned_and_released_lines_and_nothing_else() {
    let mut owned = std::collections::BTreeMap::new();
    for line in [
        &b"+41 1000\n"[..],
        b"+42 2000\n",
        b"-41\n",
        b"+43\n",
        b"+0 5\n",
        b"+44 x\n",
        b"+45 1 2\n",
        b"junk\n",
        b"+46 3000",
        b"\xff\n",
    ] {
        super::sentinel::apply_for_test(&mut owned, line);
    }
    assert_eq!(owned.into_iter().collect::<Vec<_>>(), [(42, 2000), (46, 3000)]);
}

/// The account of a stop says how long after the SIGTERM its SIGKILL went
/// out, as measured: until 2026-10-14 it said "after 10s" whatever the time
/// was, and a stop whose late walk found a process killed it 26 ms after the
/// SIGTERM (TRUST-KI-1014-2).
#[test]
fn the_interrupted_message_says_what_was_stopped_and_how() {
    use super::signals::describe_for_test as describe;
    let outcome = |terminated, killed, escalated, after: Option<u64>, left| StopOutcome {
        terminated,
        killed,
        escalated,
        killed_after: after.map(Duration::from_millis),
        left,
        ..StopOutcome::default()
    };
    assert_eq!(describe(0, StopOutcome::default(), None), "no owned child process was running");
    assert_eq!(
        describe(1, outcome(3, 0, false, None, 0), None),
        "stopped 1 child process tree(s): SIGTERM to 3 process(es)"
    );
    assert_eq!(
        describe(2, outcome(3, 1, false, Some(26), 0), None),
        "stopped 2 child process tree(s): SIGTERM to 3 process(es), then SIGKILL to 1 still \
         running 26 ms after the SIGTERM"
    );
    assert_eq!(
        describe(2, outcome(3, 2, false, Some(10_004), 0), None),
        "stopped 2 child process tree(s): SIGTERM to 3 process(es), then SIGKILL to 2 still \
         running 10.0 s after the SIGTERM"
    );
    assert_eq!(
        describe(1, outcome(2, 2, true, Some(3_240), 0), Some(libc::SIGINT)),
        "stopped 1 child process tree(s): SIGTERM to 2 process(es), then SIGKILL to 2 at once on \
         a second signal (SIGINT), 3.2 s after the SIGTERM"
    );
    // A second signal that arrived once the grace was over changed nothing.
    assert_eq!(
        describe(1, outcome(2, 2, false, Some(10_001), 0), Some(libc::SIGINT)),
        "stopped 1 child process tree(s): SIGTERM to 2 process(es), then SIGKILL to 2 still \
         running 10.0 s after the SIGTERM"
    );
    assert_eq!(
        describe(1, outcome(1, 7, false, Some(41), 1), None),
        "stopped 1 child process tree(s): SIGTERM to 1 process(es), then SIGKILL to 7 still \
         running 41 ms after the SIGTERM, and found 1 still running after its last repeated \
         SIGKILL"
    );
    assert_eq!(StopCause::Signal(libc::SIGTERM).label(), "signal SIGTERM");
    assert_eq!(StopCause::OwnerEnded.label(), "owner-ended");
}
