//! Actual two-child lifecycle diagnostics, not native loading/IPC qualification.
//! Post-fork children use only raw async-signal-safe syscalls and stack bytes.
use std::fs::File;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::time::{Duration, Instant};

use trust_process_isolation::{Budget, Limits};

use super::*;

fn budget(duration: Duration) -> Budget {
    Budget::new(
        Limits {
            frame_bytes: 1024,
            wire_bytes: 1024,
            allocation_bytes: 1024 * 1024,
            values: 1024,
            work: 16 * 1024 * 1024,
            calls: 32,
            live_handles: 8,
            depth: 8,
        },
        Instant::now() + duration,
    )
    .unwrap()
}
fn pipe() -> (File, File) {
    let mut fds = [-1; 2];
    // SAFETY: pipe2 writes a complete pair of fresh uniquely owned descriptors.
    assert_eq!(unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) }, 0);
    // SAFETY: successful pipe2 yielded two distinct fresh descriptors.
    unsafe { (File::from_raw_fd(fds[0]), File::from_raw_fd(fds[1])) }
}
fn high(fd: i32) -> OwnedFd {
    // SAFETY: the borrowed source remains live; duplication owns a new high FD.
    let fd = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 64) };
    assert!(fd >= 64);
    // SAFETY: successful fcntl returned a uniquely owned descriptor.
    unsafe { OwnedFd::from_raw_fd(fd) }
}
struct Fixture {
    child: Child,
    command: File,
}
fn fixture(b: &Budget) -> Fixture {
    let (read, command) = pipe();
    let (ready, write) = pipe();
    let child_read = high(read.as_raw_fd());
    let child_write = high(write.as_raw_fd());
    let input = child_read.as_raw_fd();
    let output = child_write.as_raw_fd();
    // SAFETY: scalar observation used in the child's PDEATHSIG race check.
    let parent = unsafe { libc::getpid() };
    // SAFETY: child uses only the raw prepared-FD routine below and _exit. It
    // neither allocates nor locks copied Rust state after multithreaded fork.
    let pid = unsafe { libc::fork() };
    assert!(pid >= 0);
    if pid == 0 {
        // SAFETY: all scalar syscalls act on the new child; high source FDs
        // avoid dup cycles, and every ambient descriptor closes before read.
        unsafe {
            if libc::setpgid(0, 0) != 0
                || libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL, 0, 0, 0) != 0
                || libc::getppid() != parent
                || libc::dup2(input, 3) != 3
                || libc::dup2(output, 4) != 4
                || libc::syscall(libc::SYS_close_range, 0u32, 2u32, 0u32) != 0
                || libc::syscall(libc::SYS_close_range, 5u32, u32::MAX, 0u32) != 0
            {
                libc::_exit(120);
            }
            let mut byte = b'R';
            if libc::write(4, (&byte as *const u8).cast(), 1) != 1 {
                libc::_exit(121);
            }
            // This is a real opaque blocking operation in the broker stand-in.
            // Parent supervision must work without polling or joining its IO.
            if libc::read(3, (&mut byte as *mut u8).cast(), 1) != 1 {
                libc::_exit(122);
            }
            libc::_exit(if byte == b'E' { 0 } else { 123 });
        }
    }
    let mut child = Child { pid, pidfd: None, reaped: false, budget: b.clone() };
    // SAFETY: the exclusive still-unreaped child reserves its PID for this open.
    let fd = unsafe { libc::syscall(libc::SYS_pidfd_open, pid, 0u32) };
    assert!(fd >= 0, "kernel fixture requires actual pidfd support");
    // SAFETY: pidfd_open returned one fresh unique owned descriptor.
    child.pidfd = Some(unsafe { OwnedFd::from_raw_fd(fd as i32) });
    drop(write);
    drop(read);
    let until = Instant::now() + Duration::from_secs(2);
    loop {
        assert!(Instant::now() < until, "fixture ready timeout");
        let mut poll = libc::pollfd { fd: ready.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: one complete live pollfd, finite wait, no retained pointer.
        let n = unsafe { libc::poll(&mut poll, 1, 1) };
        assert!(n >= 0);
        if n > 0 {
            let mut byte = 0;
            // SAFETY: one-byte writable stack record, pipe reported readiness.
            assert_eq!(
                unsafe { libc::read(ready.as_raw_fd(), (&mut byte as *mut u8).cast(), 1) },
                1
            );
            assert_eq!(byte, b'R');
            break;
        }
    }
    Fixture { child, command }
}
fn running(b: &Budget) -> (Running, [i32; 2], [File; 2]) {
    let prepared = Prepared::new(b).unwrap();
    let worker = fixture(b);
    let broker = fixture(b);
    let pids = [worker.child.pid, broker.child.pid];
    let owner = prepared.attach(worker.child, broker.child);
    armed(&owner);
    (owner, pids, [worker.command, broker.command])
}
fn armed(owner: &Running) {
    let until = Instant::now() + Duration::from_secs(2);
    loop {
        assert!(Instant::now() < until, "monitor did not arm");
        let seen = owner.observe();
        if seen.phase == Phase::Watching {
            assert!(seen.grant_valid);
            return;
        }
        assert_eq!(seen.phase, Phase::Arming, "refused before arming: {seen:?}");
        std::thread::sleep(QUANTUM);
    }
}
fn reaped(owner: &Running) -> Observation {
    let until = Instant::now() + Duration::from_secs(3);
    loop {
        assert!(Instant::now() < until, "cleanup custody remained pending");
        let seen = owner.observe();
        if seen.phase == Phase::Reaped && seen.monitor_exited {
            return seen;
        }
        assert_ne!(seen.phase, Phase::CleanupFailed);
        std::thread::sleep(QUANTUM);
    }
}
fn no_children(pids: [i32; 2]) {
    for pid in pids {
        let mut status = 0;
        // SAFETY: WNOHANG does not wait; exclusive monitor should already reap
        // this exact direct child. No numeric signal is issued after the reap.
        assert_eq!(unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) }, -1);
        assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::ECHILD));
    }
}
fn killed(status: Option<i32>) {
    let status = status.unwrap();
    assert!(libc::WIFSIGNALED(status));
    assert_eq!(libc::WTERMSIG(status), libc::SIGKILL);
}

fn finishing(owner: &Running) {
    owner.request_worker_exit().unwrap();
    let until = Instant::now() + Duration::from_secs(2);
    loop {
        assert!(Instant::now() < until, "monitor did not arm worker exit");
        let seen = owner.observe();
        assert!(seen.grant_valid, "{seen:?}");
        if seen.phase == Phase::Finishing {
            return;
        }
        assert_eq!(seen.phase, Phase::FinishRequested, "{seen:?}");
        std::thread::sleep(QUANTUM);
    }
}

#[test]
fn native_completion_waits_for_actual_zero_exit_before_parent_cleanup() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, commands) = running(&b);
    finishing(&owner);
    // Parent closure before the child exits must not signal that child. This
    // command models the pinned runtime's separately acknowledged final exit.
    owner.request_finished().unwrap();
    // SAFETY: one parent-owned command pipe, no post-fork Rust code in child.
    assert_eq!(unsafe { libc::write(commands[0].as_raw_fd(), b"E".as_ptr().cast(), 1) }, 1);
    let seen = reaped(&owner);
    assert_eq!(seen.cause, Some(Cause::ParentFinished));
    let worker = seen.worker_status.unwrap();
    assert!(libc::WIFEXITED(worker));
    assert_eq!(libc::WEXITSTATUS(worker), 0);
    killed(seen.broker_status);
    assert!(owner.finish().unwrap().grant_valid);
    no_children(pids);
}

#[test]
fn native_completion_requires_both_zero_exit_and_parent_validation() {
    for worker_exits in [false, true] {
        let b = budget(Duration::from_secs(1));
        let (owner, pids, commands) = running(&b);
        finishing(&owner);
        if worker_exits {
            // SAFETY: the fixture's fixed E command exits zero, without a
            // corresponding parent closure/receipt validation.
            assert_eq!(unsafe { libc::write(commands[0].as_raw_fd(), b"E".as_ptr().cast(), 1) }, 1);
        } else {
            owner.request_finished().unwrap();
        }
        let seen = reaped(&owner);
        assert_eq!(seen.cause, Some(Cause::Deadline));
        assert!(!owner.finish().unwrap().grant_valid);
        assert_eq!(b.check(), Err(trust_process_isolation::Error::Deadline));
        no_children(pids);
    }
}

#[test]
fn native_completion_cannot_accept_abnormal_worker_exit() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, commands) = running(&b);
    finishing(&owner);
    owner.request_finished().unwrap();
    // SAFETY: a distinct fixed command makes the owned child exit 123.
    assert_eq!(unsafe { libc::write(commands[0].as_raw_fd(), b"F".as_ptr().cast(), 1) }, 1);
    let seen = reaped(&owner);
    assert_eq!(seen.cause, Some(Cause::WorkerExited));
    assert_eq!(libc::WEXITSTATUS(seen.worker_status.unwrap()), 123);
    killed(seen.broker_status);
    assert!(!owner.finish().unwrap().grant_valid);
    no_children(pids);
}

#[test]
fn finish_cleans_two_blocked_processes_without_broker_io_join() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, _commands) = running(&b);
    owner.request_finished().unwrap();
    let seen = reaped(&owner);
    assert_eq!(seen.cause, Some(Cause::ParentFinished));
    killed(seen.worker_status);
    killed(seen.broker_status);
    let receipt = owner.finish().unwrap();
    assert!(receipt.grant_valid);
    no_children(pids);
}
#[test]
fn absolute_deadline_kills_both_and_never_reopens_the_grant() {
    let b = budget(Duration::from_secs(5));
    let prepared = Prepared::new(&b).unwrap();
    let worker = fixture(&b);
    let broker = fixture(&b);
    let pids = [worker.child.pid, broker.child.pid];
    // The original clock includes startup. Do not require Watching if that
    // clock expired during the two fixture starts: cleanup must still work.
    let owner = prepared.attach(worker.child, broker.child);
    // Wait for the original grant, rather than treating reaped()'s separate
    // finite cleanup poll as a shorter replacement invocation deadline.
    while Instant::now() < b.deadline() {
        std::thread::sleep(QUANTUM);
    }
    let seen = reaped(&owner);
    assert_eq!(seen.cause, Some(Cause::Deadline));
    killed(seen.worker_status);
    killed(seen.broker_status);
    assert!(!owner.finish().unwrap().grant_valid);
    assert_eq!(b.check(), Err(trust_process_isolation::Error::Deadline));
    no_children(pids);
}
#[test]
fn sibling_cancellation_owns_both_cleanup_paths() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, _commands) = running(&b);
    b.clone().cancel();
    let seen = reaped(&owner);
    assert_eq!(seen.cause, Some(Cause::BudgetRefused));
    assert!(!owner.finish().unwrap().grant_valid);
    no_children(pids);
}
#[test]
fn work_refusal_latches_across_cleanup_and_all_shared_owners() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, _commands) = running(&b);
    let work = b.limits().work - b.usage().unwrap().work + 1;
    assert_eq!(
        b.charge(Charge { work, ..Charge::default() }),
        Err(trust_process_isolation::Error::Budget("work"))
    );
    assert_eq!(reaped(&owner).cause, Some(Cause::BudgetRefused));
    assert!(!owner.finish().unwrap().grant_valid);
    assert_eq!(
        b.clone().charge(Charge::default()),
        Err(trust_process_isolation::Error::Budget("work"))
    );
    no_children(pids);
}
#[test]
fn poisoned_status_cannot_publish_an_earlier_successful_grant_check() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, _commands) = running(&b);
    let shared = Arc::clone(&owner.handle.shared);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _state = shared.state.lock().unwrap();
        panic!("status poison fixture");
    }));
    assert!(result.is_err());
    let seen = reaped(&owner);
    assert!(!seen.grant_valid);
    assert_eq!(seen.cause, Some(Cause::MonitorError));
    assert!(!owner.finish().unwrap().grant_valid);
    assert_eq!(b.check(), Err(trust_process_isolation::Error::Poisoned));
    no_children(pids);
}
#[test]
fn parent_refusal_is_terminal_even_after_complete_cleanup() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, _commands) = running(&b);
    owner.refuse();
    assert_eq!(reaped(&owner).cause, Some(Cause::ParentRefused));
    assert!(!owner.finish().unwrap().grant_valid);
    assert_eq!(b.check(), Err(trust_process_isolation::Error::Phase));
    no_children(pids);
}
#[test]
fn monitor_unwind_refuses_and_reaps_before_publishing_terminal_state() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, _commands) = running(&b);
    owner.handle.shared.state().panic_watch = true;
    assert_eq!(reaped(&owner).cause, Some(Cause::MonitorPanicked));
    assert!(!owner.finish().unwrap().grant_valid);
    no_children(pids);
}
#[test]
fn rendezvous_unwind_retains_late_guard_cleanup_without_arming() {
    let b = budget(Duration::from_secs(5));
    let prepared = Prepared::new(&b).unwrap();
    let worker = fixture(&b);
    let broker = fixture(&b);
    let pids = [worker.child.pid, broker.child.pid];
    prepared.handle.shared.state().panic_wait = true;
    let until = Instant::now() + Duration::from_secs(2);
    loop {
        assert!(Instant::now() < until);
        if prepared.handle.shared.state().cause == Some(Cause::MonitorPanicked) {
            break;
        }
        std::thread::sleep(QUANTUM);
    }
    let owner = prepared.attach(worker.child, broker.child);
    assert_eq!(reaped(&owner).cause, Some(Cause::MonitorPanicked));
    assert!(!owner.finish().unwrap().grant_valid);
    no_children(pids);
}
#[test]
fn transfer_unwind_keeps_both_guards_outside_the_unwinding_closure() {
    let b = budget(Duration::from_secs(5));
    let prepared = Prepared::new(&b).unwrap();
    let worker = fixture(&b);
    let broker = fixture(&b);
    let pids = [worker.child.pid, broker.child.pid];
    prepared.handle.shared.state().panic_after_transfer = true;
    let owner = prepared.attach(worker.child, broker.child);
    assert_eq!(reaped(&owner).cause, Some(Cause::MonitorPanicked));
    assert!(!owner.finish().unwrap().grant_valid);
    no_children(pids);
}
#[test]
fn caller_unwind_detaches_owned_cleanup_instead_of_joining_io() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, _commands) = running(&b);
    let shared = Arc::clone(&owner.handle.shared);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        let _owned = owner;
        panic!("caller cancellation fixture");
    }));
    assert!(result.is_err());
    let until = Instant::now() + Duration::from_secs(3);
    loop {
        assert!(Instant::now() < until);
        let state = shared.state();
        if state.phase == Phase::Reaped {
            assert_eq!(state.cause, Some(Cause::OwnerDropped));
            break;
        }
        drop(state);
        std::thread::sleep(QUANTUM);
    }
    no_children(pids);
    assert_eq!(b.check(), Err(trust_process_isolation::Error::Phase));
}
#[test]
fn unexpected_worker_exit_refuses_and_reaps_the_blocked_broker() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, commands) = running(&b);
    // SAFETY: live parent-owned pipe and immutable one-byte command.
    assert_eq!(unsafe { libc::write(commands[0].as_raw_fd(), b"E".as_ptr().cast(), 1) }, 1);
    let seen = reaped(&owner);
    assert_eq!(seen.cause, Some(Cause::WorkerExited));
    assert!(libc::WIFEXITED(seen.worker_status.unwrap()));
    assert_eq!(libc::WEXITSTATUS(seen.worker_status.unwrap()), 0);
    killed(seen.broker_status);
    assert!(!owner.finish().unwrap().grant_valid);
    no_children(pids);
}
#[test]
fn unexpected_broker_exit_refuses_and_reaps_the_blocked_worker() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, commands) = running(&b);
    // SAFETY: live parent-owned pipe and immutable one-byte command.
    assert_eq!(unsafe { libc::write(commands[1].as_raw_fd(), b"E".as_ptr().cast(), 1) }, 1);
    let seen = reaped(&owner);
    assert_eq!(seen.cause, Some(Cause::BrokerExited));
    killed(seen.worker_status);
    assert!(libc::WIFEXITED(seen.broker_status.unwrap()));
    assert_eq!(libc::WEXITSTATUS(seen.broker_status.unwrap()), 0);
    assert!(!owner.finish().unwrap().grant_valid);
    no_children(pids);
}
#[test]
fn equal_but_separate_budget_cannot_arm_a_pair() {
    let b = budget(Duration::from_secs(5));
    let other = Budget::new(b.limits(), b.deadline()).unwrap();
    let prepared = Prepared::new(&b).unwrap();
    let worker = fixture(&b);
    let broker = fixture(&other);
    let pids = [worker.child.pid, broker.child.pid];
    let owner = prepared.attach(worker.child, broker.child);
    let seen = reaped(&owner);
    assert_eq!(seen.cause, Some(Cause::InvalidPair));
    assert!(!owner.finish().unwrap().grant_valid);
    assert_eq!(other.check(), Err(trust_process_isolation::Error::Phase));
    no_children(pids);
}
#[test]
fn missing_pidfd_refuses_before_requests_and_still_reaps() {
    let b = budget(Duration::from_secs(5));
    let prepared = Prepared::new(&b).unwrap();
    let worker = fixture(&b);
    let mut broker = fixture(&b);
    let pids = [worker.child.pid, broker.child.pid];
    broker.child.pidfd = None;
    let owner = prepared.attach(worker.child, broker.child);
    assert_eq!(reaped(&owner).cause, Some(Cause::InvalidPair));
    assert!(!owner.finish().unwrap().grant_valid);
    no_children(pids);
}
#[test]
fn late_guard_transfer_is_cleanup_only_not_a_new_deadline() {
    let b = budget(Duration::from_secs(5));
    let prepared = Prepared::new(&b).unwrap();
    let worker = fixture(&b);
    let broker = fixture(&b);
    let pids = [worker.child.pid, broker.child.pid];
    while Instant::now() < b.deadline() {
        std::thread::sleep(QUANTUM);
    }
    let owner = prepared.attach(worker.child, broker.child);
    assert_eq!(reaped(&owner).cause, Some(Cause::Deadline));
    assert!(!owner.finish().unwrap().grant_valid);
    no_children(pids);
}
#[test]
fn pending_finish_refuses_and_keeps_cleanup_custody() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, _commands) = running(&b);
    let shared = Arc::clone(&owner.handle.shared);
    assert!(owner.finish().is_err());
    let until = Instant::now() + Duration::from_secs(3);
    loop {
        assert!(Instant::now() < until);
        if shared.state().phase == Phase::Reaped {
            break;
        }
        std::thread::sleep(QUANTUM);
    }
    no_children(pids);
    assert_eq!(b.check(), Err(trust_process_isolation::Error::Phase));
}
#[test]
fn one_short_monitor_admission_is_sticky_before_thread_creation() {
    let original = budget(Duration::from_secs(5));
    let limits = Limits { allocation_bytes: (STACK + BOOKKEEPING - 1) as u64, ..original.limits() };
    let b = Budget::new(limits, original.deadline()).unwrap();
    assert!(matches!(Prepared::new(&b), Err(Error::Budget(_))));
    assert_eq!(b.check(), Err(trust_process_isolation::Error::Budget("allocation bytes")));
}
#[test]
fn exact_monitor_admission_precedes_all_monitor_allocations() {
    let original = budget(Duration::from_secs(5));
    let limits = Limits { allocation_bytes: (STACK + BOOKKEEPING) as u64, ..original.limits() };
    let b = Budget::new(limits, original.deadline()).unwrap();
    let prepared = Prepared::new(&b).unwrap();
    assert_eq!(b.usage().unwrap().allocation_bytes, (STACK + BOOKKEEPING) as u64);
    drop(prepared);
    assert_eq!(b.check(), Err(trust_process_isolation::Error::Phase));
}
#[test]
fn late_receipt_does_not_promote_an_earlier_healthy_cleanup() {
    let b = budget(Duration::from_secs(5));
    let (owner, pids, _commands) = running(&b);
    owner.request_finished().unwrap();
    let seen = reaped(&owner);
    assert_eq!(seen.cause, Some(Cause::ParentFinished));
    assert!(seen.grant_valid);
    while Instant::now() < b.deadline() {
        std::thread::sleep(QUANTUM);
    }
    let receipt = owner.finish().unwrap();
    assert_eq!(receipt.cause, Cause::ParentFinished);
    assert!(!receipt.grant_valid);
    no_children(pids);
}
#[test]
fn duplicate_guard_never_counts_as_two_reaped_children() {
    let b = budget(Duration::from_secs(5));
    let prepared = Prepared::new(&b).unwrap();
    let worker = fixture(&b);
    let pid = worker.child.pid;
    let duplicate = Child {
        pid,
        pidfd: Some(high(worker.child.pidfd.as_ref().unwrap().as_raw_fd())),
        reaped: false,
        budget: b.clone(),
    };
    let owner = prepared.attach(worker.child, duplicate);
    let until = Instant::now() + Duration::from_secs(3);
    loop {
        assert!(Instant::now() < until);
        let seen = owner.observe();
        if seen.monitor_exited {
            assert_eq!(seen.phase, Phase::CleanupFailed);
            assert_eq!(seen.cause, Some(Cause::InvalidPair));
            assert!(seen.worker_status.is_some());
            assert_eq!(seen.broker_status, None);
            break;
        }
        std::thread::sleep(QUANTUM);
    }
    assert!(owner.finish().is_err());
    no_children([pid, pid]);
}
