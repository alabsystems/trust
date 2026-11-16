//@ run-pass
//@ edition: 2021
//@ only-unix
//@ needs-subprocess
//@ ignore-android no /bin/sh
//@ ignore-fuchsia no descriptor beyond stdio crosses a spawn there
//@ ignore-vxworks no /bin/sh
//@ ignore-ios no /bin/sh
//@ ignore-tvos execvp is prohibited
//@ ignore-watchos execvp is prohibited
//@ ignore-visionos no /bin/sh

// Trust: a spawned child inherits its stdio and nothing else
// (library/std/src/sys/process/unix/inherit.rs; docs/DECISION_QUEUE.md, SP-1).
// These are the cases that need this process's whole descriptor table, so they
// run here, alone, rather than among std's unit tests (`inherit/tests.rs`):
// std's exec-status descriptor in a near-empty table, a stdio source on its own
// number, a table longer than Darwin's descriptor listing, numbers past Darwin's
// file-action limit, and a thread racing the spawn. Every case runs on both
// spawn paths: `posix_spawn` (no hook) and fork/exec (a no-op `pre_exec` hook).

#![feature(rustc_private, trust_process_inherit_fds)]

extern crate libc;

use std::fs::File;
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::process::CommandExt;
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

const PATHS: [bool; 2] = [false, true];

fn sh(script: &str, fork: bool) -> Command {
    let mut cmd = Command::new("/bin/sh");
    cmd.arg("-c").arg(script);
    if fork {
        // SAFETY: the hook does nothing.
        unsafe { cmd.pre_exec(|| Ok(())) };
    }
    cmd
}

/// Raise the soft `RLIMIT_NOFILE` toward `want` (never past the hard limit)
/// and return the soft limit now in force.
fn raise_soft_limit(want: u64) -> RawFd {
    let mut limit = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
    // SAFETY: `limit` is a live `struct rlimit`.
    assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut limit) }, 0);
    if (limit.rlim_cur as u64) < want {
        let raised = libc::rlimit { rlim_cur: want.min(limit.rlim_max as u64) as _, ..limit };
        // SAFETY: as above; a refusal leaves the limit as it was.
        unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &raised) };
        // SAFETY: as above.
        assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut limit) }, 0);
    }
    (limit.rlim_cur as u64).min(1 << 20) as RawFd
}

fn unflagged_at_or_above(floor: RawFd) -> OwnedFd {
    let null = File::open("/dev/null").unwrap();
    // SAFETY: `F_DUPFD` reads one descriptor and returns a fresh one or -1.
    let fd = unsafe { libc::fcntl(null.as_raw_fd(), libc::F_DUPFD, floor) };
    assert!(fd >= floor, "F_DUPFD({floor}): {}", io::Error::last_os_error());
    // SAFETY: just created here, owned by nothing else.
    unsafe { OwnedFd::from_raw_fd(fd) }
}

fn moved_at_or_above(fd: OwnedFd, floor: RawFd) -> OwnedFd {
    // SAFETY: `F_DUPFD_CLOEXEC` reads one descriptor and returns a fresh one or -1.
    let copy = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_DUPFD_CLOEXEC, floor) };
    assert!(copy >= floor, "F_DUPFD_CLOEXEC({floor}): {}", io::Error::last_os_error());
    drop(fd);
    // SAFETY: just created here, owned by nothing else.
    unsafe { OwnedFd::from_raw_fd(copy) }
}

fn child_holds(fork: bool, fd: RawFd, all: bool) -> bool {
    let mut cmd = sh(&format!("[ -e /dev/fd/{fd} ] && exit 3; exit 0"), fork);
    if all {
        cmd.inherit_all_fds();
    }
    match cmd.status().unwrap().code() {
        Some(3) => true,
        Some(0) => false,
        other => panic!("the probe child answered {other:?}"),
    }
}

fn read_all(mut from: impl Read) -> String {
    let mut got = String::new();
    from.read_to_string(&mut got).unwrap();
    got
}

/// First, while this process holds almost nothing, so std's exec-status pipe
/// is created on the low numbers a hook places descriptors on: a failed exec
/// must still be an error, never a started child.
fn a_failed_exec_is_reported_through_hook_placements() {
    const MISSING: &str = "/nonexistent/trust-std-no-such-program";
    for fork in PATHS {
        let mut cmd = Command::new(MISSING);
        if fork {
            // Writable: were std's status descriptor among the targets, the
            // child's report would vanish into it rather than abort the child.
            let null = std::fs::OpenOptions::new().write(true).open("/dev/null").unwrap();
            // SAFETY: `dup2` is async-signal-safe; `null` lives in the hook.
            unsafe {
                cmd.pre_exec(move || {
                    let raw = null.as_raw_fd();
                    for target in 3..=9 {
                        if target != raw {
                            libc::dup2(raw, target);
                        }
                    }
                    Ok(())
                });
            }
        }
        let err = cmd.spawn().map(|mut c| c.wait()).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::NotFound, "fork={fork}: {err}");
    }
}

/// `inherit_fd` hands over the caller's own descriptors: a number the caller
/// never opened, where std's own end of the child's stdin pipe lands, is
/// refused rather than handed over (it would keep the child's stdin open).
fn inherit_fd_cannot_name_std_own_pipe_end() {
    // The two lowest free numbers; std's stdin pipe takes them in the same
    // order, its own (write) end on the second.
    let probe = [File::open("/dev/null").unwrap(), File::open("/dev/null").unwrap()];
    let ours = probe[1].as_raw_fd();
    drop(probe);
    for fork in PATHS {
        let err = sh("exit 0", fork)
            .stdin(Stdio::piped())
            .inherit_fd(ours)
            .spawn()
            .map(|mut c| c.wait())
            .unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::EBADF), "fork={fork}: {err}");
    }
}

fn an_unflagged_descriptor_reaches_no_child() {
    let held = unflagged_at_or_above(64);
    let fd = held.as_raw_fd();
    for fork in PATHS {
        assert!(child_holds(fork, fd, true), "CONTROL (fork={fork}): fd {fd}");
        assert!(!child_holds(fork, fd, false), "fork={fork}: unflagged fd {fd} reached the child");
    }
}

/// A process that has closed its stdin gets std's stdin pipe for the child on
/// fd 0 itself: a source already on its target. Darwin's `adddup2(0, 0)` and
/// every `dup2(0, 0)` leave it close-on-exec, and the child's stdin closed.
fn a_stdio_source_on_its_own_number_arrives_open() {
    // This process's own stdin (or `/dev/null` where it has none), off 0..=9.
    // SAFETY: `F_DUPFD_CLOEXEC` reads one descriptor and returns a fresh one or -1.
    let saved = match unsafe { libc::fcntl(0, libc::F_DUPFD_CLOEXEC, 10) } {
        // SAFETY: just created here, owned by nothing else.
        fd if fd >= 0 => unsafe { OwnedFd::from_raw_fd(fd) },
        _ => moved_at_or_above(File::open("/dev/null").unwrap().into(), 10),
    };
    for fork in PATHS {
        // SAFETY: fd 0 is restored from `saved` below; closing a closed one is harmless.
        unsafe { libc::close(0) };
        let spawned = sh("read l; echo \"got:$l\"", fork)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn();
        // SAFETY: two integers; puts this process's stdin back.
        assert_eq!(unsafe { libc::dup2(saved.as_raw_fd(), 0) }, 0);
        let mut child = spawned.unwrap();
        child.stdin.take().unwrap().write_all(b"x\n").unwrap();
        let out = child.wait_with_output().unwrap();
        assert_eq!(String::from_utf8_lossy(&out.stdout), "got:x\n", "fork={fork}");
    }
}

/// Darwin lists a forked child's table 1024 descriptors at a time and probes
/// past a full listing: more than that open, and one far above them.
fn a_table_longer_than_a_listing_is_stripped() {
    let held: Vec<OwnedFd> = (0..1100).map(|_| unflagged_at_or_above(3)).collect();
    let high = unflagged_at_or_above(2500);
    for fork in PATHS {
        for fd in [held[1050].as_raw_fd(), high.as_raw_fd()] {
            assert!(child_holds(fork, fd, true), "CONTROL (fork={fork}): fd {fd}");
            assert!(!child_holds(fork, fd, false), "fork={fork}: unflagged fd {fd} reached it");
        }
    }
}

/// Darwin's libc refuses a file action naming a descriptor at 10 240 or
/// above: such a spawn takes the fork path and still hands it over.
fn numbers_past_the_file_action_limit_still_cross() {
    let (reader, writer) = io::pipe().unwrap();
    let writer = moved_at_or_above(writer.into(), 10_250);
    let (out_reader, out_writer) = io::pipe().unwrap();
    let out_writer = moved_at_or_above(out_writer.into(), 10_260);
    let fd = writer.as_raw_fd();
    let mut child = sh(&format!("echo handed >&{fd}; echo out"), false)
        .inherit_fd(fd)
        .stdout(Stdio::from(out_writer))
        .spawn()
        .unwrap();
    // The temporary `Command`, which held the stdout source, is gone too.
    drop(writer);
    assert!(child.wait().unwrap().success());
    assert_eq!(read_all(reader), "handed\n");
    assert_eq!(read_all(out_reader), "out\n");
}

/// 400 spawns per path while another thread opens and holds unflagged
/// descriptors at the probed numbers: zero may reach a child.
fn no_descriptor_leaks_while_another_thread_races_the_spawn(floor: RawFd) {
    const SPAWNS: usize = 400;
    let probe = format!(
        "c=0; for f in {} {} {} {}; do [ -e /dev/fd/$f ] && c=1; done; exit $c",
        floor,
        floor + 1,
        floor + 2,
        floor + 3
    );
    {
        let held = unflagged_at_or_above(floor);
        let status = sh(&probe, false).inherit_all_fds().status().unwrap();
        assert_eq!(status.code(), Some(1), "CONTROL: the probe must see fd {}", held.as_raw_fd());
    }
    let stop = Arc::new(AtomicBool::new(false));
    let racer = {
        let stop = Arc::clone(&stop);
        std::thread::spawn(move || {
            let mut turns = 0usize;
            while !stop.load(Ordering::Relaxed) {
                let held: [OwnedFd; 4] = std::array::from_fn(|_| unflagged_at_or_above(floor));
                let until = Instant::now() + Duration::from_micros(200);
                while Instant::now() < until {
                    std::hint::spin_loop();
                }
                drop(held);
                turns += 1;
            }
            turns
        })
    };
    let mut leaks = [0usize; 2];
    for (leaked, fork) in leaks.iter_mut().zip(PATHS) {
        for _ in 0..SPAWNS {
            if sh(&probe, fork).status().unwrap().code() != Some(0) {
                *leaked += 1;
            }
        }
    }
    stop.store(true, Ordering::Relaxed);
    assert!(racer.join().unwrap() > 0, "the racer never ran");
    assert_eq!(leaks, [0, 0], "racer descriptors reached [posix_spawn, fork] children");
}

fn main() {
    a_failed_exec_is_reported_through_hook_placements();
    inherit_fd_cannot_name_std_own_pipe_end();
    let soft = raise_soft_limit(12_000);
    an_unflagged_descriptor_reaches_no_child();
    a_stdio_source_on_its_own_number_arrives_open();
    if soft > 2600 {
        a_table_longer_than_a_listing_is_stripped();
    } else {
        eprintln!("skipped: a table past a listing needs RLIMIT_NOFILE > 2600 (have {soft})");
    }
    if soft > 10_300 {
        numbers_past_the_file_action_limit_still_cross();
    } else {
        eprintln!("skipped: the file-action limit needs RLIMIT_NOFILE > 10300 (have {soft})");
    }
    no_descriptor_leaks_while_another_thread_races_the_spawn((soft - 16).min(300));
}
