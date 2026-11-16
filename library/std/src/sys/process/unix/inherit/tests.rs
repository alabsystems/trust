// Trust: inherit-nothing spawns (`inherit.rs`; docs/DECISION_QUEUE.md, SP-1).
//! Every case runs on both spawn paths: `posix_spawn` (no hook; Linux takes
//! it only where libc has `posix_spawn_file_actions_addclosefrom_np`) and
//! fork/exec (a no-op `pre_exec` hook forces it). The child is `/bin/sh`,
//! which reports what it holds through `/dev/fd`.
//!
//! The cases that must own this process's descriptor table (a stdio source
//! on its own number, a table longer than Darwin's listing, numbers past
//! Darwin's file-action limit) are `tests/ui/trust/std_spawn_inherits_nothing.rs`,
//! which runs alone in its own process.

use crate::io::{self, Read, Write};
use crate::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use crate::os::unix::process::CommandExt;
use crate::process::{Command, Stdio};
use crate::sync::Arc;
use crate::sync::atomic::{AtomicBool, Ordering};
use crate::time::{Duration, Instant};
use crate::{fs, thread};

/// The two spawn paths: `false` is `posix_spawn` where the platform takes
/// it, `true` is fork/exec.
const PATHS: [bool; 2] = [false, true];

/// `/bin/sh -c script`, on the fork path when `fork`.
fn sh(script: &str, fork: bool) -> Command {
    let mut cmd = Command::new("/bin/sh");
    cmd.arg("-c").arg(script);
    if fork {
        // SAFETY: the hook does nothing.
        unsafe { cmd.pre_exec(|| Ok(())) };
    }
    cmd
}

/// This process's soft `RLIMIT_NOFILE`, capped at 2^20.
fn soft_nofile() -> RawFd {
    let mut limit = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
    // SAFETY: `limit` is a live `struct rlimit`.
    assert_eq!(unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut limit) }, 0);
    limit.rlim_cur.min(1 << 20) as RawFd
}

/// The first of the numbers a case probes, `slot` apart from another case's
/// (the cases run concurrently): high enough that a shell holds nothing of
/// its own there, low enough for the soft limit (256 on a default Mac).
fn probe_number(slot: RawFd) -> RawFd {
    (soft_nofile() - 64).clamp(32, 400) + 8 * slot
}

/// A descriptor on `/dev/null` WITHOUT close-on-exec at `floor` or above:
/// what another thread's half-made socketpair, a C library, or this
/// process's own parent leaves for a spawn to find.
fn unflagged_at_or_above(floor: RawFd) -> OwnedFd {
    let null = fs::File::open("/dev/null").unwrap();
    // SAFETY: `F_DUPFD` reads one descriptor and returns a fresh one or -1.
    let fd = unsafe { libc::fcntl(null.as_raw_fd(), libc::F_DUPFD, floor) };
    assert!(fd >= floor, "F_DUPFD({floor}): {}", io::Error::last_os_error());
    // SAFETY: just created here, owned by nothing else.
    unsafe { OwnedFd::from_raw_fd(fd) }
}

/// `fd` moved to a close-on-exec number at `floor` or above (the original
/// is closed).
fn moved_at_or_above(fd: OwnedFd, floor: RawFd) -> OwnedFd {
    // SAFETY: `F_DUPFD_CLOEXEC` reads one descriptor and returns a fresh one or -1.
    let copy = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_DUPFD_CLOEXEC, floor) };
    assert!(copy >= floor, "F_DUPFD_CLOEXEC({floor}): {}", io::Error::last_os_error());
    drop(fd);
    // SAFETY: just created here, owned by nothing else.
    unsafe { OwnedFd::from_raw_fd(copy) }
}

/// Whether the child of `cmd` (set up by `setup`) holds `fd`.
fn child_holds(fork: bool, fd: RawFd, setup: impl FnOnce(&mut Command)) -> bool {
    let mut cmd = sh(&format!("[ -e /dev/fd/{fd} ] && exit 3; exit 0"), fork);
    setup(&mut cmd);
    match cmd.status().unwrap().code() {
        Some(3) => true,
        Some(0) => false,
        other => panic!("the probe child answered {other:?}"),
    }
}

/// What a write end of a pipe the child was handed carries back.
fn read_all(mut reader: io::PipeReader) -> String {
    let mut got = String::new();
    reader.read_to_string(&mut got).unwrap();
    got
}

/// **AN UNFLAGGED DESCRIPTOR REACHES NO CHILD**, on either path, while
/// `inherit_all_fds` (the control, and the opt-out) still hands it over.
#[test]
fn an_unflagged_descriptor_reaches_no_child() {
    let held = unflagged_at_or_above(probe_number(0));
    let fd = held.as_raw_fd();
    for fork in PATHS {
        assert!(
            child_holds(fork, fd, |cmd| {
                cmd.inherit_all_fds();
            }),
            "CONTROL (fork={fork}): inherit_all_fds must hand unflagged fd {fd} over"
        );
        assert!(!child_holds(fork, fd, |_| {}), "fork={fork}: unflagged fd {fd} reached the child");
    }
}

/// Stdio still arrives as configured: piped, null and inherited.
#[test]
fn piped_null_and_inherited_stdio_still_work() {
    for fork in PATHS {
        let mut child = sh("read l; echo \"got:$l\"; echo err >&2; exit 7", fork)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(b"in\n").unwrap();
        let out = child.wait_with_output().unwrap();
        assert_eq!(out.status.code(), Some(7), "fork={fork}");
        assert_eq!(out.stdout, b"got:in\n", "fork={fork}");
        assert_eq!(out.stderr, b"err\n", "fork={fork}");

        let out = sh("cat; echo done", fork).stdin(Stdio::null()).output().unwrap();
        assert!(out.status.success(), "fork={fork}");
        assert_eq!(out.stdout, b"done\n", "fork={fork}");

        // An inherited slot reaches the child exactly when this process
        // holds it without close-on-exec, as upstream's spawn hands it on.
        let mut want = 0;
        for target in 0..3 {
            // SAFETY: `F_GETFD` reads one descriptor's flags.
            let flags = unsafe { libc::fcntl(target, libc::F_GETFD) };
            if flags >= 0 && flags & libc::FD_CLOEXEC == 0 {
                want |= 1 << target;
            }
        }
        let status = sh(
            "c=0; [ -e /dev/fd/0 ] && c=$((c|1)); [ -e /dev/fd/1 ] && c=$((c|2)); \
             [ -e /dev/fd/2 ] && c=$((c|4)); exit $c",
            fork,
        )
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .unwrap();
        assert_eq!(status.code(), Some(want), "fork={fork}");
    }
}

/// `output()` and `status()` report the child.
#[test]
fn output_and_status_report_the_child() {
    for fork in PATHS {
        let out = sh("echo hi; echo oops >&2; exit 5", fork).output().unwrap();
        assert_eq!(out.status.code(), Some(5), "fork={fork}");
        assert_eq!(out.stdout, b"hi\n", "fork={fork}");
        assert_eq!(out.stderr, b"oops\n", "fork={fork}");
        assert!(sh("exit 0", fork).status().unwrap().success(), "fork={fork}");
        assert_eq!(sh("exit 3", fork).status().unwrap().code(), Some(3), "fork={fork}");
    }
}

/// **A `pre_exec` `dup2` PLACEMENT SURVIVES**: the hook runs after the
/// strip, and `dup2` clears its target's close-on-exec flag.
#[test]
fn a_pre_exec_dup2_placement_survives() {
    const TARGET: RawFd = 5;
    let (reader, writer) = io::pipe().unwrap();
    // Off the target: `dup2(fd, fd)` changes nothing and leaves the flag set.
    let writer = moved_at_or_above(writer.into(), 10);
    let raw = writer.as_raw_fd();
    let mut cmd = sh(&format!("echo placed >&{TARGET}"), false);
    // SAFETY: `dup2` and `last_os_error` are async-signal-safe.
    unsafe {
        cmd.pre_exec(move || {
            if libc::dup2(raw, TARGET) < 0 { Err(io::Error::last_os_error()) } else { Ok(()) }
        });
    }
    let mut child = cmd.spawn().unwrap();
    drop(writer);
    assert_eq!(read_all(reader), "placed\n");
    assert!(child.wait().unwrap().success());
}

/// **`inherit_fd` HANDS A DESCRIPTOR OVER** at its own number, close-on-exec
/// here or not, with or without `inherit_all_fds` (which alone would not
/// hand over a close-on-exec descriptor).
#[test]
fn inherit_fd_hands_a_close_on_exec_descriptor_over() {
    for fork in PATHS {
        for all in [false, true] {
            let (reader, writer) = io::pipe().unwrap();
            let fd = writer.as_raw_fd();
            let mut cmd = sh(&format!("echo handed >&{fd}"), fork);
            cmd.inherit_fd(fd);
            if all {
                cmd.inherit_all_fds();
            }
            let mut child = cmd.spawn().unwrap();
            drop(writer);
            assert_eq!(read_all(reader), "handed\n", "fork={fork} all={all}");
            assert!(child.wait().unwrap().success(), "fork={fork} all={all}");
        }
    }
    // The flag is cleared in the child only.
    let (_reader, writer) = io::pipe().unwrap();
    sh("exit 0", false).inherit_fd(writer.as_raw_fd()).status().unwrap();
    sh("exit 0", true).inherit_fd(writer.as_raw_fd()).status().unwrap();
    // SAFETY: `F_GETFD` reads one descriptor's flags.
    let flags = unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_GETFD) };
    assert!(flags >= 0 && flags & libc::FD_CLOEXEC != 0, "inherit_fd changed this process's flag");
}

/// `inherit_fd` of a number this process does not hold fails the spawn with
/// `EBADF` instead of starting a child without it.
#[test]
fn inherit_fd_of_a_closed_descriptor_fails_the_spawn() {
    let n = soft_nofile().min(4096) - 2;
    // SAFETY: `F_GETFD` reads one descriptor's flags.
    if unsafe { libc::fcntl(n, libc::F_GETFD) } >= 0 {
        eprintln!("skipped: fd {n} is in use here");
        return;
    }
    for fork in PATHS {
        let err = sh("exit 0", fork).inherit_fd(n).spawn().map(|mut c| c.wait()).unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::EBADF), "fork={fork}: {err}");
    }
}

/// **A FAILED EXEC IS STILL AN ERROR**, never a started child: the strip
/// marks std's exec-status descriptor rather than closing it, and with
/// hooks to run std keeps it off 0..=9, where this hook places descriptors.
#[test]
fn a_failed_exec_is_still_reported() {
    const MISSING: &str = "/nonexistent/trust-std-no-such-program";
    for fork in PATHS {
        let mut cmd = Command::new(MISSING);
        if fork {
            // Writable: were std's status descriptor among the targets, the
            // child's report would vanish into it rather than abort the child.
            let null = fs::OpenOptions::new().write(true).open("/dev/null").unwrap();
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

/// **ZERO LEAKS WHILE ANOTHER THREAD RACES THE SPAWN**, over 400 spawns per
/// path: a thread keeps opening unflagged descriptors and holding them for a
/// moment, the window a plain upstream spawn hands them on in (MEASURED,
/// aterm 2026-10-01: 17-27 of 200 children). The probe's control is
/// deterministic: a held unflagged descriptor at the probed number reaches an
/// `inherit_all_fds` child.
#[test]
fn no_descriptor_leaks_while_another_thread_races_the_spawn() {
    const SPAWNS: usize = 400;
    let floor = probe_number(2);
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
        thread::spawn(move || {
            let mut turns = 0usize;
            while !stop.load(Ordering::Relaxed) {
                let held = [
                    unflagged_at_or_above(floor),
                    unflagged_at_or_above(floor),
                    unflagged_at_or_above(floor),
                    unflagged_at_or_above(floor),
                ];
                let until = Instant::now() + Duration::from_micros(200);
                while Instant::now() < until {
                    crate::hint::spin_loop();
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
    let turns = racer.join().unwrap();
    assert!(turns > 0, "the racer never ran");
    assert_eq!(leaks, [0, 0], "racer descriptors reached [posix_spawn, fork] children");
}
