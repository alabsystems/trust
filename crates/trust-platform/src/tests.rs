//! Model-level unit tests. The authority on what Darwin does is
//! `tests/conformance_darwin.rs`; these pin the clauses' algebra (invariants,
//! refusals, std rows, symbol lookup) without touching the host.

use crate::call::{Call, FileAction, Oracle, Refusal, Ret};
use crate::clauses::{Darwin, step};
use crate::darwin::{self, Errno};
use crate::host::{Access, Host, OfdKind, Phase, Pid, Rlimit};
use crate::script::{self, Actor, Guard, Operand, ProgramError, ProgramStep};
use crate::std_summaries::{self, CommandShape, CommandStd, StdioPlan};
use crate::symbols::{self, ClauseId, Modeled};

fn host(soft: u64) -> (Host, Pid) {
    let mut h = Host::new(92160);
    let root = h.add_root(Rlimit { soft, hard: darwin::RLIM_INFINITY });
    let null = h.install_fresh(root, 0, OfdKind::File, Access::ReadWrite, 0, false).unwrap();
    h.install_dup(root, 1, null, false).unwrap();
    h.install_dup(root, 2, null, false).unwrap();
    (h, root)
}

fn ok(h: &Host, pid: Pid, call: Call) -> (Host, Ret) {
    let s =
        step(h, pid, &call, Oracle::Nominal).unwrap_or_else(|r| panic!("{call:?} refused: {r}"));
    s.host.check_invariants().unwrap();
    (s.host, s.result.unwrap_or_else(|e| panic!("{call:?} failed {e}")))
}

fn err(h: &Host, pid: Pid, call: Call) -> Errno {
    let s = step(h, pid, &call, Oracle::Nominal).unwrap();
    assert_eq!(&s.host, h, "{call:?} failed but changed the host");
    s.result.unwrap_err()
}

#[test]
fn pipe_is_lowest_free_and_not_cloexec() {
    let (h, p) = host(256);
    let (h, r) = ok(&h, p, Call::Pipe);
    assert_eq!(r, Ret::Pair(3, 4));
    assert!(!h.entry(p, 3).unwrap().cloexec && !h.entry(p, 4).unwrap().cloexec);
    assert_eq!(h.peer_closed(p, 3), Some(false));
    let (h, _) = ok(&h, p, Call::Close { fd: 4 });
    assert_eq!(h.peer_closed(p, 3), Some(true));
}

#[test]
fn pipe_with_one_free_slot_is_emfile_and_changes_nothing() {
    let (h, p) = host(4);
    assert_eq!(err(&h, p, Call::Pipe), Errno::EMFILE);
    let (h, r) = ok(&h, p, Call::Kqueue);
    assert_eq!(r, Ret::Int(3));
    assert!(h.entry(p, 3).unwrap().cloexec, "kqueue is born close-on-exec");
}

#[test]
fn dup2_self_keeps_cloexec_and_other_clears_it() {
    let (h, p) = host(256);
    let (h, _) = ok(&h, p, Call::Pipe);
    let (h, _) = ok(&h, p, Call::Ioctl { fd: 3, request: darwin::FIOCLEX, arg: 0 });
    let (h2, r) = ok(&h, p, Call::Dup2 { from: 3, to: 3 });
    assert_eq!((r, h2.entry(p, 3).unwrap().cloexec), (Ret::Int(3), true));
    let (h3, _) = ok(&h, p, Call::Dup2 { from: 3, to: 9 });
    assert!(!h3.entry(p, 9).unwrap().cloexec);
    assert_eq!(h3.entry(p, 9).unwrap().ofd, h3.entry(p, 3).unwrap().ofd);
    // dup2 onto the write end drops it (last reference): the read end sees EOF.
    let (h4, _) = ok(&h, p, Call::Dup2 { from: 3, to: 4 });
    assert_eq!(h4.peer_closed(p, 3), Some(true));
}

#[test]
fn limits_order_errors_like_darwin() {
    let (h, p) = host(256);
    let (h, _) = ok(&h, p, Call::Pipe);
    let (h, _) = ok(&h, p, Call::Fcntl { fd: 3, cmd: darwin::F_DUPFD, arg: 40 });
    let (h, _) = ok(
        &h,
        p,
        Call::Setrlimit { resource: darwin::RLIMIT_NOFILE, soft: 32, hard: darwin::RLIM_INFINITY },
    );
    assert!(h.entry(p, 40).is_some(), "lowering the limit closes nothing");
    assert_eq!(err(&h, p, Call::Dup2 { from: 40, to: 40 }), Errno::EBADF);
    assert_eq!(err(&h, p, Call::Fcntl { fd: 3, cmd: darwin::F_DUPFD, arg: 32 }), Errno::EINVAL);
    let (_, r) = ok(&h, p, Call::Fcntl { fd: 40, cmd: darwin::F_DUPFD, arg: 0 });
    assert_eq!(r, Ret::Int(5));
    assert_eq!(
        err(&h, p, Call::Setrlimit { resource: darwin::RLIMIT_NOFILE, soft: 100, hard: 50 }),
        Errno::EINVAL
    );
}

#[test]
fn open_at_full_table_is_emfile_before_the_path() {
    let (h, p) = host(3);
    let s =
        step(&h, p, &Call::Open { flags: darwin::O_RDONLY }, Oracle::Fail(Errno::ENOENT)).unwrap();
    assert_eq!(s.result, Err(Errno::EMFILE));
}

#[test]
fn fork_snapshots_everything_but_kqueues_and_exec_sweeps() {
    let (h, p) = host(256);
    let (h, _) = ok(&h, p, Call::Pipe);
    let (h, _) = ok(&h, p, Call::Ioctl { fd: 3, request: darwin::FIOCLEX, arg: 0 });
    let (h, _) = ok(&h, p, Call::Kqueue);
    let (h, _) = ok(&h, p, Call::Fcntl { fd: 5, cmd: darwin::F_SETFD, arg: 0 });
    let (h, r) = ok(&h, p, Call::Fork);
    let Ret::Int(c) = r else { panic!() };
    let child = Pid(u32::try_from(c).unwrap());
    assert_eq!(h.proc(child).unwrap().fds(), [0, 1, 2, 3, 4].into_iter().collect());
    assert!(matches!(h.proc(child).unwrap().phase, Phase::ForkedPreExec { parent_threads: 1 }));
    assert_eq!(h.refs(h.entry(p, 4).unwrap().ofd), 2);
    // A failed exec changes nothing.
    let s = step(&h, child, &Call::Exec, Oracle::Fail(Errno::ENOENT)).unwrap();
    assert_eq!((s.result, &s.host), (Err(Errno::ENOENT), &h));
    let (h, r) = ok(&h, child, Call::Exec);
    assert_eq!(r, Ret::NoReturn);
    assert_eq!(h.proc(child).unwrap().fds(), [0, 1, 2, 4].into_iter().collect());
    // Exec in place drops a kqueue whose FD_CLOEXEC is clear.
    let (h, _) = ok(&h, p, Call::Exec);
    assert!(h.entry(p, 5).is_none());
}

fn spawn_child_fds(
    h: &Host,
    p: Pid,
    actions: Vec<FileAction>,
    flags: i32,
) -> Result<Vec<i32>, Errno> {
    let s = step(h, p, &Call::Spawn { actions, flags }, Oracle::Nominal).unwrap();
    s.host.check_invariants().unwrap();
    let Ret::Int(c) = s.result? else { panic!() };
    let child = s.host.proc(Pid(u32::try_from(c).unwrap())).unwrap();
    assert_eq!(child.phase, Phase::Execd);
    assert!(child.table.values().all(|e| !e.cloexec), "survivors are never cloexec");
    Ok(child.fds().into_iter().collect())
}

/// The 13 posix_spawn cases measured on Darwin 25.6 (also re-measured by the
/// conformance suite).
#[test]
fn posix_spawn_matches_the_measured_cases() {
    let cd = darwin::POSIX_SPAWN_CLOEXEC_DEFAULT;
    let (h, p) = host(256);
    let (h, _) = ok(
        &h,
        p,
        Call::Socketpair { domain: darwin::AF_UNIX, ty: darwin::SOCK_STREAM, protocol: 0 },
    );
    let (h, _) = ok(&h, p, Call::Ioctl { fd: 3, request: darwin::FIOCLEX, arg: 0 });
    assert_eq!(spawn_child_fds(&h, p, vec![], 0), Ok(vec![0, 1, 2, 4]));
    assert_eq!(
        spawn_child_fds(&h, p, vec![FileAction::Dup2 { from: 3, to: 3 }], 0),
        Ok(vec![0, 1, 2, 4])
    );
    assert_eq!(spawn_child_fds(&h, p, vec![FileAction::Dup2 { from: 3, to: 3 }], cd), Ok(vec![]));
    assert_eq!(
        spawn_child_fds(&h, p, vec![FileAction::Inherit { fd: 3 }], 0),
        Ok(vec![0, 1, 2, 3, 4])
    );
    assert_eq!(spawn_child_fds(&h, p, vec![FileAction::Inherit { fd: 3 }], cd), Ok(vec![3]));
    assert_eq!(
        spawn_child_fds(&h, p, vec![FileAction::Dup2 { from: 3, to: 20 }], cd),
        Ok(vec![20])
    );
    assert_eq!(spawn_child_fds(&h, p, vec![FileAction::Close { fd: 77 }], 0), Err(Errno::EBADF));
    assert_eq!(spawn_child_fds(&h, p, vec![FileAction::Inherit { fd: 77 }], 0), Err(Errno::EBADF));
    assert_eq!(
        spawn_child_fds(
            &h,
            p,
            vec![FileAction::Close { fd: 3 }, FileAction::Dup2 { from: 3, to: 20 }],
            0
        ),
        Err(Errno::EBADF)
    );
    let o_cx = darwin::O_RDONLY | darwin::O_CLOEXEC;
    assert_eq!(
        spawn_child_fds(&h, p, vec![FileAction::Open { fd: 30, flags: o_cx }], 0),
        Ok(vec![0, 1, 2, 4, 30])
    );
    assert_eq!(
        spawn_child_fds(
            &h,
            p,
            vec![FileAction::Dup2 { from: 1, to: 1 }, FileAction::Inherit { fd: 2 }],
            cd
        ),
        Ok(vec![1, 2])
    );
    let (h2, _) = host(256);
    assert_eq!(
        spawn_child_fds(&h2, p, vec![FileAction::Open { fd: 3, flags: o_cx }], 0),
        Ok(vec![0, 1, 2])
    );
    assert_eq!(
        spawn_child_fds(&h2, p, vec![FileAction::Open { fd: 3, flags: darwin::O_RDONLY }], cd),
        Ok(vec![3])
    );
    assert_eq!(
        spawn_child_fds(&h2, p, vec![FileAction::Open { fd: 5, flags: o_cx }], cd),
        Ok(vec![5])
    );
}

#[test]
fn unmodeled_effects_are_refused_by_name() {
    let (h, p) = host(256);
    let r = step(&h, p, &Call::Fcntl { fd: 0, cmd: 50, arg: 0 }, Oracle::Nominal).unwrap_err();
    assert_eq!(r, Refusal::Unmodeled { symbol: "fcntl", detail: "F_GETPATH".into() });
    let r = step(&h, p, &Call::Fcntl { fd: 0, cmd: 999, arg: 0 }, Oracle::Nominal).unwrap_err();
    assert_eq!(r, Refusal::Unmodeled { symbol: "fcntl", detail: "cmd=999".into() });
    let r = step(&h, p, &Call::Ioctl { fd: 0, request: 0x4008_7468, arg: 0 }, Oracle::Nominal)
        .unwrap_err();
    assert_eq!(r, Refusal::Unmodeled { symbol: "ioctl", detail: "TIOCGWINSZ".into() });
    let r = step(
        &h,
        p,
        &Call::Spawn { actions: vec![], flags: darwin::POSIX_SPAWN_SETEXEC },
        Oracle::Nominal,
    )
    .unwrap_err();
    assert!(matches!(r, Refusal::Unmodeled { symbol: "posix_spawn", .. }));
    let r = step(&h, p, &Call::Getrlimit { resource: 7 }, Oracle::Nominal).unwrap_err();
    assert_eq!(r, Refusal::Unmodeled { symbol: "getrlimit", detail: "RLIMIT_NPROC".into() });
    let r = step(&h, p, &Call::Dup { fd: 0 }, Oracle::Fail(Errno::EIO)).unwrap_err();
    assert!(matches!(r, Refusal::InadmissibleOracle { symbol: "dup", .. }));
}

#[test]
fn waitpid_blocks_until_exit_and_exit_closes_everything() {
    let (h, p) = host(256);
    let (h, _) = ok(&h, p, Call::Pipe);
    let (h, Ret::Int(c)) = ok(&h, p, Call::Fork) else { panic!() };
    let child = Pid(u32::try_from(c).unwrap());
    let c32 = i32::try_from(c).unwrap();
    let (h, _) = ok(&h, p, Call::Close { fd: 4 });
    assert_eq!(h.peer_closed(p, 3), Some(false), "the child still holds the write end");
    assert_eq!(
        step(&h, p, &Call::Waitpid { pid: c32, options: 0 }, Oracle::Nominal).unwrap_err(),
        Refusal::Blocks
    );
    assert_eq!(
        step(&h, p, &Call::ReadSome { fd: 3 }, Oracle::Nominal).unwrap_err(),
        Refusal::Blocks
    );
    let (h, _) = ok(&h, child, Call::Exit { status: 0 });
    assert_eq!(h.peer_closed(p, 3), Some(true));
    let (h, r) = ok(&h, p, Call::ReadSome { fd: 3 });
    assert_eq!(r, Ret::Int(0), "end-of-file");
    let (h, _) = ok(&h, p, Call::Waitpid { pid: c32, options: 0 });
    assert!(h.proc(child).is_none());
    assert_eq!(err(&h, p, Call::Waitpid { pid: c32, options: 0 }), Errno::ECHILD);
}

/// F5: `waitpid` has options and `pid == -1`. A WNOHANG poll on a live child
/// returns 0 at once (the parent moves on while the child still holds its
/// descriptors); `-1` waits for ANY child, not "no such child".
#[test]
fn waitpid_options_and_any_child() {
    let (h, p) = host(256);
    assert_eq!(err(&h, p, Call::Waitpid { pid: -1, options: 0 }), Errno::ECHILD);
    let (h, Ret::Int(c)) = ok(&h, p, Call::Fork) else { panic!() };
    let child = Pid(u32::try_from(c).unwrap());
    let poll = Call::Waitpid { pid: -1, options: darwin::WNOHANG };
    let (h, r) = ok(&h, p, poll.clone());
    assert_eq!(r, Ret::Int(0), "WNOHANG on a live child returns 0");
    let one = Call::Waitpid { pid: i32::try_from(c).unwrap(), options: darwin::WNOHANG };
    assert_eq!(ok(&h, p, one).1, Ret::Int(0));
    assert_eq!(
        step(&h, p, &Call::Waitpid { pid: -1, options: 0 }, Oracle::Nominal).unwrap_err(),
        Refusal::Blocks,
        "waitpid(-1) waits for the live child; it is not ECHILD"
    );
    let (h, _) = ok(&h, child, Call::Exit { status: 0 });
    let (h, r) = ok(&h, p, poll);
    assert_eq!(r, Ret::Int(c), "the exited child is reaped by the poll");
    assert!(h.proc(child).is_none());
    for (pid, options) in [(0, 0), (-7, 0), (-1, darwin::WUNTRACED), (-1, darwin::WCONTINUED)] {
        let r = step(&h, p, &Call::Waitpid { pid, options }, Oracle::Nominal).unwrap_err();
        assert!(matches!(r, Refusal::Unmodeled { symbol: "waitpid", .. }), "{pid} {options}: {r}");
    }
    // Two zombies: which one `-1` reaps is not modeled.
    let (h, Ret::Int(a)) = ok(&h, p, Call::Fork) else { panic!() };
    let (h, Ret::Int(b)) = ok(&h, p, Call::Fork) else { panic!() };
    let (h, _) = ok(&h, Pid(u32::try_from(a).unwrap()), Call::Exit { status: 0 });
    let (h, _) = ok(&h, Pid(u32::try_from(b).unwrap()), Call::Exit { status: 0 });
    let r = step(&h, p, &Call::Waitpid { pid: -1, options: 0 }, Oracle::Nominal).unwrap_err();
    assert!(matches!(r, Refusal::Unmodeled { symbol: "waitpid", .. }), "{r}");
}

/// F11: the status-pipe channel carries "some data": a writer marks the
/// reader's description, a read consumes it before end-of-file.
#[test]
fn read_some_sees_data_before_eof_and_write_needs_a_reader() {
    let (h, p) = host(256);
    let (h, _) = ok(&h, p, Call::Pipe);
    assert_eq!(err(&h, p, Call::WriteSome { fd: 3 }), Errno::EBADF, "the read end");
    assert_eq!(err(&h, p, Call::ReadSome { fd: 4 }), Errno::EBADF, "the write end");
    let (h, r) = ok(&h, p, Call::WriteSome { fd: 4 });
    assert_eq!(r, Ret::Int(1));
    let (h, _) = ok(&h, p, Call::Close { fd: 4 });
    let (h, r) = ok(&h, p, Call::ReadSome { fd: 3 });
    assert_eq!(r, Ret::Int(1), "data first");
    let (h, r) = ok(&h, p, Call::ReadSome { fd: 3 });
    assert_eq!(r, Ret::Int(0), "then end-of-file");
    let (h, Ret::Pair(r, w)) = ok(&h, p, Call::Pipe) else { panic!() };
    let (h2, _) = ok(&h, p, Call::Close { fd: r });
    let e = step(&h2, p, &Call::WriteSome { fd: w }, Oracle::Nominal).unwrap_err();
    assert!(matches!(e, Refusal::Unmodeled { symbol: "write", .. }), "SIGPIPE is not modeled");
    let (h, _) = ok(&h, p, Call::Fcntl { fd: r, cmd: darwin::F_SETFL, arg: 4 });
    assert_eq!(err(&h, p, Call::ReadSome { fd: r }), Errno::EAGAIN, "non-blocking, nothing yet");
}

#[test]
fn canonical_forgets_allocation_history() {
    let (h, p) = host(256);
    let (a, _) = ok(&h, p, Call::Pipe);
    let (a, _) = ok(&a, p, Call::Close { fd: 3 });
    let (a, _) = ok(&a, p, Call::Close { fd: 4 });
    let (a, _) = ok(&a, p, Call::Pipe);
    let (b, _) = ok(&h, p, Call::Pipe);
    assert_ne!(a, b);
    assert_eq!(a.canonical(), b.canonical());
    assert_eq!(a.canonical().render(), b.canonical().render());
}

#[test]
fn symbols_resolve_mach_o_spellings_and_refuse_the_unknown() {
    let l = symbols::lookup_macho("_close$NOCANCEL").unwrap();
    assert_eq!((l.normalized.as_str(), l.variant.as_deref()), ("close", Some("$NOCANCEL")));
    assert_eq!(l.modeled, Modeled::Clause(ClauseId::Close));
    assert_eq!(symbols::lookup_macho("__exit").unwrap().modeled, Modeled::Clause(ClauseId::Exit));
    assert_eq!(
        symbols::lookup_macho("_posix_spawnp").unwrap().modeled,
        Modeled::Clause(ClauseId::Spawn)
    );
    // F6: the Mach-O symbol `_exit` is C `exit(3)`, which runs atexit
    // handlers: NOT the `_exit(2)` clause.
    let e = symbols::lookup_macho("_exit").unwrap_err();
    assert!(e.reason.contains("atexit"), "{e}");
    let e = symbols::lookup("exit").unwrap_err();
    assert!(e.reason.contains("async-signal-safe"), "{e}");
    assert_eq!(symbols::lookup("_exit").unwrap().modeled, Modeled::Clause(ClauseId::Exit));
    assert!(symbols::lookup_macho("pipe").is_err(), "a C name is not a Mach-O symbol");
    // F10 (M2): openat's dirfd is modeled for a relative path; resolution
    // relative to a real directory is refused by the clause.
    assert_eq!(symbols::lookup("openat").unwrap().modeled, Modeled::Clause(ClauseId::Openat));
    assert!(symbols::async_signal_safe("_exit") && symbols::async_signal_safe("dup2"));
    for unsafe_name in ["exit", "posix_spawn", "posix_spawnp", "pthread_create", "malloc"] {
        assert!(!symbols::async_signal_safe(unsafe_name), "{unsafe_name}");
    }
    assert_eq!(
        symbols::lookup("std::os::unix::net::UnixStream::pair").unwrap().modeled,
        Modeled::StdRow("STD-PAIR")
    );
    assert_eq!(
        symbols::lookup("std::os::fd::BorrowedFd<'_>::try_clone_to_owned").unwrap().modeled,
        Modeled::StdRow("STD-TRY-CLONE")
    );
    let e = symbols::lookup_macho("_lockf").unwrap_err();
    assert!(e.reason.contains("per process"), "{e}");
    let e = symbols::lookup_macho("_frobnicate").unwrap_err();
    assert_eq!(e.reason, "not in the platform symbol table");
    for (name, _) in symbols::modeled_names() {
        assert!(symbols::lookup(name).is_ok(), "{name}");
    }
    for (name, _) in symbols::named_gaps() {
        assert!(symbols::lookup(name).is_err(), "{name}");
    }
    // Every std row the table names exists.
    for (name, m) in symbols::modeled_names() {
        if let Modeled::StdRow(id) = m {
            assert!(std_summaries::row(id).is_some(), "{name} -> {id}");
        }
    }
}

#[test]
fn std_pair_ends_close_on_exec_with_two_windows() {
    let (h, p) = host(256);
    let row = std_summaries::std_pair(darwin::SOCK_STREAM);
    let trace = script::run(&Darwin, &h, p, &row.program, &[]).unwrap();
    assert!(!row.atomic);
    // After the socketpair step alone, both ends are inheritable: the window.
    assert!(!trace[0].host.entry(p, 3).unwrap().cloexec);
    let last = &trace.last().unwrap().host;
    assert!(last.entry(p, 3).unwrap().cloexec && last.entry(p, 4).unwrap().cloexec);
}

/// Bug 3's shape: a parent holding an unflagged descriptor spawns through
/// std's fork path with a pre_exec that only places two lanes. The model
/// strips the stray descriptor before the hooks without closing their sources.
#[test]
fn std_spawn_fork_strips_unflagged_descriptors_before_hooks() {
    let (h, p) = host(256);
    // An unflagged descriptor from foreign code (RL-FOREIGN), at 64.
    let mut h = h;
    h.install_fresh(p, 64, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    // The two lanes: a UnixStream::pair's far ends (cloexec), args 0 and 1.
    let pair = std_summaries::std_pair(darwin::SOCK_STREAM);
    let t = script::run(&Darwin, &h, p, &pair.program, &[]).unwrap();
    let h = t.last().unwrap().host.clone();
    let place = vec![
        Call::Dup2 { from: Operand::Arg(0), to: Operand::Lit(3) },
        Call::Dup2 { from: Operand::Arg(1), to: Operand::Lit(4) },
    ];
    let fr = std_summaries::command_spawn_fork(
        [StdioPlan::Inherit; 3],
        &CommandShape::with_pre_exec(),
        &[place],
    )
    .unwrap();
    let (row, fork) = (fr.row, fr.fork);
    // Lanes 3 and 4 are the sources here, so the placement is two self-copies:
    // exactly the dup2(fd, fd) trap spawnfd.rs documents.
    let trace = script::run(&Darwin, &h, p, &row.program, &[3, 4]).unwrap();
    let exec_step = row
        .program
        .iter()
        .position(|s| s.actor == Actor::Child(fork) && s.call == Call::Exec)
        .unwrap();
    let child = trace[exec_step].pid;
    let at_exec = trace[exec_step].host.proc(child).unwrap().fds();
    assert!(!at_exec.contains(&64), "the stray descriptor must not reach the child: {at_exec:?}");
    assert!(
        !at_exec.contains(&3) && !at_exec.contains(&4),
        "self-copied cloexec lanes are closed at exec"
    );
    // The parent ends with exactly what it started with.
    assert_eq!(trace.last().unwrap().host.proc(p).unwrap().fds(), h.proc(p).unwrap().fds());
}

/// Upstream keeps unflagged descriptors; this differs from Trust's default.
#[test]
fn std_spawn_fork_without_strip_leaks_an_unflagged_descriptor() {
    let (h, p) = host(256);
    // An unflagged descriptor from foreign code (RL-FOREIGN), at 64.
    let mut h = h;
    h.install_fresh(p, 64, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    // The two lanes: a UnixStream::pair's far ends (cloexec), args 0 and 1.
    let pair = std_summaries::std_pair(darwin::SOCK_STREAM);
    let t = script::run(&Darwin, &h, p, &pair.program, &[]).unwrap();
    let h = t.last().unwrap().host.clone();
    let place = vec![
        Call::Dup2 { from: Operand::Arg(0), to: Operand::Lit(3) },
        Call::Dup2 { from: Operand::Arg(1), to: Operand::Lit(4) },
    ];
    let fr = std_summaries::command_spawn_fork(
        [StdioPlan::Inherit; 3],
        &CommandShape::with_pre_exec().under(CommandStd::Upstream),
        &[place],
    )
    .unwrap();
    let (row, fork) = (fr.row, fr.fork);
    // Lanes 3 and 4 are the sources here, so the placement is two self-copies:
    // exactly the dup2(fd, fd) trap spawnfd.rs documents.
    let trace = script::run(&Darwin, &h, p, &row.program, &[3, 4]).unwrap();
    let exec_step = row
        .program
        .iter()
        .position(|s| s.actor == Actor::Child(fork) && s.call == Call::Exec)
        .unwrap();
    let child = trace[exec_step].pid;
    let at_exec = trace[exec_step].host.proc(child).unwrap().fds();
    assert!(at_exec.contains(&64), "the stray descriptor reaches the child: {at_exec:?}");
    assert!(
        !at_exec.contains(&3) && !at_exec.contains(&4),
        "self-copied cloexec lanes are closed at exec"
    );
    // The parent ends with exactly what it started with.
    assert_eq!(trace.last().unwrap().host.proc(p).unwrap().fds(), h.proc(p).unwrap().fds());
}

/// Upstream std's posix path (before SP-1): the stray descriptor rides along.
#[test]
fn std_spawn_posix_places_stdio_and_strips_unflagged() {
    let (mut h, p) = host(256);
    h.install_fresh(p, 64, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    let (row, spawn) = std_summaries::command_spawn_posix(
        [StdioPlan::Null, StdioPlan::Inherit, StdioPlan::Inherit],
        &CommandShape::default(),
    )
    .unwrap();
    let trace = script::run(&Darwin, &h, p, &row.program, &[]).unwrap();
    let Ok(Ret::Int(c)) = trace[spawn].result else { panic!() };
    let child = trace[spawn].host.proc(Pid(u32::try_from(c).unwrap())).unwrap().clone();
    assert_eq!(child.fds(), [0, 1, 2].into_iter().collect());
    let stdin = trace[spawn].host.ofd(child.table[&0].ofd).unwrap();
    assert_eq!((stdin.kind, stdin.access), (OfdKind::File, Access::ReadOnly));
    let _ = ProgramStep::root(Call::Pipe);
}

/// Upstream's POSIX row preserves unflagged descriptors.
#[test]
fn std_spawn_posix_dup2s_stdio_and_inherits_unflagged() {
    let (mut h, p) = host(256);
    h.install_fresh(p, 64, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    let (row, spawn) = std_summaries::command_spawn_posix(
        [StdioPlan::Null, StdioPlan::Inherit, StdioPlan::Inherit],
        &CommandShape::default().under(CommandStd::Upstream),
    )
    .unwrap();
    let trace = script::run(&Darwin, &h, p, &row.program, &[]).unwrap();
    let Ok(Ret::Int(c)) = trace[spawn].result else { panic!() };
    let child = trace[spawn].host.proc(Pid(u32::try_from(c).unwrap())).unwrap().clone();
    assert_eq!(child.fds(), [0, 1, 2, 64].into_iter().collect());
    let stdin = trace[spawn].host.ofd(child.table[&0].ofd).unwrap();
    assert_eq!((stdin.kind, stdin.access), (OfdKind::File, Access::ReadOnly));
    let _ = ProgramStep::root(Call::Pipe);
}

/// The same parents under Trust's std (DECISION_QUEUE SP-1, Trust
/// a7f474346f): the fork path strips the child after stdio and before the
/// hook, so the stray descriptor and the pair's own ends are closed at the
/// exec while the hook's lanes survive; the status pipe (5, 6) sat below
/// 10, so its write end moved to 10 first.
#[test]
fn trust_std_spawn_fork_hands_the_child_its_stdio_and_the_hooks_lanes_only() {
    let (mut h, p) = host(256);
    h.install_fresh(p, 64, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    let pair = std_summaries::std_pair(darwin::SOCK_STREAM);
    let t = script::run(&Darwin, &h, p, &pair.program, &[]).unwrap();
    let h = t.last().unwrap().host.clone();
    let place = vec![
        Call::Dup2 { from: Operand::Arg(0), to: Operand::Lit(20) },
        Call::Dup2 { from: Operand::Arg(1), to: Operand::Lit(21) },
    ];
    let fr = std_summaries::command_spawn_fork(
        [StdioPlan::Inherit; 3],
        &CommandShape::with_pre_exec(),
        &[place],
    )
    .unwrap();
    let trace = script::run(&Darwin, &h, p, &fr.row.program, &[3, 4]).unwrap();
    let child = trace[fr.exec].pid;
    let at_exec = trace[fr.exec].host.proc(child).unwrap().fds();
    assert_eq!(at_exec, [0, 1, 2, 20, 21].into_iter().collect());
    let moved = trace
        .iter()
        .position(|t| t.call == Call::StdStatusFd { fd: 6 })
        .expect("the status end's move");
    assert_eq!(trace[moved].result, Ok(Ret::Int(10)));
    assert_eq!(trace[fr.exec + 1].call, Call::Close { fd: 10 });
    assert_eq!(trace.last().unwrap().host.proc(p).unwrap().fds(), h.proc(p).unwrap().fds());
}

/// A status write end already at 10 or above stays where it is: the move and
/// its close are skipped, and change nothing.
#[test]
fn trust_std_spawn_fork_leaves_a_high_status_end_in_place() {
    let (mut h, p) = host(256);
    for fd in 3..10 {
        h.install_fresh(p, fd, OfdKind::Opaque, Access::ReadWrite, 0, true).unwrap();
    }
    let fr = std_summaries::command_spawn_fork(
        [StdioPlan::Inherit; 3],
        &CommandShape::with_pre_exec(),
        &[],
    )
    .unwrap();
    let k =
        fr.row.program.iter().position(|ps| matches!(ps.call, Call::StdStatusFd { .. })).unwrap();
    let trace = script::run(&Darwin, &h, p, &fr.row.program, &[]).unwrap();
    assert_eq!(trace[k].result, Ok(Ret::Int(11)), "the skipped move answers the old number");
    assert_eq!(trace[k].host, trace[k - 1].host);
    assert_eq!(trace[k + 1].host, trace[k].host);
    assert_eq!(trace[fr.exec + 1].call, Call::Close { fd: 11 });
    assert_eq!(trace.last().unwrap().host.proc(p).unwrap().fds(), h.proc(p).unwrap().fds());
}

#[test]
fn trust_std_spawn_posix_names_stdio_and_inherits_nothing_else() {
    let (mut h, p) = host(256);
    h.install_fresh(p, 64, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    let (row, spawn) = std_summaries::command_spawn_posix(
        [StdioPlan::Null, StdioPlan::Inherit, StdioPlan::Inherit],
        &CommandShape::default(),
    )
    .unwrap();
    let trace = script::run(&Darwin, &h, p, &row.program, &[]).unwrap();
    let Ok(Ret::Int(c)) = trace[spawn].result else { panic!() };
    let child = trace[spawn].host.proc(Pid(u32::try_from(c).unwrap())).unwrap().clone();
    assert_eq!(child.fds(), [0, 1, 2].into_iter().collect());
    assert!(child.table.values().all(|e| !e.cloexec));
}

/// Trust's rows refuse, by name, the branches of its std they do not model:
/// a stdio source that lands on its own target (fd 0 closed, so
/// `Stdio::null()` opens onto 0) and an inherited stdio slot that would not
/// pass an exec. Upstream's rows have neither branch.
#[test]
fn trust_std_spawn_rows_model_previously_unmodeled_stdio_branches() {
    let null = [StdioPlan::Null, StdioPlan::Inherit, StdioPlan::Inherit];
    let (h, p) = host(256);
    let (closed, _) = ok(&h, p, Call::Close { fd: 0 });
    let trust = CommandShape::default();
    let (row, spawn) = std_summaries::command_spawn_posix(null, &trust).unwrap();
    let trace = script::run(&Darwin, &closed, p, &row.program, &[]).unwrap();
    let Ok(Ret::Int(pid)) = trace[spawn].result else { panic!() };
    let child = trace[spawn].host.proc(Pid(u32::try_from(pid).unwrap())).unwrap();
    assert_eq!(child.fds(), [0, 1, 2].into_iter().collect());
    assert!(!child.table[&0].cloexec);
    let fr = std_summaries::command_spawn_fork(null, &CommandShape::with_pre_exec(), &[]).unwrap();
    let trace = script::run(&Darwin, &closed, p, &fr.row.program, &[]).unwrap();
    let child = trace[fr.exec].host.proc(trace[fr.exec].pid).unwrap();
    assert_eq!(child.fds(), [0, 1, 2].into_iter().collect());
    assert!(!child.table[&0].cloexec);
    let upstream = trust.under(CommandStd::Upstream);
    let (row, spawn) = std_summaries::command_spawn_posix(null, &upstream).unwrap();
    let trace = script::run(&Darwin, &closed, p, &row.program, &[]).unwrap();
    let Ok(Ret::Int(pid)) = trace[spawn].result else { panic!() };
    assert_eq!(
        trace[spawn].host.proc(Pid(u32::try_from(pid).unwrap())).unwrap().fds(),
        [1, 2].into_iter().collect()
    );
    let (flagged, _) = ok(&h, p, Call::Fcntl { fd: 1, cmd: darwin::F_SETFD, arg: 1 });
    let (row, spawn) = std_summaries::command_spawn_posix([StdioPlan::Inherit; 3], &trust).unwrap();
    let trace = script::run(&Darwin, &flagged, p, &row.program, &[]).unwrap();
    let Ok(Ret::Int(pid)) = trace[spawn].result else { panic!() };
    assert_eq!(
        trace[spawn].host.proc(Pid(u32::try_from(pid).unwrap())).unwrap().fds(),
        [0, 2].into_iter().collect()
    );
    assert!(trace.last().unwrap().host.entry(p, 1).unwrap().cloexec);
}
#[test]
fn cloexec_from_marks_from_first_up_and_only_in_one_thread() {
    let (h, p) = host(256);
    let (h, _) = ok(&h, p, Call::Pipe);
    let (h, _) = ok(&h, p, Call::Fcntl { fd: 3, cmd: darwin::F_DUPFD, arg: 40 });
    let (marked, r) = ok(&h, p, Call::CloexecFrom { first: 4 });
    assert_eq!(r, Ret::Int(0));
    let flags: Vec<(i32, bool)> =
        marked.proc(p).unwrap().table.iter().map(|(fd, e)| (*fd, e.cloexec)).collect();
    assert_eq!(flags, vec![(0, false), (1, false), (2, false), (3, false), (4, true), (40, true)]);
    let (threaded, _) = ok(&h, p, Call::ThreadCreate);
    assert!(matches!(
        step(&threaded, p, &Call::CloexecFrom { first: 3 }, Oracle::Nominal),
        Err(Refusal::Unmodeled { symbol: "fcntl", .. })
    ));
    assert!(matches!(
        step(&h, p, &Call::CloexecFrom { first: 3 }, Oracle::Fail(Errno::EBADF)),
        Err(Refusal::InadmissibleOracle { .. })
    ));
}

/// A skipped step changes nothing and answers its stated result; an
/// assumption that fails refuses the run at its step, by the call's name.
#[test]
fn guarded_steps_skip_and_assumptions_refuse() {
    let (h, p) = host(256);
    let r = |step, comp| Operand::Ret { step, comp };
    let program = vec![
        ProgramStep::root(Call::Pipe),
        ProgramStep::root(Call::Close { fd: r(0, 1) })
            .when(Guard::Below(r(0, 1), 4), Operand::Lit(7)),
        ProgramStep::root(Call::Close { fd: r(0, 0) })
            .when(Guard::Below(r(0, 0), 4), Operand::Lit(9)),
    ];
    let t = script::run(&Darwin, &h, p, &program, &[]).unwrap();
    assert_eq!(t[1].result, Ok(Ret::Int(7)));
    assert_eq!(t[1].host, t[0].host);
    assert!(t[2].host.entry(p, 3).is_none() && t[2].host.entry(p, 4).is_some());
    assert!(!ProgramStep::root(Call::Pipe).branches() && program[1].branches());
    let bad = vec![
        ProgramStep::root(Call::Pipe).assuming(Guard::Differ(r(0, 0), Operand::Lit(3)), "not 3"),
    ];
    assert!(matches!(
        script::run(&Darwin, &h, p, &bad, &[]),
        Err(ProgramError::Refused { step: 0, refusal: Refusal::Unmodeled { symbol: "pipe", .. } })
    ));
}

/// Exhaustive small-step closure: from a pipe+kqueue host, every pair of
/// single calls drawn from a call menu keeps the invariants.
#[test]
fn invariants_hold_over_all_two_step_sequences() {
    let (h, p) = host(8);
    let (h, _) = ok(&h, p, Call::Pipe);
    let (h, _) = ok(&h, p, Call::Kqueue);
    let menu: Vec<Call> = vec![
        Call::Pipe,
        Call::Socketpair { domain: darwin::AF_UNIX, ty: darwin::SOCK_STREAM, protocol: 0 },
        Call::Dup { fd: 3 },
        Call::Dup2 { from: 3, to: 4 },
        Call::Dup2 { from: 4, to: 7 },
        Call::Close { fd: 3 },
        Call::Close { fd: 4 },
        Call::Fcntl { fd: 4, cmd: darwin::F_DUPFD_CLOEXEC, arg: 6 },
        Call::Fcntl { fd: 3, cmd: darwin::F_SETFL, arg: i64::from(darwin::O_NONBLOCK) },
        Call::Ioctl { fd: 4, request: darwin::FIOCLEX, arg: 0 },
        Call::Fork,
        Call::Exec,
        Call::Spawn {
            actions: vec![FileAction::Dup2 { from: 4, to: 5 }],
            flags: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT,
        },
        Call::Setrlimit { resource: darwin::RLIMIT_NOFILE, soft: 4, hard: darwin::RLIM_INFINITY },
        Call::Exit { status: 0 },
    ];
    let mut checked = 0;
    for a in &menu {
        let Ok(s1) = step(&h, p, a, Oracle::Nominal) else {
            continue;
        };
        s1.host.check_invariants().unwrap();
        for b in &menu {
            for pid in s1.host.procs().map(|(pid, _)| pid).collect::<Vec<_>>() {
                if let Ok(s2) = step(&s1.host, pid, b, Oracle::Nominal) {
                    s2.host
                        .check_invariants()
                        .unwrap_or_else(|e| panic!("{a:?} then {pid:?} {b:?}: {e}"));
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 200, "{checked}");
}

/// F1: libc validates file actions at ADD time against OPEN_MAX (10240),
/// although the kernel allocates far above it. An action list holding such an
/// action cannot have been built, so the spawn refuses it instead of closing
/// (or inheriting) a descriptor libc never recorded.
#[test]
fn file_actions_beyond_open_max_are_rejected_at_add_time_and_refused_at_spawn() {
    use crate::clauses::file_action_add;
    assert_eq!(file_action_add(&FileAction::Close { fd: 10_239 }), Ok(()));
    for a in [
        FileAction::Close { fd: 20_000 },
        FileAction::Dup2 { from: 20_000, to: 7 },
        FileAction::Dup2 { from: 5, to: 20_000 },
        FileAction::Inherit { fd: 10_240 },
        FileAction::Open { fd: 20_000, flags: darwin::O_RDONLY },
        FileAction::Fchdir { fd: 20_000 },
        FileAction::Close { fd: -1 },
    ] {
        assert_eq!(file_action_add(&a), Err(Errno::EBADF), "{a:?}");
    }
    let (mut h, p) = host(1_048_576);
    h.install_fresh(p, 20_000, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    for (actions, flags) in [
        (vec![FileAction::Close { fd: 20_000 }], 0),
        (vec![FileAction::Inherit { fd: 20_000 }], darwin::POSIX_SPAWN_CLOEXEC_DEFAULT),
    ] {
        let r = step(&h, p, &Call::Spawn { actions, flags }, Oracle::Nominal).unwrap_err();
        assert!(
            matches!(&r, Refusal::Unmodeled { detail, .. } if detail.contains("OPEN_MAX")),
            "{r}"
        );
    }
}

/// F2: `/dev/fd/N` is the SAME open file description, so closing the
/// original write end does not give the reader end-of-file.
#[test]
fn dev_fd_alias_shares_the_description() {
    let (h, p) = host(256);
    let (h, _) = ok(&h, p, Call::Pipe);
    let (h, r) = ok(&h, p, Call::OpenAlias { fd: 4, flags: darwin::O_WRONLY | darwin::O_CLOEXEC });
    assert_eq!(r, Ret::Int(5));
    assert_eq!(h.entry(p, 5).unwrap().ofd, h.entry(p, 4).unwrap().ofd);
    assert!(h.entry(p, 5).unwrap().cloexec);
    let (h, _) = ok(&h, p, Call::Close { fd: 4 });
    assert_eq!(h.peer_closed(p, 3), Some(false), "the alias still holds the write description");
    assert_eq!(
        step(&h, p, &Call::ReadSome { fd: 3 }, Oracle::Nominal).unwrap_err(),
        Refusal::Blocks
    );
    // Access must lie within the description's; status bits are ignored.
    assert_eq!(err(&h, p, Call::OpenAlias { fd: 3, flags: darwin::O_WRONLY }), Errno::EACCES);
    assert_eq!(err(&h, p, Call::OpenAlias { fd: 3, flags: darwin::O_RDWR }), Errno::EACCES);
    let (h2, Ret::Int(n)) =
        ok(&h, p, Call::OpenAlias { fd: 5, flags: darwin::O_WRONLY | darwin::O_NONBLOCK })
    else {
        panic!()
    };
    assert_eq!(h2.ofd(h2.entry(p, 5).unwrap().ofd).unwrap().status, 0);
    let n = i32::try_from(n).unwrap();
    assert!(h2.entry(p, n).unwrap().cloexec, "the source's FD_CLOEXEC is copied");
    assert_eq!(err(&h, p, Call::OpenAlias { fd: 77, flags: darwin::O_RDONLY }), Errno::EBADF);
    let (h, Ret::Int(kq)) = ok(&h, p, Call::Kqueue) else { panic!() };
    let kq = i32::try_from(kq).unwrap();
    // PLATFORM-KQUEUE-ALIAS-1: the kernels disagree (EBADF on 25.6 and 27.0,
    // EACCES on 27.2), so every access mode is refused by name.
    for flags in [darwin::O_RDONLY, darwin::O_WRONLY, darwin::O_RDWR] {
        assert_eq!(
            step(&h, p, &Call::OpenAlias { fd: kq, flags }, Oracle::Nominal).unwrap_err(),
            Refusal::Unmodeled { symbol: "open", detail: crate::clauses::KQUEUE_ALIAS.to_string() },
        );
    }
    // A full table is EMFILE before the kqueue is looked at (MEASURED on 27.2).
    let (full, fp) = host(4);
    let (full, Ret::Int(fkq)) = ok(&full, fp, Call::Kqueue) else { panic!() };
    let fkq = i32::try_from(fkq).unwrap();
    for flags in [darwin::O_RDONLY, darwin::O_WRONLY, darwin::O_RDWR] {
        assert_eq!(err(&full, fp, Call::OpenAlias { fd: fkq, flags }), Errno::EMFILE);
    }
    assert_eq!(symbols::classify_open_path("/dev/fd/4"), symbols::OpenPath::FdAlias(4));
    assert_eq!(symbols::classify_open_path("/dev/stdout"), symbols::OpenPath::FdAlias(1));
    assert_eq!(symbols::classify_open_path("/dev/null"), symbols::OpenPath::DevNull);
    assert_eq!(symbols::classify_open_path("/tmp/x"), symbols::OpenPath::Other);
}

/// F4/F9/F12: open bits the model does not execute are refused by name —
/// O_EXLOCK takes a flock lock, O_EVTONLY and O_EXLOCK change F_GETFL, the
/// private 0x08000000 bit hides the descriptor from fork.
#[test]
fn open_refuses_unmodeled_bits_by_name() {
    let (h, p) = host(256);
    for (bits, name) in [
        (darwin::O_EXLOCK, "O_EXLOCK"),
        (darwin::O_SHLOCK, "O_SHLOCK"),
        (darwin::O_EVTONLY, "O_EVTONLY"),
        (darwin::O_CLOFORK_PRIVATE, "O_CLOFORK"),
        (darwin::O_RESOLVE_BENEATH, "O_RESOLVE_BENEATH"),
        (0x0004_0000, "unknown bits"),
    ] {
        for call in [
            Call::Open { flags: darwin::O_RDONLY | bits },
            Call::Spawn {
                actions: vec![FileAction::Open { fd: 9, flags: darwin::O_RDONLY | bits }],
                flags: 0,
            },
        ] {
            let r = step(&h, p, &call, Oracle::Nominal).unwrap_err();
            assert!(
                matches!(&r, Refusal::Unmodeled { detail, .. } if detail.contains(name)),
                "{call:?}: {r}"
            );
        }
    }
    for ok_bits in [
        darwin::O_CREAT | darwin::O_TRUNC | darwin::O_EXCL,
        darwin::O_NOFOLLOW | darwin::O_DIRECTORY | darwin::O_NOCTTY | darwin::O_CLOEXEC,
    ] {
        ok(&h, p, Call::Open { flags: darwin::O_RDONLY | ok_bits });
    }
}

/// PLATFORM-CLOFORK-1: Darwin 27 keeps `FD_CLOFORK` through `F_SETFD` and
/// drops the descriptor at `fork`. The model has no such flag, so an `F_SETFD`
/// carrying it is refused by name, and so is `F_DUPFD_CLOFORK`. A closed
/// descriptor is still `EBADF`, and every bit above the two is still ignored.
#[test]
fn setfd_refuses_clofork_by_name() {
    let (h, p) = host(256);
    let (h, Ret::Pair(rd, _)) = ok(&h, p, Call::Pipe) else { panic!() };
    for arg in [darwin::FD_CLOFORK, darwin::FD_CLOEXEC | darwin::FD_CLOFORK, 0xffff] {
        let call = Call::Fcntl { fd: rd, cmd: darwin::F_SETFD, arg };
        let r = step(&h, p, &call, Oracle::Nominal).unwrap_err();
        assert!(
            matches!(&r, Refusal::Unmodeled { symbol: "fcntl", detail } if detail.contains("FD_CLOFORK")),
            "F_SETFD({arg}): {r}"
        );
    }
    let closed = Call::Fcntl { fd: 77, cmd: darwin::F_SETFD, arg: darwin::FD_CLOFORK };
    assert_eq!(step(&h, p, &closed, Oracle::Nominal).unwrap().result, Err(Errno::EBADF));
    for (arg, getfd) in [(5, 1), (4, 0), (9, 1), (8, 0)] {
        let (h, _) = ok(&h, p, Call::Fcntl { fd: rd, cmd: darwin::F_SETFD, arg });
        let (_, r) = ok(&h, p, Call::Fcntl { fd: rd, cmd: darwin::F_GETFD, arg: 0 });
        assert_eq!(r, Ret::Int(getfd), "F_SETFD({arg})");
    }
    let dup = Call::Fcntl { fd: rd, cmd: 115, arg: 10 };
    let r = step(&h, p, &dup, Oracle::Nominal).unwrap_err();
    assert!(
        matches!(&r, Refusal::Unmodeled { symbol: "fcntl", detail } if detail == "F_DUPFD_CLOFORK"),
        "{r}"
    );
}

/// F8: F_SETFL on a kqueue fails ENOTTY for every argument, but the bits
/// change anyway.
#[test]
fn kqueue_setfl_fails_enotty_and_still_sets_the_bits() {
    let (h, p) = host(256);
    let (h, Ret::Int(kq)) = ok(&h, p, Call::Kqueue) else { panic!() };
    let kq = i32::try_from(kq).unwrap();
    for (arg, getfl) in [(4, 0x6), (8, 0xa), (0, 0x2)] {
        let s = step(&h, p, &Call::Fcntl { fd: kq, cmd: darwin::F_SETFL, arg }, Oracle::Nominal)
            .unwrap();
        assert_eq!(s.result, Err(Errno::ENOTTY));
        assert_eq!(s.host.ofd(s.host.entry(p, kq).unwrap().ofd).unwrap().getfl(), getfl);
    }
}

/// F10: errno order and socket kinds.
#[test]
fn socket_errno_order_and_accept_kinds() {
    let (h, p) = host(3);
    // A full table: socket() allocates before it checks the shape ...
    for (d, t, pr) in [
        (darwin::AF_UNIX, darwin::SOCK_STREAM | darwin::LINUX_SOCK_CLOEXEC, 0),
        (darwin::AF_UNIX, darwin::SOCK_SEQPACKET, 0),
        (darwin::AF_UNIX, darwin::SOCK_STREAM, 7),
    ] {
        assert_eq!(err(&h, p, Call::Socket { domain: d, ty: t, protocol: pr }), Errno::EMFILE);
    }
    // ... socketpair checks the type first, then allocates, then connects.
    let pair = |d, t| Call::Socketpair { domain: d, ty: t, protocol: 0 };
    assert_eq!(
        err(&h, p, pair(darwin::AF_UNIX, darwin::SOCK_STREAM | darwin::LINUX_SOCK_CLOEXEC)),
        Errno::EPROTONOSUPPORT
    );
    assert_eq!(err(&h, p, pair(darwin::AF_INET, darwin::SOCK_STREAM)), Errno::EMFILE);
    let (h, p) = host(256);
    assert_eq!(err(&h, p, pair(darwin::AF_INET, darwin::SOCK_STREAM)), Errno::EOPNOTSUPP);
    // accept: a datagram socket is EOPNOTSUPP, a stream socket that is not
    // listening is EINVAL — whatever the environment does.
    let (h, Ret::Int(dg)) =
        ok(&h, p, Call::Socket { domain: darwin::AF_UNIX, ty: darwin::SOCK_DGRAM, protocol: 0 })
    else {
        panic!()
    };
    let dg = i32::try_from(dg).unwrap();
    assert_eq!(err(&h, p, Call::Accept { fd: dg }), Errno::EOPNOTSUPP);
    let listen = |fd| Call::SocketOp { fd, op: crate::call::SocketOp::Listen };
    assert_eq!(err(&h, p, listen(dg)), Errno::EOPNOTSUPP);
    let (h, Ret::Int(st)) =
        ok(&h, p, Call::Socket { domain: darwin::AF_UNIX, ty: darwin::SOCK_STREAM, protocol: 0 })
    else {
        panic!()
    };
    let st = i32::try_from(st).unwrap();
    assert_eq!(err(&h, p, Call::Accept { fd: st }), Errno::EINVAL);
    assert!(matches!(
        step(&h, p, &Call::Accept { fd: st }, Oracle::Fail(Errno::EINVAL)),
        Err(Refusal::InadmissibleOracle { .. })
    ));
    let (h, _) = ok(&h, p, listen(st));
    ok(&h, p, Call::Accept { fd: st });
    // An environment descriptor of unknown kind is not guessed at.
    let mut h = h;
    h.install_fresh(p, 40, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    assert!(matches!(
        step(&h, p, &Call::Accept { fd: 40 }, Oracle::Nominal),
        Err(Refusal::Unmodeled { .. })
    ));
}

/// F10: addfchdir fails the spawn on a closed descriptor (EBADF), a kqueue
/// (EINVAL) and a non-vnode (EINVAL); addchdir has no descriptor effect.
#[test]
fn spawn_fchdir_outcomes() {
    let (h, p) = host(256);
    let spawn = |h: &Host, a: FileAction| {
        step(h, p, &Call::Spawn { actions: vec![a], flags: 0 }, Oracle::Nominal).unwrap().result
    };
    assert_eq!(spawn(&h, FileAction::Fchdir { fd: 77 }), Err(Errno::EBADF));
    let (h, Ret::Int(kq)) = ok(&h, p, Call::Kqueue) else { panic!() };
    assert_eq!(
        spawn(&h, FileAction::Fchdir { fd: i32::try_from(kq).unwrap() }),
        Err(Errno::EINVAL)
    );
    let (h, Ret::Pair(r, _)) = ok(&h, p, Call::Pipe) else { panic!() };
    assert_eq!(spawn(&h, FileAction::Fchdir { fd: r }), Err(Errno::EINVAL));
    assert!(spawn(&h, FileAction::Fchdir { fd: 0 }).is_ok(), "fd 0 is a vnode here");
    assert!(spawn(&h, FileAction::Chdir).is_ok());
}

/// F3: a torn table copy misses slots (never adds any).
#[test]
fn torn_fork_and_spawn_copy_a_subset() {
    use std::collections::BTreeSet;
    let (h, p) = host(256);
    let (h, _) = ok(&h, p, Call::Pipe);
    let missed: BTreeSet<i32> = [4].into_iter().collect();
    let s = crate::clauses::step_torn(&h, p, &Call::Fork, Oracle::Nominal, &missed).unwrap();
    let Ok(Ret::Int(c)) = s.result else { panic!() };
    let child = s.host.proc(Pid(u32::try_from(c).unwrap())).unwrap();
    assert_eq!(child.fds(), [0, 1, 2, 3].into_iter().collect());
    s.host.check_invariants().unwrap();
    // posix_spawn: an adddup2 from a missed slot fails the spawn EBADF.
    let spawn = Call::Spawn { actions: vec![FileAction::Dup2 { from: 4, to: 9 }], flags: 0 };
    let s = crate::clauses::step_torn(&h, p, &spawn, Oracle::Nominal, &missed).unwrap();
    assert_eq!(s.result, Err(Errno::EBADF));
    // Only fork/spawn can be torn, and only open slots can be missed.
    assert!(crate::clauses::step_torn(&h, p, &Call::Pipe, Oracle::Nominal, &missed).is_err());
    let closed: BTreeSet<i32> = [9].into_iter().collect();
    assert!(crate::clauses::step_torn(&h, p, &Call::Fork, Oracle::Nominal, &closed).is_err());
}

/// F7: std's own path choice on Darwin.
#[test]
fn std_takes_the_fork_path_for_setsid_and_cwd_with_a_relative_program() {
    use std_summaries::{CommandShape, SpawnPath, spawn_path};
    assert_eq!(spawn_path(&CommandShape::default()), SpawnPath::Posix);
    assert_eq!(spawn_path(&CommandShape::with_pre_exec()), SpawnPath::Fork);
    assert_eq!(spawn_path(&CommandShape { setsid: true, ..Default::default() }), SpawnPath::Fork);
    assert_eq!(spawn_path(&CommandShape { cwd: true, ..Default::default() }), SpawnPath::Posix);
    assert_eq!(
        spawn_path(&CommandShape { cwd: true, program_relative: true, ..Default::default() }),
        SpawnPath::Fork
    );
    let (row, _) = std_summaries::command_spawn_posix(
        [StdioPlan::Inherit; 3],
        &CommandShape { cwd: true, pgroup: true, ..Default::default() },
    )
    .unwrap();
    assert!(row.program.iter().any(|s| matches!(&s.call, Call::Spawn { actions, flags }
        if actions.contains(&FileAction::Chdir) && flags & darwin::POSIX_SPAWN_SETPGROUP != 0)));
    assert!(
        std_summaries::command_spawn_posix(
            [StdioPlan::Inherit; 3],
            &CommandShape { setsid: true, ..Default::default() }
        )
        .is_err()
    );
    assert!(
        std_summaries::command_spawn_fork(
            [StdioPlan::Inherit; 3],
            &CommandShape { setsid: true, ..Default::default() },
            &[]
        )
        .is_err(),
        "setsid is a child step the model does not run"
    );
}

/// F13: std's Apple `Socket::new` sets SO_NOSIGPIPE; its accept retries EINTR.
#[test]
fn std_socket_rows_set_nosigpipe_and_accept_retries_eintr() {
    for row in [std_summaries::std_unix_listener_bind(), std_summaries::std_unix_stream_connect()] {
        assert!(
            matches!(
                row.program[2].call,
                Call::SocketOp { op: crate::call::SocketOp::Setsockopt, .. }
            ),
            "{}",
            row.id
        );
    }
    assert_eq!(std_summaries::std_accept().retried_eintr, vec![0]);
}

/// F14: render names every field a clause reads; canonical forgets reaped
/// pids.
#[test]
fn render_is_complete_and_canonical_reuses_reaped_pids() {
    let (h, p) = host(256);
    let mut lowered = h.clone();
    lowered = step(
        &lowered,
        p,
        &Call::Setrlimit {
            resource: darwin::RLIMIT_NOFILE,
            soft: 100,
            hard: darwin::RLIM_INFINITY,
        },
        Oracle::Nominal,
    )
    .unwrap()
    .host;
    assert_ne!(h.render(), lowered.render(), "RLIMIT_NOFILE is rendered");
    let threaded = step(&h, p, &Call::ThreadCreate, Oracle::Nominal).unwrap().host;
    assert_ne!(h.render(), threaded.render(), "threads are rendered");
    let (f, Ret::Int(c)) = ok(&h, p, Call::Fork) else { panic!() };
    let (f, _) = ok(&f, Pid(u32::try_from(c).unwrap()), Call::Exit { status: 0 });
    let (f, _) = ok(&f, p, Call::Waitpid { pid: i32::try_from(c).unwrap(), options: 0 });
    assert_eq!(f.canonical(), h.canonical(), "fork + reap leaves no trace in the canonical host");
    let mut gui = Host::new(92160);
    let r = gui.add_root_with_threads(Rlimit { soft: 256, hard: 256 }, 4);
    let (g, Ret::Int(c)) = ok(&gui, r, Call::Fork) else { panic!() };
    assert_eq!(
        g.proc(Pid(u32::try_from(c).unwrap())).unwrap().phase,
        Phase::ForkedPreExec { parent_threads: 4 }
    );
}

// ---- M2: flock, the namespace, identity ---------------------------------------------

use crate::host::{LockMode, NodeKind};

/// The working directory the M2 tests' relative names resolve against.
const CWD: &str = "/private/tmp/m2";

fn named_host() -> (Host, Pid) {
    let (mut h, p) = host(256);
    h.set_cwd(CWD).unwrap();
    h.add_name("/dev/null", NodeKind::CharDevice).unwrap();
    (h, p)
}

/// An open, continued at once if it has not returned (no other thread).
fn open_named(h: &Host, p: Pid, path: &str, flags: i32) -> (Host, i32) {
    let (mut h, mut r) = ok(h, p, Call::OpenPath { at: None, path: path.to_string(), flags });
    while let Ret::Pending { fd } = r {
        (h, r) = ok(&h, p, Call::Resume { fd });
    }
    let Ret::Int(fd) = r else { panic!("{r:?}") };
    (h, i32::try_from(fd).unwrap())
}

fn flk(h: &Host, p: Pid, fd: i32, op: i32) -> Result<(Host, Ret), Errno> {
    let s = step(h, p, &Call::Flock { fd, op }, Oracle::Nominal).unwrap();
    s.host.check_invariants().unwrap();
    s.result.map(|r| (s.host, r))
}

#[test]
fn two_opens_of_one_name_reach_one_node_and_fstat_says_so() {
    let (h, p) = named_host();
    let create = darwin::O_WRONLY | darwin::O_CREAT | darwin::O_TRUNC | darwin::O_CLOEXEC;
    let (h, a) = open_named(&h, p, "m.log", create);
    let (h, b) = open_named(&h, p, "m.log", darwin::O_RDONLY);
    let (_, sa) = ok(&h, p, Call::Fstat { fd: a });
    let (_, sb) = ok(&h, p, Call::Fstat { fd: b });
    assert_eq!(sa, sb);
    assert!(matches!(sa, Ret::Stat { ftype: darwin::S_IFREG, .. }));
    assert_ne!(h.entry(p, a).unwrap().ofd, h.entry(p, b).unwrap().ofd, "two descriptions");
    let (h, n) = open_named(&h, p, "/dev/null", darwin::O_RDONLY);
    let (_, sn) = ok(&h, p, Call::Fstat { fd: n });
    assert_ne!(sn, sa);
    assert_eq!(err(&h, p, Call::Fstat { fd: 77 }), Errno::EBADF);
    // An anonymous open's node is not known: identity is refused by name.
    let (h, anon) = ok(&h, p, Call::Open { flags: darwin::O_RDONLY });
    let Ret::Int(anon) = anon else { panic!() };
    let fd = i32::try_from(anon).unwrap();
    assert!(matches!(
        step(&h, p, &Call::Fstat { fd }, Oracle::Nominal),
        Err(Refusal::Unmodeled { symbol: "fstat", .. })
    ));
}

#[test]
fn flock_conflicts_per_node_and_lives_on_the_description() {
    let (h, p) = named_host();
    let (h, a) = open_named(&h, p, "m.log", darwin::O_RDWR | darwin::O_CREAT);
    let (h, b) = open_named(&h, p, "m.log", darwin::O_RDONLY);
    let (h, _) = flk(&h, p, a, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
    let o = h.entry(p, a).unwrap().ofd;
    assert_eq!(h.ofd(o).unwrap().lock, Some(LockMode::Exclusive));
    assert_eq!(h.ofd(o).unwrap().getfl() & darwin::FHASLOCK, darwin::FHASLOCK);
    // Another description on the node conflicts, even in this process.
    assert_eq!(flk(&h, p, b, darwin::LOCK_SH | darwin::LOCK_NB).unwrap_err(), Errno::EAGAIN);
    let bo = h.entry(p, b).unwrap().ofd;
    let failed = flk(&h, p, b, darwin::LOCK_SH | darwin::LOCK_NB);
    assert!(failed.is_err());
    assert_eq!(h.ofd(bo).unwrap().getfl() & darwin::FHASLOCK, 0, "a refused request sets nothing");
    // A dup is the same description: it holds the lock, it re-locks freely.
    let (h, d) = ok(&h, p, Call::Dup { fd: a });
    let Ret::Int(d) = d else { panic!() };
    let d = i32::try_from(d).unwrap();
    let (h, _) = flk(&h, p, d, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
    // Closing one of the two does not release; LOCK_UN through the other does.
    let (h, _) = ok(&h, p, Call::Close { fd: a });
    assert_eq!(flk(&h, p, b, darwin::LOCK_EX | darwin::LOCK_NB).unwrap_err(), Errno::EAGAIN);
    let (h, _) = flk(&h, p, d, darwin::LOCK_UN).unwrap();
    let (h, _) = flk(&h, p, b, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
    // FHASLOCK stays after LOCK_UN and F_SETFL.
    let (h, _) = ok(&h, p, Call::Fcntl { fd: d, cmd: darwin::F_SETFL, arg: 0 });
    assert_eq!(
        h.ofd(h.entry(p, d).unwrap().ofd).unwrap().getfl() & darwin::FHASLOCK,
        darwin::FHASLOCK
    );
}

#[test]
fn a_fork_child_keeps_the_lock_until_its_last_copy_goes() {
    let (h, p) = named_host();
    let (h, a) = open_named(&h, p, "m.log", darwin::O_RDONLY | darwin::O_CREAT | darwin::O_CLOEXEC);
    let (h, _) = flk(&h, p, a, darwin::LOCK_EX).unwrap();
    let (h, c) = ok(&h, p, Call::Fork);
    let Ret::Int(c) = c else { panic!() };
    let child = Pid(u32::try_from(c).unwrap());
    let (h, _) = ok(&h, p, Call::Close { fd: a });
    let (h, b) = open_named(&h, p, "m.log", darwin::O_RDONLY);
    assert_eq!(flk(&h, p, b, darwin::LOCK_EX | darwin::LOCK_NB).unwrap_err(), Errno::EAGAIN);
    // The child's exec drops its close-on-exec copy: the lock goes with it.
    let (h2, _) = ok(&h, child, Call::Exec);
    flk(&h2, p, b, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
    // So does its exit.
    let (h3, _) = ok(&h, child, Call::Exit { status: 0 });
    flk(&h3, p, b, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
    // And LOCK_UN through the child's copy releases it for every holder.
    let (h4, _) = flk(&h, child, a, darwin::LOCK_UN).unwrap();
    flk(&h4, p, b, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
}

#[test]
fn flock_op_decoding_and_conversions_are_darwins() {
    let (h, p) = named_host();
    let (h, a) = open_named(&h, p, "m.log", darwin::O_RDONLY | darwin::O_CREAT);
    let (h, b) = open_named(&h, p, "m.log", darwin::O_RDONLY);
    for op in [0, darwin::LOCK_NB, 16, 32] {
        assert_eq!(flk(&h, p, a, op).unwrap_err(), Errno::EBADF, "op {op}");
    }
    assert_eq!(flk(&h, p, 77, darwin::LOCK_EX).unwrap_err(), Errno::EBADF);
    // SH|EX is EX; UN|EX is UN; UN on an unlocked description is 0.
    let (h1, _) = flk(&h, p, a, darwin::LOCK_SH | darwin::LOCK_EX).unwrap();
    assert_eq!(flk(&h1, p, b, darwin::LOCK_SH | darwin::LOCK_NB).unwrap_err(), Errno::EAGAIN);
    let (h1, _) = flk(&h1, p, a, darwin::LOCK_UN | darwin::LOCK_EX).unwrap();
    flk(&h1, p, b, darwin::LOCK_SH | darwin::LOCK_NB).unwrap();
    flk(&h, p, a, darwin::LOCK_UN).unwrap();
    // Two shared locks coexist; a failed LOCK_NB upgrade KEEPS the shared lock.
    let (h2, _) = flk(&h, p, a, darwin::LOCK_SH).unwrap();
    let (h2, _) = flk(&h2, p, b, darwin::LOCK_SH).unwrap();
    assert_eq!(flk(&h2, p, a, darwin::LOCK_EX | darwin::LOCK_NB).unwrap_err(), Errno::EAGAIN);
    let ao = h2.entry(p, a).unwrap().ofd;
    assert_eq!(h2.ofd(ao).unwrap().lock, Some(LockMode::Shared));
    // A blocking upgrade that must wait drops SH first on Darwin: refused.
    assert!(matches!(
        step(&h2, p, &Call::Flock { fd: a, op: darwin::LOCK_EX }, Oracle::Nominal),
        Err(Refusal::Unmodeled { symbol: "flock", .. })
    ));
    // A blocking fresh request that must wait SLEEPS: it has not returned,
    // its number is in flight, and its resumption is not enabled until the
    // lock is free (or a signal interrupts it).
    let (h3, _) = flk(&h, p, a, darwin::LOCK_EX).unwrap();
    let (slept, r) = flk(&h3, p, b, darwin::LOCK_SH).unwrap();
    assert_eq!(r, Ret::Pending { fd: b });
    assert_eq!(step(&slept, p, &Call::Resume { fd: b }, Oracle::Nominal), Err(Refusal::Blocks));
    let s = step(&slept, p, &Call::Resume { fd: b }, Oracle::Fail(Errno::EINTR)).unwrap();
    assert_eq!((s.result, s.host.proc(p).unwrap().inflight.len()), (Err(Errno::EINTR), 0));
    // A downgrade is granted at once and lets a shared lock in.
    let (h3, _) = flk(&h3, p, a, darwin::LOCK_SH).unwrap();
    flk(&h3, p, b, darwin::LOCK_SH | darwin::LOCK_NB).unwrap();
    // The sleeper is granted once the lock is free; it holds the description
    // its number named when it started.
    let (freed, _) = flk(&slept, p, a, darwin::LOCK_UN).unwrap();
    let (granted, r) = ok(&freed, p, Call::Resume { fd: b });
    assert_eq!(r, Ret::Int(0));
    let bo = granted.entry(p, b).unwrap().ofd;
    assert_eq!(granted.ofd(bo).unwrap().lock, Some(LockMode::Shared));
    // EINTR is not an outcome of a call that no longer waits.
    assert_eq!(
        step(&freed, p, &Call::Resume { fd: b }, Oracle::Fail(Errno::EINTR)),
        Err(Refusal::Blocks)
    );
}

#[test]
fn close_and_dup2_wait_for_a_sleeping_flock() {
    let (h, p) = named_host();
    let (h, a) = open_named(&h, p, "m.log", darwin::O_RDWR | darwin::O_CREAT);
    let (h, w) = open_named(&h, p, "m.log", darwin::O_RDONLY);
    let (h, z) = open_named(&h, p, "/dev/null", darwin::O_RDONLY);
    let (h, _) = flk(&h, p, a, darwin::LOCK_EX).unwrap();
    let (slept, _) = flk(&h, p, w, darwin::LOCK_EX).unwrap();
    // MEASURED (P7, P18): close(w) and dup2(z, w) wait for the flock.
    assert_eq!(step(&slept, p, &Call::Close { fd: w }, Oracle::Nominal), Err(Refusal::Blocks));
    assert_eq!(
        step(&slept, p, &Call::Dup2 { from: z, to: w }, Oracle::Nominal),
        Err(Refusal::Blocks)
    );
    // Its number is still open (F_GETFD works); a second call on it is refused.
    assert_eq!(ok(&slept, p, Call::Fcntl { fd: w, cmd: darwin::F_GETFD, arg: 0 }).1, Ret::Int(0));
    assert!(matches!(
        step(&slept, p, &Call::Flock { fd: w, op: darwin::LOCK_EX }, Oracle::Nominal),
        Err(Refusal::Unmodeled { symbol: "flock", .. })
    ));
    // The holder lets go: the flock returns 0 holding the lock, then the
    // close goes through and the lock ends with the description.
    let (h, _) = flk(&slept, p, a, darwin::LOCK_UN).unwrap();
    let (h, _) = ok(&h, p, Call::Resume { fd: w });
    let (h, _) = ok(&h, p, Call::Close { fd: w });
    flk(&h, p, a, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
}

#[test]
fn a_pending_open_reserves_its_number_and_a_waiting_fifo_opener_counts() {
    let (h, p) = named_host();
    let (h, _) = ok(&h, p, Call::Mkfifo { path: "fifo".into() });
    let rd = Call::OpenPath { at: None, path: "fifo".into(), flags: darwin::O_RDONLY };
    let (h, r) = ok(&h, p, rd);
    assert_eq!(r, Ret::Pending { fd: 3 }, "the read side waits for a writer");
    // MEASURED (P3): the number is reserved — F_GETFD and close are EBADF,
    // dup skips it, dup2 onto it waits.
    assert_eq!(err(&h, p, Call::Fcntl { fd: 3, cmd: darwin::F_GETFD, arg: 0 }), Errno::EBADF);
    assert_eq!(err(&h, p, Call::Close { fd: 3 }), Errno::EBADF);
    assert_eq!(ok(&h, p, Call::Dup { fd: 0 }).1, Ret::Int(4));
    assert_eq!(step(&h, p, &Call::Dup2 { from: 0, to: 3 }, Oracle::Nominal), Err(Refusal::Blocks));
    assert_eq!(step(&h, p, &Call::Resume { fd: 3 }, Oracle::Nominal), Err(Refusal::Blocks));
    // ...and the waiting reader counts: O_WRONLY|O_NONBLOCK opens (the model
    // said ENXIO before the M2 review), a blocking write open returns at once.
    let (h2, w) =
        open_named(&h, p, "fifo", darwin::O_WRONLY | darwin::O_NONBLOCK | darwin::O_CLOEXEC);
    assert_eq!(w, 4);
    let (h2, r) = ok(&h2, p, Call::Resume { fd: 3 });
    assert_eq!(r, Ret::Int(3));
    let o3 = h2.entry(p, 3).unwrap().ofd;
    assert_eq!(h2.ofd(o3).unwrap().access, Access::ReadOnly);
    let (h3, w) = open_named(&h, p, "fifo", darwin::O_WRONLY);
    assert_eq!(w, 4);
    ok(&h3, p, Call::Resume { fd: 3 });
    // Interrupted, the reservation goes and the count drops: ENXIO again.
    let s = step(&h, p, &Call::Resume { fd: 3 }, Oracle::Fail(Errno::EINTR)).unwrap();
    assert_eq!(s.result, Err(Errno::EINTR));
    let back = step(
        &s.host,
        p,
        &Call::OpenPath {
            at: None,
            path: "fifo".into(),
            flags: darwin::O_WRONLY | darwin::O_NONBLOCK,
        },
        Oracle::Nominal,
    )
    .unwrap();
    assert_eq!(back.result, Err(Errno::ENXIO));
    // Its exit (or exec) abandons a pending open.
    let (h4, c) = ok(&h, p, Call::Fork);
    let Ret::Int(c) = c else { panic!() };
    let child = Pid(u32::try_from(c).unwrap());
    let (h4, r) =
        ok(&h4, child, Call::OpenPath { at: None, path: "fifo".into(), flags: darwin::O_WRONLY });
    // The parent's waiting reader is a reader: the child's write open returns
    // at once, at its OWN lowest free number (a fork copies no reservation).
    assert_eq!(r, Ret::Int(3), "the parent's waiting reader is a reader");
    assert!(h4.proc(child).unwrap().inflight.is_empty(), "a fork copies no call in flight");
    let (h4, _) = ok(&h4, p, Call::Exit { status: 0 });
    assert!(h4.proc(p).unwrap().inflight.is_empty());
}

#[test]
fn an_o_creat_lock_open_creates_the_file_before_it_locks() {
    let (h, p) = named_host();
    let flags = darwin::O_RDWR
        | darwin::O_CREAT
        | darwin::O_EXCL
        | darwin::O_EXLOCK
        | darwin::O_NONBLOCK
        | darwin::O_CLOEXEC;
    let (h, r) = ok(&h, p, Call::OpenPath { at: None, path: "new.lock".into(), flags });
    assert_eq!(r, Ret::Pending { fd: 3 }, "created, not yet locked");
    // A racer opens the new file and takes the lock first (MEASURED, P20).
    let (h, b) = open_named(&h, p, "new.lock", darwin::O_RDONLY);
    let (h, _) = flk(&h, p, b, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
    let s = step(&h, p, &Call::Resume { fd: 3 }, Oracle::Nominal).unwrap();
    assert_eq!(s.result, Err(Errno::EAGAIN));
    assert!(s.host.name(&format!("{CWD}/new.lock")).is_some(), "the file stays created");
    assert!(s.host.proc(p).unwrap().inflight.is_empty() && s.host.entry(p, 3).is_none());
    // A retry with O_EXCL is EEXIST.
    let again = step(
        &s.host,
        p,
        &Call::OpenPath { at: None, path: "new.lock".into(), flags },
        Oracle::Nominal,
    );
    assert_eq!(again.unwrap().result, Err(Errno::EEXIST));
}

#[test]
fn posix_spawn_is_two_steps_and_the_child_holds_every_copy_between() {
    let (h, p) = named_host();
    let (h, a) = open_named(&h, p, "m.log", darwin::O_RDONLY | darwin::O_CREAT | darwin::O_CLOEXEC);
    let (h, _) = flk(&h, p, a, darwin::LOCK_EX).unwrap();
    let (h, c) = ok(&h, p, Call::SpawnBegin);
    let Ret::Int(c) = c else { panic!() };
    let child = Pid(u32::try_from(c).unwrap());
    assert!(matches!(h.proc(child).unwrap().phase, Phase::Spawning { .. }));
    assert!(h.entry(child, a).is_some_and(|e| e.cloexec), "close-on-exec entries are copied");
    // The parent's last close does not release the lock while the child
    // holds its copy (MEASURED, p4/p4b).
    let (h, _) = ok(&h, p, Call::Close { fd: a });
    let (h, b) = open_named(&h, p, "m.log", darwin::O_RDONLY);
    assert_eq!(flk(&h, p, b, darwin::LOCK_EX | darwin::LOCK_NB).unwrap_err(), Errno::EAGAIN);
    // SpawnEnd: the sweep drops the copy, the lock ends.
    let end = Call::SpawnEnd { child: c as i32, actions: Vec::new(), flags: 0 };
    let (done, r) = ok(&h, p, end.clone());
    assert_eq!(r, Ret::Int(c));
    assert_eq!(done.proc(child).unwrap().phase, Phase::Execd);
    flk(&done, p, b, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
    // A failed spawn tears the child down: its copies go, the lock ends.
    let s = step(&h, p, &end, Oracle::Fail(Errno::ENOENT)).unwrap();
    assert_eq!(s.result, Err(Errno::ENOENT));
    assert!(s.host.proc(child).is_none());
    s.host.check_invariants().unwrap();
    flk(&s.host, p, b, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
    // fork1's failure makes no process.
    let s = step(&h, p, &Call::SpawnBegin, Oracle::Fail(Errno::EAGAIN)).unwrap();
    assert_eq!((s.result, s.host.procs().count()), (Err(Errno::EAGAIN), h.procs().count()));
    // Only the caller ends its own spawn in progress.
    assert!(matches!(
        step(&h, b_pid(&h, p), &end, Oracle::Nominal),
        Err(Refusal::Unmodeled { .. } | Refusal::NotLive(_))
    ));
}

/// Some live process other than `p` (for the "not your spawn" check).
fn b_pid(h: &Host, p: Pid) -> Pid {
    h.procs().map(|(q, _)| q).find(|q| *q != p).unwrap()
}

#[test]
fn the_atomic_spawn_is_its_two_halves() {
    let (h, p) = named_host();
    let (h, a) = open_named(&h, p, "m.log", darwin::O_RDONLY | darwin::O_CREAT | darwin::O_CLOEXEC);
    let (h, _) = ok(&h, p, Call::Fcntl { fd: a, cmd: darwin::F_DUPFD, arg: 10 });
    for (actions, flags) in [
        (Vec::new(), 0),
        (vec![FileAction::Dup2 { from: a, to: 7 }], darwin::POSIX_SPAWN_CLOEXEC_DEFAULT),
        (vec![FileAction::Close { fd: 10 }, FileAction::Inherit { fd: a }], 0),
        (vec![FileAction::Close { fd: 9 }], 0),
    ] {
        for oracle in [Oracle::Nominal, Oracle::Fail(Errno::ENOENT)] {
            let atomic =
                step(&h, p, &Call::Spawn { actions: actions.clone(), flags }, oracle).unwrap();
            let begun = step(&h, p, &Call::SpawnBegin, Oracle::Nominal).unwrap();
            let Ok(Ret::Int(c)) = begun.result else { panic!() };
            let split = step(
                &begun.host,
                p,
                &Call::SpawnEnd { child: c as i32, actions: actions.clone(), flags },
                oracle,
            )
            .unwrap();
            assert_eq!(atomic.result, split.result, "{actions:?} {oracle:?}");
            assert_eq!(atomic.host.canonical().render(), split.host.canonical().render());
        }
    }
}

#[test]
fn the_namespace_has_one_spelling_per_file() {
    let (h, p) = named_host();
    let (h, _) = open_named(&h, p, "Lease.lock", darwin::O_RDWR | darwin::O_CREAT);
    let refused = |h: &Host, path: &str| {
        matches!(
            step(
                h,
                p,
                &Call::OpenPath {
                    at: None,
                    path: path.into(),
                    flags: darwin::O_RDONLY | darwin::O_CREAT
                },
                Oracle::Nominal
            ),
            Err(Refusal::Unmodeled { .. })
        )
    };
    // MEASURED (P10): each of these reaches the one file on Darwin.
    for alias in [
        "lease.LOCK",
        "./Lease.lock",
        "sub/../Lease.lock",
        "/private/tmp//m2/Lease.lock",
        "/tmp/m2/Lease.lock",
        "/private/tmp/m2/Lease.lock/",
        "/System/Volumes/Data/private/tmp/m2/Lease.lock",
    ] {
        assert!(refused(&h, alias), "{alias}");
    }
    // The canonical absolute spelling IS the relative one.
    let (h, x) = open_named(&h, p, "/private/tmp/m2/Lease.lock", darwin::O_RDONLY);
    let (h, y) = open_named(&h, p, "Lease.lock", darwin::O_RDONLY);
    assert_eq!(ok(&h, p, Call::Fstat { fd: x }).1, ok(&h, p, Call::Fstat { fd: y }).1);
    // Without a working directory a relative path is refused.
    let (bare, q) = host(256);
    assert!(matches!(
        step(&bare, q, &Call::OpenPath { at: None, path: "x".into(), flags: 0 }, Oracle::Nominal),
        Err(Refusal::Unmodeled { .. })
    ));
    assert!(bare.clone().add_name("rel", NodeKind::Regular).is_err());
    // A relative symlink target names a file in the LINK's directory
    // (MEASURED: sub/rl -> Lease.lock is sub/Lease.lock, absent: ENOENT).
    let (h, _) = ok(&h, p, Call::Symlink { target: "Lease.lock".into(), path: "sub/rl".into() });
    let s =
        step(&h, p, &Call::OpenPath { at: None, path: "sub/rl".into(), flags: 0 }, Oracle::Nominal);
    assert_eq!(s.unwrap().result, Err(Errno::ENOENT));
    // A path through a symlink (not its last component) is refused.
    let (h, _) = ok(&h, p, Call::Symlink { target: "/private/tmp".into(), path: "dirlink".into() });
    assert!(refused(&h, "dirlink/m2/Lease.lock"));
    // Cloning devices and per-process aliases are refused by name (P10b, p8).
    assert!(refused(&h, "/dev/ptmx") && refused(&h, "/dev/tty"));
    assert!(matches!(symbols::classify_open_path("/dev/ptmx"), symbols::OpenPath::Refused(_)));
}

#[test]
fn flock_is_enotsup_on_what_is_not_a_lockable_vnode() {
    let (h, p) = named_host();
    let (h, _) = ok(&h, p, Call::Pipe);
    assert_eq!(flk(&h, p, 3, 0).unwrap_err(), Errno::ENOTSUP, "before the op is decoded");
    assert_eq!(flk(&h, p, 4, darwin::LOCK_UN).unwrap_err(), Errno::ENOTSUP);
    let (h, _) = ok(&h, p, Call::Kqueue);
    assert_eq!(flk(&h, p, 5, darwin::LOCK_EX | darwin::LOCK_NB).unwrap_err(), Errno::ENOTSUP);
    let (h, _) = ok(&h, p, Call::Mkfifo { path: "fifo".into() });
    let (h, f) = open_named(&h, p, "fifo", darwin::O_RDWR);
    assert_eq!(flk(&h, p, f, darwin::LOCK_EX | darwin::LOCK_NB).unwrap_err(), Errno::ENOTSUP);
    // A FIFO is a vnode: its op is decoded FIRST (MEASURED, the M2 model
    // review's P1), then every request is ENOTSUP.
    for op in [0, darwin::LOCK_NB, 16] {
        assert_eq!(flk(&h, p, f, op).unwrap_err(), Errno::EBADF, "op {op}");
    }
    assert_eq!(flk(&h, p, f, darwin::LOCK_UN).unwrap_err(), Errno::ENOTSUP);
    assert_eq!(flk(&h, p, f, darwin::LOCK_SH).unwrap_err(), Errno::ENOTSUP);
    // /dev/null is one node: two opens of it conflict.
    let (h, n1) = open_named(&h, p, "/dev/null", darwin::O_RDWR);
    let (h, n2) = open_named(&h, p, "/dev/null", darwin::O_RDONLY);
    let (h, _) = flk(&h, p, n1, darwin::LOCK_EX | darwin::LOCK_NB).unwrap();
    assert_eq!(flk(&h, p, n2, darwin::LOCK_EX | darwin::LOCK_NB).unwrap_err(), Errno::EAGAIN);
    // stdio here is an anonymous /dev/null: refused, the model cannot tell.
    assert!(matches!(
        step(&h, p, &Call::Flock { fd: 0, op: darwin::LOCK_EX }, Oracle::Nominal),
        Err(Refusal::Unmodeled { symbol: "flock", .. })
    ));
}

#[test]
fn open_lock_bits_take_the_lock_as_part_of_the_open() {
    let (h, p) = named_host();
    // Creating and locking: two steps (the lock comes after the creation).
    let (h, r) = ok(
        &h,
        p,
        Call::OpenPath {
            at: None,
            path: "m.log".into(),
            flags: darwin::O_RDONLY | darwin::O_CREAT | darwin::O_EXLOCK,
        },
    );
    assert_eq!(r, Ret::Pending { fd: 3 });
    let (h, r) = ok(&h, p, Call::Resume { fd: 3 });
    assert_eq!(r, Ret::Int(3));
    let a = 3;
    let ao = h.entry(p, a).unwrap().ofd;
    assert_eq!(h.ofd(ao).unwrap().lock, Some(LockMode::Exclusive));
    assert_eq!(h.ofd(ao).unwrap().getfl(), darwin::FHASLOCK);
    let nb = darwin::O_RDONLY | darwin::O_NONBLOCK;
    let before = h.clone();
    let s = step(
        &h,
        p,
        &Call::OpenPath { at: None, path: "m.log".into(), flags: nb | darwin::O_SHLOCK },
        Oracle::Nominal,
    )
    .unwrap();
    assert_eq!((s.result, &s.host), (Err(Errno::EAGAIN), &before), "no descriptor is allocated");
    // A blocking lock open that must wait reserves its number and waits.
    let waits = step(
        &h,
        p,
        &Call::OpenPath {
            at: None,
            path: "m.log".into(),
            flags: darwin::O_RDONLY | darwin::O_EXLOCK,
        },
        Oracle::Nominal,
    )
    .unwrap();
    assert_eq!(waits.result, Ok(Ret::Pending { fd: 4 }));
    assert_eq!(
        step(&waits.host, p, &Call::Resume { fd: 4 }, Oracle::Nominal),
        Err(Refusal::Blocks)
    );
    assert_eq!(ok(&waits.host, p, Call::Dup { fd: 0 }).1, Ret::Int(5), "4 is reserved (P14)");
    let (h, _) = flk(&h, p, a, darwin::LOCK_UN).unwrap();
    let (h, s1) = open_named(&h, p, "m.log", nb | darwin::O_SHLOCK);
    let (h, _) = open_named(&h, p, "m.log", nb | darwin::O_SHLOCK);
    assert_eq!(
        h.ofd(h.entry(p, s1).unwrap().ofd).unwrap().getfl(),
        darwin::O_NONBLOCK | darwin::FHASLOCK
    );
    // Both bits: exclusive.
    let s = step(
        &h,
        p,
        &Call::OpenPath {
            at: None,
            path: "m.log".into(),
            flags: nb | darwin::O_SHLOCK | darwin::O_EXLOCK,
        },
        Oracle::Nominal,
    )
    .unwrap();
    assert_eq!(s.result, Err(Errno::EAGAIN));
    // FIFOs: ENXIO first, then ENOTSUP.
    let (h, _) = ok(&h, p, Call::Mkfifo { path: "fifo".into() });
    let fifo = |flags| {
        step(&h, p, &Call::OpenPath { at: None, path: "fifo".into(), flags }, Oracle::Nominal)
            .unwrap()
            .result
    };
    assert_eq!(fifo(darwin::O_WRONLY | darwin::O_NONBLOCK | darwin::O_EXLOCK), Err(Errno::ENXIO));
    assert_eq!(fifo(darwin::O_RDONLY | darwin::O_NONBLOCK | darwin::O_EXLOCK), Err(Errno::ENOTSUP));
    // An anonymous open still refuses the lock bits.
    assert!(matches!(
        step(&h, p, &Call::Open { flags: darwin::O_RDONLY | darwin::O_EXLOCK }, Oracle::Nominal),
        Err(Refusal::Unmodeled { .. })
    ));
}

#[test]
fn the_namespace_is_darwins_for_fifos_symlinks_and_unlink() {
    let (h, p) = named_host();
    let open = |h: &Host, path: &str, flags| {
        step(h, p, &Call::OpenPath { at: None, path: path.into(), flags }, Oracle::Nominal)
    };
    assert_eq!(open(&h, "missing", darwin::O_RDONLY).unwrap().result, Err(Errno::ENOENT));
    let (h, _) = ok(&h, p, Call::Mkfifo { path: "fifo".into() });
    assert_eq!(
        step(&h, p, &Call::Mkfifo { path: "fifo".into() }, Oracle::Nominal).unwrap().result,
        Err(Errno::EEXIST)
    );
    // A FIFO: the read side waits for a writer, O_NONBLOCK opens it at once;
    // the write side without a reader is ENXIO under O_NONBLOCK.
    assert_eq!(open(&h, "fifo", darwin::O_RDONLY).unwrap().result, Ok(Ret::Pending { fd: 3 }));
    assert_eq!(
        open(&h, "fifo", darwin::O_WRONLY | darwin::O_NONBLOCK).unwrap().result,
        Err(Errno::ENXIO)
    );
    let (h, held) = open_named(&h, p, "fifo", darwin::O_RDWR | darwin::O_CLOEXEC);
    let (h, far) = open_named(&h, p, "fifo", darwin::O_RDONLY | darwin::O_CLOEXEC);
    let (_, s1) = ok(&h, p, Call::Fstat { fd: held });
    let (_, s2) = ok(&h, p, Call::Fstat { fd: far });
    assert_eq!(s1, s2, "both ends of a named FIFO are one node");
    assert!(matches!(s1, Ret::Stat { ftype: darwin::S_IFIFO, .. }));
    // Unlink: the name goes, the node lives on while open.
    let (h, _) = ok(&h, p, Call::Unlink { path: "fifo".into() });
    assert_eq!(
        step(&h, p, &Call::Unlink { path: "fifo".into() }, Oracle::Nominal).unwrap().result,
        Err(Errno::ENOENT)
    );
    assert_eq!(open(&h, "fifo", darwin::O_RDWR).unwrap().result, Err(Errno::ENOENT));
    let (h, s3) = ok(&h, p, Call::Fstat { fd: far });
    assert_eq!(s3, s1);
    let (h, _) = ok(&h, p, Call::Close { fd: held });
    let (h, _) = ok(&h, p, Call::Close { fd: far });
    assert_eq!(h.nodes().count(), 1, "only /dev/null is left");
    // Symlinks: followed; O_NOFOLLOW is ELOOP; O_CREAT|O_EXCL on one is EEXIST;
    // O_CREAT through a dangling one creates the target.
    let (h, _) = ok(&h, p, Call::Symlink { target: "m.log".into(), path: "lnk".into() });
    assert_eq!(open(&h, "lnk", darwin::O_RDONLY).unwrap().result, Err(Errno::ENOENT));
    assert_eq!(
        open(&h, "lnk", darwin::O_RDONLY | darwin::O_NOFOLLOW).unwrap().result,
        Err(Errno::ELOOP)
    );
    assert_eq!(
        open(&h, "lnk", darwin::O_RDONLY | darwin::O_CREAT | darwin::O_EXCL).unwrap().result,
        Err(Errno::EEXIST)
    );
    let (h, l) = open_named(&h, p, "lnk", darwin::O_RDONLY | darwin::O_CREAT);
    let (h, m) = open_named(&h, p, "m.log", darwin::O_RDONLY);
    assert_eq!(ok(&h, p, Call::Fstat { fd: l }).1, ok(&h, p, Call::Fstat { fd: m }).1);
    assert_eq!(
        step(&h, p, &Call::Symlink { target: "x".into(), path: "lnk".into() }, Oracle::Nominal)
            .unwrap()
            .result,
        Err(Errno::EEXIST)
    );
}

#[test]
fn openat_reads_its_dirfd_only_for_a_relative_path() {
    let (h, p) = named_host();
    let at = |h: &Host, d: i32, path: &str| {
        step(
            h,
            p,
            &Call::OpenPath { at: Some(d), path: path.into(), flags: darwin::O_RDONLY },
            Oracle::Nominal,
        )
    };
    assert!(
        at(&h, 777, "/dev/null").unwrap().result.is_ok(),
        "an absolute path ignores a closed dirfd"
    );
    assert_eq!(at(&h, 777, "rel").unwrap().result, Err(Errno::EBADF));
    assert!(at(&h, darwin::AT_FDCWD, "/dev/null").unwrap().result.is_ok());
    let (h, f) = open_named(&h, p, "m.log", darwin::O_RDONLY | darwin::O_CREAT);
    assert_eq!(at(&h, f, "rel").unwrap().result, Err(Errno::ENOTDIR));
    let (h, _) = ok(&h, p, Call::Pipe);
    assert_eq!(at(&h, 4, "rel").unwrap().result, Err(Errno::ENOTSUP));
    // Allocation first: a full table is EMFILE whatever the dirfd.
    let (full, _) = ok(
        &h,
        p,
        Call::Setrlimit { resource: darwin::RLIMIT_NOFILE, soft: 6, hard: darwin::RLIM_INFINITY },
    );
    assert_eq!(at(&full, 777, "rel").unwrap().result, Err(Errno::EMFILE));
    assert_eq!(
        step(
            &full,
            p,
            &Call::OpenPath { at: None, path: "missing".into(), flags: 0 },
            Oracle::Nominal
        )
        .unwrap()
        .result,
        Err(Errno::EMFILE)
    );
}

#[test]
fn directories_open_read_only_and_refuse_writes() {
    let (mut h, p) = named_host();
    h.add_name("dir", NodeKind::Directory).unwrap();
    let open = |flags| {
        step(&h, p, &Call::OpenPath { at: None, path: "dir".into(), flags }, Oracle::Nominal)
            .unwrap()
            .result
    };
    assert!(open(darwin::O_RDONLY | darwin::O_CREAT).is_ok());
    assert_eq!(open(darwin::O_WRONLY), Err(Errno::EISDIR));
    assert_eq!(open(darwin::O_RDONLY | darwin::O_TRUNC), Err(Errno::EISDIR));
    assert_eq!(open(darwin::O_RDONLY | darwin::O_CREAT | darwin::O_EXCL), Err(Errno::EEXIST));
    assert_eq!(
        step(&h, p, &Call::Unlink { path: "dir".into() }, Oracle::Nominal).unwrap().result,
        Err(Errno::EPERM)
    );
    assert_eq!(
        step(
            &h,
            p,
            &Call::OpenPath {
                at: None,
                path: "/dev/null".into(),
                flags: darwin::O_RDONLY | darwin::O_DIRECTORY
            },
            Oracle::Nominal
        )
        .unwrap()
        .result,
        Err(Errno::ENOTDIR)
    );
}

#[test]
fn m2_symbols_join_their_clauses() {
    for (name, clause) in [
        ("flock", ClauseId::Flock),
        ("openat", ClauseId::Openat),
        ("fstat", ClauseId::Fstat),
        ("mkfifo", ClauseId::Mkfifo),
        ("unlink", ClauseId::Unlink),
        ("symlink", ClauseId::Symlink),
    ] {
        assert_eq!(symbols::lookup(name).unwrap().modeled, Modeled::Clause(clause), "{name}");
    }
    assert_eq!(
        symbols::lookup_macho("_fstat$INODE64").unwrap().modeled,
        Modeled::Clause(ClauseId::Fstat)
    );
    assert!(symbols::lookup("lockf").is_err() && symbols::lookup("stat").is_err());
    let row =
        std_summaries::std_open_path("m.log", darwin::O_WRONLY | darwin::O_CREAT | darwin::O_TRUNC);
    assert_eq!(row.id, "STD-OPEN");
    let (h, p) = named_host();
    let t = script::run(&Darwin, &h, p, &row.program, &[]).unwrap();
    assert_eq!(t[0].result, Ok(Ret::Int(3)));
    assert!(t[0].host.entry(p, 3).unwrap().cloexec);
}

#[test]
fn invariants_hold_over_all_m2_three_step_sequences() {
    let (h, p) = named_host();
    let (h, a) = open_named(&h, p, "m.log", darwin::O_RDONLY | darwin::O_CREAT | darwin::O_CLOEXEC);
    let (h, _) = flk(&h, p, a, darwin::LOCK_SH).unwrap();
    let (h, _) = ok(&h, p, Call::Mkfifo { path: "fifo".into() });
    let path = |s: &str| s.to_string();
    let menu: Vec<Call> = vec![
        Call::OpenPath { at: None, path: path("m.log"), flags: darwin::O_RDONLY },
        Call::OpenPath {
            at: None,
            path: path("m.log"),
            flags: darwin::O_RDONLY | darwin::O_EXLOCK | darwin::O_NONBLOCK,
        },
        Call::OpenPath { at: None, path: path("fifo"), flags: darwin::O_RDWR },
        Call::OpenPath { at: None, path: path("new"), flags: darwin::O_WRONLY | darwin::O_CREAT },
        Call::Flock { fd: 3, op: darwin::LOCK_EX | darwin::LOCK_NB },
        Call::Flock { fd: 4, op: darwin::LOCK_EX | darwin::LOCK_NB },
        Call::Flock { fd: 4, op: darwin::LOCK_SH | darwin::LOCK_NB },
        Call::Flock { fd: 3, op: darwin::LOCK_UN },
        Call::Dup { fd: 3 },
        Call::Dup2 { from: 4, to: 3 },
        Call::Close { fd: 3 },
        Call::Close { fd: 4 },
        Call::Unlink { path: path("m.log") },
        Call::Unlink { path: path("fifo") },
        Call::Symlink { target: path("m.log"), path: path("lnk") },
        Call::Fork,
        Call::Exec,
        Call::Exit { status: 0 },
    ];
    let mut checked = 0;
    let mut frontier = vec![h];
    for _ in 0..3 {
        let mut next = Vec::new();
        for host in &frontier {
            for c in &menu {
                for pid in host.procs().map(|(pid, _)| pid).collect::<Vec<_>>() {
                    if let Ok(s) = step(host, pid, c, Oracle::Nominal) {
                        s.host.check_invariants().unwrap_or_else(|e| panic!("{pid:?} {c:?}: {e}"));
                        checked += 1;
                        if next.len() < 4000 {
                            next.push(s.host);
                        }
                    }
                }
            }
        }
        frontier = next;
    }
    assert!(checked > 2000, "{checked}");
}

/// PLATFORM-KQUEUE-ALIAS-1: Darwin 27.2 sets FD_CLOFORK on the descriptor
/// `kqueue()` returns and 25.6 has no such bit, so its F_GETFD is refused by
/// name; a dup, F_DUPFD_CLOEXEC and an F_SETFD answer as they do on both.
#[test]
fn kqueue_getfd_is_refused_until_its_flags_are_set() {
    let (h, p) = host(256);
    let (h, Ret::Int(kq)) = ok(&h, p, Call::Kqueue) else { panic!() };
    let kq = i32::try_from(kq).unwrap();
    let getfd = |fd| Call::Fcntl { fd, cmd: darwin::F_GETFD, arg: 0 };
    assert_eq!(
        step(&h, p, &getfd(kq), Oracle::Nominal).unwrap_err(),
        Refusal::Unmodeled { symbol: "fcntl", detail: crate::clauses::KQUEUE_GETFD.to_string() },
    );
    let (h, Ret::Int(d)) = ok(&h, p, Call::Dup { fd: kq }) else { panic!() };
    assert_eq!(ok(&h, p, getfd(i32::try_from(d).unwrap())).1, Ret::Int(0));
    let dupfd_cloexec = Call::Fcntl { fd: kq, cmd: darwin::F_DUPFD_CLOEXEC, arg: 0 };
    let (h, Ret::Int(dc)) = ok(&h, p, dupfd_cloexec) else { panic!() };
    assert_eq!(ok(&h, p, getfd(i32::try_from(dc).unwrap())).1, Ret::Int(1));
    let (h, _) = ok(&h, p, Call::Fcntl { fd: kq, cmd: darwin::F_SETFD, arg: 1 });
    assert_eq!(ok(&h, p, getfd(kq)).1, Ret::Int(1));
    let (h, _) = ok(&h, p, Call::Fcntl { fd: kq, cmd: darwin::F_SETFD, arg: 0 });
    assert_eq!(ok(&h, p, getfd(kq)).1, Ret::Int(0));
}

/// EW-9: trust-platform has no build script. Its old probe emitted a cfg no
/// code read, and its OUT_DIR put the build tree's absolute path into an
/// artifact, which makes a seeded stage 1 rebuild this crate and everything
/// above it. Cargo runs `build.rs` at the package root unless the manifest
/// says `build = false`, and runs whatever a `build = "…"` key names.
#[test]
fn no_build_script() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    assert!(!root.join("build.rs").exists(), "crates/trust-platform/build.rs is back");
    let manifest = std::fs::read_to_string(root.join("Cargo.toml")).unwrap();
    let names_one = |line: &str| {
        let line = line.trim();
        line.strip_prefix("build")
            .and_then(|rest| rest.trim_start().strip_prefix('='))
            .is_some_and(|value| value.trim() != "false")
    };
    assert!(
        !manifest.lines().any(names_one),
        "crates/trust-platform/Cargo.toml names a build script"
    );
}
