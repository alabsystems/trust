//! Model-level unit tests of the X3a rows (design §2.6, census PR 13): the
//! listing and sysctl clauses, the symbol table's new names and gaps, the
//! fixed rows, the `Command` rows, and the fidelity catalog. What Darwin
//! does is `tests/conformance_darwin.rs`'s to say; these pin the algebra.

use crate::call::{Call, Oracle, Refusal, Ret, Semantics, SysResult};
use crate::clauses::{Darwin, step};
use crate::darwin::{self, Errno};
use crate::host::{Access, Host, OfdKind, Phase, Pid, Rlimit};
use crate::introspect::{self, ListedFd};
use crate::script::{self, Actor, Guard, Operand, Program, ProgramStep, When};
use crate::std_summaries::{
    self, CommandOp, CommandShape, CommandStd, SpawnPath, StdioPlan, command_row,
    command_spawn_fork, command_spawn_posix, fidelity,
};
use crate::symbols::{self, ClauseId, Modeled};

fn host() -> (Host, Pid) {
    let mut h = Host::new(92160);
    let root = h.add_root(Rlimit { soft: 256, hard: darwin::RLIM_INFINITY });
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

fn fds(l: &[ListedFd]) -> Vec<i32> {
    l.iter().map(|e| e.fd).collect()
}

/// pipe (3, 4), kqueue (5), F_DUPFD 50, socket (6), cloexec /dev/null (7).
fn busy() -> (Host, Pid) {
    let (h, p) = host();
    let (h, _) = ok(&h, p, Call::Pipe);
    let (h, _) = ok(&h, p, Call::Kqueue);
    let (h, _) = ok(&h, p, Call::Fcntl { fd: 3, cmd: darwin::F_DUPFD, arg: 50 });
    let (h, _) =
        ok(&h, p, Call::Socket { domain: darwin::AF_UNIX, ty: darwin::SOCK_STREAM, protocol: 0 });
    let (h, _) = ok(&h, p, Call::Open { flags: darwin::O_RDONLY | darwin::O_CLOEXEC });
    (h, p)
}

#[test]
fn listing_is_ascending_lowest_first_and_typed() {
    let (h, p) = busy();
    let all = introspect::listing(&h, p, 512).unwrap().unwrap();
    assert_eq!(fds(&all), vec![0, 1, 2, 3, 4, 5, 6, 7, 50]);
    let types: Vec<Option<u32>> = all.iter().map(|e| e.fdtype).collect();
    let (v, pp, kq, so) = (
        Some(introspect::PROX_FDTYPE_VNODE),
        Some(introspect::PROX_FDTYPE_PIPE),
        Some(introspect::PROX_FDTYPE_KQUEUE),
        Some(introspect::PROX_FDTYPE_SOCKET),
    );
    assert_eq!(types, vec![v, v, v, pp, pp, kq, so, v, pp]);
    assert_eq!(fds(&introspect::listing(&h, p, 16).unwrap().unwrap()), vec![0, 1]);
    // Rounded down to whole entries.
    assert_eq!(fds(&introspect::listing(&h, p, 23).unwrap().unwrap()), vec![0, 1]);
    for short in [0, 7] {
        assert_eq!(introspect::listing(&h, p, short).unwrap(), Err(Errno::ENOMEM));
    }
    // The step: the byte count, and nothing changes.
    let s = step(&h, p, &Call::ListOwnFds { bytes: 512 }, Oracle::Nominal).unwrap();
    assert_eq!(s.result, Ok(Ret::Int(72)));
    assert_eq!(s.host, h);
    let s = step(&h, p, &Call::ListOwnFds { bytes: 7 }, Oracle::Nominal).unwrap();
    assert_eq!(s.result, Err(Errno::ENOMEM));
    // The trait's default is the module's.
    assert_eq!(Darwin.listing(&h, p, 40), introspect::listing(&h, p, 40));
}

#[test]
fn listing_ignores_rlimit_and_cloexec_and_follows_the_fork_copy() {
    let (h, p) = busy();
    let (h, _) = ok(
        &h,
        p,
        Call::Setrlimit { resource: darwin::RLIMIT_NOFILE, soft: 20, hard: darwin::RLIM_INFINITY },
    );
    assert!(fds(&introspect::listing(&h, p, 512).unwrap().unwrap()).contains(&50));
    let (h, child) = ok(&h, p, Call::Fork);
    let Ret::Int(c) = child else { panic!() };
    let c = Pid(u32::try_from(c).unwrap());
    // The child lists its own table: the kqueue (5) was not copied.
    assert_eq!(
        fds(&introspect::listing(&h, c, 512).unwrap().unwrap()),
        vec![0, 1, 2, 3, 4, 6, 7, 50]
    );
}

#[test]
fn listing_refuses_a_negative_size_a_multithreaded_caller_and_an_unknown_process() {
    let (h, p) = busy();
    assert!(matches!(
        introspect::listing(&h, p, -8),
        Err(Refusal::Unmodeled { symbol: "proc_pidinfo", ref detail }) if detail.contains("4294967288")
    ));
    let (h2, _) = ok(&h, p, Call::ThreadCreate);
    assert!(matches!(
        step(&h2, p, &Call::ListOwnFds { bytes: 512 }, Oracle::Nominal),
        Err(Refusal::Unmodeled { symbol: "proc_pidinfo", ref detail }) if detail.contains("2 threads")
    ));
    assert_eq!(introspect::listing(&h, Pid(99), 512), Err(Refusal::NoSuchProcess(Pid(99))));
    // No environment failure is admissible: the listing is the host's.
    assert!(matches!(
        step(&h, p, &Call::ListOwnFds { bytes: 512 }, Oracle::Fail(Errno::ENOMEM)),
        Err(Refusal::InadmissibleOracle { .. })
    ));
    // An environment-provided description of unknown kind lists untyped.
    let mut h3 = h.clone();
    h3.install_fresh(p, 60, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    let l = introspect::listing(&h3, p, 512).unwrap().unwrap();
    assert_eq!(l.last(), Some(&ListedFd { fd: 60, fdtype: None }));
}

#[test]
fn sysctl_answers_maxfilesperproc_only() {
    let (h, p) = host();
    let get = |oldlen| Call::Sysctl { name: "kern.maxfilesperproc".to_string(), oldlen };
    for oldlen in [4, 8] {
        let s = step(&h, p, &get(oldlen), Oracle::Nominal).unwrap();
        assert_eq!(s.result, Ok(Ret::Int(92160)));
        assert_eq!(s.host, h);
    }
    for oldlen in [0, 2, 3] {
        assert_eq!(step(&h, p, &get(oldlen), Oracle::Nominal).unwrap().result, Err(Errno::ENOMEM));
    }
    let other = Call::Sysctl { name: "kern.maxfiles".to_string(), oldlen: 4 };
    assert!(matches!(
        step(&h, p, &other, Oracle::Nominal),
        Err(Refusal::Unmodeled { symbol: "sysctlbyname", ref detail }) if detail.contains("system-wide")
    ));
    let unknown = Call::Sysctl { name: "hw.ncpu".to_string(), oldlen: 4 };
    assert!(matches!(
        step(&h, p, &unknown, Oracle::Nominal),
        Err(Refusal::Unmodeled { symbol: "sysctlbyname", ref detail }) if detail.starts_with("hw.ncpu")
    ));
    // A host whose limit does not fit an int is refused, never wrapped.
    let mut big = Host::new(1 << 40);
    let q = big.add_root(Rlimit { soft: 256, hard: 256 });
    assert!(step(&big, q, &get(4), Oracle::Nominal).is_err());
}

#[test]
fn x3a_symbols_resolve_and_gaps_are_named() {
    for (name, clause) in
        [("proc_pidinfo", ClauseId::ListOwnFds), ("sysctlbyname", ClauseId::Sysctl)]
    {
        assert_eq!(symbols::lookup(name).unwrap().modeled, Modeled::Clause(clause));
        let macho = format!("_{name}");
        assert_eq!(symbols::lookup_macho(&macho).unwrap().modeled, Modeled::Clause(clause));
    }
    assert_eq!(Call::<i32>::ListOwnFds { bytes: 8 }.symbol(), "proc_pidinfo");
    assert_eq!(Call::<i32>::Sysctl { name: String::new(), oldlen: 4 }.symbol(), "sysctlbyname");
    assert!(symbols::async_signal_safe("proc_pidinfo"));
    assert!(!symbols::async_signal_safe("sysctlbyname"));
    for gap in
        ["system", "popen", "pclose", "daemon", "syscall", "dlsym", "sysctl", "proc_pidfdinfo"]
    {
        let e = symbols::lookup(gap).unwrap_err();
        assert_ne!(e.reason, "not in the platform symbol table", "{gap} must be a NAMED gap");
        assert!(symbols::named_gaps().any(|(n, _)| n == gap));
    }
    for (path, m) in [
        ("std::process::Command::output", Modeled::StdCommandOutput),
        ("std::process::Command::status", Modeled::StdCommandStatus),
        ("std::os::unix::process::CommandExt::exec", Modeled::StdCommandExec),
        ("std::thread::spawn::<{closure}, ()>", Modeled::StdRow("STD-THREAD-SPAWN")),
        ("std::thread::Builder::spawn", Modeled::StdRow("STD-THREAD-SPAWN")),
        ("std::thread::Scope::<'_, '_>::spawn", Modeled::StdRow("STD-THREAD-SPAWN")),
    ] {
        assert_eq!(symbols::lookup(path).unwrap().modeled, m, "{path}");
        assert!(symbols::modeled_names().any(|(_, mm)| mm == m));
    }
    for lock in ["lock", "lock_shared", "try_lock", "try_lock_shared", "unlock"] {
        let e = symbols::lookup(&format!("std::fs::File::{lock}")).unwrap_err();
        assert!(e.reason.starts_with("STD-FILE-LOCK"), "{lock}: {}", e.reason);
    }
    assert!(symbols::lookup("std::process::Child::wait").unwrap_err().reason.contains("Child"));
}

#[test]
fn drops_of_carriers_are_std_drop_fd_and_composites_are_named() {
    for carrier in symbols::FD_CARRIERS {
        assert_eq!(
            symbols::lookup_drop(carrier).unwrap().modeled,
            Modeled::StdRow("STD-DROP-FD"),
            "{carrier}"
        );
    }
    assert_eq!(
        symbols::lookup_drop("::std::fs::File").unwrap().normalized,
        "std::fs::File".to_string()
    );
    for composite in ["std::process::Child", "std::process::Command", "std::os::fd::BorrowedFd<'_>"]
    {
        let e = symbols::lookup_drop(composite).unwrap_err();
        assert_ne!(e.reason, "the drop of a type the table does not know to carry a descriptor");
    }
    assert!(symbols::lookup_drop("std::vec::Vec<std::os::fd::OwnedFd>").is_err());
    assert!(symbols::lookup_drop("my_crate::Lane").is_err());
}

fn run_root(h: &Host, p: Pid, program: &Program, args: &[i32]) -> (Host, Vec<SysResult>) {
    let trace = script::run(&Darwin, h, p, program, args).unwrap();
    (
        trace.last().map_or_else(|| h.clone(), |t| t.host.clone()),
        trace.iter().map(|t| t.result).collect(),
    )
}

#[test]
fn std_drop_fd_closes_one_reference() {
    let (h, p) = host();
    let (h, _) = ok(&h, p, Call::Pipe);
    let (h, _) = ok(&h, p, Call::Dup { fd: 3 });
    let row = std_summaries::row("STD-DROP-FD").unwrap();
    assert!(row.atomic && row.returns.is_empty());
    let (h2, _) = run_root(&h, p, &row.program, &[3]);
    assert_eq!(h2.proc(p).unwrap().fds().into_iter().collect::<Vec<_>>(), vec![0, 1, 2, 4, 5]);
    // The description lives on through the dup; the writer's reader is not gone.
    assert_eq!(h2.peer_closed(p, 4), Some(false));
    let (h3, _) = run_root(&h2, p, &row.program, &[5]);
    assert_eq!(h3.peer_closed(p, 4), Some(true));
    assert_eq!(row, std_summaries::std_drop_fd());
}

#[test]
fn std_thread_spawn_counts_a_thread_and_makes_fork_children_restricted() {
    let (h, p) = host();
    let row = std_summaries::row("STD-THREAD-SPAWN").unwrap();
    let (h, _) = run_root(&h, p, &row.program, &[]);
    assert_eq!(h.proc(p).unwrap().threads, 2);
    let (h, child) = ok(&h, p, Call::Fork);
    let Ret::Int(c) = child else { panic!() };
    let c = h.proc(Pid(u32::try_from(c).unwrap())).unwrap();
    assert_eq!(c.phase, Phase::ForkedPreExec { parent_threads: 2 });
}

/// Run a command row's program, letting the child exit (the image's own
/// step) the first time a step blocks; a guarded step is skipped where its
/// guard fails ([`script::When`]) and an assumption must hold.
fn run_command(h: &Host, p: Pid, cr: &std_summaries::CommandRow) -> (Host, Vec<SysResult>) {
    let mut host = h.clone();
    let mut results: Vec<SysResult> = Vec::new();
    let mut exited = false;
    for (k, ps) in cr.row.program.iter().enumerate() {
        let pid = script::actor_pid(ps.actor, p, &results).unwrap();
        if let Some(v) = ps.skipped(k, &[], &results).unwrap() {
            results.push(Ok(Ret::Int(i64::from(v))));
            ps.check_assumed(k, &[], &results).unwrap();
            continue;
        }
        let call = ps.call.map(|op| op.resolve(&[], &results).unwrap());
        let s = match step(&host, pid, &call, ps.oracle) {
            Err(Refusal::Blocks) if !exited => {
                let child =
                    script::actor_pid(Actor::Child(cr.spawn.unwrap()), p, &results).unwrap();
                host = step(&host, child, &Call::Exit { status: 0 }, Oracle::Nominal).unwrap().host;
                exited = true;
                step(&host, pid, &call, ps.oracle).unwrap()
            }
            other => other.unwrap_or_else(|e| panic!("{call:?}: {e}")),
        };
        host = s.host;
        results.push(s.result);
        ps.check_assumed(k, &[], &results).unwrap();
    }
    (host, results)
}

#[test]
fn output_defaults_null_stdin_and_piped_out_err_and_leaves_nothing() {
    let (h, p) = host();
    let cr = command_row(CommandOp::Output, [None; 3], &CommandShape::default(), &[]).unwrap();
    assert_eq!(cr.stdio, [StdioPlan::Null, StdioPlan::Piped, StdioPlan::Piped]);
    assert_eq!(cr.path, Some(SpawnPath::Posix));
    assert_eq!(cr.row.id, "STD-COMMAND-OUTPUT");
    assert_eq!(cr.ours, [None; 3]);
    assert!(cr.error_tail.is_empty(), "the posix path follows the uniform rule");
    let calls: Vec<&'static str> = cr.row.program.iter().map(|ps| ps.call.symbol()).collect();
    assert_eq!(
        calls,
        vec![
            "open",
            "pipe",
            "ioctl",
            "ioctl",
            "pipe",
            "ioctl",
            "ioctl",
            "posix_spawn",
            "close",
            "close",
            "close",
            "read",
            "read",
            "close",
            "close",
            "waitpid"
        ]
    );
    let Call::Spawn { actions, .. } = &cr.row.program[cr.image].call else { panic!() };
    assert_eq!(actions.len(), 3);
    let (h2, results) = run_command(&h, p, &cr);
    assert_eq!(h2.proc(p).unwrap().fds(), h.proc(p).unwrap().fds(), "every temporary is closed");
    assert_eq!(h2.procs().count(), 1, "the child is reaped");
    assert_eq!(results[11], Ok(Ret::Int(0)), "stdout reads end-of-file");
    assert_eq!(cr.row.retried_eintr, vec![15]);
}

#[test]
fn output_one_piped_stream_and_a_piped_stdin() {
    let shape = CommandShape::default();
    let cr = command_row(CommandOp::Output, [None, Some(StdioPlan::Inherit), None], &shape, &[])
        .unwrap();
    let reads = cr.row.program.iter().filter(|ps| matches!(ps.call, Call::ReadSome { .. })).count();
    assert_eq!(reads, 1);
    let user = [Some(StdioPlan::Piped), Some(StdioPlan::Null), Some(StdioPlan::Null)];
    let cr = command_row(CommandOp::Output, user, &shape, &[]).unwrap();
    let (h, p) = host();
    let (h2, _) = run_command(&h, p, &cr);
    assert_eq!(h2.proc(p).unwrap().fds(), h.proc(p).unwrap().fds());
}

#[test]
fn status_waits_and_drops_the_child_handles_after() {
    let (h, p) = host();
    let user = [Some(StdioPlan::Piped), None, Some(StdioPlan::Piped)];
    let cr = command_row(CommandOp::Status, user, &CommandShape::default(), &[]).unwrap();
    assert_eq!(cr.stdio, [StdioPlan::Piped, StdioPlan::Inherit, StdioPlan::Piped]);
    let tail: Vec<&'static str> =
        cr.row.program.iter().skip(cr.image + 1).map(|ps| ps.call.symbol()).collect();
    // theirs (stdin read end, stderr write end), our stdin, the wait, our stderr.
    assert_eq!(tail, vec!["close", "close", "close", "waitpid", "close"]);
    let (h2, _) = run_command(&h, p, &cr);
    assert_eq!(h2.proc(p).unwrap().fds(), h.proc(p).unwrap().fds());
    assert_eq!(h2.procs().count(), 1);
}

#[test]
fn fork_path_rows_run_hooks_and_spell_out_the_error_tail() {
    let (h, p) = host();
    let (h, _) = ok(
        &h,
        p,
        Call::Socketpair { domain: darwin::AF_UNIX, ty: darwin::SOCK_STREAM, protocol: 0 },
    );
    let hook = vec![Call::Dup2 { from: Operand::Lit(3), to: Operand::Lit(10) }];
    let cr =
        command_row(CommandOp::Output, [None; 3], &CommandShape::with_pre_exec(), &[hook]).unwrap();
    assert_eq!(cr.path, Some(SpawnPath::Fork));
    assert_eq!(cr.row.program[cr.image].call, Call::Exec);
    assert_eq!(cr.row.program[cr.image].actor, Actor::Child(cr.spawn.unwrap()));
    // reap, status read end, the three child stdio, the two parent ends.
    let tail: Vec<&'static str> = cr.error_tail.iter().map(Call::symbol).collect();
    assert_eq!(tail, vec!["waitpid", "close", "close", "close", "close", "close", "close"]);
    assert_eq!(cr.child_error.len(), 2);
    let (h2, _) = run_command(&h, p, &cr);
    assert_eq!(h2.proc(p).unwrap().fds(), h.proc(p).unwrap().fds());
    assert_eq!(h2.procs().count(), 1);
    // Retried on EINTR: the child's three stdio dup2s and the wait, not the hook.
    let retried: Vec<&'static str> =
        cr.row.retried_eintr.iter().map(|k| cr.row.program[*k].call.symbol()).collect();
    assert_eq!(
        retried,
        vec![
            "std::process::place_stdio",
            "std::process::place_stdio",
            "std::process::place_stdio",
            "waitpid"
        ]
    );
    let hook_at = cr
        .row
        .program
        .iter()
        .position(|ps| ps.call == Call::Dup2 { from: Operand::Lit(3), to: Operand::Lit(10) })
        .unwrap();
    assert!(!cr.row.retried_eintr.contains(&hook_at));
}

#[test]
fn spawn_rows_refuse_piped_but_the_command_row_returns_the_parent_ends() {
    let shape = CommandShape::default();
    let piped = [StdioPlan::Inherit, StdioPlan::Piped, StdioPlan::Inherit];
    assert!(command_spawn_posix(piped, &shape).unwrap_err().contains("CommandRow"));
    assert!(command_spawn_fork(piped, &CommandShape::with_pre_exec(), &[]).is_err());
    let cr =
        command_row(CommandOp::Spawn, [None, Some(StdioPlan::Piped), None], &shape, &[]).unwrap();
    assert_eq!(cr.row.id, "STD-SPAWN-POSIX");
    let ours = cr.ours[1].unwrap();
    let (h, p) = host();
    let (h2, results) = run_root(&h, p, &cr.row.program, &[]);
    let fd = ours.resolve(&[], &results).unwrap();
    assert!(h2.entry(p, fd).is_some_and(|e| e.cloexec), "the Child's stdout end stays open");
}

/// Trust SP1's operations preserve status/error operands when steps move.
#[test]
fn spawn_rows_capture_sp1_inheritance_and_status_relocation() {
    let r = |step, comp| Operand::Ret { step, comp };
    let null = [StdioPlan::Null, StdioPlan::Inherit, StdioPlan::Inherit];
    let fork = CommandShape::with_pre_exec();
    let fr = command_spawn_fork(null, &fork, &[]).unwrap();
    let expect: Program = vec![
        ProgramStep::root(Call::Open { flags: darwin::O_RDONLY | darwin::O_CLOEXEC }),
        ProgramStep::root(Call::Sysctl {
            name: introspect::SYSCTL_MAXFILESPERPROC.to_string(),
            oldlen: 4,
        }),
        ProgramStep::root(Call::Pipe),
        ProgramStep::root(Call::Ioctl { fd: r(2, 0), request: darwin::FIOCLEX, arg: 0 }),
        ProgramStep::root(Call::Ioctl { fd: r(2, 1), request: darwin::FIOCLEX, arg: 0 }),
        ProgramStep::root(Call::StdStatusFd { fd: r(2, 1) }),
        ProgramStep::root(Call::StdCloseMovedStatus { old: r(2, 1), new: r(5, 0) }),
        ProgramStep::root(Call::Fork),
        ProgramStep::by(Actor::Child(7), Call::Close { fd: r(2, 0) }),
        ProgramStep::by(Actor::Child(7), Call::StdPlaceFd { from: r(0, 0), to: Operand::Lit(0) }),
        ProgramStep::by(Actor::Child(7), Call::StdMarkCloexec),
        ProgramStep::by(Actor::Child(7), Call::Exec),
        ProgramStep::root(Call::Close { fd: r(5, 0) }),
        ProgramStep::root(Call::ReadSome { fd: r(2, 0) }),
        ProgramStep::root(Call::Close { fd: r(2, 0) }),
        ProgramStep::root(Call::Close { fd: r(0, 0) }),
    ];
    assert_eq!(fr.row.program, expect);
    assert_eq!(fr.row.retried_eintr, vec![9]);
    assert_eq!(fr.child_error, vec![Call::WriteSome { fd: r(5, 0) }, Call::Exit { status: 1 }]);
    assert_eq!(fr.ours, [None; 3]);
    let (row, spawn) = command_spawn_posix(null, &CommandShape::default()).unwrap();
    assert_eq!(spawn, 3);
    assert_eq!(row.program.len(), 5);
    assert_eq!(
        row.program[spawn].call,
        Call::Spawn {
            actions: vec![
                crate::FileAction::PlaceStdio { from: r(0, 0), to: Operand::Lit(0) },
                crate::FileAction::InheritIf { fd: Operand::Lit(1), enabled: r(1, 0) },
                crate::FileAction::InheritIf { fd: Operand::Lit(2), enabled: r(2, 0) },
            ],
            flags: darwin::POSIX_SPAWN_SETSIGDEF | darwin::POSIX_SPAWN_CLOEXEC_DEFAULT
        }
    );
}

/// Upstream's original rows remain a separate contract.
#[test]
fn spawn_rows_for_inherit_and_null_are_unchanged() {
    let r = |step, comp| Operand::Ret { step, comp };
    let null = [StdioPlan::Null, StdioPlan::Inherit, StdioPlan::Inherit];
    let upstream = CommandShape::default().under(CommandStd::Upstream);
    let fork = CommandShape::with_pre_exec().under(CommandStd::Upstream);
    let fr = command_spawn_fork(null, &fork, &[]).unwrap();
    let expect: Program = vec![
        ProgramStep::root(Call::Open { flags: darwin::O_RDONLY | darwin::O_CLOEXEC }),
        ProgramStep::root(Call::Pipe),
        ProgramStep::root(Call::Ioctl { fd: r(1, 0), request: darwin::FIOCLEX, arg: 0 }),
        ProgramStep::root(Call::Ioctl { fd: r(1, 1), request: darwin::FIOCLEX, arg: 0 }),
        ProgramStep::root(Call::Fork),
        ProgramStep::by(Actor::Child(4), Call::Close { fd: r(1, 0) }),
        ProgramStep::by(Actor::Child(4), Call::Dup2 { from: r(0, 0), to: Operand::Lit(0) }),
        ProgramStep::by(Actor::Child(4), Call::Exec),
        ProgramStep::root(Call::Close { fd: r(1, 1) }),
        ProgramStep::root(Call::ReadSome { fd: r(1, 0) }),
        ProgramStep::root(Call::Close { fd: r(1, 0) }),
        ProgramStep::root(Call::Close { fd: r(0, 0) }),
    ];
    assert_eq!(fr.row.program, expect);
    assert_eq!(fr.row.retried_eintr, vec![6]);
    assert_eq!(fr.ours, [None; 3]);
    let (row, spawn) = command_spawn_posix(null, &upstream).unwrap();
    assert_eq!(spawn, 1);
    assert_eq!(row.program.len(), 3);
    assert_eq!(
        row.program[1].call,
        Call::Spawn {
            actions: vec![crate::FileAction::Dup2 { from: r(0, 0), to: Operand::Lit(0) }],
            flags: darwin::POSIX_SPAWN_SETSIGDEF
        }
    );
}

/// A program's steps without the prose of its assumptions: actor, call,
/// skip and assumed guard.
type StepShape = (Actor, Call<Operand>, Option<When>, Option<Guard>);

fn shape_of(program: &Program) -> Vec<StepShape> {
    program
        .iter()
        .map(|ps| (ps.actor, ps.call.clone(), ps.when, ps.assume.map(|a| a.guard)))
        .collect()
}

/// Trust's std (DECISION_QUEUE SP-1, Trust a7f474346f): the fork row reads
/// the strip's bound, moves a status write end below 10 to 10 or above,
/// strips the child after its stdio, and assumes each stdio source lands off
/// its target; the posix row names each inherited stdio slot it found
/// passing an exec, under `CLOEXEC_DEFAULT`.
#[test]
fn trust_spawn_rows_for_inherit_and_null() {
    let r = |step, comp| Operand::Ret { step, comp };
    let lit = Operand::Lit;
    let null = [StdioPlan::Null, StdioPlan::Inherit, StdioPlan::Inherit];
    let c = Actor::Child(7);
    let fr = command_spawn_fork(null, &CommandShape::with_pre_exec(), &[]).unwrap();
    let expect: Vec<StepShape> = vec![
        (Actor::Root, Call::Open { flags: darwin::O_RDONLY | darwin::O_CLOEXEC }, None, None),
        (
            Actor::Root,
            Call::Sysctl { name: introspect::SYSCTL_MAXFILESPERPROC.to_string(), oldlen: 4 },
            None,
            None,
        ),
        (Actor::Root, Call::Pipe, None, None),
        (Actor::Root, Call::Ioctl { fd: r(2, 0), request: darwin::FIOCLEX, arg: 0 }, None, None),
        (Actor::Root, Call::Ioctl { fd: r(2, 1), request: darwin::FIOCLEX, arg: 0 }, None, None),
        (Actor::Root, Call::StdStatusFd { fd: r(2, 1) }, None, None),
        (Actor::Root, Call::StdCloseMovedStatus { old: r(2, 1), new: r(5, 0) }, None, None),
        (Actor::Root, Call::Fork, None, None),
        (c, Call::Close { fd: r(2, 0) }, None, None),
        (c, Call::StdPlaceFd { from: r(0, 0), to: lit(0) }, None, None),
        (c, Call::StdMarkCloexec, None, None),
        (c, Call::Exec, None, None),
        (Actor::Root, Call::Close { fd: r(5, 0) }, None, None),
        (Actor::Root, Call::ReadSome { fd: r(2, 0) }, None, None),
        (Actor::Root, Call::Close { fd: r(2, 0) }, None, None),
        (Actor::Root, Call::Close { fd: r(0, 0) }, None, None),
    ];
    assert_eq!(shape_of(&fr.row.program), expect);
    assert_eq!((fr.fork, fr.exec, fr.status_read), (7, 11, 13));
    assert_eq!(fr.row.retried_eintr, vec![9]);
    assert_eq!(fr.child_error, vec![Call::WriteSome { fd: r(5, 0) }, Call::Exit { status: 1 }]);
    let path = CommandShape { path_in_env_bare_program: true, ..CommandShape::default() };
    let plain = command_spawn_fork(null, &path, &[]).unwrap();
    assert!(plain.row.program.iter().all(|ps| ps.when.is_none()));
    assert!(plain.row.program.iter().any(|ps| ps.call == Call::StdMarkCloexec));
    assert!(plain.row.program.iter().all(|ps| !matches!(ps.call, Call::StdStatusFd { .. })));
    let (row, spawn) = command_spawn_posix(null, &CommandShape::default()).unwrap();
    assert_eq!(spawn, 3);
    let expect: Vec<StepShape> = vec![
        (Actor::Root, Call::Open { flags: darwin::O_RDONLY | darwin::O_CLOEXEC }, None, None),
        (Actor::Root, Call::StdPassesExec { fd: lit(1) }, None, None),
        (Actor::Root, Call::StdPassesExec { fd: lit(2) }, None, None),
        (
            Actor::Root,
            Call::Spawn {
                actions: vec![
                    crate::FileAction::PlaceStdio { from: r(0, 0), to: lit(0) },
                    crate::FileAction::InheritIf { fd: lit(1), enabled: r(1, 0) },
                    crate::FileAction::InheritIf { fd: lit(2), enabled: r(2, 0) },
                ],
                flags: darwin::POSIX_SPAWN_SETSIGDEF | darwin::POSIX_SPAWN_CLOEXEC_DEFAULT,
            },
            None,
            None,
        ),
        (Actor::Root, Call::Close { fd: r(0, 0) }, None, None),
    ];
    assert_eq!(shape_of(&row.program), expect);
}
#[test]
fn exec_row_dup2s_in_place_and_its_failure_keeps_the_dup2() {
    let (h, p) = host();
    let user = [Some(StdioPlan::Null), None, Some(StdioPlan::Piped)];
    let cr = command_row(CommandOp::Exec, user, &CommandShape::default(), &[]).unwrap();
    assert_eq!(cr.path, None);
    assert_eq!(cr.row.id, "STD-COMMANDEXT-EXEC");
    assert!(cr.row.program.iter().all(|ps| ps.actor == Actor::Root));
    assert_eq!(cr.row.program[cr.image].call, Call::Exec);
    // Success: the owned /dev/null and both pipe ends are close-on-exec.
    let (h2, _) = run_root(&h, p, &cr.row.program, &[]);
    assert_eq!(h2.proc(p).unwrap().phase, Phase::Execd);
    assert_eq!(h2.proc(p).unwrap().fds().into_iter().collect::<Vec<_>>(), vec![0, 1, 2]);
    // Failure: the dup2s stay; the error tail drops what setup opened.
    let mut failing = cr.row.program.clone();
    failing[cr.image].oracle = Oracle::Fail(Errno::ENOENT);
    failing.extend(cr.error_tail.iter().cloned().map(ProgramStep::root));
    let (h3, results) = run_root(&h, p, &failing, &[]);
    assert_eq!(results[cr.image], Err(Errno::ENOENT));
    assert_eq!(h3.proc(p).unwrap().fds().into_iter().collect::<Vec<_>>(), vec![0, 1, 2]);
    let fd0 = h3.ofd(h3.entry(p, 0).unwrap().ofd).unwrap();
    assert_eq!(fd0.access, Access::ReadOnly, "fd 0 is now the /dev/null the exec opened");
    // A shape whose do_exec steps the model does not run is refused.
    let cwd = CommandShape { cwd: true, ..CommandShape::default() };
    assert!(command_row(CommandOp::Exec, [None; 3], &cwd, &[]).unwrap_err().contains("chdir"));
    // Closures need a shape that says so (std's fork-path trigger).
    let hook = vec![Call::Close { fd: Operand::Lit(9) }];
    assert!(command_row(CommandOp::Status, [None; 3], &CommandShape::default(), &[hook]).is_err());
}

#[test]
fn every_row_declares_its_fidelity() {
    let shape = CommandShape::default();
    let fork = CommandShape::with_pre_exec();
    let mut ids: Vec<&'static str> = std_summaries::rows().iter().map(|r| r.id).collect();
    ids.push(std_summaries::std_open(darwin::O_RDONLY).id);
    ids.push(command_spawn_fork([StdioPlan::Inherit; 3], &fork, &[]).unwrap().row.id);
    ids.push(command_spawn_posix([StdioPlan::Inherit; 3], &shape).unwrap().0.id);
    for op in [CommandOp::Spawn, CommandOp::Output, CommandOp::Status, CommandOp::Exec] {
        for s in [&shape, &fork] {
            ids.push(command_row(op, [None; 3], s, &[]).unwrap().row.id);
        }
    }
    for id in &ids {
        assert!(fidelity(id).is_some(), "row {id} declares no fidelity");
    }
    for id in ["STD-DROP-FD", "STD-COMMAND-OUTPUT", "STD-THREAD-SPAWN"] {
        assert!(!fidelity(id).unwrap().under.is_empty(), "{id} elides steps it must name");
    }
    assert!(!fidelity("STD-THREAD-SPAWN").unwrap().over.is_empty());
    assert_eq!(fidelity("STD-PIPE").unwrap(), std_summaries::Fidelity { under: &[], over: &[] });
    assert!(fidelity("STD-NO-SUCH-ROW").is_none());
}

#[test]
fn x3a_calls_keep_the_host_invariants_under_every_admissible_oracle() {
    let (h, p) = busy();
    for call in [
        Call::ListOwnFds { bytes: 64 },
        Call::ListOwnFds { bytes: 0 },
        Call::Sysctl { name: "kern.maxfilesperproc".to_string(), oldlen: 4 },
    ] {
        for o in crate::oracle_space(&call) {
            let s = step(&h, p, &call, o).unwrap();
            s.host.check_invariants().unwrap();
            assert_eq!(s.host, h, "{call:?} changed the host");
        }
    }
}

#[test]
fn sp1_strip_keeps_sources_open_and_hooks_survive_above_a_lowered_limit() {
    let (mut h, p) = host();
    h.install_fresh(p, 180, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    let (h, _) = ok(&h, p, Call::Pipe);
    let (h, _) = ok(
        &h,
        p,
        Call::Setrlimit { resource: darwin::RLIMIT_NOFILE, soft: 16, hard: darwin::RLIM_INFINITY },
    );
    let hook = vec![Call::Dup2 { from: Operand::Lit(3), to: Operand::Lit(9) }];
    let fr = command_spawn_fork([StdioPlan::Inherit; 3], &CommandShape::with_pre_exec(), &[hook])
        .unwrap();
    let trace = script::run(&Darwin, &h, p, &fr.row.program, &[]).unwrap();
    let mark = trace.iter().find(|s| s.call == Call::StdMarkCloexec).unwrap();
    assert!(mark.host.entry(mark.pid, 180).unwrap().cloexec);
    assert!(mark.host.entry(mark.pid, 3).unwrap().cloexec, "marking must retain hook sources");
    assert_eq!(mark.host.proc(p).unwrap().table, trace[fr.fork].host.proc(p).unwrap().table);
    let end = trace.last().unwrap();
    let child = trace[fr.exec].pid;
    assert_eq!(end.host.proc(child).unwrap().fds(), [0, 1, 2, 9].into_iter().collect());
    assert_eq!(end.host.entry(child, 9).unwrap().ofd, h.entry(p, 3).unwrap().ofd);
    assert_eq!(end.host.proc(p).unwrap().table, h.proc(p).unwrap().table);
}

#[test]
fn sp1_closed_and_cloexec_inherited_stdio_differ_from_owned_same_number_stdio() {
    for shape in [CommandShape::default(), CommandShape::with_pre_exec()] {
        let (h, p) = host();
        let (h, _) = ok(&h, p, Call::Close { fd: 1 });
        let (h, _) = ok(&h, p, Call::Fcntl { fd: 2, cmd: darwin::F_SETFD, arg: 1 });
        let cr = command_row(CommandOp::Status, [None; 3], &shape, &[]).unwrap();
        let trace = script::run(&Darwin, &h, p, &cr.row.program[..=cr.image], &[]).unwrap();
        let last = trace.last().unwrap();
        let child = script::actor_pid(
            Actor::Child(cr.spawn.unwrap()),
            p,
            &trace.iter().map(|s| s.result).collect::<Vec<_>>(),
        )
        .unwrap();
        assert_eq!(last.host.proc(child).unwrap().fds(), [0].into_iter().collect());
        assert_eq!(last.host.proc(p).unwrap().table.get(&2), h.proc(p).unwrap().table.get(&2));

        let (h, p) = host();
        let (h, _) = ok(&h, p, Call::Close { fd: 0 });
        let cr = command_row(CommandOp::Status, [Some(StdioPlan::Null), None, None], &shape, &[])
            .unwrap();
        let trace = script::run(&Darwin, &h, p, &cr.row.program[..=cr.image], &[]).unwrap();
        let rs: Vec<_> = trace.iter().map(|s| s.result).collect();
        let child = script::actor_pid(Actor::Child(cr.spawn.unwrap()), p, &rs).unwrap();
        let end = &trace.last().unwrap().host;
        let e = end.entry(child, 0).expect("owned fd0 survives same-number placement");
        assert!(!e.cloexec);
        assert_eq!(end.ofd(e.ofd).unwrap().access, Access::ReadOnly);
    }
    // Replacement exec keeps its legacy inheritance while placing owned fd0.
    let (mut h, p) = host();
    h.install_fresh(p, 180, OfdKind::Opaque, Access::ReadWrite, 0, false).unwrap();
    let (h, _) = ok(&h, p, Call::Close { fd: 0 });
    let cr = command_row(
        CommandOp::Exec,
        [Some(StdioPlan::Null), None, None],
        &CommandShape::default(),
        &[],
    )
    .unwrap();
    let t = script::run(&Darwin, &h, p, &cr.row.program, &[]).unwrap();
    assert_eq!(t.last().unwrap().host.proc(p).unwrap().fds(), [0, 1, 2, 180].into_iter().collect());
}

#[test]
fn sp1_status_relocation_exposes_both_aliases_then_closes_only_a_moved_source() {
    for soft in [8, 256] {
        let (h, p) = host();
        let (h, _) = ok(&h, p, Call::Pipe);
        let (h, _) = ok(&h, p, Call::Fcntl { fd: 4, cmd: darwin::F_SETFD, arg: 1 });
        let (h, _) = ok(
            &h,
            p,
            Call::Setrlimit { resource: darwin::RLIMIT_NOFILE, soft, hard: darwin::RLIM_INFINITY },
        );
        let (copied, Ret::Int(new)) = ok(&h, p, Call::StdStatusFd { fd: 4 }) else { panic!() };
        let new = i32::try_from(new).unwrap();
        assert_eq!(new, if soft == 8 { 4 } else { 10 });
        assert_eq!(copied.entry(p, 4), h.entry(p, 4), "the dup event leaves the old writer open");
        assert_eq!(copied.entry(p, new).unwrap().ofd, h.entry(p, 4).unwrap().ofd);
        assert!(copied.entry(p, new).unwrap().cloexec);
        let (closed, _) = ok(&copied, p, Call::StdCloseMovedStatus { old: 4, new });
        assert_eq!(closed.entry(p, 4).is_none(), new != 4);
        assert!(closed.entry(p, new).is_some());
        assert_eq!(closed.entry(p, 3), h.entry(p, 3));
        let (high, p) = host();
        let (high, _) = ok(&high, p, Call::Pipe);
        let (high, _) = ok(&high, p, Call::Fcntl { fd: 4, cmd: darwin::F_DUPFD_CLOEXEC, arg: 20 });
        let (high, _) = ok(
            &high,
            p,
            Call::Setrlimit {
                resource: darwin::RLIMIT_NOFILE,
                soft: 8,
                hard: darwin::RLIM_INFINITY,
            },
        );
        let (same, ret) = ok(&high, p, Call::StdStatusFd { fd: 20 });
        assert_eq!(ret, Ret::Int(20));
        assert_eq!(same, high, "an already-high writer neither allocates nor closes");
    }
}

#[test]
fn sp1_failed_exec_reports_on_the_relocated_or_fallback_writer_and_reaps() {
    for (soft, target) in [(256, 6), (8, 7)] {
        let (h, p) = host();
        let (h, _) = ok(&h, p, Call::Pipe);
        let (h, _) = ok(
            &h,
            p,
            Call::Setrlimit { resource: darwin::RLIMIT_NOFILE, soft, hard: darwin::RLIM_INFINITY },
        );
        let hook = vec![Call::Dup2 { from: Operand::Lit(3), to: Operand::Lit(target) }];
        let fr =
            command_spawn_fork([StdioPlan::Inherit; 3], &CommandShape::with_pre_exec(), &[hook])
                .unwrap();
        let mut program = fr.row.program.clone();
        program[fr.exec].oracle = Oracle::Fail(Errno::ENOENT);
        program.splice(
            fr.exec + 1..fr.exec + 1,
            fr.child_error.iter().cloned().map(|c| ProgramStep::by(Actor::Child(fr.fork), c)),
        );
        program.extend(fr.parent_error.iter().cloned().map(ProgramStep::root));
        let t = script::run(&Darwin, &h, p, &program, &[]).unwrap();
        assert_eq!(t[fr.exec].result, Err(Errno::ENOENT));
        // ReadSome abstracts the error message as present data (one unit).
        assert_eq!(t[fr.status_read + fr.child_error.len()].result, Ok(Ret::Int(1)));
        assert_eq!(t.last().unwrap().host.proc(p).unwrap().table, h.proc(p).unwrap().table);
        assert_eq!(t.last().unwrap().host.procs().count(), 1, "the failed child was reaped");
    }
}

#[test]
fn sp1_posix_guards_are_captured_before_the_raw_spawn_copy_window() {
    use crate::FileAction;
    let (h, p) = host();
    let (_, guard) = ok(&h, p, Call::StdPassesExec { fd: 1 });
    assert_eq!(guard, Ret::Int(1));
    let actions = vec![FileAction::InheritIf { fd: 1, enabled: 1 }];
    let (h, _) = ok(&h, p, Call::Fcntl { fd: 1, cmd: darwin::F_SETFD, arg: 1 });
    let (h, Ret::Int(child)) = ok(&h, p, Call::SpawnBegin) else { panic!() };
    let child = i32::try_from(child).unwrap();
    let (end, _) =
        ok(&h, p, Call::SpawnEnd { child, actions, flags: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT });
    assert_eq!(
        end.proc(Pid(u32::try_from(child).unwrap())).unwrap().fds(),
        [1].into_iter().collect()
    );
    assert!(end.entry(p, 1).unwrap().cloexec, "only the child's flag is cleared");
    assert!(
        step(
            &end,
            p,
            &Call::Spawn { actions: vec![FileAction::InheritIf { fd: 1, enabled: 2 }], flags: 0 },
            Oracle::Nominal
        )
        .is_err()
    );
    // Literal raw actions keep the original Darwin self-dup contract.
    let (raw, Ret::Int(c)) =
        ok(&end, p, Call::Spawn { actions: vec![FileAction::Dup2 { from: 1, to: 1 }], flags: 0 })
    else {
        panic!()
    };
    assert!(raw.entry(Pid(u32::try_from(c).unwrap()), 1).is_none());
}

#[test]
fn sp1_compositions_refuse_unsupported_callers_and_keep_selected_primitive_semantics() {
    use crate::Step;
    struct RefuseSet;
    impl Semantics for RefuseSet {
        fn step_raw(&self, h: &Host, p: Pid, c: &Call, o: Oracle) -> Result<Step, Refusal> {
            if matches!(c, Call::Fcntl { cmd: darwin::F_SETFD, .. }) {
                Ok(Step { host: h.clone(), result: Err(Errno::EBADF) })
            } else {
                Darwin.step_raw(h, p, c, o)
            }
        }
    }
    let (h, p) = host();
    assert!(step(&h, p, &Call::StdMarkCloexec, Oracle::Nominal).is_err());
    assert!(matches!(
        step(&h, Pid(999), &Call::StdMarkCloexec, Oracle::Nominal),
        Err(Refusal::NoSuchProcess(_))
    ));
    assert!(matches!(
        step(&h, p, &Call::StdPassesExec { fd: 0 }, Oracle::Fail(Errno::EINTR)),
        Err(Refusal::InadmissibleOracle { .. })
    ));
    let (h, _) = ok(&h, p, Call::Fcntl { fd: 0, cmd: darwin::F_SETFD, arg: 1 });
    assert_eq!(
        RefuseSet
            .step(&h, p, &Call::StdPlaceFd { from: 0, to: 0 }, Oracle::Nominal)
            .unwrap()
            .result,
        Err(Errno::EBADF)
    );
    let (h, _) = ok(&h, p, Call::ThreadCreate);
    assert!(step(&h, p, &Call::StdPlaceFd { from: 0, to: 0 }, Oracle::Nominal).is_err());
    let (h, _) = ok(&h, p, Call::Exit { status: 0 });
    assert!(matches!(
        step(&h, p, &Call::StdPassesExec { fd: 0 }, Oracle::Nominal),
        Err(Refusal::NotLive(_))
    ));
}
