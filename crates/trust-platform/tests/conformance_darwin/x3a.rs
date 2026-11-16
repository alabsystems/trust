//! X3a conformance (design §2.6, census PR 13): the descriptor listing
//! (`proc_pidinfo(PROC_PIDLISTFDS)`), `sysctlbyname("kern.maxfilesperproc")`,
//! STD-DROP-FD, STD-THREAD-SPAWN, STD-COMMAND-OUTPUT, STD-COMMAND-STATUS and
//! STD-COMMANDEXT-EXEC — each run on the real host beside its model row,
//! each with spec mutants that must be killed — plus two harness checks:
//! std's `File::lock` is the description-level `flock` (STD-FILE-LOCK's
//! premise), and the suite passes with a 200-character `TMPDIR` (its
//! `AF_UNIX` sockets are bound by a short relative name, after any leftover
//! file of that name is removed).

use std::ffi::c_int;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::path::PathBuf;

use trust_platform::call::{Call, Oracle, Refusal, Ret, Semantics, Step, SysResult};
use trust_platform::darwin::{self, Errno};
use trust_platform::host::{Host, Pid};
use trust_platform::introspect::{self, ListedFd};
use trust_platform::script::{self, Actor, Operand, ProgramStep};
use trust_platform::std_summaries::{
    self, CommandOp, CommandRow, CommandShape, CommandStd, StdRow, StdioPlan, command_row,
};
use trust_platform::step;

use super::{
    Act, B, Env, MISSING, MutFn, PROBE_SOFT, Probe, Real, Rec, Spec, StdCall, c, compare_obs,
    errno, fcntl, lit, r, resolve_call, sock, sockpair,
};

/// The std calls this module adds to the probe vocabulary.
#[derive(Clone, Debug)]
pub(super) enum XStd {
    /// `drop(OwnedFd::from_raw_fd(fd))` (STD-DROP-FD).
    DropFd(Operand),
    /// `thread::spawn` of a thread that parks forever (STD-THREAD-SPAWN);
    /// the result is the process's thread count afterwards.
    ThreadSpawn,
    /// `Command::output()` of the reporter (STD-COMMAND-OUTPUT).
    Output { user: [Option<StdioPlan>; 3], hooks: Option<Vec<Call<Operand>>> },
    /// `Command::status()` of the reporter (STD-COMMAND-STATUS).
    Status { user: [Option<StdioPlan>; 3], hooks: Option<Vec<Call<Operand>>> },
    /// Explicit Trust opt-out, preserving upstream inheritance.
    StatusInheritAll { user: [Option<StdioPlan>; 3], hooks: Option<Vec<Call<Operand>>> },
    /// `CommandExt::exec()` by a forked child (STD-COMMANDEXT-EXEC): of the
    /// reporter, or (`missing`) of a path that does not exist.
    Exec { user: [Option<StdioPlan>; 3], hooks: Option<Vec<Call<Operand>>>, missing: bool },
}

impl XStd {
    fn op(&self) -> Option<CommandOp> {
        match self {
            XStd::Output { .. } => Some(CommandOp::Output),
            XStd::Status { .. } | XStd::StatusInheritAll { .. } => Some(CommandOp::Status),
            XStd::Exec { .. } => Some(CommandOp::Exec),
            XStd::DropFd(_) | XStd::ThreadSpawn => None,
        }
    }

    /// Spawns the reporter as a child (its table is reported as
    /// `Child(step)`).
    pub(super) fn spawns_reporter(&self) -> bool {
        matches!(self, XStd::Output { .. } | XStd::Status { .. } | XStd::StatusInheritAll { .. })
    }

    /// Execs the reporter in the acting process.
    pub(super) fn exec_success(&self) -> bool {
        matches!(self, XStd::Exec { missing: false, .. })
    }
}

fn x(act: &Act) -> Option<&XStd> {
    match act {
        Act::Std(StdCall::X(x)) => Some(x),
        _ => None,
    }
}

/// A forked child block may make this std call.
pub(super) fn child_ok(sc: &StdCall) -> bool {
    matches!(sc, StdCall::X(XStd::Exec { .. }))
}

/// The probe root may make this std call (it cannot exec itself).
pub(super) fn root_ok(sc: &StdCall) -> bool {
    !matches!(sc, StdCall::X(XStd::Exec { .. }))
}

/// The act ends a child block (the process becomes the reporter).
pub(super) fn ends_block(act: &Act) -> bool {
    x(act).is_some_and(XStd::exec_success)
}

/// The act execs the reporter in the acting process.
pub(super) fn is_exec_success(act: &Act) -> bool {
    x(act).is_some_and(XStd::exec_success)
}

/// The act spawns the reporter as a child.
pub(super) fn spawns_reporter(act: &Act) -> bool {
    x(act).is_some_and(XStd::spawns_reporter)
}

// =============================================================================
// Probes
// =============================================================================

fn list(bytes: i32) -> Call<Operand> {
    Call::ListOwnFds { bytes }
}

fn sysctl(oldlen: u64) -> Call<Operand> {
    Call::Sysctl { name: introspect::SYSCTL_MAXFILESPERPROC.to_string(), oldlen }
}

fn xs(x: XStd) -> Act {
    Act::Std(StdCall::X(x))
}

#[allow(clippy::too_many_lines)]
pub(super) fn probes(env: &Env) -> Vec<Probe> {
    use darwin::*;
    let mut out = Vec::new();

    // The listing: ascending, the lowest `bytes / 8` entries, kqueues and
    // close-on-exec descriptors included, descriptors above a lowered soft
    // limit included, ENOMEM below one entry; a fork child lists its own
    // table (no kqueue).
    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let k = b.root(c(Call::Kqueue));
    b.root(c(fcntl(r(p, 0), F_DUPFD, 50)));
    b.root(c(sock(AF_UNIX, SOCK_STREAM)));
    b.root(Act::OpenNull(O_RDONLY | O_CLOEXEC));
    b.root(c(list(512)));
    b.root(c(list(16)));
    b.root(c(list(12)));
    b.root(c(list(7)));
    b.root(c(list(0)));
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: 20, hard: env.hard }));
    b.root(c(list(512)));
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: PROBE_SOFT, hard: env.hard }));
    let f = b.root(c(Call::Fork));
    b.child(f, c(list(512)));
    b.child(f, c(list(24)));
    b.child(f, c(Call::Exit { status: 0 }));
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    b.root(c(Call::Close { fd: r(k, 0) }));
    out.push(b.done("list-own-fds"));

    let mut b = B::default();
    b.root(c(sysctl(4)));
    b.root(c(sysctl(8)));
    b.root(c(sysctl(2)));
    b.root(c(sysctl(0)));
    out.push(b.done("sysctl-maxfilesperproc"));

    // STD-DROP-FD: one of two references (the description stays), the last
    // one (the pipe's write end loses its reader), a socketpair end (the peer
    // reads end-of-file), a std File.
    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let d = b.root(c(Call::Dup { fd: r(p, 0) }));
    b.root(xs(XStd::DropFd(r(p, 0))));
    b.root(xs(XStd::DropFd(r(d, 0))));
    let s = b.root(c(sockpair(SOCK_STREAM)));
    b.root(xs(XStd::DropFd(r(s, 0))));
    let f = b.root(Act::Std(StdCall::OpenNullRo));
    b.root(xs(XStd::DropFd(r(f, 0))));
    out.push(b.done("std-drop-fd"));

    // STD-THREAD-SPAWN: the result is the thread count afterwards.
    let mut b = B::default();
    b.root(xs(XStd::ThreadSpawn));
    b.root(Act::Observe);
    out.push(b.done("std-thread-spawn"));

    // STD-COMMAND-STATUS on both paths. SP1 strips the unflagged socketpair
    // from every image; `waitpid(-1, WNOHANG)`
    // answering ECHILD shows status() reaped its child.
    let mut b = B::default();
    let lk = b.root(c(sockpair(SOCK_STREAM)));
    let status = |user, hooks| xs(XStd::Status { user, hooks });
    b.root(status([None; 3], None));
    b.root(c(Call::Waitpid { pid: lit(-1), options: WNOHANG }));
    b.root(status([Some(StdioPlan::Null), None, Some(StdioPlan::Piped)], None));
    b.root(status([None; 3], Some(vec![fcntl(r(lk, 0), F_SETFD, 1)])));
    b.root(c(Call::Waitpid { pid: lit(-1), options: WNOHANG }));
    out.push(b.done("std-command-status"));

    // STD-COMMAND-OUTPUT: the defaults (stdin null, stdout and stderr piped),
    // one piped stream either way, a piped stdin (dropped unread), and the
    // fork path with a lane — the one descriptor above stdio its child gets
    // under Trust's std (SP-1). Its status pipe (10, 11) sits above 9, so
    // its write end stays where it is.
    let mut b = B::default();
    let lk = b.root(c(sockpair(SOCK_STREAM)));
    let output = |user, hooks| xs(XStd::Output { user, hooks });
    b.root(output([None; 3], None));
    b.root(output([None, Some(StdioPlan::Inherit), None], None));
    b.root(output([None, None, Some(StdioPlan::Null)], None));
    b.root(output([Some(StdioPlan::Piped), Some(StdioPlan::Null), Some(StdioPlan::Null)], None));
    b.root(output([None; 3], Some(vec![Call::Dup2 { from: r(lk, 0), to: lit(10) }])));
    b.root(c(Call::Waitpid { pid: lit(-1), options: WNOHANG }));
    out.push(b.done("std-command-output"));

    // STD-COMMANDEXT-EXEC in a fork child: a failing exec keeps the stdio
    // dup2 it made and drops what it opened; a successful one (a lane placed
    // by a pre_exec hook, stderr piped) is the reporter.
    let mut b = B::default();
    let lk = b.root(c(sockpair(SOCK_STREAM)));
    let f = b.root(c(Call::Fork));
    b.child(
        f,
        xs(XStd::Exec { user: [Some(StdioPlan::Null), None, None], hooks: None, missing: true }),
    );
    b.child(f, Act::Observe);
    b.child(
        f,
        xs(XStd::Exec {
            user: [None, None, Some(StdioPlan::Piped)],
            hooks: Some(vec![Call::Dup2 { from: r(lk, 1), to: lit(9) }]),
            missing: false,
        }),
    );
    b.child(f, Act::ImageExits);
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    out.push(b.done("std-commandext-exec"));

    // SP1 lists live entries rather than stopping at a lowered soft limit.
    // Hook placements survive; every parent flag remains unchanged.
    let mut b = B::default();
    let lk = b.root(c(sockpair(darwin::SOCK_STREAM)));
    b.root(c(fcntl(r(lk, 0), darwin::F_DUPFD, 180)));
    b.root(c(Call::Setrlimit { resource: darwin::RLIMIT_NOFILE, soft: 16, hard: env.hard }));
    b.root(xs(XStd::Status {
        user: [None; 3],
        hooks: Some(vec![Call::Dup2 { from: r(lk, 0), to: lit(9) }]),
    }));
    b.root(xs(XStd::Status { user: [None; 3], hooks: None }));
    b.root(c(fcntl(lit(180), darwin::F_GETFD, 0)));
    out.push(b.done("std-sp1-above-lowered-soft-limit"));

    // Null stdio allocated at its own number must clear CLOEXEC. Inherit
    // must instead leave closed/CLOEXEC slots absent from the new image.
    let mut b = B::default();
    b.root(c(Call::Close { fd: lit(0) }));
    for hooks in [None, Some(Vec::new())] {
        b.root(xs(XStd::Status { user: [Some(StdioPlan::Null), None, None], hooks }));
    }
    b.root(c(Call::Dup2 { from: lit(1), to: lit(0) }));
    b.root(c(fcntl(lit(2), darwin::F_SETFD, 1)));
    b.root(xs(XStd::Status { user: [None; 3], hooks: None }));
    b.root(c(Call::Close { fd: lit(1) }));
    b.root(xs(XStd::Status { user: [None; 3], hooks: None }));
    b.root(xs(XStd::Status { user: [None; 3], hooks: Some(Vec::new()) }));
    out.push(b.done("std-sp1-closed-and-same-number-stdio"));

    // A failed F_DUPFD_CLOEXEC floor10 allocation retains the original
    // writer, which must still close and report EOF on a successful exec.
    let mut b = B::default();
    b.root(c(Call::Setrlimit { resource: darwin::RLIMIT_NOFILE, soft: 8, hard: env.hard }));
    b.root(xs(XStd::Status { user: [None; 3], hooks: Some(Vec::new()) }));
    b.root(c(Call::Waitpid { pid: lit(-1), options: darwin::WNOHANG }));
    out.push(b.done("std-sp1-status-relocation-fallback"));

    // Explicit opt-out is a positive legacy control, on both spawn paths.
    let mut b = B::default();
    b.root(c(sockpair(darwin::SOCK_STREAM)));
    b.root(xs(XStd::StatusInheritAll { user: [None; 3], hooks: None }));
    b.root(xs(XStd::StatusInheritAll { user: [None; 3], hooks: Some(Vec::new()) }));
    out.push(b.done("std-sp1-explicit-upstream-inheritance"));

    out
}

// =============================================================================
// Real execution
// =============================================================================

/// `proc_pidinfo(getpid(), PROC_PIDLISTFDS, 0, buf, bytes)` into a stack
/// buffer of 512 entries (`bytes` must not exceed it). Returns the result
/// and the entries written.
pub(super) fn real_list(bytes: i32) -> (SysResult, Vec<(i32, u32)>) {
    const CAP: usize = 512;
    let mut buf = [libc::proc_fdinfo { proc_fd: -1, proc_fdtype: 0 }; CAP];
    let cap = c_int::try_from(CAP * std::mem::size_of::<libc::proc_fdinfo>()).unwrap_or(0);
    if bytes > cap {
        return (Err(Errno(-1)), Vec::new());
    }
    // SAFETY: `buf` is `cap >= bytes` writable bytes of `proc_fdinfo`; errno
    // is this thread's.
    let n = unsafe {
        *libc::__error() = 0;
        libc::proc_pidinfo(
            libc::getpid(),
            introspect::PROC_PIDLISTFDS,
            0,
            buf.as_mut_ptr().cast(),
            bytes,
        )
    };
    if n <= 0 {
        let e = errno();
        if n == 0 && e.0 == 0 {
            return (Ok(Ret::Int(0)), Vec::new());
        }
        return (Err(e), Vec::new());
    }
    let count = usize::try_from(n).unwrap_or(0) / std::mem::size_of::<libc::proc_fdinfo>();
    let listed = buf.iter().take(count).map(|f| (f.proc_fd, f.proc_fdtype)).collect();
    (Ok(Ret::Int(i64::from(n))), listed)
}

/// Trust std's strip (`FdStrip::apply` on Darwin,
/// `library/std/src/sys/process/unix/inherit.rs`) as the probe's
/// [`Call::CloexecFrom`]: list this process's own table into a stack buffer,
/// then `F_GETFD` and, where `FD_CLOEXEC` is clear, `F_SETFD` on every listed
/// descriptor from `first` up. A listing that fails or fills the buffer (std
/// would then probe numbers up to its bound) is `Errno(-5)`, which the model
/// never answers.
pub(super) fn real_cloexec_from(first: c_int) -> SysResult {
    const SLOTS: usize = 512;
    let mut buf = [libc::proc_fdinfo { proc_fd: -1, proc_fdtype: 0 }; SLOTS];
    let bytes = c_int::try_from(SLOTS * std::mem::size_of::<libc::proc_fdinfo>()).unwrap_or(0);
    // SAFETY: `buf` is `bytes` writable bytes of `proc_fdinfo`.
    let n = unsafe {
        libc::proc_pidinfo(
            libc::getpid(),
            introspect::PROC_PIDLISTFDS,
            0,
            buf.as_mut_ptr().cast(),
            bytes,
        )
    };
    let count = usize::try_from(n).unwrap_or(0) / std::mem::size_of::<libc::proc_fdinfo>();
    if count == 0 || count >= SLOTS {
        return Err(Errno(-5));
    }
    for e in buf.iter().take(count) {
        if e.proc_fd < first {
            continue;
        }
        // SAFETY: integer arguments only; a closed number is a harmless -1.
        unsafe {
            let flags = libc::fcntl(e.proc_fd, libc::F_GETFD);
            if flags >= 0 && flags & libc::FD_CLOEXEC == 0 {
                libc::fcntl(e.proc_fd, libc::F_SETFD, flags | libc::FD_CLOEXEC);
            }
        }
    }
    Ok(Ret::Int(0))
}

/// `sysctlbyname(name, buf, &oldlen, NULL, 0)` into a 16-byte buffer. A
/// success that does not report 4 bytes is `Errno(-4)`, which the model
/// never answers.
pub(super) fn real_sysctl(name: &str, oldlen: u64) -> SysResult {
    let mut n = [0u8; 64];
    if name.len() >= n.len() {
        return Err(Errno(-1));
    }
    n[..name.len()].copy_from_slice(name.as_bytes());
    let mut buf = [0u8; 16];
    let mut len = usize::try_from(oldlen).unwrap_or(0).min(buf.len());
    // SAFETY: a NUL-terminated name, a live buffer of at least `len` bytes,
    // and `len` itself; nothing is written to the sysctl.
    let rc = unsafe {
        libc::sysctlbyname(
            n.as_ptr().cast(),
            buf.as_mut_ptr().cast(),
            &mut len,
            std::ptr::null_mut(),
            0,
        )
    };
    if rc < 0 {
        return Err(errno());
    }
    if len != 4 {
        return Err(Errno(-4));
    }
    Ok(Ret::Int(i64::from(i32::from_ne_bytes([buf[0], buf[1], buf[2], buf[3]]))))
}

/// This process's thread count (`PROC_PIDTASKINFO`'s `pti_threadnum`).
fn thread_count() -> i64 {
    // SAFETY: an all-zero proc_taskinfo is valid.
    let mut ti: libc::proc_taskinfo = unsafe { std::mem::zeroed() };
    let size = c_int::try_from(std::mem::size_of::<libc::proc_taskinfo>()).unwrap_or(0);
    // SAFETY: `ti` is `size` writable bytes.
    let n = unsafe {
        libc::proc_pidinfo(libc::getpid(), libc::PROC_PIDTASKINFO, 0, (&raw mut ti).cast(), size)
    };
    if n == size { i64::from(ti.pti_threadnum) } else { -1 }
}

/// The listing's record line, for a fork child's record file.
pub(super) fn encode_listing(i: usize, listed: &[(i32, u32)]) -> String {
    let mut s = format!("L {i}");
    for (fd, ty) in listed {
        s.push_str(&format!(" {fd}/{ty}"));
    }
    s.push('\n');
    s
}

pub(super) fn decode_listing(rest: &str) -> Vec<(i32, u32)> {
    rest.split_whitespace()
        .filter_map(|e| {
            let (fd, ty) = e.split_once('/')?;
            Some((fd.parse().ok()?, ty.parse().ok()?))
        })
        .collect()
}

fn stdio(plan: StdioPlan) -> std::process::Stdio {
    match plan {
        StdioPlan::Inherit => std::process::Stdio::inherit(),
        StdioPlan::Null => std::process::Stdio::null(),
        StdioPlan::Piped => std::process::Stdio::piped(),
    }
}

fn configure(
    cmd: &mut std::process::Command,
    real: &Real<'_>,
    user: [Option<StdioPlan>; 3],
    hooks: Option<&[Call<Operand>]>,
) {
    use std::os::unix::process::CommandExt;
    if let Some(p) = user[0] {
        cmd.stdin(stdio(p));
    }
    if let Some(p) = user[1] {
        cmd.stdout(stdio(p));
    }
    if let Some(p) = user[2] {
        cmd.stderr(stdio(p));
    }
    if let Some(hooks) = hooks {
        let hooks: Vec<Call> =
            hooks.iter().filter_map(|h| resolve_call(h, &real.results)).collect();
        let sock = real.sock.clone();
        let ns = real.ns.clone();
        // SAFETY: the closure runs dup2/fcntl through `real_call` (no
        // allocation for those arms) in the child.
        unsafe {
            cmd.pre_exec(move || {
                for h in &hooks {
                    let _ = super::real_call(h, &sock, &ns);
                }
                Ok(())
            });
        }
    }
}

/// A root-actor X call on the real host.
pub(super) fn real_std(real: &mut Real<'_>, x: &XStd, i: usize) -> SysResult {
    let io = |e: std::io::Error| Errno(e.raw_os_error().unwrap_or(0));
    match x {
        XStd::DropFd(op) => {
            let fd = op.resolve(&[], &real.results).unwrap_or(-1);
            // SAFETY: the probe owns `fd` and never uses it again.
            drop(unsafe { OwnedFd::from_raw_fd(fd) });
            Ok(Ret::Int(0))
        }
        XStd::ThreadSpawn => {
            let h = std::thread::spawn(|| {
                loop {
                    std::thread::park();
                }
            });
            std::mem::forget(h);
            Ok(Ret::Int(thread_count()))
        }
        XStd::Output { user, hooks }
        | XStd::Status { user, hooks }
        | XStd::StatusInheritAll { user, hooks } => {
            let mut cmd = real.reporter_command(i);
            if matches!(x, XStd::StatusInheritAll { .. }) {
                use std::os::unix::process::CommandExt;
                cmd.inherit_all_fds();
            }
            configure(&mut cmd, real, *user, hooks.as_deref());
            let ok = if matches!(x, XStd::Output { .. }) {
                cmd.output().map(|o| o.status.success()).map_err(io)?
            } else {
                cmd.status().map(|s| s.success()).map_err(io)?
            };
            // The reporter exits 0 once it has written its table.
            if ok { Ok(Ret::Int(0)) } else { Err(Errno(-2)) }
        }
        XStd::Exec { .. } => Err(Errno(0)),
    }
}

/// A child-actor X call (inside `Real::child_block`); returns only when the
/// exec failed.
pub(super) fn child_std(real: &mut Real<'_>, k: usize, i: usize, x: &XStd) {
    use std::os::unix::process::CommandExt;
    // `validate` admits only `Exec` in a child block.
    let XStd::Exec { user, hooks, missing } = x else {
        return;
    };
    let mut cmd =
        if *missing { std::process::Command::new(MISSING) } else { real.reporter_command(i) };
    configure(&mut cmd, real, *user, hooks.as_deref());
    if !*missing {
        real.append(k, "BLOCKEND\n");
    }
    let e = cmd.exec();
    let r = Err(Errno(e.raw_os_error().unwrap_or(0)));
    real.results[i] = r;
    real.record(k, i, Some(&r));
    if !*missing {
        // SAFETY: leaving the child.
        unsafe { libc::_exit(99) };
    }
}

// =============================================================================
// Model replay
// =============================================================================

fn resolve(call: &Call<Operand>, args: &[i32], results: &[SysResult]) -> Option<Call> {
    let mut bad = false;
    let out = call.map(|op| {
        op.resolve(args, results).unwrap_or_else(|| {
            bad = true;
            -1
        })
    });
    if bad { None } else { Some(out) }
}

/// Compare a [`Call::ListOwnFds`]'s real entries with the spec's listing of
/// the host before the call.
pub(super) fn check_listing(
    spec: &dyn Spec,
    h: &Host,
    pid: Pid,
    bytes: i32,
    rec: &Rec,
) -> Result<(), String> {
    let Some(real) = &rec.listing else {
        return Ok(());
    };
    let model = match spec.listing(h, pid, bytes) {
        Ok(Ok(l)) => l,
        Ok(Err(e)) => return Err(format!("listing: model {e}, kernel listed {real:?}")),
        Err(refusal) => return Err(format!("listing refused: {refusal}")),
    };
    let same = model.len() == real.len()
        && model
            .iter()
            .zip(real)
            .all(|(m, (fd, ty))| m.fd == *fd && m.fdtype.is_none_or(|t| t == *ty));
    if !same {
        let m: Vec<String> = model
            .iter()
            .map(|e| format!("{}/{}", e.fd, e.fdtype.map_or("?".to_string(), |t| t.to_string())))
            .collect();
        let k: Vec<String> = real.iter().map(|(fd, ty)| format!("{fd}/{ty}")).collect();
        return Err(format!("listing: model [{}], kernel [{}]", m.join(" "), k.join(" ")));
    }
    Ok(())
}

/// The model side of an X call: `(host after, result, child observation
/// already compared)`.
pub(super) fn replay(
    spec: &dyn Spec,
    h: &Host,
    pid: Pid,
    x: &XStd,
    results: &[SysResult],
    rec: &Rec,
    i: usize,
) -> Result<(Host, SysResult, bool), String> {
    match x {
        XStd::DropFd(op) => {
            let fd = op.resolve(&[], results).ok_or("unresolved operand")?;
            let mut row = std_summaries::std_drop_fd();
            spec.mutate_row(&mut row);
            let host = run_row(spec, h, pid, &row, &[fd])?;
            Ok((host, Ok(Ret::Int(0)), false))
        }
        XStd::ThreadSpawn => {
            let mut row = std_summaries::std_thread_spawn();
            spec.mutate_row(&mut row);
            let host = run_row(spec, h, pid, &row, &[])?;
            let threads = host.proc(pid).map_or(-1, |p| i64::from(p.threads));
            Ok((host, Ok(Ret::Int(threads)), false))
        }
        XStd::Output { user, hooks }
        | XStd::Status { user, hooks }
        | XStd::StatusInheritAll { user, hooks }
        | XStd::Exec { user, hooks, .. } => {
            let mut cfg = CmdCfg {
                op: x.op().ok_or("not a command")?,
                user: *user,
                hooks: hooks.as_ref().map(|hs| lit_hooks(hs, results)).transpose()?,
            };
            spec.mutate_cfg(&mut cfg);
            let mut shape = CommandShape {
                pre_exec: cfg.hooks.is_some(),
                inherit_all_fds: matches!(x, XStd::StatusInheritAll { .. }),
                ..CommandShape::default()
            };
            spec.mutate_shape(&mut shape);
            let hook_lists: Vec<Vec<Call<Operand>>> = cfg.hooks.clone().into_iter().collect();
            let mut cr = command_row(cfg.op, cfg.user, &shape, &hook_lists)?;
            spec.mutate_command(&mut cr);
            if cr.spawn.is_some() {
                spec.mutate_spawn(&mut cr.row);
            }
            match x {
                XStd::Exec { missing, .. } => {
                    let (host, result) = run_exec(spec, h, pid, &cr, *missing)?;
                    Ok((host, result, false))
                }
                _ => {
                    let host = run_command(spec, h, pid, &cr, rec, i)?;
                    Ok((host, Ok(Ret::Int(0)), true))
                }
            }
        }
    }
}

/// A command's configuration, before its row is built (what a `Cfg`
/// mutant changes).
pub(super) struct CmdCfg {
    pub op: CommandOp,
    pub user: [Option<StdioPlan>; 3],
    pub hooks: Option<Vec<Call<Operand>>>,
}

fn lit_hooks(hooks: &[Call<Operand>], results: &[SysResult]) -> Result<Vec<Call<Operand>>, String> {
    hooks
        .iter()
        .map(|h| resolve(h, &[], results).map(|c| c.map(|v| Operand::Lit(*v))))
        .collect::<Option<_>>()
        .ok_or_else(|| "unresolved hook operand".to_string())
}

/// A fixed row, straight through.
fn run_row(
    spec: &dyn Spec,
    h: &Host,
    pid: Pid,
    row: &StdRow,
    args: &[i32],
) -> Result<Host, String> {
    let trace = script::run(spec, h, pid, &row.program, args)
        .map_err(|e| format!("std row {}: {e:?}", row.id))?;
    Ok(trace.last().map_or_else(|| h.clone(), |t| t.host.clone()))
}

fn step_err(row: &StdRow, k: usize, e: impl std::fmt::Display) -> String {
    format!("std row {} step {k}: {e}", row.id)
}

/// `Command::output`/`status`: the row's program, where a step that blocks
/// (a read or a wait on the reporter) lets the reporter exit — the one
/// environment step of the real run — and is retried. The reporter
/// snapshots its table at some moment between its exec
/// ([`CommandRow::image`]) and its exit while the parent runs on (closing
/// the child's stdio, dropping a stdin end — which a pipe read end in the
/// child then sees as end-of-file), so its table must equal the model's at
/// SOME state of that window.
fn run_command(
    spec: &dyn Spec,
    h: &Host,
    root: Pid,
    cr: &CommandRow,
    rec: &Rec,
    i: usize,
) -> Result<Host, String> {
    let row = &cr.row;
    let spawn = cr.spawn.ok_or("a command row without a spawn step")?;
    let mut host = h.clone();
    let mut results: Vec<SysResult> = Vec::new();
    let mut exited = false;
    let mut window: Vec<Host> = Vec::new();
    let program_err = |k: usize, e: script::ProgramError| step_err(row, k, format!("{e:?}"));
    for (k, ps) in row.program.iter().enumerate() {
        let pid = script::actor_pid(ps.actor, root, &results)
            .ok_or_else(|| step_err(row, k, "no such actor"))?;
        // A step std makes only on some descriptor numbers ([`script::When`]).
        if let Some(v) = ps.skipped(k, &[], &results).map_err(|e| program_err(k, e))? {
            results.push(Ok(Ret::Int(i64::from(v))));
            ps.check_assumed(k, &[], &results).map_err(|e| program_err(k, e))?;
            if k >= cr.image && !exited {
                window.push(host.clone());
            }
            continue;
        }
        let call =
            resolve(&ps.call, &[], &results).ok_or_else(|| step_err(row, k, "unresolved"))?;
        let s = match spec.step(&host, pid, &call, ps.oracle) {
            Err(Refusal::Blocks) if !exited => {
                let child = script::actor_pid(Actor::Child(spawn), root, &results)
                    .ok_or_else(|| step_err(row, k, "blocks with no child"))?;
                let exit = Call::Exit { status: 0 };
                host = spec
                    .step(&host, child, &exit, Oracle::Nominal)
                    .map_err(|e| step_err(row, k, format!("the reporter's exit: {e}")))?
                    .host;
                exited = true;
                spec.step(&host, pid, &call, ps.oracle)
                    .map_err(|e| step_err(row, k, format!("after the reporter exited: {e}")))?
            }
            other => other.map_err(|e| step_err(row, k, e))?,
        };
        host = s.host;
        results.push(s.result);
        if let Err(e) = s.result {
            return Err(step_err(row, k, format!("{call:?} failed {e}; the real call succeeded")));
        }
        ps.check_assumed(k, &[], &results).map_err(|e| program_err(k, e))?;
        if k >= cr.image && !exited {
            window.push(host.clone());
        }
    }
    let child = script::actor_pid(Actor::Child(spawn), root, &results)
        .ok_or_else(|| format!("std row {}: no child", row.id))?;
    for (actor, fds) in &rec.obs {
        if *actor != Actor::Child(i) {
            continue;
        }
        let view = [(child, fds.as_slice())];
        if !window.iter().any(|w| compare_obs(w, &view).is_ok()) {
            let at_exec = window.first().map_or_else(
                || "no state between exec and exit".to_string(),
                |w| compare_obs(w, &view).err().unwrap_or_default(),
            );
            return Err(format!(
                "the reporter's table matches no model state between its exec and its exit \
                 (at the exec: {at_exec})"
            ));
        }
    }
    Ok(host)
}

/// `CommandExt::exec` by `pid`: the row, with the `execvp` failing `ENOENT`
/// and the error tail run when `missing`.
fn run_exec(
    spec: &dyn Spec,
    h: &Host,
    pid: Pid,
    cr: &CommandRow,
    missing: bool,
) -> Result<(Host, SysResult), String> {
    let mut program: Vec<ProgramStep> = cr.row.program.clone();
    if missing {
        if let Some(ps) = program.get_mut(cr.image) {
            ps.oracle = Oracle::Fail(Errno::ENOENT);
        }
        program.extend(cr.error_tail.iter().map(|c| ProgramStep::root(c.clone())));
    }
    let trace = script::run(spec, h, pid, &program, &[])
        .map_err(|e| format!("std row {}: {e:?}", cr.row.id))?;
    let host = trace.last().map_or_else(|| h.clone(), |t| t.host.clone());
    let result = trace.get(cr.image).map_or(Err(Errno(0)), |t| t.result);
    Ok((host, result))
}

// =============================================================================
// Spec mutants
// =============================================================================

type ListFn = fn(&Host, Pid, i32) -> Result<Result<Vec<ListedFd>, Errno>, Refusal>;

/// How an X3a mutant departs from the real spec.
pub(super) enum XKind {
    /// A clause (`Semantics::step`).
    Step(MutFn),
    /// The listing ([`Semantics::listing`]).
    Listing(ListFn),
    /// A fixed std row, by id.
    Row(&'static str, fn(&mut StdRow)),
    /// A command's configuration before its row is built.
    Cfg(fn(&mut CmdCfg)),
    /// A built command row, by op.
    Command(CommandOp, fn(&mut CommandRow)),
    /// A `Command`'s shape before its row is built (every op).
    Shape(fn(&mut CommandShape)),
    /// Every built row that spawns: STD-SPAWN-FORK/POSIX and the spawn
    /// inside STD-COMMAND-OUTPUT/STATUS.
    Spawn(fn(&mut StdRow)),
}

pub(super) struct XMutant {
    pub name: &'static str,
    pub clause: &'static str,
    pub kind: XKind,
}

impl Semantics for XMutant {
    fn step_raw(
        &self,
        host: &Host,
        pid: Pid,
        call: &Call,
        oracle: Oracle,
    ) -> Result<Step, Refusal> {
        match self.kind {
            XKind::Step(f) => f(host, pid, call, oracle),
            _ => step(host, pid, call, oracle),
        }
    }

    fn listing(
        &self,
        host: &Host,
        pid: Pid,
        bytes: i32,
    ) -> Result<Result<Vec<ListedFd>, Errno>, Refusal> {
        match self.kind {
            XKind::Listing(f) => f(host, pid, bytes),
            _ => introspect::listing(host, pid, bytes),
        }
    }
}

impl Spec for XMutant {
    fn mutate_row(&self, row: &mut StdRow) {
        if let XKind::Row(id, f) = self.kind
            && row.id == id
        {
            f(row);
        }
    }

    fn mutate_cfg(&self, cfg: &mut CmdCfg) {
        if let XKind::Cfg(f) = self.kind {
            f(cfg);
        }
    }

    fn mutate_command(&self, cr: &mut CommandRow) {
        if let XKind::Command(op, f) = self.kind
            && cr.op == op
        {
            f(cr);
        }
    }

    fn mutate_shape(&self, shape: &mut CommandShape) {
        if let XKind::Shape(f) = self.kind {
            f(shape);
        }
    }

    fn mutate_spawn(&self, row: &mut StdRow) {
        if let XKind::Spawn(f) = self.kind {
            f(row);
        }
    }
}

/// The step index of the first step matching `f`.
fn find_step(row: &StdRow, f: impl Fn(&ProgramStep) -> bool) -> Option<usize> {
    row.program.iter().position(f)
}

/// Make `CloexecFrom` with `first` one higher (and so leave `first` itself
/// unmarked).
fn cloexec_from_skipping_first(h: &Host, p: Pid, c: &Call, o: Oracle) -> Result<Step, Refusal> {
    match c {
        Call::CloexecFrom { first } => step(h, p, &Call::CloexecFrom { first: first + 1 }, o),
        _ => step(h, p, c, o),
    }
}

/// `CloexecFrom` that CLOSES every descriptor from `first` up instead of
/// marking it.
fn cloexec_from_closing(h: &Host, p: Pid, c: &Call, o: Oracle) -> Result<Step, Refusal> {
    let Call::CloexecFrom { first } = c else {
        return step(h, p, c, o);
    };
    let fds: Vec<i32> = h
        .proc(p)
        .map(|pr| pr.table.range(*first..).map(|(fd, _)| *fd).collect())
        .unwrap_or_default();
    let mut host = h.clone();
    for fd in fds {
        host = step(&host, p, &Call::Close { fd }, Oracle::Nominal)?.host;
    }
    Ok(Step { host, result: Ok(Ret::Int(0)) })
}

/// A call with no effect, standing in for a removed step so that later
/// steps' `Ret` operands keep their indices.
fn noop() -> Call<Operand> {
    Call::Fcntl { fd: Operand::Lit(0), cmd: darwin::F_GETFD, arg: 0 }
}

/// The descriptors a command row's child `dup2`s onto 0..=2 (posix actions
/// or fork-child steps).
fn child_stdio(cr: &CommandRow) -> Vec<Operand> {
    let mut out = Vec::new();
    for ps in &cr.row.program {
        match &ps.call {
            Call::Spawn { actions, .. } => {
                for a in actions {
                    if let trust_platform::FileAction::Dup2 { from, to: Operand::Lit(n) }
                    | trust_platform::FileAction::PlaceStdio { from, to: Operand::Lit(n) } = a
                        && (0..=2).contains(n)
                    {
                        out.push(*from);
                    }
                }
            }
            Call::Dup2 { from, to: Operand::Lit(n) }
            | Call::StdPlaceFd { from, to: Operand::Lit(n) }
                if ps.actor != Actor::Root && (0..=2).contains(n) =>
            {
                out.push(*from);
            }
            _ => {}
        }
    }
    out
}

fn darwin_listing(h: &Host, p: Pid, bytes: i32) -> Result<Result<Vec<ListedFd>, Errno>, Refusal> {
    introspect::listing(h, p, bytes)
}

/// The whole table's listing (as if the buffer were unbounded).
fn all_listed(h: &Host, p: Pid) -> Result<Vec<ListedFd>, Refusal> {
    Ok(introspect::listing(h, p, i32::MAX)?.unwrap_or_default())
}

#[allow(clippy::too_many_lines)]
pub(super) fn mutants() -> Vec<XMutant> {
    vec![
        XMutant {
            name: "list-own-fds-descending",
            clause: "proc_pidinfo PROC_PIDLISTFDS",
            kind: XKind::Listing(|h, p, bytes| {
                Ok(darwin_listing(h, p, bytes)?.map(|mut l| {
                    l.reverse();
                    l
                }))
            }),
        },
        XMutant {
            name: "list-own-fds-keeps-highest",
            clause: "proc_pidinfo PROC_PIDLISTFDS",
            kind: XKind::Listing(|h, p, bytes| {
                let n = darwin_listing(h, p, bytes)?.map(|l| l.len());
                let all = all_listed(h, p)?;
                Ok(n.map(|n| all[all.len() - n..].to_vec()))
            }),
        },
        XMutant {
            name: "list-own-fds-omits-kqueue",
            clause: "proc_pidinfo PROC_PIDLISTFDS",
            kind: XKind::Listing(|h, p, bytes| {
                Ok(darwin_listing(h, p, bytes)?.map(|l| {
                    l.into_iter()
                        .filter(|e| e.fdtype != Some(introspect::PROX_FDTYPE_KQUEUE))
                        .collect()
                }))
            }),
        },
        XMutant {
            name: "list-own-fds-only-inheritable",
            clause: "proc_pidinfo PROC_PIDLISTFDS",
            kind: XKind::Listing(|h, p, bytes| {
                Ok(darwin_listing(h, p, bytes)?.map(|l| {
                    l.into_iter().filter(|e| h.entry(p, e.fd).is_some_and(|x| !x.cloexec)).collect()
                }))
            }),
        },
        XMutant {
            name: "list-own-fds-capped-at-soft-rlimit",
            clause: "proc_pidinfo PROC_PIDLISTFDS",
            kind: XKind::Listing(|h, p, bytes| {
                let soft = h.proc(p).map_or(0, |pr| pr.nofile.soft);
                Ok(darwin_listing(h, p, bytes)?.map(|l| {
                    l.into_iter().filter(|e| u64::try_from(e.fd).unwrap_or(0) < soft).collect()
                }))
            }),
        },
        XMutant {
            name: "list-own-fds-counts-entries",
            clause: "proc_pidinfo PROC_PIDLISTFDS",
            kind: XKind::Step(|h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let (Call::ListOwnFds { .. }, Ok(Ret::Int(b))) = (c, s.result) {
                    return Ok(Step { host: s.host, result: Ok(Ret::Int(b / 8)) });
                }
                Ok(s)
            }),
        },
        XMutant {
            name: "list-own-fds-short-buffer-is-empty",
            clause: "proc_pidinfo PROC_PIDLISTFDS",
            kind: XKind::Step(|h, p, c, o| {
                let s = step(h, p, c, o)?;
                if matches!(c, Call::ListOwnFds { .. }) && s.result == Err(Errno::ENOMEM) {
                    return Ok(Step { host: s.host, result: Ok(Ret::Int(0)) });
                }
                Ok(s)
            }),
        },
        XMutant {
            name: "sysctl-reads-soft-rlimit",
            clause: "sysctlbyname kern.maxfilesperproc",
            kind: XKind::Step(|h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let (Call::Sysctl { .. }, Ok(Ret::Int(_))) = (c, s.result) {
                    let soft = h.proc(p).map_or(0, |pr| pr.nofile.soft);
                    let soft = i64::try_from(soft).unwrap_or(i64::MAX);
                    return Ok(Step { host: s.host, result: Ok(Ret::Int(soft)) });
                }
                Ok(s)
            }),
        },
        XMutant {
            name: "sysctl-short-buffer-succeeds",
            clause: "sysctlbyname kern.maxfilesperproc",
            kind: XKind::Step(|h, p, c, o| match c {
                Call::Sysctl { name, oldlen } if *oldlen < 4 => {
                    step(h, p, &Call::Sysctl { name: name.clone(), oldlen: 4 }, o)
                }
                _ => step(h, p, c, o),
            }),
        },
        XMutant {
            name: "thread-create-not-counted",
            clause: "pthread_create",
            kind: XKind::Step(|h, p, c, o| {
                if matches!(c, Call::ThreadCreate) {
                    return Ok(Step { host: h.clone(), result: Ok(Ret::Int(0)) });
                }
                step(h, p, c, o)
            }),
        },
        XMutant {
            name: "std-drop-fd-elided",
            clause: "STD-DROP-FD",
            kind: XKind::Row("STD-DROP-FD", |row| row.program.clear()),
        },
        XMutant {
            name: "std-thread-spawn-no-thread",
            clause: "STD-THREAD-SPAWN",
            kind: XKind::Row("STD-THREAD-SPAWN", |row| row.program.clear()),
        },
        XMutant {
            name: "std-output-stdin-inherited",
            clause: "STD-COMMAND-OUTPUT",
            kind: XKind::Cfg(|cfg| {
                if cfg.op == CommandOp::Output && cfg.user[0].is_none() {
                    cfg.user[0] = Some(StdioPlan::Inherit);
                }
            }),
        },
        XMutant {
            name: "std-output-keeps-child-ends",
            clause: "STD-COMMAND-OUTPUT",
            kind: XKind::Command(CommandOp::Output, |cr| {
                let theirs = child_stdio(cr);
                let from = cr.spawn.map_or(0, |s| s + 1);
                for ps in cr.row.program.iter_mut().skip(from) {
                    if ps.actor == Actor::Root
                        && matches!(&ps.call, Call::Close { fd } if theirs.contains(fd))
                    {
                        ps.call = noop();
                    }
                }
            }),
        },
        XMutant {
            name: "std-status-no-wait",
            clause: "STD-COMMAND-STATUS",
            kind: XKind::Command(CommandOp::Status, |cr| {
                for ps in &mut cr.row.program {
                    if ps.actor == Actor::Root && matches!(ps.call, Call::Waitpid { .. }) {
                        ps.call = noop();
                    }
                }
            }),
        },
        XMutant {
            name: "std-status-stdin-null",
            clause: "STD-COMMAND-STATUS",
            kind: XKind::Cfg(|cfg| {
                if cfg.op == CommandOp::Status && cfg.user[0].is_none() {
                    cfg.user[0] = Some(StdioPlan::Null);
                }
            }),
        },
        XMutant {
            name: "std-exec-no-stdio-dup2",
            clause: "STD-COMMANDEXT-EXEC",
            kind: XKind::Command(CommandOp::Exec, |cr| {
                for ps in &mut cr.row.program {
                    if matches!(
                        ps.call,
                        Call::Dup2 { to: Operand::Lit(0..=2), .. }
                            | Call::StdPlaceFd { to: Operand::Lit(0..=2), .. }
                    ) {
                        ps.call = noop();
                    }
                }
            }),
        },
        XMutant {
            name: "std-exec-ignores-pre-exec",
            clause: "STD-COMMANDEXT-EXEC",
            kind: XKind::Cfg(|cfg| {
                if cfg.op == CommandOp::Exec {
                    cfg.hooks = None;
                }
            }),
        },
        XMutant {
            name: "std-output-ignores-pre-exec",
            clause: "STD-COMMAND-OUTPUT (fork path)",
            kind: XKind::Cfg(|cfg| {
                if cfg.op == CommandOp::Output {
                    cfg.hooks = None;
                }
            }),
        },
        XMutant {
            name: "std-exec-failure-keeps-child-stdio",
            clause: "STD-COMMANDEXT-EXEC",
            kind: XKind::Command(CommandOp::Exec, |cr| cr.error_tail.clear()),
        },
        XMutant {
            name: "std-spawn-upstream-inheritance",
            clause: "STD-SPAWN-FORK/POSIX, STD-COMMAND-OUTPUT/STATUS (SP-1)",
            kind: XKind::Shape(|shape| shape.std = CommandStd::Upstream),
        },
        XMutant {
            name: "std-spawn-fork-no-strip",
            clause: "STD-SPAWN-FORK (SP-1 strip)",
            kind: XKind::Spawn(|row| {
                for ps in &mut row.program {
                    if matches!(ps.call, Call::CloexecFrom { .. } | Call::StdMarkCloexec) {
                        ps.call = noop();
                    }
                }
            }),
        },
        XMutant {
            name: "std-spawn-fork-strip-after-pre-exec",
            clause: "STD-SPAWN-FORK (SP-1 strip)",
            kind: XKind::Spawn(|row| {
                let strip = find_step(row, |ps| {
                    matches!(ps.call, Call::CloexecFrom { .. } | Call::StdMarkCloexec)
                });
                let exec =
                    find_step(row, |ps| ps.actor != Actor::Root && matches!(ps.call, Call::Exec));
                if let (Some(s), Some(e)) = (strip, exec)
                    && s < e
                {
                    row.program[s..e].rotate_left(1);
                }
            }),
        },
        XMutant {
            name: "std-spawn-fork-status-end-not-moved",
            clause: "STD-SPAWN-FORK (SP-1 status pipe above 9)",
            kind: XKind::Spawn(|row| {
                for ps in &mut row.program {
                    if let Call::StdStatusFd { fd } = ps.call {
                        ps.when = Some(script::When {
                            guard: script::Guard::Below(Operand::Lit(0), i32::MIN),
                            otherwise: fd,
                        });
                    }
                    if let Some(w) = &mut ps.when {
                        w.guard = script::Guard::Below(Operand::Lit(0), i32::MIN);
                    }
                }
            }),
        },
        XMutant {
            name: "std-spawn-posix-no-cloexec-default",
            clause: "STD-SPAWN-POSIX (SP-1 CLOEXEC_DEFAULT)",
            kind: XKind::Spawn(|row| {
                for ps in &mut row.program {
                    if let Call::Spawn { flags, .. } = &mut ps.call {
                        *flags &= !darwin::POSIX_SPAWN_CLOEXEC_DEFAULT;
                    }
                }
            }),
        },
        XMutant {
            name: "std-spawn-posix-inherited-stdio-unnamed",
            clause: "STD-SPAWN-POSIX (SP-1 addinherit_np)",
            kind: XKind::Spawn(|row| {
                for ps in &mut row.program {
                    if let Call::Spawn { actions, .. } = &mut ps.call {
                        actions.retain(|a| {
                            !matches!(
                                a,
                                trust_platform::FileAction::Inherit { .. }
                                    | trust_platform::FileAction::InheritIf { .. }
                            )
                        });
                    }
                }
            }),
        },
        XMutant {
            name: "cloexec-from-no-effect",
            clause: "Trust std strip (CloexecFrom)",
            kind: XKind::Step(|h, p, c, o| {
                if matches!(c, Call::CloexecFrom { .. }) {
                    return Ok(Step { host: h.clone(), result: Ok(Ret::Int(0)) });
                }
                step(h, p, c, o)
            }),
        },
        XMutant {
            name: "cloexec-from-skips-first",
            clause: "Trust std strip (CloexecFrom)",
            kind: XKind::Step(cloexec_from_skipping_first),
        },
        XMutant {
            name: "cloexec-from-closes",
            clause: "Trust std strip (CloexecFrom)",
            kind: XKind::Step(cloexec_from_closing),
        },
        XMutant {
            name: "spawn-row-stdout-dup2-dropped",
            clause: "STD-COMMAND-OUTPUT (posix_spawn adddup2)",
            kind: XKind::Command(CommandOp::Output, |cr| {
                for ps in &mut cr.row.program {
                    if let Call::Spawn { actions, .. } = &mut ps.call {
                        actions.retain(|a| {
                            !matches!(
                                a,
                                trust_platform::FileAction::Dup2 { to: Operand::Lit(1), .. }
                                    | trust_platform::FileAction::PlaceStdio {
                                        to: Operand::Lit(1),
                                        ..
                                    }
                            )
                        });
                    }
                }
            }),
        },
        XMutant {
            name: "std-sp1-strip-elided",
            clause: "STD-COMMAND-STATUS SP1",
            kind: XKind::Command(CommandOp::Status, |cr| {
                for ps in &mut cr.row.program {
                    if matches!(ps.call, Call::StdMarkCloexec) {
                        ps.call = noop();
                    }
                    if let Call::Spawn { flags, .. } = &mut ps.call {
                        *flags &= !darwin::POSIX_SPAWN_CLOEXEC_DEFAULT;
                    }
                }
            }),
        },
        XMutant {
            name: "std-status-old-writer-not-closed",
            clause: "STD-COMMAND-STATUS relocation",
            kind: XKind::Command(CommandOp::Status, |cr| {
                for ps in &mut cr.row.program {
                    if matches!(ps.call, Call::StdCloseMovedStatus { .. }) {
                        ps.call = noop();
                    }
                }
            }),
        },
        XMutant {
            name: "std-same-number-stdio-is-raw-dup2",
            clause: "STD-COMMAND-STATUS placement",
            kind: XKind::Command(CommandOp::Status, |cr| {
                for ps in &mut cr.row.program {
                    if let Call::StdPlaceFd { from, to } = ps.call {
                        ps.call = Call::Dup2 { from, to };
                    }
                    if let Call::Spawn { actions, .. } = &mut ps.call {
                        for a in actions {
                            if let trust_platform::FileAction::PlaceStdio { from, to } = *a {
                                *a = trust_platform::FileAction::Dup2 { from, to };
                            }
                        }
                    }
                }
            }),
        },
        XMutant {
            name: "std-posix-inherits-closed-stdio",
            clause: "STD-COMMAND-STATUS passes_exec",
            kind: XKind::Command(CommandOp::Status, |cr| {
                for ps in &mut cr.row.program {
                    if let Call::Spawn { actions, .. } = &mut ps.call {
                        for a in actions {
                            if let trust_platform::FileAction::InheritIf { fd, .. } = *a {
                                *a = trust_platform::FileAction::Inherit { fd };
                            }
                        }
                    }
                }
            }),
        },
    ]
}

// =============================================================================
// Harness checks
// =============================================================================

/// STD-FILE-LOCK's premise, on the real std: `File::lock` is `flock` on the
/// open file DESCRIPTION — it sets `FHASLOCK` (0x4000) in `F_GETFL`; a
/// second description of the same file conflicts even within this process
/// (a POSIX record lock would not); `LOCK_UN` through a duplicate releases
/// it.
pub(super) fn std_file_lock_is_flock(env: &Env) -> Result<String, String> {
    use std::fs::{File, TryLockError};
    const FHASLOCK: c_int = 0x4000;
    let path = env.dir.join("std-file-lock.probe");
    let e = |what: &str, err: std::io::Error| format!("{what}: {err}");
    let a = File::create(&path).map_err(|err| e("create", err))?;
    a.lock().map_err(|err| e("File::lock", err))?;
    // SAFETY: a plain descriptor query.
    let fl = unsafe { libc::fcntl(a.as_raw_fd(), libc::F_GETFL) };
    if fl < 0 || fl & FHASLOCK == 0 {
        return Err(format!("after File::lock, F_GETFL is {fl:#x}: FHASLOCK clear, not flock"));
    }
    let b = File::open(&path).map_err(|err| e("open", err))?;
    match b.try_lock() {
        Err(TryLockError::WouldBlock) => {}
        other => {
            return Err(format!(
                "a second description's try_lock answered {other:?}, not WouldBlock: not a \
                 description-level lock"
            ));
        }
    }
    let a2 = a.try_clone().map_err(|err| e("try_clone", err))?;
    a2.unlock().map_err(|err| e("unlock through the duplicate", err))?;
    b.try_lock()
        .map_err(|err| format!("after unlock through a duplicate, try_lock answered {err:?}"))?;
    b.unlock().map_err(|err| e("unlock", err))?;
    drop((a, a2, b));
    let _ = std::fs::remove_file(&path);
    Ok("STD-FILE-LOCK: std's File::lock is the description-level flock on this host \
        (FHASLOCK set; a second description conflicts; LOCK_UN through a dup releases it) — \
        a named gap until its std row over the flock clause (in the model since \
        Trust.Platform/darwin/v1, M2) is written"
        .to_string())
}

/// The flag that runs [`long_tmpdir_run`].
pub(super) const LONG_TMPDIR_FLAG: &str = "--trust-platform-long-tmpdir";

/// The probes that bind and connect `AF_UNIX` sockets.
const SOCKET_PROBES: &[&str] = &["accept", "std-rows"];

/// Re-run the socket probes in a child of this binary whose `TMPDIR` is 200
/// characters long — past `sun_path` (104 bytes) once a file name is
/// appended, which the suite used to bind under — with a leftover socket
/// file where each probe binds.
pub(super) fn long_tmpdir_check(env: &Env) -> Result<String, String> {
    let base = env.dir.join("long-tmpdir-");
    let pad = 200usize.saturating_sub(base.as_os_str().len()).max(1);
    let mut long = base.into_os_string();
    long.push("x".repeat(pad));
    let long = PathBuf::from(long);
    std::fs::create_dir_all(&long).map_err(|e| format!("create the long TMPDIR: {e}"))?;
    let exe = std::env::current_exe().map_err(|e| format!("current_exe: {e}"))?;
    let out = std::process::Command::new(exe)
        .arg(LONG_TMPDIR_FLAG)
        .env("TMPDIR", &long)
        .output()
        .map_err(|e| format!("run the long-TMPDIR child: {e}"))?;
    let _ = std::fs::remove_dir_all(&long);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    if !out.status.success() {
        return Err(format!("the long-TMPDIR run failed ({}):\n{text}", out.status));
    }
    Ok(text.lines().last().unwrap_or("").to_string())
}

/// The long-`TMPDIR` child: the socket probes, Darwin only, each with a stale
/// socket file where it binds.
pub(super) fn long_tmpdir_run() -> c_int {
    let len = std::env::temp_dir().as_os_str().len();
    if len < 200 {
        println!("long-TMPDIR run: TMPDIR has only {len} characters");
        return 1;
    }
    let env = super::make_env();
    let old_path = env.dir.join("p0.sock").as_os_str().len();
    if old_path < 104 {
        println!(
            "long-TMPDIR run: the old socket path ({old_path} bytes) would still fit sun_path"
        );
        return 1;
    }
    let probes: Vec<Probe> =
        super::probes(&env).into_iter().filter(|p| SOCKET_PROBES.contains(&p.name)).collect();
    if probes.len() != SOCKET_PROBES.len() {
        println!("long-TMPDIR run: found {} of the socket probes", probes.len());
        return 1;
    }
    if let Err(e) = std::env::set_current_dir(&env.dir) {
        println!("long-TMPDIR run: chdir: {e}");
        return 1;
    }
    let mut ok = true;
    for (pi, p) in probes.iter().enumerate() {
        // An earlier run's leftover socket file where the probe binds.
        let stale = format!("p{pi}.sock");
        drop(std::os::unix::net::UnixListener::bind(&stale));
        if !std::path::Path::new(&stale).exists() {
            println!("long-TMPDIR run: could not leave a stale socket at {stale}");
            ok = false;
        }
        let lines = super::run_probe(pi, p, &[], &[], &env);
        let pass = lines.iter().any(|l| l.starts_with("PASS\tDarwin\t"))
            && !lines.iter().any(|l| l.starts_with("REALERR") || l.starts_with("FAIL\tDarwin"));
        if !pass {
            println!("long-TMPDIR run: probe {} failed: {lines:?}", p.name);
            ok = false;
        }
    }
    let _ = std::env::set_current_dir("/");
    let _ = std::fs::remove_dir_all(&env.dir);
    if !ok {
        return 1;
    }
    println!(
        "long TMPDIR ({len} characters; the old absolute socket path would be {old_path} bytes, \
         sun_path holds 104): {} socket probes pass over stale socket files",
        probes.len()
    );
    0
}
