//! Conformance of trust-platform's Darwin clauses with the real kernel, and
//! the spec-mutant kill matrix.
//!
//! Every probe is a straight-line program of platform calls. It runs ONCE on
//! the real host, in a fresh forked "probe root" process whose stdio is
//! `/dev/null`, whose other descriptors are closed and whose
//! `RLIMIT_NOFILE` soft limit is 256 — so its initial descriptor table is
//! exactly known. After every step the acting process snapshots its own
//! table (the full open set from `proc_pidinfo(PROC_PIDLISTFDS)`, and per
//! descriptor `F_GETFD`, `F_GETFL`, `fstat` identity and `poll` readability);
//! a process that execs is this same binary re-executed as a reporter that
//! snapshots its table before it opens anything. The recorded real trace is
//! then replayed on the model — `Darwin`, and every spec mutant — and
//! compared step by step: each call's result, each observed table.
//!
//! PASS criteria (the process exits non-zero otherwise):
//! * `Darwin` agrees with the kernel on every step of every probe;
//! * every spec mutant disagrees with the kernel somewhere (is KILLED).
//!
//! The binary owns `main` (no libtest): it must stay single-threaded so
//! `fork` is safe and nothing else opens descriptors while it measures, and
//! the reporter must start without std's runtime init (which would reopen a
//! closed fd 0/1/2 on /dev/null).
//!
//! The Command rows model Trust's default descriptor strip. A separate premise
//! check requires that default and the explicit `inherit_all_fds` opt-out to
//! stay distinct on both the posix_spawn and fork paths.

#![no_main]
#![feature(trust_process_inherit_fds)]

use std::collections::BTreeMap;
use std::ffi::{CStr, CString, c_char, c_int};
use std::os::fd::{BorrowedFd, IntoRawFd};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use trust_platform::call::{Call, FileAction, Oracle, Refusal, Ret, Semantics, Step, SysResult};
use trust_platform::darwin::{self, Errno};
use trust_platform::host::{Access, Host, LockMode, NodeKind, OfdKind, Peer, Pid, Rlimit};
use trust_platform::script::{self, Actor, Operand, ProgramStep};
use trust_platform::std_summaries::{self, CommandShape, StdRow, StdioPlan};
use trust_platform::{Darwin, step};

/// The X3a rows' probes, replay and mutants (design §2.6, census PR 13).
#[path = "conformance_darwin/x3a.rs"]
mod x3a;

#[path = "conformance_darwin/std_model.rs"]
mod std_model;

unsafe extern "C" {
    fn posix_spawn_file_actions_addinherit_np(
        fa: *mut libc::posix_spawn_file_actions_t,
        fd: c_int,
    ) -> c_int;
    fn posix_spawn_file_actions_addchdir_np(
        fa: *mut libc::posix_spawn_file_actions_t,
        path: *const c_char,
    ) -> c_int;
    fn posix_spawn_file_actions_addfchdir_np(
        fa: *mut libc::posix_spawn_file_actions_t,
        fd: c_int,
    ) -> c_int;
}

const REPORTER_FLAG: &str = "--trust-platform-fdreport";
/// The reporter, then waiting to be killed: an exec'd image that LIVES on
/// (what an exec'd child holding an inherited description looks like).
const REPORTER_PARK_FLAG: &str = "--trust-platform-fdreport-park";
const MISSING: &str = "/nonexistent/trust-platform-conformance";
const PROBE_SOFT: u64 = 256;

// =============================================================================
// Real snapshots
// =============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
struct RealFd {
    fd: i32,
    cloexec: bool,
    getfl: i32,
    dev: i64,
    ino: u64,
    ptype: i32,
    /// `poll(POLLIN)` reports readable/hung-up right now: data is pending
    /// (only `WriteSome` writes any) or the peer is gone.
    readable: bool,
}

impl RealFd {
    fn encode(&self) -> String {
        format!(
            "{}:{}:{}:{}:{}:{}:{}",
            self.fd,
            self.cloexec as u8,
            self.getfl,
            self.dev,
            self.ino,
            self.ptype,
            self.readable as u8
        )
    }

    fn decode(s: &str) -> Option<RealFd> {
        let mut it = s.split(':');
        Some(RealFd {
            fd: it.next()?.parse().ok()?,
            cloexec: it.next()? == "1",
            getfl: it.next()?.parse().ok()?,
            dev: it.next()?.parse().ok()?,
            ino: it.next()?.parse().ok()?,
            ptype: it.next()?.parse().ok()?,
            readable: it.next()? == "1",
        })
    }
}

/// This process's whole descriptor table. Opens nothing.
fn snapshot() -> Vec<RealFd> {
    let mut buf: Vec<libc::proc_fdinfo> =
        vec![libc::proc_fdinfo { proc_fd: 0, proc_fdtype: 0 }; 4096];
    let bytes =
        c_int::try_from(buf.len() * std::mem::size_of::<libc::proc_fdinfo>()).unwrap_or(c_int::MAX);
    // SAFETY: the buffer is live and `bytes` long; the kernel writes at most that.
    let n = unsafe {
        libc::proc_pidinfo(libc::getpid(), libc::PROC_PIDLISTFDS, 0, buf.as_mut_ptr().cast(), bytes)
    };
    let count = usize::try_from(n).unwrap_or(0) / std::mem::size_of::<libc::proc_fdinfo>();
    let mut out = Vec::with_capacity(count);
    for info in &buf[..count] {
        let fd = info.proc_fd;
        // SAFETY: plain descriptor queries; a closed number answers -1.
        let (cx, fl) = unsafe { (libc::fcntl(fd, libc::F_GETFD), libc::fcntl(fd, libc::F_GETFL)) };
        // SAFETY: `st` is a live stat buffer.
        let mut st: libc::stat = unsafe { std::mem::zeroed() };
        unsafe { libc::fstat(fd, &mut st) };
        let ptype = i32::try_from(info.proc_fdtype).unwrap_or(-1);
        let mut readable = false;
        if ptype == libc::PROX_FDTYPE_PIPE || ptype == libc::PROX_FDTYPE_SOCKET {
            let mut pfd = libc::pollfd { fd, events: libc::POLLIN, revents: 0 };
            // SAFETY: one live pollfd, zero timeout.
            let r = unsafe { libc::poll(&mut pfd, 1, 0) };
            readable = r > 0 && pfd.revents & (libc::POLLIN | libc::POLLHUP) != 0;
        }
        out.push(RealFd {
            fd,
            cloexec: cx > 0 && cx & libc::FD_CLOEXEC != 0,
            getfl: fl,
            dev: i64::from(st.st_dev),
            ino: st.st_ino,
            ptype,
            readable,
        });
    }
    out.sort_by_key(|f| f.fd);
    out
}

fn errno() -> Errno {
    Errno(std::io::Error::last_os_error().raw_os_error().unwrap_or(0))
}

fn cvt(r: c_int) -> SysResult {
    if r < 0 { Err(errno()) } else { Ok(Ret::Int(i64::from(r))) }
}

// =============================================================================
// Probes
// =============================================================================

#[derive(Clone, Debug)]
enum StdCall {
    Pipe,
    Pair,
    PairDgram,
    TryClone(Operand),
    OpenNullRo,
    UnixBind,
    UnixConnect,
    Accept(Operand),
    /// `Command::spawn` with inherited stdio and ONE `pre_exec` closure
    /// running these calls (errors ignored, like aterm's strip).
    SpawnFork(Vec<Call<Operand>>),
    /// [`StdCall::SpawnFork`] of a program that does not exist
    /// ([`MISSING`]): std's fork-path error path (the child reports its
    /// `execvp` errno on the status pipe and `_exit(1)`s). The result is the
    /// child's pid when the parent's status read saw end-of-file, else the
    /// errno; nothing is reported.
    SpawnForkMissing(Vec<Call<Operand>>),
    /// `Command::spawn` without closures (std's posix_spawnp path).
    SpawnPosix {
        stdin_null: bool,
    },
    /// An X3a std call ([`x3a::XStd`]).
    X(x3a::XStd),
}

#[derive(Clone, Debug)]
enum Act {
    Call(Call<Operand>, Oracle),
    OpenNull(i32),
    OpenMissing(i32),
    /// `open("/")` (a directory vnode).
    OpenRoot,
    /// `open("/dev/fd/N", flags)` (fdesc).
    OpenAlias(Operand, i32),
    /// exec this binary as the reporter (success).
    ExecHelper,
    /// exec this binary as the reporter that then PARKS (lives on until
    /// killed): the image keeps every descriptor the exec kept.
    ExecParker,
    /// exec a path that does not exist (ENOENT).
    ExecMissing,
    SpawnHelper(Vec<FileAction<Operand>>, i32),
    SpawnMissing(Vec<FileAction<Operand>>, i32),
    /// Spawn the helper with these actions, where every `FileAction::Chdir`
    /// names a directory that does not exist (the spawn fails `ENOENT`).
    SpawnChdirMissing(Vec<FileAction<Operand>>, i32),
    /// The exec'd/spawned reporter exits by itself (model: `_exit` by it).
    ImageExits,
    /// A forked child stops executing and waits to be killed.
    Park,
    /// The root kills this (parked) child with SIGKILL (model: its `_exit`).
    Kill,
    /// Snapshot only.
    Observe,
    Std(StdCall),
}

#[derive(Clone, Debug)]
struct PStep {
    actor: Actor,
    act: Act,
}

struct Probe {
    name: &'static str,
    steps: Vec<PStep>,
}

#[derive(Default)]
struct B {
    steps: Vec<PStep>,
}

impl B {
    fn root(&mut self, act: Act) -> usize {
        self.steps.push(PStep { actor: Actor::Root, act });
        self.steps.len() - 1
    }
    fn child(&mut self, k: usize, act: Act) -> usize {
        self.steps.push(PStep { actor: Actor::Child(k), act });
        self.steps.len() - 1
    }
    /// Spawned/exec'd reporter exits, root reaps it.
    fn reap(&mut self, k: usize) {
        self.child(k, Act::ImageExits);
        self.root(c(Call::Waitpid { pid: r(k, 0), options: 0 }));
    }
    fn spawn(&mut self, actions: Vec<FileAction<Operand>>, flags: i32) -> usize {
        let s = self.root(Act::SpawnHelper(actions, flags));
        self.reap(s);
        s
    }
    fn done(self, name: &'static str) -> Probe {
        Probe { name, steps: self.steps }
    }
}

fn r(step: usize, comp: u8) -> Operand {
    Operand::Ret { step, comp }
}
fn lit(v: i32) -> Operand {
    Operand::Lit(v)
}
fn c(call: Call<Operand>) -> Act {
    Act::Call(call, Oracle::Nominal)
}
fn fail(call: Call<Operand>, e: Errno) -> Act {
    Act::Call(call, Oracle::Fail(e))
}
fn fcntl(fd: Operand, cmd: i32, arg: i64) -> Call<Operand> {
    Call::Fcntl { fd, cmd, arg }
}
fn ioctl(fd: Operand, request: u64, arg: i32) -> Call<Operand> {
    Call::Ioctl { fd, request, arg }
}
fn sockpair(ty: i32) -> Call<Operand> {
    Call::Socketpair { domain: darwin::AF_UNIX, ty, protocol: 0 }
}
fn sock(domain: i32, ty: i32) -> Call<Operand> {
    Call::Socket { domain, ty, protocol: 0 }
}

struct Env {
    maxfiles: u64,
    hard: u64,
    exe: CString,
    dir: PathBuf,
}

fn op(path: &str, flags: i32) -> Call<Operand> {
    Call::OpenPath { at: None, path: path.to_string(), flags }
}
fn opat(at: Operand, path: &str, flags: i32) -> Call<Operand> {
    Call::OpenPath { at: Some(at), path: path.to_string(), flags }
}
fn fl(fd: Operand, o: i32) -> Call<Operand> {
    Call::Flock { fd, op: o }
}

/// The M2 probes: `flock` on the description (dups, fork children, exec,
/// exit), its op decoding and conversions, non-vnodes, `O_EXLOCK`/`O_SHLOCK`,
/// the namespace (FIFOs, symlinks, unlink, directories), `openat`'s dirfd
/// and `fstat` identity.
#[allow(clippy::too_many_lines)]
fn m2_probes(env: &Env) -> Vec<Probe> {
    use darwin::*;
    let h = env.hard;
    let mut out = Vec::new();
    let (ex, sh, nb, un) = (LOCK_EX, LOCK_SH, LOCK_NB, LOCK_UN);

    // Lock modes, op decoding, conversions, FHASLOCK.
    let mut b = B::default();
    let a = r(b.root(c(op("m.log", O_RDWR | O_CREAT))), 0);
    let bb = r(b.root(c(op("m.log", O_RDONLY))), 0);
    b.root(c(fl(a, ex | nb)));
    b.root(c(fl(bb, sh | nb)));
    b.root(Act::Observe);
    for bad in [0, nb, 16, 32] {
        b.root(c(fl(a, bad)));
    }
    b.root(c(fl(lit(77), ex)));
    b.root(c(fl(a, sh | ex)));
    b.root(c(fl(bb, sh | nb)));
    b.root(c(fl(a, un | ex)));
    b.root(c(fl(bb, sh | nb)));
    b.root(c(fl(a, sh | nb)));
    b.root(c(fl(a, ex | nb)));
    b.root(c(fl(bb, un)));
    let cc = r(b.root(c(op("m.log", O_RDONLY))), 0);
    b.root(c(fl(cc, ex | nb)));
    b.root(c(fl(a, un)));
    b.root(c(fl(cc, ex | nb)));
    b.root(c(fl(a, un)));
    b.root(c(fcntl(cc, F_SETFL, 0)));
    b.root(c(fl(cc, un)));
    b.root(Act::Observe);
    out.push(b.done("flock-modes-and-ops"));

    // The lock is the description's: a dup holds it; closing one of two does
    // not release it; LOCK_UN through the other does; dup2 over the last
    // reference releases it.
    let mut b = B::default();
    let a = r(b.root(c(op("m.log", O_RDONLY | O_CREAT))), 0);
    b.root(c(fl(a, ex)));
    let d = r(b.root(c(Call::Dup { fd: a })), 0);
    b.root(c(fl(d, ex | nb)));
    b.root(c(Call::Close { fd: a }));
    let bb = r(b.root(c(op("m.log", O_RDONLY))), 0);
    b.root(c(fl(bb, ex | nb)));
    b.root(c(fl(d, un)));
    b.root(c(fl(bb, ex | nb)));
    b.root(c(fl(bb, un)));
    let e = r(b.root(c(op("m.log", O_RDONLY))), 0);
    b.root(c(fl(e, ex)));
    b.root(c(fl(bb, ex | nb)));
    b.root(c(Call::Dup2 { from: d, to: e }));
    b.root(c(fl(bb, ex | nb)));
    out.push(b.done("flock-dup-close-dup2"));

    // A fork child's copy keeps the lock after the parent's last close; the
    // child's exit releases it.
    let mut b = B::default();
    let a = r(b.root(c(op("m.log", O_RDONLY | O_CREAT | O_CLOEXEC))), 0);
    b.root(c(fl(a, ex)));
    let f = b.root(c(Call::Fork));
    b.child(f, Act::Park);
    b.root(c(Call::Close { fd: a }));
    let bb = r(b.root(c(op("m.log", O_RDONLY))), 0);
    b.root(c(fl(bb, ex | nb)));
    b.child(f, Act::Kill);
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    b.root(c(fl(bb, ex | nb)));
    out.push(b.done("flock-fork-child-keeps-it"));

    // LOCK_UN through a child's copy releases it for every holder.
    let mut b = B::default();
    let a = r(b.root(c(op("m.log", O_RDONLY | O_CREAT))), 0);
    b.root(c(fl(a, ex)));
    let f = b.root(c(Call::Fork));
    b.child(f, c(fl(a, un)));
    b.child(f, Act::Park);
    let bb = r(b.root(c(op("m.log", O_RDONLY))), 0);
    b.root(c(fl(bb, ex | nb)));
    b.child(f, Act::Kill);
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    out.push(b.done("flock-unlock-through-a-child"));

    // exec drops a close-on-exec copy (and its lock) while the image lives;
    // an unflagged copy survives the exec and keeps the lock.
    let mut b = B::default();
    let a = r(b.root(c(op("m.log", O_RDONLY | O_CREAT | O_CLOEXEC))), 0);
    b.root(c(fl(a, ex)));
    let f = b.root(c(Call::Fork));
    b.child(f, Act::ExecParker);
    b.root(c(Call::Close { fd: a }));
    let bb = r(b.root(c(op("m.log", O_RDONLY))), 0);
    b.root(c(fl(bb, ex | nb)));
    b.root(c(fl(bb, un)));
    b.child(f, Act::Kill);
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    let a2 = r(b.root(c(op("m.log", O_RDONLY))), 0);
    b.root(c(fl(a2, ex)));
    let f2 = b.root(c(Call::Fork));
    b.child(f2, Act::ExecParker);
    b.root(c(Call::Close { fd: a2 }));
    b.root(c(fl(bb, ex | nb)));
    b.child(f2, Act::Kill);
    b.root(c(Call::Waitpid { pid: r(f2, 0), options: 0 }));
    b.root(c(fl(bb, ex | nb)));
    out.push(b.done("flock-exec-and-exit"));

    // ENOTSUP on what is not a lockable vnode (before the op is decoded);
    // /dev/null and a directory are lockable, and one node.
    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    b.root(c(fl(r(p, 0), ex | nb)));
    b.root(c(fl(r(p, 0), 0)));
    b.root(c(fl(r(p, 1), un)));
    let sp = b.root(c(sockpair(SOCK_STREAM)));
    b.root(c(fl(r(sp, 0), ex | nb)));
    let k = b.root(c(Call::Kqueue));
    b.root(c(fl(r(k, 0), ex | nb)));
    b.root(c(Call::Mkfifo { path: "fifo".into() }));
    let fi = r(b.root(c(op("fifo", O_RDWR))), 0);
    b.root(c(fl(fi, ex | nb)));
    b.root(c(fl(fi, un)));
    // A FIFO is a vnode: the op is decoded first (the M2 model review's P1).
    for bad in [0, nb, 16] {
        b.root(c(fl(fi, bad)));
    }
    b.root(c(fl(fi, sh)));
    let n1 = r(b.root(c(op("/dev/null", O_RDWR))), 0);
    let n2 = r(b.root(c(op("/dev/null", O_RDONLY))), 0);
    b.root(c(fl(n1, ex | nb)));
    b.root(c(fl(n2, ex | nb)));
    b.root(c(fl(n1, un)));
    let d1 = r(b.root(c(op("dir", O_RDONLY))), 0);
    let d2 = r(b.root(c(op("dir", O_RDONLY))), 0);
    b.root(c(fl(d1, ex | nb)));
    b.root(c(fl(d2, sh | nb)));
    b.root(c(fl(d1, un)));
    b.root(Act::Observe);
    out.push(b.done("flock-what-locks"));

    // O_EXLOCK / O_SHLOCK.
    let mut b = B::default();
    let a = r(b.root(c(op("m.log", O_RDONLY | O_CREAT | O_EXLOCK | O_CLOEXEC))), 0);
    b.root(Act::Observe);
    b.root(c(op("m.log", O_RDONLY | O_EXLOCK | O_NONBLOCK)));
    b.root(c(op("m.log", O_RDONLY | O_SHLOCK | O_NONBLOCK)));
    let bb = r(b.root(c(op("m.log", O_RDONLY))), 0);
    b.root(c(fl(bb, sh | nb)));
    b.root(c(fl(a, un)));
    b.root(c(op("m.log", O_RDONLY | O_SHLOCK | O_NONBLOCK)));
    b.root(c(op("m.log", O_RDONLY | O_SHLOCK | O_NONBLOCK)));
    b.root(c(op("m.log", O_RDONLY | O_EXLOCK | O_SHLOCK | O_NONBLOCK)));
    b.root(c(Call::Mkfifo { path: "fifo".into() }));
    b.root(c(op("fifo", O_WRONLY | O_NONBLOCK | O_EXLOCK)));
    b.root(c(op("fifo", O_RDONLY | O_NONBLOCK | O_EXLOCK)));
    b.root(c(op("/dev/null", O_RDONLY | O_EXLOCK | O_NONBLOCK)));
    b.root(Act::Observe);
    out.push(b.done("open-lock-bits"));

    // The namespace: create/exclusive, FIFOs, unlink, symlinks, directories,
    // fstat identity.
    let mut b = B::default();
    b.root(c(op("missing", O_RDONLY)));
    let m = r(b.root(c(op("m.log", O_RDWR | O_CREAT | O_EXCL))), 0);
    b.root(c(op("m.log", O_RDWR | O_CREAT | O_EXCL)));
    b.root(c(Call::Mkfifo { path: "fifo".into() }));
    b.root(c(Call::Mkfifo { path: "fifo".into() }));
    b.root(c(op("fifo", O_WRONLY | O_NONBLOCK)));
    let rd = r(b.root(c(op("fifo", O_RDONLY | O_NONBLOCK))), 0);
    let wr = r(b.root(c(op("fifo", O_WRONLY | O_NONBLOCK))), 0);
    b.root(c(op("fifo", O_RDWR)));
    b.root(Act::Observe);
    b.root(c(Call::Fstat { fd: rd }));
    b.root(c(Call::Fstat { fd: wr }));
    b.root(c(Call::Unlink { path: "fifo".into() }));
    b.root(c(Call::Unlink { path: "fifo".into() }));
    b.root(c(op("fifo", O_RDWR)));
    b.root(c(Call::Fstat { fd: rd }));
    b.root(c(Call::Symlink { target: "m.log".into(), path: "lnk".into() }));
    b.root(c(op("lnk", O_RDONLY | O_NOFOLLOW)));
    let l = r(b.root(c(op("lnk", O_RDONLY))), 0);
    b.root(c(Call::Fstat { fd: l }));
    b.root(c(Call::Fstat { fd: m }));
    b.root(c(op("lnk", O_RDONLY | O_CREAT | O_EXCL)));
    b.root(c(Call::Symlink { target: "x".into(), path: "lnk".into() }));
    b.root(c(Call::Symlink { target: "nothere".into(), path: "dangling".into() }));
    b.root(c(op("dangling", O_RDONLY)));
    b.root(c(op("dangling", O_RDONLY | O_CREAT)));
    let t = r(b.root(c(op("nothere", O_RDONLY))), 0);
    b.root(c(Call::Fstat { fd: t }));
    b.root(c(Call::Unlink { path: "lnk".into() }));
    b.root(c(op("dir", O_WRONLY)));
    b.root(c(op("dir", O_RDONLY | O_TRUNC)));
    let d = r(b.root(c(op("dir", O_RDONLY | O_CREAT))), 0);
    b.root(c(Call::Fstat { fd: d }));
    b.root(c(op("dir", O_RDONLY | O_CREAT | O_EXCL)));
    b.root(c(Call::Unlink { path: "dir".into() }));
    b.root(c(op("m.log", O_RDONLY | O_DIRECTORY)));
    b.root(c(op("/dev/null", O_RDONLY | O_DIRECTORY)));
    let n = r(b.root(c(op("/dev/null", O_RDONLY))), 0);
    b.root(c(Call::Fstat { fd: n }));
    b.root(c(Call::Fstat { fd: lit(77) }));
    b.root(Act::Observe);
    out.push(b.done("namespace-and-identity"));

    // openat's dirfd, and allocation before everything.
    let mut b = B::default();
    b.root(c(opat(lit(777), "/dev/null", O_RDONLY)));
    b.root(c(opat(lit(777), "rel", O_RDONLY)));
    b.root(c(opat(lit(AT_FDCWD), "m.log", O_RDONLY | O_CREAT)));
    let f = r(b.root(c(op("m.log", O_RDONLY))), 0);
    b.root(c(opat(f, "rel", O_RDONLY)));
    let p = b.root(c(Call::Pipe));
    b.root(c(opat(r(p, 0), "rel", O_RDONLY)));
    let k = b.root(c(Call::Kqueue));
    b.root(c(opat(r(k, 0), "rel", O_RDONLY)));
    b.root(c(fl(f, ex)));
    b.root(c(Call::Mkfifo { path: "fifo".into() }));
    let full = b.root(c(Call::Getrlimit { resource: RLIMIT_NOFILE }));
    let _ = full;
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: 10, hard: h }));
    b.root(c(Call::Dup { fd: lit(0) }));
    b.root(c(opat(lit(777), "rel", O_RDONLY)));
    b.root(c(op("missing", O_RDONLY)));
    b.root(c(op("fifo", O_WRONLY | O_NONBLOCK)));
    b.root(c(op("m.log", O_RDONLY | O_EXLOCK | O_NONBLOCK)));
    b.root(c(Call::Mkfifo { path: "fifo".into() }));
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: PROBE_SOFT, hard: h }));
    out.push(b.done("openat-and-emfile-first"));

    // A relative symlink target names a file in the LINK's directory (the M2
    // model review's P10): dir/rl -> m.log is dir/m.log, not the m.log beside
    // dir; O_CREAT through it creates dir/m.log.
    let mut b = B::default();
    let top = r(b.root(c(op("m.log", O_RDWR | O_CREAT))), 0);
    b.root(c(Call::Symlink { target: "m.log".into(), path: "dir/rl".into() }));
    b.root(c(op("dir/rl", O_RDONLY)));
    let inner = r(b.root(c(op("dir/rl", O_RDONLY | O_CREAT))), 0);
    b.root(c(Call::Fstat { fd: top }));
    b.root(c(Call::Fstat { fd: inner }));
    let same = r(b.root(c(op("dir/m.log", O_RDONLY))), 0);
    b.root(c(Call::Fstat { fd: same }));
    b.root(c(fl(inner, ex | nb)));
    b.root(c(fl(top, ex | nb)));
    b.root(c(fl(same, ex | nb)));
    b.root(Act::Observe);
    out.push(b.done("symlink-target-is-relative-to-the-link"));
    out
}

#[allow(clippy::too_many_lines)]
fn probes(env: &Env) -> Vec<Probe> {
    use darwin::*;
    let h = env.hard;
    let mut out = Vec::new();

    let mut b = B::default();
    b.root(c(Call::Pipe));
    out.push(b.done("pipe"));

    let mut b = B::default();
    b.root(c(Call::Pipe));
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: 6, hard: h }));
    b.root(c(Call::Pipe));
    let k = b.root(c(Call::Kqueue));
    b.root(c(Call::Pipe));
    b.root(c(Call::Dup { fd: lit(0) }));
    b.root(Act::OpenNull(O_RDONLY));
    b.root(Act::OpenMissing(O_RDONLY));
    b.root(c(sock(AF_UNIX, SOCK_STREAM)));
    b.root(c(sockpair(SOCK_STREAM)));
    b.root(c(Call::Close { fd: r(k, 0) }));
    b.root(c(sockpair(SOCK_STREAM)));
    b.root(c(sock(AF_UNIX, SOCK_STREAM)));
    // Full table: socket() allocates before it checks the shape; socketpair
    // checks the type, then allocates, then connects; an fdesc open
    // allocates before it looks at N.
    b.root(c(sock(AF_UNIX, SOCK_SEQPACKET)));
    b.root(c(sock(AF_UNIX, SOCK_STREAM | LINUX_SOCK_CLOEXEC)));
    b.root(c(Call::Socket { domain: AF_UNIX, ty: SOCK_STREAM, protocol: 7 }));
    b.root(c(sockpair(SOCK_STREAM | LINUX_SOCK_CLOEXEC)));
    b.root(c(Call::Socketpair { domain: AF_INET, ty: SOCK_STREAM, protocol: 0 }));
    b.root(Act::OpenAlias(lit(77), O_RDONLY));
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: PROBE_SOFT, hard: h }));
    out.push(b.done("table-full"));

    // A full table is EMFILE for a kqueue's alias too: allocation comes first,
    // before the kqueue refusal (PLATFORM-KQUEUE-ALIAS-1).
    let mut b = B::default();
    let k = b.root(c(Call::Kqueue));
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: 4, hard: h }));
    b.root(Act::OpenAlias(r(k, 0), O_RDONLY));
    b.root(Act::OpenAlias(r(k, 0), O_RDWR));
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: PROBE_SOFT, hard: h }));
    out.push(b.done("kqueue-alias-table-full"));

    let mut b = B::default();
    b.root(c(sockpair(SOCK_STREAM)));
    b.root(c(sockpair(SOCK_DGRAM)));
    b.root(c(sockpair(SOCK_SEQPACKET)));
    b.root(c(sockpair(SOCK_STREAM | LINUX_SOCK_CLOEXEC)));
    b.root(c(Call::Socketpair { domain: AF_INET, ty: SOCK_STREAM, protocol: 0 }));
    b.root(c(Call::Socketpair { domain: AF_UNIX, ty: SOCK_STREAM, protocol: 5 }));
    out.push(b.done("socketpair"));

    let mut b = B::default();
    b.root(c(sock(AF_UNIX, SOCK_STREAM)));
    b.root(c(sock(AF_INET, SOCK_STREAM)));
    b.root(c(sock(AF_INET6, SOCK_DGRAM)));
    b.root(c(sock(AF_UNIX, SOCK_SEQPACKET)));
    b.root(c(sock(AF_UNIX, SOCK_STREAM | LINUX_SOCK_CLOEXEC)));
    b.root(c(sock(AF_UNIX, SOCK_DGRAM)));
    out.push(b.done("socket"));

    let mut b = B::default();
    let l = b.root(c(sock(AF_UNIX, SOCK_STREAM)));
    b.root(c(Call::SocketOp { fd: r(l, 0), op: trust_platform::SocketOp::Bind }));
    b.root(c(Call::SocketOp { fd: r(l, 0), op: trust_platform::SocketOp::Listen }));
    b.root(c(fcntl(r(l, 0), F_SETFL, i64::from(O_NONBLOCK))));
    let cl = b.root(c(sock(AF_UNIX, SOCK_STREAM)));
    b.root(c(Call::SocketOp { fd: r(cl, 0), op: trust_platform::SocketOp::Connect }));
    b.root(c(Call::Accept { fd: r(l, 0) }));
    b.root(fail(Call::Accept { fd: r(l, 0) }, Errno::EAGAIN));
    let p = b.root(c(Call::Pipe));
    b.root(c(Call::Accept { fd: r(p, 0) }));
    b.root(c(Call::SocketOp { fd: r(p, 0), op: trust_platform::SocketOp::Bind }));
    b.root(c(Call::Accept { fd: lit(77) }));
    // A datagram socket cannot accept or listen; a stream socket that is not
    // listening cannot accept.
    let dg = b.root(c(sock(AF_UNIX, SOCK_DGRAM)));
    b.root(c(Call::Accept { fd: r(dg, 0) }));
    b.root(c(Call::SocketOp { fd: r(dg, 0), op: trust_platform::SocketOp::Listen }));
    let st = b.root(c(sock(AF_UNIX, SOCK_STREAM)));
    b.root(c(Call::Accept { fd: r(st, 0) }));
    out.push(b.done("accept"));

    let mut b = B::default();
    b.root(Act::OpenNull(O_RDONLY));
    b.root(Act::OpenNull(O_RDWR | O_CLOEXEC));
    b.root(Act::OpenNull(O_WRONLY | O_APPEND));
    b.root(Act::OpenNull(O_RDONLY | O_NONBLOCK));
    b.root(Act::OpenMissing(O_RDONLY));
    out.push(b.done("open"));

    let mut b = B::default();
    let k = b.root(c(Call::Kqueue));
    b.root(c(fcntl(r(k, 0), F_SETFD, 0)));
    b.root(c(fcntl(r(k, 0), F_DUPFD, 10)));
    b.root(c(Call::Pipe));
    let f = b.root(c(Call::Fork));
    b.child(f, Act::Observe);
    b.child(f, c(Call::Exit { status: 0 }));
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    b.root(c(Call::Close { fd: r(k, 0) }));
    out.push(b.done("kqueue-fork"));

    let mut b = B::default();
    let f = b.root(c(Call::Fork));
    let k = b.child(f, c(Call::Kqueue));
    b.child(f, c(fcntl(r(k, 0), F_SETFD, 0)));
    b.child(f, Act::ExecHelper);
    b.child(f, Act::ImageExits);
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    out.push(b.done("kqueue-exec"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let rd = r(p, 0);
    b.root(c(fcntl(rd, F_GETFD, 0)));
    b.root(c(fcntl(rd, F_SETFD, 1)));
    b.root(c(fcntl(rd, F_GETFD, 0)));
    b.root(c(fcntl(rd, F_SETFD, 0)));
    b.root(c(fcntl(rd, F_GETFD, 0)));
    // Bits above FD_CLOEXEC and FD_CLOFORK are ignored (MEASURED on Darwin 25.6
    // and 27). FD_CLOFORK itself is refused by name: `clofork_is_refused_by_name`.
    b.root(c(fcntl(rd, F_SETFD, 5)));
    b.root(c(fcntl(rd, F_GETFD, 0)));
    b.root(c(fcntl(rd, F_SETFD, 4)));
    b.root(c(fcntl(rd, F_GETFD, 0)));
    b.root(c(fcntl(lit(77), F_GETFD, 0)));
    b.root(c(fcntl(lit(-1), F_GETFD, 0)));
    b.root(c(fcntl(lit(77), F_SETFD, 1)));
    out.push(b.done("fcntl-fd-flags"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let (rd, wr) = (r(p, 0), r(p, 1));
    b.root(c(fcntl(rd, F_DUPFD, 0)));
    b.root(c(fcntl(rd, F_DUPFD, 10)));
    b.root(c(fcntl(rd, F_SETFD, 1)));
    b.root(c(fcntl(rd, F_DUPFD, 10)));
    b.root(c(fcntl(rd, F_DUPFD_CLOEXEC, 10)));
    b.root(c(fcntl(wr, F_DUPFD_CLOEXEC, 0)));
    b.root(c(fcntl(rd, F_DUPFD, -1)));
    b.root(c(fcntl(lit(77), F_DUPFD, 0)));
    b.root(c(fcntl(rd, F_DUPFD, 256)));
    out.push(b.done("fcntl-dupfd"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let (rd, wr) = (r(p, 0), r(p, 1));
    let d = b.root(c(Call::Dup { fd: wr }));
    b.root(c(fcntl(rd, F_GETFL, 0)));
    b.root(c(fcntl(wr, F_GETFL, 0)));
    b.root(c(fcntl(wr, F_SETFL, i64::from(O_NONBLOCK | O_APPEND))));
    b.root(c(fcntl(r(d, 0), F_GETFL, 0)));
    let junk = O_RDWR | O_CLOEXEC | 0x10 | 0x100 | O_FSYNC | O_DSYNC | O_ASYNC;
    b.root(c(fcntl(wr, F_SETFL, i64::from(junk))));
    b.root(c(fcntl(r(d, 0), F_GETFL, 0)));
    b.root(c(fcntl(wr, F_GETFD, 0)));
    b.root(c(fcntl(wr, F_SETFL, 0)));
    let s = b.root(c(sockpair(SOCK_STREAM)));
    b.root(c(fcntl(r(s, 0), F_SETFL, i64::from(O_NONBLOCK))));
    b.root(c(fcntl(r(s, 1), F_GETFL, 0)));
    b.root(c(fcntl(lit(77), F_SETFL, 0)));
    out.push(b.done("fcntl-fl"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    b.root(c(fcntl(r(p, 0), F_SETFD, 1)));
    b.root(c(Call::Dup { fd: r(p, 0) }));
    b.root(c(Call::Close { fd: r(p, 0) }));
    b.root(c(Call::Dup { fd: r(p, 1) }));
    b.root(c(Call::Dup { fd: lit(77) }));
    b.root(c(Call::Dup { fd: lit(-1) }));
    out.push(b.done("dup"));

    let mut b = B::default();
    let s = b.root(c(sockpair(SOCK_STREAM)));
    let (s0, s1) = (r(s, 0), r(s, 1));
    b.root(c(ioctl(s0, FIOCLEX, 0)));
    b.root(c(Call::Dup2 { from: s0, to: lit(10) }));
    b.root(c(fcntl(lit(10), F_SETFD, 1)));
    b.root(c(Call::Dup2 { from: lit(10), to: lit(10) }));
    b.root(c(Call::Dup2 { from: s0, to: lit(-1) }));
    b.root(c(Call::Dup2 { from: lit(77), to: lit(5) }));
    b.root(c(Call::Dup2 { from: s0, to: lit(256) }));
    b.root(c(Call::Dup2 { from: s0, to: s1 }));
    out.push(b.done("dup2"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let d = b.root(c(Call::Dup { fd: r(p, 1) }));
    b.root(c(Call::Close { fd: r(p, 1) }));
    b.root(c(Call::Close { fd: r(d, 0) }));
    b.root(c(Call::Close { fd: r(p, 1) }));
    b.root(c(Call::Close { fd: lit(-1) }));
    out.push(b.done("close"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let d = b.root(c(Call::Dup { fd: r(p, 0) }));
    b.root(c(ioctl(r(p, 0), FIOCLEX, 0)));
    b.root(c(ioctl(r(p, 0), FIONCLEX, 0)));
    b.root(c(ioctl(r(p, 0), FIOCLEX, 0)));
    b.root(c(ioctl(r(p, 0), FIONBIO, 1)));
    b.root(c(fcntl(r(d, 0), F_GETFL, 0)));
    b.root(c(ioctl(r(p, 0), FIONBIO, 0)));
    b.root(c(ioctl(lit(77), FIOCLEX, 0)));
    out.push(b.done("ioctl"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let (rd, wr) = (r(p, 0), r(p, 1));
    b.root(c(fcntl(rd, F_SETFD, 1)));
    b.root(c(sockpair(SOCK_STREAM)));
    let f = b.root(c(Call::Fork));
    b.child(f, Act::Observe);
    b.child(f, c(fcntl(wr, F_SETFD, 1)));
    b.child(f, c(Call::Close { fd: rd }));
    b.child(f, c(fcntl(wr, F_SETFL, i64::from(O_NONBLOCK))));
    b.child(f, c(Call::Exit { status: 0 }));
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    out.push(b.done("fork-snapshot"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let f = b.root(c(Call::Fork));
    b.child(f, Act::Park);
    b.root(c(Call::Close { fd: r(p, 1) }));
    b.child(f, Act::Kill);
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    out.push(b.done("fork-refcount-eof"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    b.root(c(ioctl(r(p, 0), FIOCLEX, 0)));
    let s = b.root(c(sockpair(SOCK_STREAM)));
    let k = b.root(c(Call::Kqueue));
    b.root(c(fcntl(r(k, 0), F_SETFD, 0)));
    let f = b.root(c(Call::Fork));
    b.child(f, c(Call::Dup2 { from: r(s, 0), to: lit(10) }));
    b.child(f, c(Call::Dup2 { from: r(s, 1), to: r(s, 1) }));
    b.child(f, c(ioctl(r(s, 1), FIOCLEX, 0)));
    b.child(f, c(fcntl(r(p, 1), F_DUPFD, 20)));
    b.child(f, Act::ExecHelper);
    b.child(f, Act::ImageExits);
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    out.push(b.done("fork-exec"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    b.root(c(ioctl(r(p, 0), FIOCLEX, 0)));
    let f = b.root(c(Call::Fork));
    b.child(f, Act::ExecMissing);
    b.child(f, Act::Observe);
    b.child(f, c(Call::Exit { status: 3 }));
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    out.push(b.done("exec-failure"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    b.root(c(ioctl(r(p, 1), FIOCLEX, 0)));
    let f = b.root(c(Call::Fork));
    b.child(f, Act::ExecHelper);
    b.child(f, Act::ImageExits);
    b.root(c(Call::Close { fd: r(p, 1) }));
    b.root(c(Call::ReadSome { fd: r(p, 0) }));
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    out.push(b.done("exec-closes-status-pipe"));

    // std's exec-failure report: the child writes to the status pipe and
    // exits; the parent reads data before end-of-file.
    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    b.root(c(ioctl(r(p, 1), FIOCLEX, 0)));
    let f = b.root(c(Call::Fork));
    b.child(f, Act::ExecMissing);
    b.child(f, c(Call::WriteSome { fd: r(p, 1) }));
    b.child(f, c(Call::Exit { status: 1 }));
    b.root(c(Call::Close { fd: r(p, 1) }));
    b.root(c(Call::ReadSome { fd: r(p, 0) }));
    b.root(c(Call::ReadSome { fd: r(p, 0) }));
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    b.root(c(Call::WriteSome { fd: r(p, 0) }));
    out.push(b.done("status-pipe-error-report"));

    // F_SETFL on a kqueue: ENOTTY for every argument, the bits change anyway.
    let mut b = B::default();
    let k = b.root(c(Call::Kqueue));
    b.root(c(fcntl(r(k, 0), F_SETFL, i64::from(O_NONBLOCK))));
    b.root(c(fcntl(r(k, 0), F_GETFL, 0)));
    b.root(c(fcntl(r(k, 0), F_SETFL, i64::from(O_APPEND))));
    b.root(c(fcntl(r(k, 0), F_SETFL, 0)));
    b.root(c(fcntl(r(k, 0), F_GETFL, 0)));
    // kqueue()'s own descriptor: its F_GETFD is refused by name
    // (`kqueue_getfd_is_refused_by_name`); a dup reads 0, and F_SETFD sets the
    // flags exactly.
    let d = b.root(c(Call::Dup { fd: r(k, 0) }));
    b.root(c(fcntl(r(d, 0), F_GETFD, 0)));
    b.root(c(fcntl(r(k, 0), F_SETFD, 1)));
    b.root(c(fcntl(r(k, 0), F_GETFD, 0)));
    b.root(c(fcntl(r(k, 0), F_SETFD, 0)));
    b.root(c(fcntl(r(k, 0), F_GETFD, 0)));
    out.push(b.done("kqueue-setfl"));

    // /dev/fd/N: the same open file description. A kqueue's alias is not
    // here: the model refuses it by name (`kqueue_alias_is_refused_by_name`).
    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let (rd, wr) = (r(p, 0), r(p, 1));
    let a = b.root(Act::OpenAlias(wr, O_WRONLY | O_CLOEXEC));
    b.root(c(Call::Close { fd: wr }));
    b.root(Act::OpenAlias(rd, O_WRONLY));
    b.root(Act::OpenAlias(rd, O_RDWR));
    b.root(Act::OpenAlias(r(a, 0), O_WRONLY | O_NONBLOCK | O_APPEND));
    b.root(c(fcntl(r(a, 0), F_SETFL, i64::from(O_NONBLOCK))));
    b.root(Act::OpenAlias(lit(77), O_RDONLY));
    b.root(Act::OpenAlias(lit(0), O_RDONLY));
    b.root(Act::OpenAlias(lit(0), O_RDWR));
    b.root(c(Call::Close { fd: r(a, 0) }));
    out.push(b.done("dev-fd-alias"));

    // waitpid: WNOHANG on a live child returns 0; -1 waits for any child.
    let mut b = B::default();
    let f = b.root(c(Call::Fork));
    b.child(f, Act::Park);
    b.root(c(Call::Waitpid { pid: r(f, 0), options: WNOHANG }));
    b.root(c(Call::Waitpid { pid: lit(-1), options: WNOHANG }));
    b.child(f, Act::Kill);
    b.root(c(Call::Waitpid { pid: lit(-1), options: 0 }));
    b.root(c(Call::Waitpid { pid: lit(-1), options: WNOHANG }));
    out.push(b.done("waitpid-options"));

    // addfchdir / addchdir outcomes.
    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let k = b.root(c(Call::Kqueue));
    let dir = b.root(Act::OpenRoot);
    b.root(Act::SpawnHelper(vec![FileAction::Fchdir { fd: lit(77) }], 0));
    b.root(Act::SpawnHelper(vec![FileAction::Fchdir { fd: r(k, 0) }], 0));
    b.root(Act::SpawnHelper(vec![FileAction::Fchdir { fd: r(p, 0) }], 0));
    b.spawn(vec![FileAction::Fchdir { fd: r(dir, 0) }], 0);
    b.spawn(vec![FileAction::Chdir], 0);
    b.root(Act::SpawnChdirMissing(vec![FileAction::Chdir], 0));
    out.push(b.done("spawn-chdir"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    b.root(c(ioctl(r(p, 0), FIOCLEX, 0)));
    let k = b.root(c(Call::Kqueue));
    b.root(c(fcntl(r(k, 0), F_SETFD, 0)));
    b.spawn(vec![], 0);
    out.push(b.done("spawn-plain"));

    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    let (rd, wr) = (r(p, 0), r(p, 1));
    b.root(c(ioctl(rd, FIOCLEX, 0)));
    b.spawn(vec![FileAction::Dup2 { from: rd, to: lit(20) }], 0);
    b.spawn(vec![FileAction::Dup2 { from: rd, to: rd }], 0);
    b.spawn(vec![FileAction::Inherit { fd: rd }], 0);
    b.spawn(vec![FileAction::Close { fd: wr }], 0);
    b.root(Act::SpawnHelper(vec![FileAction::Close { fd: lit(77) }], 0));
    b.spawn(vec![FileAction::Open { fd: lit(30), flags: O_RDONLY | O_CLOEXEC }], 0);
    b.spawn(vec![FileAction::Open { fd: lit(5), flags: O_RDONLY | O_CLOEXEC }], 0);
    b.root(Act::SpawnHelper(vec![FileAction::Dup2 { from: lit(77), to: lit(5) }], 0));
    b.root(Act::SpawnHelper(vec![FileAction::Inherit { fd: lit(77) }], 0));
    b.root(Act::SpawnMissing(vec![], 0));
    b.spawn(vec![FileAction::Close { fd: wr }, FileAction::Dup2 { from: rd, to: wr }], 0);
    out.push(b.done("spawn-file-actions"));

    let mut b = B::default();
    let cd = POSIX_SPAWN_CLOEXEC_DEFAULT;
    let p = b.root(c(Call::Pipe));
    let (rd, wr) = (r(p, 0), r(p, 1));
    b.root(c(ioctl(rd, FIOCLEX, 0)));
    b.spawn(vec![], cd);
    b.spawn(vec![FileAction::Dup2 { from: wr, to: lit(5) }], cd);
    b.spawn(vec![FileAction::Inherit { fd: wr }], cd);
    b.spawn(
        vec![FileAction::Dup2 { from: lit(1), to: lit(1) }, FileAction::Inherit { fd: lit(2) }],
        cd,
    );
    b.spawn(vec![FileAction::Dup2 { from: rd, to: rd }], cd);
    b.spawn(vec![FileAction::Inherit { fd: rd }], cd);
    b.spawn(vec![FileAction::Open { fd: lit(9), flags: O_RDONLY }], cd);
    b.spawn(vec![FileAction::Open { fd: lit(5), flags: O_RDONLY | O_CLOEXEC }], cd);
    b.spawn(
        vec![FileAction::Dup2 { from: wr, to: lit(5) }],
        cd | POSIX_SPAWN_SETSIGDEF | POSIX_SPAWN_SETSIGMASK,
    );
    out.push(b.done("spawn-cloexec-default"));

    let mut b = B::default();
    b.root(c(Call::Getrlimit { resource: RLIMIT_NOFILE }));
    let p = b.root(c(Call::Pipe));
    let rd = r(p, 0);
    let hi = b.root(c(fcntl(rd, F_DUPFD, 20)));
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: 16, hard: h }));
    b.root(c(Call::Getrlimit { resource: RLIMIT_NOFILE }));
    b.root(c(fcntl(rd, F_DUPFD, 16)));
    b.root(c(fcntl(rd, F_DUPFD, 15)));
    b.root(c(Call::Dup2 { from: rd, to: lit(16) }));
    b.root(c(Call::Dup2 { from: r(hi, 0), to: r(hi, 0) }));
    b.root(c(fcntl(r(hi, 0), F_DUPFD, 0)));
    b.spawn(vec![], 0);
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: 100, hard: 50 }));
    if h == RLIM_INFINITY {
        b.root(c(Call::Setrlimit {
            resource: RLIMIT_NOFILE,
            soft: RLIM_INFINITY,
            hard: RLIM_INFINITY,
        }));
        b.root(c(Call::Getrlimit { resource: RLIMIT_NOFILE }));
        let mf = i64::try_from(env.maxfiles).unwrap_or(i64::MAX);
        b.root(c(fcntl(rd, F_DUPFD, mf)));
        let top = b.root(c(fcntl(rd, F_DUPFD, mf - 1)));
        b.root(c(Call::Close { fd: r(top, 0) }));
        b.root(c(Call::Setrlimit {
            resource: RLIMIT_NOFILE,
            soft: env.maxfiles + 100,
            hard: RLIM_INFINITY,
        }));
        b.root(c(Call::Getrlimit { resource: RLIMIT_NOFILE }));
    }
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: PROBE_SOFT, hard: 1000 }));
    b.root(c(Call::Setrlimit { resource: RLIMIT_NOFILE, soft: PROBE_SOFT, hard: 2000 }));
    b.root(c(Call::Getrlimit { resource: RLIMIT_NOFILE }));
    out.push(b.done("rlimit"));

    let mut b = B::default();
    let sp = b.root(Act::Std(StdCall::Pipe));
    b.root(Act::Std(StdCall::Pair));
    b.root(Act::Std(StdCall::PairDgram));
    b.root(Act::Std(StdCall::TryClone(r(sp, 0))));
    b.root(Act::Std(StdCall::OpenNullRo));
    let lb = b.root(Act::Std(StdCall::UnixBind));
    b.root(Act::Std(StdCall::UnixConnect));
    b.root(Act::Std(StdCall::Accept(r(lb, 0))));
    b.root(c(Call::Close { fd: lit(0) }));
    b.root(Act::Std(StdCall::TryClone(r(sp, 0))));
    out.push(b.done("std-rows"));

    // Trust SP1: both spawn paths strip unflagged descriptors. Hooks run
    // after marking, so their placements survive; raw dup2 self-copies of
    // CLOEXEC sources still close at exec. Retain the former bug's probes.
    let mut b = B::default();
    let pr = b.root(Act::Std(StdCall::Pair));
    let sx = b.root(c(sockpair(SOCK_STREAM)));
    b.root(c(fcntl(r(sx, 0), F_DUPFD, 64)));
    let lanes = vec![
        Call::Dup2 { from: r(pr, 0), to: lit(10) },
        Call::Dup2 { from: r(pr, 1), to: lit(11) },
    ];
    let s1 = b.root(Act::Std(StdCall::SpawnFork(lanes.clone())));
    b.reap(s1);
    let mut strip: Vec<Call<Operand>> = (3..70).map(|fd| fcntl(lit(fd), F_SETFD, 1)).collect();
    strip.extend(lanes);
    let s2 = b.root(Act::Std(StdCall::SpawnFork(strip)));
    b.reap(s2);
    let s3 = b.root(Act::Std(StdCall::SpawnPosix { stdin_null: true }));
    b.reap(s3);
    let selfcopy = vec![
        Call::Dup2 { from: r(pr, 0), to: r(pr, 0) },
        Call::Dup2 { from: r(pr, 1), to: r(pr, 1) },
    ];
    let s4 = b.root(Act::Std(StdCall::SpawnFork(selfcopy)));
    b.reap(s4);
    out.push(b.done("std-command-spawn"));

    // Trust's std moves the fork path's exec-status write end above 9 when
    // pre_exec hooks run (SP-1, `dup_above_conventional`): a hook's dup2
    // onto 6, where the end sat (pipe 5, 6), no longer swallows a failed
    // exec's report (spawn returns ENOENT), while one onto 10, where it now
    // sits, does: the status read sees end-of-file once the hook has run,
    // and spawn returns a child that is about to exit. That hook places the
    // first end of a socketpair it makes itself (5 and 6 in the child, whose
    // status read end 5 std closed and whose 6 moved), so the errno the
    // child then writes lands on a description the parent never holds: the
    // parent's own tables do not race that late write.
    let mut b = B::default();
    let pr = b.root(c(sockpair(SOCK_STREAM)));
    b.root(Act::Std(StdCall::SpawnForkMissing(vec![Call::Dup2 { from: r(pr, 0), to: lit(6) }])));
    let s = b.root(Act::Std(StdCall::SpawnForkMissing(vec![
        sockpair(SOCK_STREAM),
        Call::Dup2 { from: lit(5), to: lit(10) },
    ])));
    b.root(c(Call::Waitpid { pid: r(s, 0), options: 0 }));
    out.push(b.done("std-spawn-status-floor"));

    // Trust std's strip as one clause (`Call::CloexecFrom`): in a forked
    // child, every descriptor from `first` up is marked close-on-exec (one
    // already flagged stays flagged; none is closed), so the exec keeps
    // only those below it.
    let mut b = B::default();
    let p = b.root(c(Call::Pipe));
    b.root(c(sockpair(SOCK_STREAM)));
    b.root(c(fcntl(r(p, 0), F_DUPFD, 64)));
    b.root(c(fcntl(r(p, 1), F_DUPFD_CLOEXEC, 70)));
    let f = b.root(c(Call::Fork));
    b.child(f, c(Call::CloexecFrom { first: 4 }));
    b.child(f, Act::Observe);
    b.child(f, Act::ExecHelper);
    b.child(f, Act::ImageExits);
    b.root(c(Call::Waitpid { pid: r(f, 0), options: 0 }));
    out.push(b.done("cloexec-from"));

    out.extend(x3a::probes(env));
    out
}

/// Structural checks a probe must pass before it is run.
fn validate(p: &Probe) -> Result<(), String> {
    let mut forked: BTreeMap<usize, bool> = BTreeMap::new(); // fork step -> block ended
    for (i, s) in p.steps.iter().enumerate() {
        match (s.actor, &s.act) {
            (Actor::Root, Act::Call(Call::Fork, _)) => {
                forked.insert(i, false);
            }
            (
                Actor::Root,
                Act::ExecHelper
                | Act::ExecParker
                | Act::ExecMissing
                | Act::Park
                | Act::Kill
                | Act::ImageExits,
            ) => {
                return Err(format!("step {i}: the probe root cannot {:?}", s.act));
            }
            (Actor::Root, Act::Std(sc)) if !x3a::root_ok(sc) => {
                return Err(format!("step {i}: the probe root cannot {:?}", s.act));
            }
            (Actor::Child(k), act) => {
                let is_fork = forked.contains_key(&k);
                let performer_is_child = !matches!(act, Act::Kill | Act::ImageExits);
                if performer_is_child {
                    if !is_fork {
                        return Err(format!("step {i}: Child({k}) is not a forked child"));
                    }
                    if forked[&k] {
                        return Err(format!("step {i}: Child({k})'s block already ended"));
                    }
                    if matches!(act, Act::Std(sc) if !x3a::child_ok(sc))
                        || matches!(act, Act::SpawnHelper(..) | Act::SpawnMissing(..))
                        || matches!(act, Act::Call(Call::Fork, _))
                    {
                        return Err(format!("step {i}: unsupported in a child block"));
                    }
                    if matches!(
                        act,
                        Act::ExecHelper
                            | Act::ExecParker
                            | Act::Park
                            | Act::Call(Call::Exit { .. }, _)
                    ) || x3a::ends_block(act)
                    {
                        forked.insert(k, true);
                    }
                    // A block must be contiguous after its fork.
                    let prev = &p.steps[i - 1];
                    let contiguous = i - 1 == k || prev.actor == Actor::Child(k);
                    if !contiguous {
                        return Err(format!("step {i}: Child({k})'s block is not contiguous"));
                    }
                }
            }
            _ => {}
        }
    }
    if let Some((k, _)) = forked.iter().find(|(_, ended)| !**ended) {
        return Err(format!(
            "fork step {k}'s block never ends (Exit, ExecHelper, ExecParker or Park)"
        ));
    }
    Ok(())
}

// =============================================================================
// Real execution
// =============================================================================

#[derive(Clone, Debug, Default)]
struct Rec {
    result: Option<SysResult>,
    obs: Vec<(Actor, Vec<RealFd>)>,
    error: Option<String>,
    /// A `ListOwnFds` step's entries `(fd, proc_fdtype)`, when it succeeded.
    listing: Option<Vec<(i32, u32)>>,
}

struct Real<'a> {
    pi: usize,
    probe: &'a Probe,
    env: &'a Env,
    results: Vec<SysResult>,
    recs: Vec<Rec>,
    sock: PathBuf,
    /// The real directory the model's relative path names live in.
    ns: PathBuf,
}

fn resolve_call(call: &Call<Operand>, results: &[SysResult]) -> Option<Call> {
    let mut bad = false;
    let out = call.map(|op| {
        op.resolve(&[], results).unwrap_or_else(|| {
            bad = true;
            -1
        })
    });
    if bad { None } else { Some(out) }
}

fn resolve_actions(
    actions: &[FileAction<Operand>],
    results: &[SysResult],
) -> Option<Vec<FileAction>> {
    match resolve_call(&Call::Spawn { actions: actions.to_vec(), flags: 0 }, results)? {
        Call::Spawn { actions, .. } => Some(actions),
        _ => None,
    }
}

/// The `sockaddr_un` for `path`, or `None` when it does not fit `sun_path`
/// (never truncated: a truncated path names some OTHER file).
fn sockaddr(path: &Path) -> Option<(libc::sockaddr_un, libc::socklen_t)> {
    // SAFETY: an all-zero sockaddr_un is valid.
    let mut addr: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    addr.sun_family = libc::AF_UNIX as libc::sa_family_t;
    let bytes = path.as_os_str().as_encoded_bytes();
    if bytes.len() >= addr.sun_path.len() {
        return None;
    }
    for (i, b) in bytes.iter().enumerate() {
        addr.sun_path[i] = *b as c_char;
    }
    let len = std::mem::size_of::<libc::sockaddr_un>();
    addr.sun_len = u8::try_from(len).unwrap_or(u8::MAX);
    Some((addr, libc::socklen_t::try_from(len).unwrap_or(0)))
}

/// One plain call on the real kernel. Async-signal-safe for the calls a
/// `pre_exec` hook makes (dup2, fcntl, close, ioctl): no allocation there.
/// The real path of a model path name: an absolute name as is (`/dev/null`),
/// a relative one in this probe's namespace directory — except the relative
/// path of an `openat` with a real `dirfd`, which the kernel must resolve (or
/// refuse) against that descriptor.
fn ns_path(ns: &Path, path: &str, at_real_dirfd: bool) -> CString {
    if path.starts_with('/') || at_real_dirfd {
        CString::new(path).unwrap_or_default()
    } else {
        CString::new(ns.join(path).as_os_str().as_encoded_bytes()).unwrap_or_default()
    }
}

/// The canonical spelling of an existing directory (`/var/folders/…` is
/// `/private/var/folders/…`): the model's working directory for it.
fn canonical_dir(dir: &Path) -> String {
    std::fs::canonicalize(dir)
        .ok()
        .and_then(|p| p.to_str().map(str::to_string))
        .unwrap_or_else(|| dir.to_string_lossy().into_owned())
}

/// A real node identity as one number (`dev`, `ino`): the conformance
/// compares identities by equality only, through a bijection with the
/// model's node ids.
fn node_key(dev: libc::dev_t, ino: u64) -> u64 {
    (u64::from(dev as u32) << 32) ^ (ino & 0xffff_ffff) ^ ((ino >> 32) << 48)
}

fn real_call(call: &Call, sock: &Path, ns: &Path) -> SysResult {
    // SAFETY (whole function): each arm is one syscall on plain integers or
    // on live local buffers.
    unsafe {
        match *call {
            Call::Pipe => {
                let mut fds = [0; 2];
                if libc::pipe(fds.as_mut_ptr()) < 0 {
                    Err(errno())
                } else {
                    Ok(Ret::Pair(fds[0], fds[1]))
                }
            }
            Call::Socketpair { domain, ty, protocol } => {
                let mut fds = [0; 2];
                if libc::socketpair(domain, ty, protocol, fds.as_mut_ptr()) < 0 {
                    Err(errno())
                } else {
                    Ok(Ret::Pair(fds[0], fds[1]))
                }
            }
            Call::Socket { domain, ty, protocol } => cvt(libc::socket(domain, ty, protocol)),
            Call::SocketOp { fd, op } => {
                let Some((addr, len)) = sockaddr(sock) else {
                    return Err(Errno::ENAMETOOLONG);
                };
                let rc = match op {
                    trust_platform::SocketOp::Bind => {
                        // An earlier run's socket file at this name would make
                        // the bind EADDRINUSE: the harness, not the probe, owns
                        // the name.
                        libc::unlink(addr.sun_path.as_ptr());
                        libc::bind(fd, (&raw const addr).cast(), len)
                    }
                    trust_platform::SocketOp::Listen => libc::listen(fd, 8),
                    trust_platform::SocketOp::Connect => {
                        libc::connect(fd, (&raw const addr).cast(), len)
                    }
                    _ => return Err(Errno::EINVAL),
                };
                cvt(rc)
            }
            Call::Accept { fd } => {
                cvt(libc::accept(fd, std::ptr::null_mut(), std::ptr::null_mut()))
            }
            Call::Kqueue => cvt(libc::kqueue()),
            Call::Fcntl { fd, cmd, arg } => {
                cvt(libc::fcntl(fd, cmd, c_int::try_from(arg).unwrap_or(c_int::MAX)))
            }
            Call::Dup { fd } => cvt(libc::dup(fd)),
            Call::Dup2 { from, to } => cvt(libc::dup2(from, to)),
            Call::Close { fd } => cvt(libc::close(fd)),
            Call::Ioctl { fd, request, arg } => {
                if request == darwin::FIONBIO {
                    let mut v: c_int = arg;
                    cvt(libc::ioctl(fd, request as libc::c_ulong, &mut v))
                } else {
                    cvt(libc::ioctl(fd, request as libc::c_ulong))
                }
            }
            Call::Getrlimit { resource } => {
                let mut rl = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
                if libc::getrlimit(resource, &mut rl) < 0 {
                    Err(errno())
                } else {
                    Ok(Ret::Rlimit { soft: rl.rlim_cur, hard: rl.rlim_max })
                }
            }
            Call::Setrlimit { resource, soft, hard } => {
                let rl = libc::rlimit { rlim_cur: soft, rlim_max: hard };
                cvt(libc::setrlimit(resource, &rl))
            }
            Call::Waitpid { pid, options } => {
                if options & libc::WNOHANG != 0 {
                    let mut st = 0;
                    return cvt(libc::waitpid(pid, &mut st, options));
                }
                // A blocking wait, polled so a hung probe times out.
                let deadline = Instant::now() + Duration::from_secs(30);
                loop {
                    let mut st = 0;
                    let rc = libc::waitpid(pid, &mut st, libc::WNOHANG);
                    if rc > 0 {
                        return Ok(Ret::Int(i64::from(rc)));
                    }
                    if rc < 0 {
                        return Err(errno());
                    }
                    if Instant::now() > deadline {
                        if pid > 0 {
                            libc::kill(pid, libc::SIGKILL);
                        }
                        return Err(Errno(60)); // ETIMEDOUT
                    }
                    std::thread::sleep(Duration::from_millis(1));
                }
            }
            Call::ReadSome { fd } => {
                let mut buf = [0u8; 64];
                let mut pfd = libc::pollfd { fd, events: libc::POLLIN, revents: 0 };
                if libc::poll(&mut pfd, 1, 10_000) == 0 {
                    return Err(Errno(60));
                }
                let n = libc::read(fd, buf.as_mut_ptr().cast(), buf.len());
                if n < 0 { Err(errno()) } else { Ok(Ret::Int(i64::from(n > 0))) }
            }
            Call::WriteSome { fd } => {
                let byte = [0u8; 1];
                let n = libc::write(fd, byte.as_ptr().cast(), 1);
                if n < 0 { Err(errno()) } else { Ok(Ret::Int(1)) }
            }
            Call::Flock { fd, op } => cvt(libc::flock(fd, op)),
            Call::Fstat { fd } => {
                let mut st: libc::stat = std::mem::zeroed();
                if libc::fstat(fd, &mut st) < 0 {
                    Err(errno())
                } else {
                    let ftype = i32::from(st.st_mode) & darwin::S_IFMT;
                    Ok(Ret::Stat { node: node_key(st.st_dev, st.st_ino), ftype })
                }
            }
            Call::OpenPath { at, ref path, flags } => {
                let real_dirfd = at.is_some_and(|d| d != darwin::AT_FDCWD);
                let p = ns_path(ns, path, real_dirfd);
                match at {
                    None => cvt(libc::open(p.as_ptr(), flags, 0o644 as libc::c_uint)),
                    Some(d) => cvt(libc::openat(d, p.as_ptr(), flags, 0o644 as libc::c_uint)),
                }
            }
            Call::Mkfifo { ref path } => {
                cvt(libc::mkfifo(ns_path(ns, path, false).as_ptr(), 0o600))
            }
            Call::Unlink { ref path } => cvt(libc::unlink(ns_path(ns, path, false).as_ptr())),
            // The target as written: a relative one names a file in the
            // LINK's directory, as in the model (`Host::link_target`).
            Call::Symlink { ref target, ref path } => cvt(libc::symlink(
                CString::new(target.as_str()).unwrap_or_default().as_ptr(),
                ns_path(ns, path, false).as_ptr(),
            )),
            Call::ListOwnFds { bytes } => x3a::real_list(bytes).0,
            Call::Sysctl { ref name, oldlen } => x3a::real_sysctl(name, oldlen),
            Call::CloexecFrom { first } => x3a::real_cloexec_from(first),
            Call::StdPlaceFd { .. }
            | Call::StdClearCloexec { .. }
            | Call::StdPassesExec { .. }
            | Call::StdMarkCloexec
            | Call::StdStatusFd { .. }
            | Call::StdCloseMovedStatus { .. } => {
                panic!("a raw kernel call contains a std composition")
            }
            Call::Open { .. }
            | Call::OpenAlias { .. }
            | Call::Fork
            | Call::Exec
            | Call::Spawn { .. }
            | Call::SpawnBegin
            | Call::SpawnEnd { .. }
            | Call::Resume { .. }
            | Call::Exit { .. }
            | Call::ThreadCreate => Err(Errno::EINVAL),
        }
    }
}

/// Wait until child `pid` has exited, leaving it unreaped (`waitid` with
/// `WNOWAIT`): the probe's own `waitpid` step reaps it later.
fn wait_exited(pid: libc::pid_t) -> Result<(), String> {
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        // SAFETY: an all-zero siginfo_t is valid; `info` is live.
        let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
        // SAFETY: a plain wait on our own child that reaps nothing.
        let rc = unsafe {
            libc::waitid(
                libc::P_PID,
                libc::id_t::try_from(pid).unwrap_or(0),
                &mut info,
                libc::WEXITED | libc::WNOWAIT | libc::WNOHANG,
            )
        };
        if rc < 0 {
            return Err(format!("waitid({pid}): {}", errno()));
        }
        if info.si_pid == pid {
            return Ok(());
        }
        if Instant::now() > deadline {
            return Err(format!("child {pid} never exited"));
        }
        std::thread::sleep(Duration::from_millis(1));
    }
}

fn real_open(path: &str, flags: i32) -> SysResult {
    let p = CString::new(path).unwrap_or_default();
    // SAFETY: a NUL-terminated path; mode is passed as the variadic int.
    cvt(unsafe { libc::open(p.as_ptr(), flags, 0o644 as libc::c_uint) })
}

impl Real<'_> {
    fn rec_path(&self, k: usize) -> PathBuf {
        self.env.dir.join(format!("p{}-c{}.rec", self.pi, k))
    }

    fn report_path(&self, i: usize) -> PathBuf {
        self.env.dir.join(format!("p{}-s{}.helper", self.pi, i))
    }

    fn run(mut self) -> Vec<Rec> {
        for i in 0..self.probe.steps.len() {
            let st = self.probe.steps[i].clone();
            match st.actor {
                Actor::Root => self.root_step(i, &st.act),
                Actor::Child(k) => {
                    if let Act::Kill = st.act
                        && let Ok(Ret::Int(pid)) = self.results[k]
                    {
                        let pid = i32::try_from(pid).unwrap_or(-1);
                        // SAFETY: our own child.
                        unsafe { libc::kill(pid, libc::SIGKILL) };
                        // The model's child is dead at this step: so is the
                        // real one before the root acts again.
                        if let Err(e) = wait_exited(pid) {
                            self.recs[i].error = Some(e);
                        }
                    }
                }
            }
        }
        self.collect();
        self.recs
    }

    fn set(&mut self, i: usize, r: SysResult) {
        self.results[i] = r;
        self.recs[i].result = Some(r);
    }

    fn root_step(&mut self, i: usize, act: &Act) {
        let r = match act {
            Act::Call(Call::Fork, _) => {
                // SAFETY: this process is single-threaded.
                let pid = unsafe { libc::fork() };
                if pid == 0 {
                    self.child_block(i);
                }
                if pid < 0 {
                    self.set(i, Err(errno()));
                } else {
                    self.set(i, Ok(Ret::Int(i64::from(pid))));
                    if let Err(e) = self.wait_blockend(i) {
                        self.recs[i].error = Some(e);
                    }
                    let me = Actor::Child(i);
                    // A block that ends in `_exit`: in the model the child is
                    // gone before the root's next step, but the real child
                    // writes BLOCKEND just BEFORE its `_exit` — wait (without
                    // reaping) until it has exited, or a root observation of
                    // a pipe it held races its descriptors' close.
                    let ends_in_exit = self
                        .probe
                        .steps
                        .iter()
                        .skip(i + 1)
                        .take_while(|s| s.actor == me)
                        .last()
                        .is_some_and(|s| matches!(s.act, Act::Call(Call::Exit { .. }, _)));
                    if ends_in_exit && let Err(e) = wait_exited(pid) {
                        self.recs[i].error = Some(e);
                    }
                    // A block that ends in an exec: the reporter must have
                    // snapshotted before the root acts again, or a later root
                    // step (a close) races the child's observation.
                    let exec_at = self
                        .probe
                        .steps
                        .iter()
                        .enumerate()
                        .skip(i + 1)
                        .take_while(|(_, s)| s.actor == me)
                        .find(|(_, s)| {
                            matches!(s.act, Act::ExecHelper | Act::ExecParker)
                                || x3a::is_exec_success(&s.act)
                        })
                        .map(|(j, _)| j);
                    if let Some(j) = exec_at
                        && let Err(e) = self.wait_report(j)
                    {
                        self.recs[j].error = Some(e);
                    }
                }
                return;
            }
            Act::Call(Call::ListOwnFds { bytes }, _) => {
                let (r, listed) = x3a::real_list(*bytes);
                if r.is_ok() {
                    self.recs[i].listing = Some(listed);
                }
                r
            }
            Act::Call(call, _) => match resolve_call(call, &self.results) {
                Some(call) => real_call(&call, &self.sock, &self.ns),
                None => {
                    self.recs[i].error = Some("unresolved operand".into());
                    Err(Errno(0))
                }
            },
            Act::OpenNull(flags) => real_open("/dev/null", *flags),
            Act::OpenMissing(flags) => real_open(MISSING, *flags),
            Act::OpenRoot => real_open("/", libc::O_RDONLY),
            Act::OpenAlias(op, flags) => match op.resolve(&[], &self.results) {
                Some(fd) => real_open(&format!("/dev/fd/{fd}"), *flags),
                None => Err(Errno(0)),
            },
            Act::SpawnHelper(actions, flags)
            | Act::SpawnMissing(actions, flags)
            | Act::SpawnChdirMissing(actions, flags) => {
                let path = if matches!(act, Act::SpawnMissing(..)) {
                    CString::new(MISSING).unwrap_or_default()
                } else {
                    self.env.exe.clone()
                };
                let chdir = if matches!(act, Act::SpawnChdirMissing(..)) { MISSING } else { "/" };
                match resolve_actions(actions, &self.results) {
                    Some(actions) => self.real_spawn(&path, &actions, *flags, chdir, i),
                    None => Err(Errno(0)),
                }
            }
            Act::Std(sc) => self.real_std(sc, i),
            Act::Observe => Ok(Ret::Int(0)),
            other => {
                self.recs[i].error = Some(format!("root cannot {other:?}"));
                Err(Errno(0))
            }
        };
        if !matches!(act, Act::Observe) {
            self.set(i, r);
        }
        let spawns = matches!(
            act,
            Act::SpawnHelper(..) | Act::Std(StdCall::SpawnFork(_) | StdCall::SpawnPosix { .. })
        ) || x3a::spawns_reporter(act);
        if spawns
            && r.is_ok()
            && let Err(e) = self.wait_report(i)
        {
            self.recs[i].error = Some(e);
        }
        self.recs[i].obs.push((Actor::Root, snapshot()));
    }

    fn real_spawn(
        &self,
        path: &CString,
        actions: &[FileAction],
        flags: i32,
        chdir: &str,
        i: usize,
    ) -> SysResult {
        let chdir = CString::new(chdir).unwrap_or_default();
        let report =
            CString::new(self.report_path(i).as_os_str().as_encoded_bytes()).unwrap_or_default();
        let flag = CString::new(REPORTER_FLAG).unwrap_or_default();
        let devnull = CString::new("/dev/null").unwrap_or_default();
        let argv = [path.as_ptr(), flag.as_ptr(), report.as_ptr(), std::ptr::null()];
        let envp: [*const c_char; 1] = [std::ptr::null()];
        // SAFETY: the action/attr objects are initialised before use and
        // destroyed once; argv/envp are NULL-terminated and outlive the call.
        unsafe {
            let mut fa: libc::posix_spawn_file_actions_t = std::ptr::null_mut();
            let mut at: libc::posix_spawnattr_t = std::ptr::null_mut();
            libc::posix_spawn_file_actions_init(&mut fa);
            libc::posix_spawnattr_init(&mut at);
            let mut rc = libc::posix_spawnattr_setflags(
                &mut at,
                libc::c_short::try_from(flags).unwrap_or(0),
            );
            for a in actions {
                if rc != 0 {
                    break;
                }
                rc = match *a {
                    FileAction::Close { fd } => {
                        libc::posix_spawn_file_actions_addclose(&mut fa, fd)
                    }
                    FileAction::Dup2 { from, to } => {
                        libc::posix_spawn_file_actions_adddup2(&mut fa, from, to)
                    }
                    FileAction::Open { fd, flags } => libc::posix_spawn_file_actions_addopen(
                        &mut fa,
                        fd,
                        devnull.as_ptr(),
                        flags,
                        0,
                    ),
                    FileAction::Inherit { fd } => {
                        posix_spawn_file_actions_addinherit_np(&mut fa, fd)
                    }
                    FileAction::Chdir => {
                        posix_spawn_file_actions_addchdir_np(&mut fa, chdir.as_ptr())
                    }
                    FileAction::Fchdir { fd } => posix_spawn_file_actions_addfchdir_np(&mut fa, fd),
                    // Only modeled std rows use these builders. Raw probe
                    // actions must name actual POSIX operations.
                    FileAction::InheritIf { .. } | FileAction::PlaceStdio { .. } => {
                        panic!("a raw kernel probe contains an unresolved std builder")
                    }
                };
            }
            let mut pid: libc::pid_t = 0;
            if rc == 0 {
                rc = libc::posix_spawn(
                    &mut pid,
                    path.as_ptr(),
                    &fa,
                    &at,
                    argv.as_ptr().cast(),
                    envp.as_ptr().cast(),
                );
            }
            libc::posix_spawn_file_actions_destroy(&mut fa);
            libc::posix_spawnattr_destroy(&mut at);
            if rc != 0 { Err(Errno(rc)) } else { Ok(Ret::Int(i64::from(pid))) }
        }
    }

    fn real_std(&mut self, sc: &StdCall, i: usize) -> SysResult {
        use std::os::unix::net::{UnixDatagram, UnixListener, UnixStream};
        use std::os::unix::process::CommandExt;
        let io = |e: std::io::Error| Errno(e.raw_os_error().unwrap_or(0));
        let pair = |a: i32, b: i32| Ok(Ret::Pair(a, b));
        let one = |a: i32| Ok(Ret::Int(i64::from(a)));
        let arg = |op: &Operand, results: &[SysResult]| op.resolve(&[], results).unwrap_or(-1);
        match sc {
            StdCall::Pipe => {
                let (rd, wr) = std::io::pipe().map_err(io)?;
                pair(rd.into_raw_fd(), wr.into_raw_fd())
            }
            StdCall::Pair => {
                let (a, b) = UnixStream::pair().map_err(io)?;
                pair(a.into_raw_fd(), b.into_raw_fd())
            }
            StdCall::PairDgram => {
                let (a, b) = UnixDatagram::pair().map_err(io)?;
                pair(a.into_raw_fd(), b.into_raw_fd())
            }
            StdCall::TryClone(op) => {
                let fd = arg(op, &self.results);
                // SAFETY: `fd` is open for the duration of the call.
                let b = unsafe { BorrowedFd::borrow_raw(fd) };
                one(b.try_clone_to_owned().map_err(io)?.into_raw_fd())
            }
            StdCall::OpenNullRo => one(std::fs::File::open("/dev/null").map_err(io)?.into_raw_fd()),
            StdCall::UnixBind => {
                // As for a raw bind: remove a leftover socket file first.
                let _ = std::fs::remove_file(&self.sock);
                one(UnixListener::bind(&self.sock).map_err(io)?.into_raw_fd())
            }
            StdCall::UnixConnect => one(UnixStream::connect(&self.sock).map_err(io)?.into_raw_fd()),
            StdCall::Accept(op) => {
                use std::os::fd::FromRawFd;
                let fd = arg(op, &self.results);
                // SAFETY: the listener descriptor is open; ManuallyDrop keeps it.
                let l = std::mem::ManuallyDrop::new(unsafe { UnixListener::from_raw_fd(fd) });
                let (s, _) = l.accept().map_err(io)?;
                one(s.into_raw_fd())
            }
            StdCall::SpawnFork(hooks) => {
                let hooks: Vec<Call> =
                    hooks.iter().filter_map(|h| resolve_call(h, &self.results)).collect();
                let mut cmd = self.reporter_command(i);
                let sock = self.sock.clone();
                let ns = self.ns.clone();
                // SAFETY: the closure runs dup2/fcntl/close/ioctl through
                // `real_call` (no allocation for those arms) in the child.
                unsafe {
                    cmd.pre_exec(move || {
                        for h in &hooks {
                            let _ = real_call(h, &sock, &ns);
                        }
                        Ok(())
                    });
                }
                let child = cmd.spawn().map_err(io)?;
                let pid = child.id();
                std::mem::forget(child);
                Ok(Ret::Int(i64::from(pid)))
            }
            StdCall::SpawnForkMissing(hooks) => {
                let hooks: Vec<Call> =
                    hooks.iter().filter_map(|h| resolve_call(h, &self.results)).collect();
                let mut cmd = std::process::Command::new(MISSING);
                let sock = self.sock.clone();
                let ns = self.ns.clone();
                // SAFETY: as for `SpawnFork`.
                unsafe {
                    cmd.pre_exec(move || {
                        for h in &hooks {
                            let _ = real_call(h, &sock, &ns);
                        }
                        Ok(())
                    });
                }
                let child = cmd.spawn().map_err(io)?;
                let pid = child.id();
                std::mem::forget(child);
                Ok(Ret::Int(i64::from(pid)))
            }
            StdCall::SpawnPosix { stdin_null } => {
                let mut cmd = self.reporter_command(i);
                if *stdin_null {
                    cmd.stdin(std::process::Stdio::null());
                }
                let child = cmd.spawn().map_err(io)?;
                let pid = child.id();
                std::mem::forget(child);
                Ok(Ret::Int(i64::from(pid)))
            }
            StdCall::X(x) => x3a::real_std(self, x, i),
        }
    }

    fn reporter_command(&self, i: usize) -> std::process::Command {
        use std::os::unix::ffi::OsStrExt;
        let exe = std::ffi::OsStr::from_bytes(self.env.exe.as_bytes());
        let mut cmd = std::process::Command::new(exe);
        cmd.arg(REPORTER_FLAG).arg(self.report_path(i));
        cmd
    }

    fn append(&self, k: usize, line: &str) {
        use std::io::Write;
        if let Ok(mut f) =
            std::fs::OpenOptions::new().create(true).append(true).open(self.rec_path(k))
        {
            let _ = f.write_all(line.as_bytes());
        }
    }

    fn record(&self, k: usize, i: usize, r: Option<&SysResult>) {
        let fds = snapshot();
        let mut s = String::new();
        if let Some(r) = r {
            s.push_str(&format!("R {i} {}\n", encode_result(r)));
        }
        s.push_str(&format!("O {i}"));
        for f in &fds {
            s.push(' ');
            s.push_str(&f.encode());
        }
        s.push('\n');
        self.append(k, &s);
    }

    /// Runs in the forked child: the block of steps whose actor is
    /// `Child(k)`. Never returns.
    fn child_block(&mut self, k: usize) -> ! {
        let me = Actor::Child(k);
        let steps = self.probe.steps.clone();
        let mut i = k + 1;
        while i < steps.len() && steps[i].actor == me {
            match &steps[i].act {
                Act::Call(Call::Exit { status }, _) => {
                    self.append(k, &format!("R {i} noreturn\nBLOCKEND\n"));
                    // SAFETY: leaving the child.
                    unsafe { libc::_exit(*status) };
                }
                Act::Call(Call::ListOwnFds { bytes }, _) => {
                    let (r, listed) = x3a::real_list(*bytes);
                    self.results[i] = r;
                    if r.is_ok() {
                        self.append(k, &x3a::encode_listing(i, &listed));
                    }
                    self.record(k, i, Some(&r));
                }
                Act::Call(call, _) => {
                    let r = resolve_call(call, &self.results)
                        .map_or(Err(Errno(0)), |c| real_call(&c, &self.sock, &self.ns));
                    self.results[i] = r;
                    self.record(k, i, Some(&r));
                }
                Act::Std(StdCall::X(x)) => x3a::child_std(self, k, i, x),
                Act::OpenNull(flags) | Act::OpenMissing(flags) => {
                    let path = if matches!(steps[i].act, Act::OpenNull(_)) {
                        "/dev/null"
                    } else {
                        MISSING
                    };
                    let r = real_open(path, *flags);
                    self.results[i] = r;
                    self.record(k, i, Some(&r));
                }
                Act::ExecHelper | Act::ExecParker | Act::ExecMissing => {
                    let helper = matches!(steps[i].act, Act::ExecHelper | Act::ExecParker);
                    let path = if helper {
                        self.env.exe.clone()
                    } else {
                        CString::new(MISSING).unwrap_or_default()
                    };
                    let report = CString::new(self.report_path(i).as_os_str().as_encoded_bytes())
                        .unwrap_or_default();
                    let flag = if matches!(steps[i].act, Act::ExecParker) {
                        REPORTER_PARK_FLAG
                    } else {
                        REPORTER_FLAG
                    };
                    let flag = CString::new(flag).unwrap_or_default();
                    let argv = [path.as_ptr(), flag.as_ptr(), report.as_ptr(), std::ptr::null()];
                    if helper {
                        self.append(k, "BLOCKEND\n");
                    }
                    // SAFETY: NULL-terminated argv of live CStrings.
                    unsafe { libc::execv(path.as_ptr(), argv.as_ptr()) };
                    let r = Err(errno());
                    self.results[i] = r;
                    self.record(k, i, Some(&r));
                    if helper {
                        // SAFETY: leaving the child.
                        unsafe { libc::_exit(99) };
                    }
                }
                Act::Observe => self.record(k, i, None),
                Act::Park => {
                    self.append(k, "BLOCKEND\n");
                    loop {
                        // SAFETY: async-signal-safe wait for SIGKILL.
                        unsafe { libc::pause() };
                    }
                }
                _ => {}
            }
            i += 1;
        }
        self.append(k, "BLOCKEND\n");
        // SAFETY: leaving the child.
        unsafe { libc::_exit(98) }
    }

    fn wait_blockend(&self, k: usize) -> Result<(), String> {
        let deadline = Instant::now() + Duration::from_secs(20);
        loop {
            if std::fs::read_to_string(self.rec_path(k))
                .is_ok_and(|s| s.lines().any(|l| l == "BLOCKEND"))
            {
                return Ok(());
            }
            if Instant::now() > deadline {
                return Err(format!("child of step {k} never finished its block"));
            }
            std::thread::sleep(Duration::from_millis(1));
        }
    }

    fn wait_report(&self, i: usize) -> Result<(), String> {
        let deadline = Instant::now() + Duration::from_secs(20);
        while !self.report_path(i).exists() {
            if Instant::now() > deadline {
                return Err(format!("the reporter of step {i} wrote no table"));
            }
            std::thread::sleep(Duration::from_millis(1));
        }
        Ok(())
    }

    /// Fold the children's records and the reporters' tables into `recs`.
    fn collect(&mut self) {
        for (k, s) in self.probe.steps.iter().enumerate() {
            if !matches!((s.actor, &s.act), (Actor::Root, Act::Call(Call::Fork, _))) {
                continue;
            }
            let text = std::fs::read_to_string(self.rec_path(k)).unwrap_or_default();
            for line in text.lines() {
                let mut parts = line.splitn(3, ' ');
                let tag = parts.next().unwrap_or("");
                let Some(i) = parts.next().and_then(|v| v.parse::<usize>().ok()) else {
                    continue;
                };
                let rest = parts.next().unwrap_or("");
                match tag {
                    "L" => self.recs[i].listing = Some(x3a::decode_listing(rest)),
                    "R" => self.recs[i].result = decode_result(rest),
                    "O" => {
                        let fds = rest.split_whitespace().filter_map(RealFd::decode).collect();
                        self.recs[i].obs.push((Actor::Child(k), fds));
                    }
                    _ => {}
                }
            }
        }
        for (i, s) in self.probe.steps.iter().enumerate() {
            let exec_actor = match (&s.act, s.actor) {
                (Act::ExecHelper | Act::ExecParker, a) => a,
                (act, a) if x3a::is_exec_success(act) => a,
                (act, _) if x3a::spawns_reporter(act) => Actor::Child(i),
                (
                    Act::SpawnHelper(..)
                    | Act::Std(StdCall::SpawnFork(_) | StdCall::SpawnPosix { .. }),
                    _,
                ) => Actor::Child(i),
                _ => continue,
            };
            match std::fs::read_to_string(self.report_path(i)) {
                Ok(text) => {
                    let fds = text
                        .lines()
                        .filter_map(|l| l.strip_prefix("H "))
                        .filter_map(RealFd::decode)
                        .collect();
                    self.recs[i].obs.push((exec_actor, fds));
                    if matches!(s.act, Act::ExecHelper | Act::ExecParker)
                        || x3a::is_exec_success(&s.act)
                    {
                        self.recs[i].result = Some(Ok(Ret::NoReturn));
                    }
                }
                Err(_) => {
                    if matches!(self.recs[i].result, Some(Ok(_)))
                        || matches!(s.act, Act::ExecHelper | Act::ExecParker)
                        || x3a::is_exec_success(&s.act)
                    {
                        self.recs[i].error = Some("the reporter wrote no table".into());
                    }
                }
            }
        }
    }
}

fn encode_result(r: &SysResult) -> String {
    match r {
        Ok(Ret::Int(v)) => format!("int {v}"),
        Ok(Ret::Pair(a, b)) => format!("pair {a} {b}"),
        Ok(Ret::Rlimit { soft, hard }) => format!("rlimit {soft} {hard}"),
        Ok(Ret::Stat { node, ftype }) => format!("stat {node} {ftype}"),
        Ok(Ret::NoReturn) => "noreturn".into(),
        Ok(Ret::Pending { fd }) => format!("pending {fd}"),
        Err(e) => format!("err {}", e.0),
    }
}

fn decode_result(s: &str) -> Option<SysResult> {
    let v: Vec<&str> = s.split_whitespace().collect();
    Some(match v.as_slice() {
        ["int", x] => Ok(Ret::Int(x.parse().ok()?)),
        ["pair", a, b] => Ok(Ret::Pair(a.parse().ok()?, b.parse().ok()?)),
        ["rlimit", a, b] => Ok(Ret::Rlimit { soft: a.parse().ok()?, hard: b.parse().ok()? }),
        ["stat", n, t] => Ok(Ret::Stat { node: n.parse().ok()?, ftype: t.parse().ok()? }),
        ["noreturn"] => Ok(Ret::NoReturn),
        ["pending", fd] => Ok(Ret::Pending { fd: fd.parse().ok()? }),
        ["err", e] => Err(Errno(e.parse().ok()?)),
        _ => return None,
    })
}

// =============================================================================
// Model replay and comparison
// =============================================================================

fn std_row(
    sem: &dyn Spec,
    sc: &StdCall,
    results: &[SysResult],
) -> Result<(StdRow, Vec<i32>), String> {
    let arg = |op: &Operand| {
        op.resolve(&[], results).ok_or_else(|| "unresolved std argument".to_string())
    };
    Ok(match sc {
        StdCall::Pipe => (std_summaries::std_pipe(), vec![]),
        StdCall::Pair => (std_summaries::std_pair(darwin::SOCK_STREAM), vec![]),
        StdCall::PairDgram => (std_summaries::std_pair(darwin::SOCK_DGRAM), vec![]),
        StdCall::TryClone(op) => (std_summaries::std_try_clone(), vec![arg(op)?]),
        StdCall::OpenNullRo => (std_summaries::std_open(darwin::O_RDONLY), vec![]),
        StdCall::UnixBind => (std_summaries::std_unix_listener_bind(), vec![]),
        StdCall::UnixConnect => (std_summaries::std_unix_stream_connect(), vec![]),
        StdCall::Accept(op) => (std_summaries::std_accept(), vec![arg(op)?]),
        StdCall::SpawnFork(hooks) => {
            let mut fr = spawn_fork_row(sem, hooks, results)?;
            sem.mutate_spawn(&mut fr.row);
            (fr.row, vec![])
        }
        StdCall::SpawnPosix { stdin_null } => {
            let stdin = if *stdin_null { StdioPlan::Null } else { StdioPlan::Inherit };
            let mut shape = CommandShape::default();
            sem.mutate_shape(&mut shape);
            let stdio = [stdin, StdioPlan::Inherit, StdioPlan::Inherit];
            let mut row = std_summaries::command_spawn_posix(stdio, &shape)?.0;
            sem.mutate_spawn(&mut row);
            (row, vec![])
        }
        StdCall::SpawnForkMissing(_) => {
            return Err("a missing program's spawn replays in spawn_fork_missing".to_string());
        }
        StdCall::X(_) => return Err("an X3a call replays in x3a::replay".to_string()),
    })
}

/// STD-SPAWN-FORK for [`StdCall::SpawnFork`]'s command (inherited stdio, one
/// `pre_exec` closure of these calls), under the spec's shape.
fn spawn_fork_row(
    sem: &dyn Spec,
    hooks: &[Call<Operand>],
    results: &[SysResult],
) -> Result<std_summaries::ForkRow, String> {
    let hooks: Vec<Call<Operand>> = hooks
        .iter()
        .map(|h| resolve_call(h, results).map(|c| c.map(|v| Operand::Lit(*v))))
        .collect::<Option<_>>()
        .ok_or("unresolved hook operand")?;
    let mut shape = CommandShape::with_pre_exec();
    sem.mutate_shape(&mut shape);
    std_summaries::command_spawn_fork([StdioPlan::Inherit; 3], &shape, &[hooks])
}

/// The model of [`StdCall::SpawnForkMissing`]: STD-SPAWN-FORK with the
/// child's `execvp` failing `ENOENT` and the row's error path — the child
/// writes its errno to the status write end and `_exit(1)`s; when the
/// parent's status read then returns data, it reaps the child
/// ([`std_summaries::ForkRow::parent_error`]) and the spawn returns
/// `ENOENT`, and when it returns end-of-file, the child's pid.
fn spawn_fork_missing(
    sem: &dyn Spec,
    h: &Host,
    root: Pid,
    hooks: &[Call<Operand>],
    results: &[SysResult],
) -> Result<(Host, SysResult), String> {
    let mut fr = spawn_fork_row(sem, hooks, results)?;
    sem.mutate_spawn(&mut fr.row);
    let child = Actor::Child(fr.fork);
    // Steps after the exec name only steps before the fork, so the error
    // path's insertions keep every operand's index.
    let program = |reaped: bool| -> Vec<ProgramStep> {
        let row = &fr.row.program;
        let mut p: Vec<ProgramStep> = row[..=fr.exec].to_vec();
        p[fr.exec].oracle = Oracle::Fail(Errno::ENOENT);
        p.extend(fr.child_error.iter().map(|c| ProgramStep::by(child, c.clone())));
        p.extend(row[fr.exec + 1..=fr.status_read].iter().cloned());
        if reaped {
            p.extend(fr.parent_error.iter().map(|c| ProgramStep::root(c.clone())));
        }
        p.extend(row[fr.status_read + 1..].iter().cloned());
        p
    };
    let status_at = fr.status_read + fr.child_error.len();
    let run = |p: &[ProgramStep]| {
        script::run(sem, h, root, p, &[]).map_err(|e| format!("std row {}: {e:?}", fr.row.id))
    };
    let trace = run(&program(false))?;
    let reported = matches!(trace.get(status_at).map(|t| t.result), Some(Ok(Ret::Int(n))) if n > 0);
    let trace = if reported { run(&program(true))? } else { trace };
    let host = trace.last().map_or_else(|| h.clone(), |t| t.host.clone());
    let result = if reported {
        Err(Errno::ENOENT)
    } else {
        trace.get(fr.fork).map_or(Err(Errno(0)), |t| t.result)
    };
    Ok((host, result))
}

fn returns_pid(act: &Act) -> bool {
    matches!(
        act,
        Act::Call(Call::Fork | Call::Waitpid { .. }, _)
            | Act::SpawnHelper(..)
            | Act::SpawnMissing(..)
            | Act::SpawnChdirMissing(..)
            | Act::Std(
                StdCall::SpawnFork(_) | StdCall::SpawnPosix { .. } | StdCall::SpawnForkMissing(_)
            )
    )
}

fn same_result(act: &Act, model: &SysResult, real: &SysResult) -> bool {
    if returns_pid(act) {
        match (model, real) {
            // Model pids are not the kernel's, but "no child yet" (a WNOHANG
            // poll's 0) is not a pid.
            (Ok(Ret::Int(a)), Ok(Ret::Int(b))) => (*a == 0) == (*b == 0),
            (Ok(_), Ok(_)) => true,
            (Err(a), Err(b)) => a == b,
            _ => false,
        }
    } else {
        model == real
    }
}

/// Compare the model's view of each observed process with the real tables.
fn compare_obs(h: &Host, views: &[(Pid, &[RealFd])]) -> Result<(), String> {
    // (ofd, (dev, ino), where) for pipes and sockets, for the identity check.
    let mut idents: Vec<(trust_platform::OfdId, (i64, u64), String)> = Vec::new();
    // (node, (dev, ino), where) for descriptions a named open put on a node.
    let mut nodes: Vec<(trust_platform::NodeId, (i64, u64), String)> = Vec::new();
    for (pid, real) in views {
        let proc = h.proc(*pid).ok_or_else(|| format!("model has no process {pid:?}"))?;
        let model_fds: Vec<i32> = proc.table.keys().copied().collect();
        let real_fds: Vec<i32> = real.iter().map(|f| f.fd).collect();
        if model_fds != real_fds {
            return Err(format!("{pid:?} descriptors: model {model_fds:?}, real {real_fds:?}"));
        }
        for rf in real.iter() {
            let e = proc.table[&rf.fd];
            if e.cloexec != rf.cloexec {
                return Err(format!(
                    "{pid:?} fd {}: FD_CLOEXEC model {}, real {}",
                    rf.fd, e.cloexec, rf.cloexec
                ));
            }
            let o = h.ofd(e.ofd).ok_or("dangling entry")?;
            if o.kind != OfdKind::Opaque && o.getfl() != rf.getfl {
                return Err(format!(
                    "{pid:?} fd {}: F_GETFL model {:#x}, real {:#x}",
                    rf.fd,
                    o.getfl(),
                    rf.getfl
                ));
            }
            let tracked = matches!(o.kind, OfdKind::PipeRead | OfdKind::Socket { .. })
                && o.peer != Peer::None;
            if tracked {
                let readable = o.peer == Peer::Closed || o.unread;
                if readable != rf.readable {
                    return Err(format!(
                        "{pid:?} fd {}: readable (data or end-of-file) model {readable}, real {}",
                        rf.fd, rf.readable
                    ));
                }
            }
            // fstat names a pipe end or an AF_UNIX socket uniquely; an
            // AF_INET/AF_INET6 socket answers st_ino 0 (no identity to compare).
            if matches!(o.kind, OfdKind::PipeRead | OfdKind::PipeWrite | OfdKind::Socket { .. })
                && rf.ino != 0
            {
                idents.push((e.ofd, (rf.dev, rf.ino), format!("{pid:?}/fd{}", rf.fd)));
            }
            if let Some(n) = o.node {
                nodes.push((n, (rf.dev, rf.ino), format!("{pid:?}/fd{}", rf.fd)));
            }
        }
    }
    for (i, a) in idents.iter().enumerate() {
        for b in &idents[i + 1..] {
            let model_same = a.0 == b.0;
            let real_same = a.1 == b.1;
            if model_same != real_same {
                return Err(format!(
                    "{} and {}: same open file description in the model: {model_same}, in the kernel: {real_same}",
                    a.2, b.2
                ));
            }
        }
    }
    for (i, a) in nodes.iter().enumerate() {
        for b in &nodes[i + 1..] {
            let (model_same, real_same) = (a.0 == b.0, a.1 == b.1);
            if model_same != real_same {
                return Err(format!(
                    "{} and {}: same node in the model: {model_same}, in the kernel: {real_same}",
                    a.2, b.2
                ));
            }
        }
    }
    Ok(())
}

fn label(s: &PStep) -> String {
    let who = match s.actor {
        Actor::Root => "root".to_string(),
        Actor::Child(k) => format!("child@{k}"),
    };
    let what = match &s.act {
        Act::Call(c, Oracle::Nominal) => format!("{c:?}"),
        Act::Call(c, o) => format!("{c:?} [{o:?}]"),
        other => format!("{other:?}"),
    };
    format!("{who} {what}")
}

struct Replayed {
    steps: usize,
    observations: usize,
}

/// A spec the probes replay: the clauses ([`Semantics`]) plus the std rows
/// built from them, which an X3a row mutant changes.
trait Spec: Semantics {
    fn mutate_row(&self, _row: &mut StdRow) {}
    fn mutate_cfg(&self, _cfg: &mut x3a::CmdCfg) {}
    fn mutate_command(&self, _cr: &mut std_summaries::CommandRow) {}
    /// A `Command`'s shape before its row is built (`Command::spawn`,
    /// `output`, `status`, `exec`).
    fn mutate_shape(&self, _shape: &mut CommandShape) {}
    /// A built row that spawns (STD-SPAWN-FORK/POSIX, the spawn inside
    /// STD-COMMAND-OUTPUT/STATUS).
    fn mutate_spawn(&self, _row: &mut StdRow) {}
}

impl Spec for Darwin {}
impl Spec for Mutant {}

fn replay(
    sem: &dyn Spec,
    init: &Host,
    root: Pid,
    probe: &Probe,
    init_real: &[RealFd],
    recs: &[Rec],
) -> Result<Replayed, String> {
    compare_obs(init, &[(root, init_real)]).map_err(|e| format!("initial table: {e}"))?;
    let mut h = init.clone();
    let mut results: Vec<SysResult> = Vec::new();
    let mut observations = 1;
    let mut stat_nodes: BTreeMap<u64, u64> = BTreeMap::new();
    let mut stat_nodes_back: BTreeMap<u64, u64> = BTreeMap::new();
    let refused = |i: usize, r: Refusal| format!("step {i}: refused: {r}");
    for (i, st) in probe.steps.iter().enumerate() {
        let pid = script::actor_pid(st.actor, root, &results)
            .ok_or_else(|| format!("step {i}: no such actor"))?;
        // A probe is single-threaded: a call that has not returned is
        // continued at once (a real one that waited would have hung the run).
        let one = |h: &Host, call: Call, o: Oracle| {
            let mut s = sem.step(h, pid, &call, o).map_err(|r| refused(i, r))?;
            while let Ok(Ret::Pending { fd }) = s.result {
                s = sem
                    .step(&s.host, pid, &Call::Resume { fd }, Oracle::Nominal)
                    .map_err(|r| refused(i, r))?;
            }
            Ok::<Step, String>(s)
        };
        let unresolved = || format!("step {i}: unresolved operand");
        let mut child_obs_done = false;
        let (next, res): (Host, Option<SysResult>) = match &st.act {
            Act::Call(call, o) => {
                let call = resolve_call(call, &results).ok_or_else(unresolved)?;
                if let Call::ListOwnFds { bytes } = call {
                    x3a::check_listing(sem, &h, pid, bytes, &recs[i])
                        .map_err(|e| format!("step {i} [{}]: {e}", label(st)))?;
                }
                let s = one(&h, call, *o)?;
                (s.host, Some(s.result))
            }
            Act::Std(StdCall::X(x)) => {
                let (host, result, done) = x3a::replay(sem, &h, pid, x, &results, &recs[i], i)
                    .map_err(|e| format!("step {i} [{}]: {e}", label(st)))?;
                child_obs_done = done;
                (host, Some(result))
            }
            Act::OpenNull(f) => {
                let s = one(&h, Call::Open { flags: *f }, Oracle::Nominal)?;
                (s.host, Some(s.result))
            }
            Act::OpenMissing(f) => {
                let s = one(&h, Call::Open { flags: *f }, Oracle::Fail(Errno::ENOENT))?;
                (s.host, Some(s.result))
            }
            Act::OpenRoot => {
                let s = one(&h, Call::Open { flags: darwin::O_RDONLY }, Oracle::Nominal)?;
                (s.host, Some(s.result))
            }
            Act::OpenAlias(op, f) => {
                let fd = op.resolve(&[], &results).ok_or_else(unresolved)?;
                let s = one(&h, Call::OpenAlias { fd, flags: *f }, Oracle::Nominal)?;
                (s.host, Some(s.result))
            }
            Act::ExecHelper | Act::ExecParker | Act::ExecMissing => {
                let o = if matches!(st.act, Act::ExecHelper | Act::ExecParker) {
                    Oracle::Nominal
                } else {
                    Oracle::Fail(Errno::ENOENT)
                };
                let s = one(&h, Call::Exec, o)?;
                (s.host, Some(s.result))
            }
            Act::SpawnHelper(actions, flags)
            | Act::SpawnMissing(actions, flags)
            | Act::SpawnChdirMissing(actions, flags) => {
                let actions = resolve_actions(actions, &results).ok_or_else(unresolved)?;
                let o = if matches!(st.act, Act::SpawnHelper(..)) {
                    Oracle::Nominal
                } else {
                    Oracle::Fail(Errno::ENOENT)
                };
                let s = one(&h, Call::Spawn { actions, flags: *flags }, o)?;
                (s.host, Some(s.result))
            }
            Act::ImageExits => (one(&h, Call::Exit { status: 0 }, Oracle::Nominal)?.host, None),
            Act::Kill => (one(&h, Call::Exit { status: 128 + 9 }, Oracle::Nominal)?.host, None),
            Act::Park | Act::Observe => (h.clone(), None),
            Act::Std(StdCall::SpawnForkMissing(hooks)) => {
                let (host, result) = spawn_fork_missing(sem, &h, pid, hooks, &results)
                    .map_err(|e| format!("step {i} [{}]: {e}", label(st)))?;
                (host, Some(result))
            }
            Act::Std(sc) => {
                let (row, args) = std_row(sem, sc, &results)?;
                let trace = script::run(sem, &h, pid, &row.program, &args)
                    .map_err(|e| format!("step {i}: std row {}: {e:?}", row.id))?;
                let rs: Vec<SysResult> = trace.iter().map(|t| t.result).collect();
                let vals: Option<Vec<i32>> =
                    row.returns.iter().map(|op| op.resolve(&args, &rs)).collect();
                let result = match vals.as_deref() {
                    Some([a]) => Ok(Ret::Int(i64::from(*a))),
                    Some([a, b]) => Ok(Ret::Pair(*a, *b)),
                    _ => Err(rs.iter().find_map(|r| r.err()).unwrap_or(Errno(0))),
                };
                (trace.last().map_or_else(|| h.clone(), |t| t.host.clone()), Some(result))
            }
        };
        h = next;
        results.push(res.unwrap_or(Err(Errno(0))));
        // fstat identities: equal model nodes <-> equal real (dev, ino).
        if let (
            Some(Ok(Ret::Stat { node: mn, ftype: mt })),
            Some(Ok(Ret::Stat { node: rn, ftype: rt })),
        ) = (&res, &recs[i].result)
        {
            let fwd = *stat_nodes.entry(*mn).or_insert(*rn);
            let back = *stat_nodes_back.entry(*rn).or_insert(*mn);
            if fwd != *rn || back != *mn || mt != rt {
                return Err(format!(
                    "step {i} [{}]: fstat model node {mn} type {mt:#o}, kernel node {rn:#x} type \
                     {rt:#o}: the identities do not correspond",
                    label(st)
                ));
            }
        } else if let (Some(m), Some(real)) = (&res, &recs[i].result)
            && !same_result(&st.act, m, real)
        {
            return Err(format!("step {i} [{}]: model returned {m:?}, kernel {real:?}", label(st)));
        }
        let mut views: Vec<(Pid, &[RealFd])> = Vec::new();
        for (actor, fds) in &recs[i].obs {
            if child_obs_done && *actor == Actor::Child(i) {
                continue;
            }
            let p = script::actor_pid(*actor, root, &results)
                .ok_or_else(|| format!("step {i}: observed actor unknown"))?;
            views.push((p, fds.as_slice()));
        }
        compare_obs(&h, &views).map_err(|e| format!("step {i} [{}]: {e}", label(st)))?;
        observations += views.len();
    }
    Ok(Replayed { steps: probe.steps.len(), observations })
}

// =============================================================================
// Spec mutants
// =============================================================================

type MutFn = fn(&Host, Pid, &Call, Oracle) -> Result<Step, Refusal>;

struct Mutant {
    name: &'static str,
    clause: &'static str,
    f: MutFn,
}

impl Semantics for Mutant {
    fn step_raw(
        &self,
        host: &Host,
        pid: Pid,
        call: &Call,
        oracle: Oracle,
    ) -> Result<Step, Refusal> {
        (self.f)(host, pid, call, oracle)
    }
}

fn app(h: Host, pid: Pid, call: Call) -> Host {
    step(&h, pid, &call, Oracle::Nominal).map(|s| s.host).unwrap_or(h)
}
fn setcx(h: Host, pid: Pid, fd: i32, on: bool) -> Host {
    app(h, pid, Call::Fcntl { fd, cmd: darwin::F_SETFD, arg: i64::from(on) })
}
fn int(r: &SysResult) -> Option<i32> {
    match r {
        Ok(Ret::Int(v)) => i32::try_from(*v).ok(),
        _ => None,
    }
}
fn post(
    s: Result<Step, Refusal>,
    f: impl FnOnce(Host, &SysResult) -> Host,
) -> Result<Step, Refusal> {
    let s = s?;
    let host = f(s.host, &s.result);
    Ok(Step { host, result: s.result })
}
fn cloexec_new(s: Result<Step, Refusal>, pid: Pid, on: bool) -> Result<Step, Refusal> {
    post(s, |h, r| match r {
        Ok(Ret::Int(v)) => setcx(h, pid, i32::try_from(*v).unwrap_or(-1), on),
        Ok(Ret::Pair(a, b)) => setcx(setcx(h, pid, *a, on), pid, *b, on),
        _ => h,
    })
}
fn child_of(r: &SysResult) -> Option<Pid> {
    int(r).and_then(|v| u32::try_from(v).ok()).map(Pid)
}

#[allow(clippy::too_many_lines)]
fn mutants() -> Vec<Mutant> {
    use darwin::*;
    vec![
        Mutant {
            name: "kqueue-setfl-succeeds",
            clause: "fcntl F_SETFL",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if matches!(c, Call::Fcntl { cmd: F_SETFL, .. }) && s.result == Err(Errno::ENOTTY) {
                    return Ok(Step { host: s.host, result: Ok(Ret::Int(0)) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "fdesc-open-is-a-fresh-description",
            clause: "open /dev/fd/N",
            f: |h, p, c, o| match *c {
                Call::OpenAlias { flags, .. } => step(h, p, &Call::Open { flags }, o),
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "fdesc-open-ignores-the-source-cloexec",
            clause: "open /dev/fd/N",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                match (c, s.result) {
                    (Call::OpenAlias { flags, .. }, Ok(Ret::Int(fd))) => {
                        let fd = i32::try_from(fd).unwrap_or(-1);
                        let host = setcx(s.host, p, fd, flags & O_CLOEXEC != 0);
                        Ok(Step { host, result: s.result })
                    }
                    _ => Ok(s),
                }
            },
        },
        Mutant {
            name: "accept-ignores-kind-and-listen",
            clause: "accept",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if matches!(c, Call::Accept { .. })
                    && matches!(s.result, Err(Errno::EINVAL | Errno::EOPNOTSUPP))
                {
                    let sock = Call::Socket { domain: AF_UNIX, ty: SOCK_STREAM, protocol: 0 };
                    return step(h, p, &sock, Oracle::Nominal);
                }
                Ok(s)
            },
        },
        Mutant {
            name: "socket-checks-shape-before-table",
            clause: "socket",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let Call::Socket { domain: AF_UNIX, ty, protocol } = *c
                    && s.result == Err(Errno::EMFILE)
                    && (ty == SOCK_SEQPACKET || ty & LINUX_SOCK_CLOEXEC != 0 || protocol != 0)
                {
                    return Ok(Step { host: s.host, result: Err(Errno::EPROTONOSUPPORT) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "waitpid-wnohang-blocks",
            clause: "waitpid",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if matches!(c, Call::Waitpid { options, .. } if options & WNOHANG != 0)
                    && s.result == Ok(Ret::Int(0))
                {
                    return Err(Refusal::Blocks);
                }
                Ok(s)
            },
        },
        Mutant {
            name: "waitpid-any-child-is-echild",
            clause: "waitpid",
            f: |h, p, c, o| match *c {
                Call::Waitpid { pid: -1, .. } => {
                    Ok(Step { host: h.clone(), result: Err(Errno::ECHILD) })
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "fchdir-has-no-effect",
            clause: "posix_spawn addfchdir",
            f: |h, p, c, o| match c {
                Call::Spawn { actions, flags } => {
                    let actions = actions
                        .iter()
                        .filter(|a| !matches!(a, FileAction::Fchdir { .. }))
                        .copied()
                        .collect();
                    step(h, p, &Call::Spawn { actions, flags: *flags }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "status-read-ignores-data",
            clause: "read (status pipe)",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if matches!(c, Call::ReadSome { .. }) && s.result == Ok(Ret::Int(1)) {
                    // As if the data were not there: end-of-file once the
                    // writer is gone, else not enabled.
                    let Call::ReadSome { fd } = *c else {
                        return Ok(s);
                    };
                    return match s.host.peer_closed(p, fd) {
                        Some(true) => Ok(Step { host: s.host, result: Ok(Ret::Int(0)) }),
                        _ => Err(Refusal::Blocks),
                    };
                }
                Ok(s)
            },
        },
        Mutant {
            name: "pipe-born-cloexec",
            clause: "pipe",
            f: |h, p, c, o| {
                if matches!(c, Call::Pipe) {
                    cloexec_new(step(h, p, c, o), p, true)
                } else {
                    step(h, p, c, o)
                }
            },
        },
        Mutant {
            name: "pipe-not-lowest-free",
            clause: "pipe/allocation",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let (Call::Pipe, Ok(Ret::Pair(a, b))) = (c, s.result)
                    && s.host.entry(p, b + 1).is_none()
                {
                    let h2 = app(
                        app(s.host, p, Call::Dup2 { from: b, to: b + 1 }),
                        p,
                        Call::Close { fd: b },
                    );
                    return Ok(Step { host: h2, result: Ok(Ret::Pair(a, b + 1)) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "socketpair-born-cloexec",
            clause: "socketpair",
            f: |h, p, c, o| {
                if matches!(c, Call::Socketpair { .. }) {
                    cloexec_new(step(h, p, c, o), p, true)
                } else {
                    step(h, p, c, o)
                }
            },
        },
        Mutant {
            name: "socket-born-cloexec",
            clause: "socket",
            f: |h, p, c, o| {
                if matches!(c, Call::Socket { .. }) {
                    cloexec_new(step(h, p, c, o), p, true)
                } else {
                    step(h, p, c, o)
                }
            },
        },
        Mutant {
            name: "sock-cloexec-type-flag-accepted",
            clause: "socket/socketpair",
            f: |h, p, c, o| match *c {
                Call::Socket { domain, ty, protocol } if ty & LINUX_SOCK_CLOEXEC != 0 => {
                    cloexec_new(
                        step(
                            h,
                            p,
                            &Call::Socket { domain, ty: ty & !LINUX_SOCK_CLOEXEC, protocol },
                            o,
                        ),
                        p,
                        true,
                    )
                }
                Call::Socketpair { domain, ty, protocol } if ty & LINUX_SOCK_CLOEXEC != 0 => {
                    cloexec_new(
                        step(
                            h,
                            p,
                            &Call::Socketpair { domain, ty: ty & !LINUX_SOCK_CLOEXEC, protocol },
                            o,
                        ),
                        p,
                        true,
                    )
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "socket-op-ignores-kind",
            clause: "bind/listen/connect",
            f: |h, p, c, o| {
                if let Call::SocketOp { fd, .. } = *c
                    && h.entry(p, fd).is_some()
                {
                    return Ok(Step { host: h.clone(), result: Ok(Ret::Int(0)) });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "accept-born-cloexec",
            clause: "accept",
            f: |h, p, c, o| {
                if matches!(c, Call::Accept { .. }) {
                    cloexec_new(step(h, p, c, o), p, true)
                } else {
                    step(h, p, c, o)
                }
            },
        },
        Mutant {
            name: "accept-drops-listener-status",
            clause: "accept",
            f: |h, p, c, o| {
                if !matches!(c, Call::Accept { .. }) {
                    return step(h, p, c, o);
                }
                post(step(h, p, c, o), |h2, r| match int(r) {
                    Some(fd) => app(h2, p, Call::Fcntl { fd, cmd: F_SETFL, arg: 0 }),
                    None => h2,
                })
            },
        },
        Mutant {
            name: "open-ignores-o-cloexec",
            clause: "open",
            f: |h, p, c, o| match *c {
                Call::Open { flags } => step(h, p, &Call::Open { flags: flags & !O_CLOEXEC }, o),
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "open-path-before-table",
            clause: "open",
            f: |h, p, c, o| {
                if let (Call::Open { .. }, Oracle::Fail(e)) = (c, o) {
                    return Ok(Step { host: h.clone(), result: Err(e) });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "kqueue-born-inheritable",
            clause: "kqueue",
            f: |h, p, c, o| {
                if matches!(c, Call::Kqueue) {
                    cloexec_new(step(h, p, c, o), p, false)
                } else {
                    step(h, p, c, o)
                }
            },
        },
        Mutant {
            name: "setfd-cannot-clear",
            clause: "fcntl F_SETFD",
            f: |h, p, c, o| {
                if let Call::Fcntl { fd, cmd: F_SETFD, arg } = *c
                    && arg & 1 == 0
                    && h.entry(p, fd).is_some()
                {
                    return Ok(Step { host: h.clone(), result: Ok(Ret::Int(0)) });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "getfd-inverted",
            clause: "fcntl F_GETFD",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let (Call::Fcntl { cmd: F_GETFD, .. }, Ok(Ret::Int(v))) = (c, s.result) {
                    return Ok(Step { host: s.host, result: Ok(Ret::Int(1 - v)) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "dupfd-copies-cloexec",
            clause: "fcntl F_DUPFD",
            f: |h, p, c, o| {
                if let Call::Fcntl { fd, cmd: F_DUPFD, .. } = *c {
                    let src = h.entry(p, fd).map(|e| e.cloexec);
                    return post(step(h, p, c, o), |h2, r| match (int(r), src) {
                        (Some(n), Some(cx)) => setcx(h2, p, n, cx),
                        _ => h2,
                    });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "dupfd-cloexec-clears",
            clause: "fcntl F_DUPFD_CLOEXEC",
            f: |h, p, c, o| match *c {
                Call::Fcntl { fd, cmd: F_DUPFD_CLOEXEC, arg } => {
                    step(h, p, &Call::Fcntl { fd, cmd: F_DUPFD, arg }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "dupfd-ignores-floor",
            clause: "fcntl F_DUPFD",
            f: |h, p, c, o| match *c {
                Call::Fcntl { fd, cmd: cmd @ (F_DUPFD | F_DUPFD_CLOEXEC), arg } if arg >= 0 => {
                    step(h, p, &Call::Fcntl { fd, cmd, arg: 0 }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "setfl-per-descriptor",
            clause: "fcntl F_SETFL",
            f: |h, p, c, o| {
                let Call::Fcntl { fd, cmd: F_SETFL, arg } = *c else {
                    return step(h, p, c, o);
                };
                let Some(e) = h.entry(p, fd) else {
                    return step(h, p, c, o);
                };
                if h.refs(e.ofd) < 2 {
                    return step(h, p, c, o);
                }
                let old = *h.ofd(e.ofd).ok_or(Refusal::Blocks)?;
                let mut h2 = app(h.clone(), p, Call::Close { fd });
                let bits = i32::try_from(arg).unwrap_or(0) & SETFL_MASK;
                h2.install_fresh(p, fd, old.kind, old.access, bits, e.cloexec)
                    .map_err(|_| Refusal::Blocks)?;
                Ok(Step { host: h2, result: Ok(Ret::Int(0)) })
            },
        },
        Mutant {
            name: "setfl-ignores-append",
            clause: "fcntl F_SETFL",
            f: |h, p, c, o| match *c {
                Call::Fcntl { fd, cmd: F_SETFL, arg } => step(
                    h,
                    p,
                    &Call::Fcntl { fd, cmd: F_SETFL, arg: arg & !i64::from(O_APPEND) },
                    o,
                ),
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "dup-copies-cloexec",
            clause: "dup",
            f: |h, p, c, o| {
                if let Call::Dup { fd } = *c {
                    let src = h.entry(p, fd).map(|e| e.cloexec);
                    return post(step(h, p, c, o), |h2, r| match (int(r), src) {
                        (Some(n), Some(cx)) => setcx(h2, p, n, cx),
                        _ => h2,
                    });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "dup2-keeps-source-cloexec",
            clause: "dup2",
            f: |h, p, c, o| {
                if let Call::Dup2 { from, to } = *c {
                    let src = h.entry(p, from).map(|e| e.cloexec);
                    if from != to {
                        return post(step(h, p, c, o), |h2, r| match (r, src) {
                            (Ok(_), Some(cx)) => setcx(h2, p, to, cx),
                            _ => h2,
                        });
                    }
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "dup2-self-clears-cloexec",
            clause: "dup2",
            f: |h, p, c, o| {
                if let Call::Dup2 { from, to } = *c
                    && from == to
                {
                    return post(step(h, p, c, o), |h2, r| {
                        if r.is_ok() { setcx(h2, p, to, false) } else { h2 }
                    });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "dup2-self-before-limit",
            clause: "dup2",
            f: |h, p, c, o| {
                if let Call::Dup2 { from, to } = *c
                    && from == to
                    && h.entry(p, from).is_some()
                {
                    return Ok(Step { host: h.clone(), result: Ok(Ret::Int(i64::from(to))) });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "close-drops-description",
            clause: "close",
            f: |h, p, c, o| {
                let Call::Close { fd } = *c else {
                    return step(h, p, c, o);
                };
                let ofd = h.entry(p, fd).map(|e| e.ofd);
                post(step(h, p, c, o), |mut h2, _| {
                    if let Some(ofd) = ofd {
                        for (q, f) in h2.holders(ofd) {
                            h2 = app(h2, q, Call::Close { fd: f });
                        }
                    }
                    h2
                })
            },
        },
        Mutant {
            name: "fioclex-per-description",
            clause: "ioctl FIOCLEX",
            f: |h, p, c, o| {
                let Call::Ioctl { fd, request: FIOCLEX, .. } = *c else {
                    return step(h, p, c, o);
                };
                let ofd = h.entry(p, fd).map(|e| e.ofd);
                post(step(h, p, c, o), |mut h2, _| {
                    if let Some(ofd) = ofd {
                        for (q, f) in h2.holders(ofd) {
                            if q == p {
                                h2 = setcx(h2, q, f, true);
                            }
                        }
                    }
                    h2
                })
            },
        },
        Mutant {
            name: "fionclex-noop",
            clause: "ioctl FIONCLEX",
            f: |h, p, c, o| {
                if let Call::Ioctl { fd, request: FIONCLEX, .. } = *c
                    && h.entry(p, fd).is_some()
                {
                    return Ok(Step { host: h.clone(), result: Ok(Ret::Int(0)) });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "fork-drops-cloexec",
            clause: "fork",
            f: |h, p, c, o| {
                if !matches!(c, Call::Fork) {
                    return step(h, p, c, o);
                }
                post(step(h, p, c, o), |mut h2, r| {
                    if let Some(child) = child_of(r) {
                        let doomed: Vec<i32> = h2
                            .proc(child)
                            .map(|pr| {
                                pr.table
                                    .iter()
                                    .filter(|(_, e)| e.cloexec)
                                    .map(|(f, _)| *f)
                                    .collect()
                            })
                            .unwrap_or_default();
                        for f in doomed {
                            h2 = app(h2, child, Call::Close { fd: f });
                        }
                    }
                    h2
                })
            },
        },
        Mutant {
            name: "fork-copies-kqueue",
            clause: "fork",
            f: |h, p, c, o| {
                if !matches!(c, Call::Fork) {
                    return step(h, p, c, o);
                }
                let kq: Vec<(i32, trust_platform::Entry)> = h
                    .proc(p)
                    .map(|pr| {
                        pr.table
                            .iter()
                            .filter(|(_, e)| {
                                h.ofd(e.ofd).is_some_and(|x| x.kind == OfdKind::Kqueue)
                            })
                            .map(|(f, e)| (*f, *e))
                            .collect()
                    })
                    .unwrap_or_default();
                post(step(h, p, c, o), |mut h2, r| {
                    if let Some(child) = child_of(r) {
                        for (f, e) in &kq {
                            let _ = h2.install_dup(child, *f, e.ofd, e.cloexec);
                        }
                    }
                    h2
                })
            },
        },
        Mutant {
            name: "fork-unshared-descriptions",
            clause: "fork",
            f: |h, p, c, o| {
                if !matches!(c, Call::Fork) {
                    return step(h, p, c, o);
                }
                post(step(h, p, c, o), |mut h2, r| {
                    if let Some(child) = child_of(r) {
                        let entries: Vec<(i32, trust_platform::Entry)> = h2
                            .proc(child)
                            .map(|pr| pr.table.iter().map(|(f, e)| (*f, *e)).collect())
                            .unwrap_or_default();
                        for (f, e) in entries {
                            let Some(old) = h2.ofd(e.ofd).copied() else {
                                continue;
                            };
                            h2 = app(h2, child, Call::Close { fd: f });
                            let _ = h2.install_fresh(
                                child, f, old.kind, old.access, old.status, e.cloexec,
                            );
                        }
                    }
                    h2
                })
            },
        },
        Mutant {
            name: "exec-failure-drops-cloexec",
            clause: "execve",
            f: |h, p, c, o| {
                if let (Call::Exec, Oracle::Fail(e)) = (c, o) {
                    let mut h2 = h.clone();
                    let doomed: Vec<i32> = h
                        .proc(p)
                        .map(|pr| {
                            pr.table.iter().filter(|(_, e)| e.cloexec).map(|(f, _)| *f).collect()
                        })
                        .unwrap_or_default();
                    for f in doomed {
                        h2 = app(h2, p, Call::Close { fd: f });
                    }
                    return Ok(Step { host: h2, result: Err(e) });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "exec-keeps-cloexec",
            clause: "execve",
            f: |h, p, c, o| {
                if let (Call::Exec, Oracle::Nominal) = (c, o) {
                    let mut h2 = h.clone();
                    let fds: Vec<i32> =
                        h.proc(p).map(|pr| pr.table.keys().copied().collect()).unwrap_or_default();
                    for f in fds {
                        h2 = setcx(h2, p, f, false);
                    }
                    return step(&h2, p, c, o);
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "exec-keeps-kqueue",
            clause: "execve",
            f: |h, p, c, o| {
                if let (Call::Exec, Oracle::Nominal) = (c, o) {
                    let kq: Vec<i32> = h
                        .proc(p)
                        .map(|pr| {
                            pr.table
                                .iter()
                                .filter(|(_, e)| {
                                    !e.cloexec
                                        && h.ofd(e.ofd).is_some_and(|x| x.kind == OfdKind::Kqueue)
                                })
                                .map(|(f, _)| *f)
                                .collect()
                        })
                        .unwrap_or_default();
                    return post(step(h, p, c, o), |mut h2, _| {
                        for f in kq {
                            let _ = h2.install_fresh(
                                p,
                                f,
                                OfdKind::Kqueue,
                                Access::ReadWrite,
                                0,
                                false,
                            );
                        }
                        h2
                    });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "spawn-ignores-cloexec-default",
            clause: "posix_spawn",
            f: |h, p, c, o| match c {
                Call::Spawn { actions, flags } => step(
                    h,
                    p,
                    &Call::Spawn {
                        actions: actions.clone(),
                        flags: flags & !POSIX_SPAWN_CLOEXEC_DEFAULT,
                    },
                    o,
                ),
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "spawn-dup2-self-clears-cloexec",
            clause: "posix_spawn adddup2",
            f: |h, p, c, o| match c {
                Call::Spawn { actions, flags } => {
                    let actions = actions
                        .iter()
                        .map(|a| match *a {
                            FileAction::Dup2 { from, to } if from == to => {
                                FileAction::Inherit { fd: from }
                            }
                            other => other,
                        })
                        .collect();
                    step(h, p, &Call::Spawn { actions, flags: *flags }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "spawn-inherit-keeps-cloexec",
            clause: "posix_spawn addinherit_np",
            f: |h, p, c, o| match c {
                Call::Spawn { actions, flags } => {
                    let actions = actions
                        .iter()
                        .map(|a| match *a {
                            FileAction::Inherit { fd } => FileAction::Dup2 { from: fd, to: fd },
                            other => other,
                        })
                        .collect();
                    step(h, p, &Call::Spawn { actions, flags: *flags }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "spawn-cloexec-default-marks-first",
            clause: "posix_spawn CLOEXEC_DEFAULT",
            f: |h, p, c, o| match c {
                Call::Spawn { actions, flags } if flags & POSIX_SPAWN_CLOEXEC_DEFAULT != 0 => {
                    let clear: Vec<i32> = h
                        .proc(p)
                        .map(|pr| {
                            pr.table.iter().filter(|(_, e)| !e.cloexec).map(|(f, _)| *f).collect()
                        })
                        .unwrap_or_default();
                    let mut h2 = h.clone();
                    for f in &clear {
                        h2 = setcx(h2, p, *f, true);
                    }
                    post(
                        step(
                            &h2,
                            p,
                            &Call::Spawn {
                                actions: actions.clone(),
                                flags: flags & !POSIX_SPAWN_CLOEXEC_DEFAULT,
                            },
                            o,
                        ),
                        |mut h3, _| {
                            for f in &clear {
                                h3 = setcx(h3, p, *f, false);
                            }
                            h3
                        },
                    )
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "spawn-addopen-ignores-o-cloexec",
            clause: "posix_spawn addopen",
            f: |h, p, c, o| match c {
                Call::Spawn { actions, flags } => {
                    let actions = actions
                        .iter()
                        .map(|a| match *a {
                            FileAction::Open { fd, flags } => {
                                FileAction::Open { fd, flags: flags & !O_CLOEXEC }
                            }
                            other => other,
                        })
                        .collect();
                    step(h, p, &Call::Spawn { actions, flags: *flags }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "spawn-copies-kqueue",
            clause: "posix_spawn",
            f: |h, p, c, o| {
                let Call::Spawn { flags, .. } = c else {
                    return step(h, p, c, o);
                };
                if flags & POSIX_SPAWN_CLOEXEC_DEFAULT != 0 {
                    return step(h, p, c, o);
                }
                let kq: Vec<(i32, trust_platform::Entry)> = h
                    .proc(p)
                    .map(|pr| {
                        pr.table
                            .iter()
                            .filter(|(_, e)| {
                                !e.cloexec
                                    && h.ofd(e.ofd).is_some_and(|x| x.kind == OfdKind::Kqueue)
                            })
                            .map(|(f, e)| (*f, *e))
                            .collect()
                    })
                    .unwrap_or_default();
                post(step(h, p, c, o), |mut h2, r| {
                    if let Some(child) = child_of(r) {
                        for (f, e) in &kq {
                            let _ = h2.install_dup(child, *f, e.ofd, false);
                        }
                    }
                    h2
                })
            },
        },
        Mutant {
            name: "getrlimit-reports-hard-as-soft",
            clause: "getrlimit",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let Ok(Ret::Rlimit { hard, .. }) = s.result {
                    return Ok(Step { host: s.host, result: Ok(Ret::Rlimit { soft: hard, hard }) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "setrlimit-lowering-closes",
            clause: "setrlimit",
            f: |h, p, c, o| {
                let Call::Setrlimit { soft, .. } = *c else {
                    return step(h, p, c, o);
                };
                post(step(h, p, c, o), |mut h2, r| {
                    if r.is_ok() {
                        let doomed: Vec<i32> = h2
                            .proc(p)
                            .map(|pr| {
                                pr.table
                                    .keys()
                                    .copied()
                                    .filter(|f| u64::try_from(*f).unwrap_or(0) >= soft)
                                    .collect()
                            })
                            .unwrap_or_default();
                        for f in doomed {
                            h2 = app(h2, p, Call::Close { fd: f });
                        }
                    }
                    h2
                })
            },
        },
        Mutant {
            name: "setrlimit-clamps-to-maxfiles",
            clause: "setrlimit",
            f: |h, p, c, o| {
                let Call::Setrlimit { resource, soft, hard } = *c else {
                    return step(h, p, c, o);
                };
                let mf = h.max_files_per_proc();
                post(step(h, p, c, o), |h2, r| {
                    if r.is_ok() && soft > mf {
                        app(h2, p, Call::Setrlimit { resource, soft: mf, hard })
                    } else {
                        h2
                    }
                })
            },
        },
        Mutant {
            name: "allocation-ignores-soft-limit",
            clause: "allocation",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                let limited = matches!(s.result, Err(Errno::EMFILE | Errno::EINVAL | Errno::EBADF));
                let allocating = matches!(
                    c,
                    Call::Pipe
                        | Call::Socketpair { .. }
                        | Call::Socket { .. }
                        | Call::Kqueue
                        | Call::Open { .. }
                        | Call::Dup { .. }
                        | Call::Dup2 { .. }
                        | Call::Fcntl { cmd: F_DUPFD | F_DUPFD_CLOEXEC, .. }
                );
                let Some(nofile) = h.proc(p).map(|pr| pr.nofile) else {
                    return Ok(s);
                };
                if !(limited && allocating) || nofile.soft >= nofile.hard {
                    return Ok(s);
                }
                let raised = app(
                    h.clone(),
                    p,
                    Call::Setrlimit {
                        resource: RLIMIT_NOFILE,
                        soft: nofile.hard,
                        hard: nofile.hard,
                    },
                );
                match step(&raised, p, c, o) {
                    Ok(s2) if s2.result.is_ok() => {
                        let back = app(
                            s2.host,
                            p,
                            Call::Setrlimit {
                                resource: RLIMIT_NOFILE,
                                soft: nofile.soft,
                                hard: nofile.hard,
                            },
                        );
                        Ok(Step { host: back, result: s2.result })
                    }
                    _ => Ok(s),
                }
            },
        },
        Mutant {
            name: "exit-keeps-descriptors",
            clause: "_exit",
            f: |h, p, c, o| {
                if !matches!(c, Call::Exit { .. }) {
                    return step(h, p, c, o);
                }
                let old: Vec<(i32, trust_platform::Entry, trust_platform::Ofd)> = h
                    .proc(p)
                    .map(|pr| {
                        pr.table
                            .iter()
                            .filter_map(|(f, e)| h.ofd(e.ofd).map(|x| (*f, *e, *x)))
                            .collect()
                    })
                    .unwrap_or_default();
                post(step(h, p, c, o), |mut h2, _| {
                    for (f, e, x) in old {
                        if h2.ofd(e.ofd).is_some() {
                            let _ = h2.install_dup(p, f, e.ofd, e.cloexec);
                        } else if let Ok(n) =
                            h2.install_fresh(p, f, x.kind, x.access, x.status, e.cloexec)
                            && let Peer::Open(peer) = x.peer
                        {
                            let _ = h2.link_peers(n, peer);
                        }
                    }
                    h2
                })
            },
        },
    ]
}

/// The lock of the description `pid`'s `fd` names, if any.
fn lock_of(h: &Host, pid: Pid, fd: i32) -> Option<LockMode> {
    h.entry(pid, fd).and_then(|e| h.ofd(e.ofd)).and_then(|o| o.lock)
}

/// Release the lock of description `ofd` through any of its holders.
fn unlock_ofd(h: Host, ofd: trust_platform::OfdId) -> Host {
    match h.holders(ofd).first().copied() {
        Some((holder, fd)) => app(h, holder, Call::Flock { fd, op: darwin::LOCK_UN }),
        None => h,
    }
}

/// The M2 kill matrix: each mutant is a plausible wrong reading of a measured
/// flock / namespace / identity rule.
#[allow(clippy::too_many_lines)]
fn m2_mutants() -> Vec<Mutant> {
    use darwin::*;
    vec![
        Mutant {
            name: "close-always-releases-the-lock",
            clause: "close / flock",
            f: |h, p, c, o| match *c {
                Call::Close { fd } if lock_of(h, p, fd).is_some() => {
                    let held = app(h.clone(), p, Call::Flock { fd, op: LOCK_UN });
                    step(&held, p, c, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "lock-dies-with-the-lockers-last-descriptor",
            clause: "close / flock (per process)",
            f: |h, p, c, o| {
                let Call::Close { fd } = *c else {
                    return step(h, p, c, o);
                };
                let Some(ofd) = h.entry(p, fd).map(|e| e.ofd) else {
                    return step(h, p, c, o);
                };
                let s = step(h, p, c, o)?;
                let still_mine = s.host.holders(ofd).iter().any(|(q, _)| *q == p);
                let locked = s.host.ofd(ofd).is_some_and(|x| x.lock.is_some());
                if locked && !still_mine {
                    return Ok(Step { host: unlock_ofd(s.host, ofd), result: s.result });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "unlock-is-per-descriptor",
            clause: "flock LOCK_UN",
            f: |h, p, c, o| match *c {
                Call::Flock { fd, op } if op & LOCK_UN != 0 => {
                    let shared = h.entry(p, fd).is_some_and(|e| h.refs(e.ofd) > 1);
                    if shared && lock_of(h, p, fd).is_some() {
                        return Ok(Step { host: h.clone(), result: Ok(Ret::Int(0)) });
                    }
                    step(h, p, c, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "failed-nb-upgrade-drops-the-shared-lock",
            clause: "flock conversion (Linux reading)",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let Call::Flock { fd, op } = *c
                    && op & LOCK_EX != 0
                    && s.result == Err(Errno::EAGAIN)
                    && lock_of(h, p, fd) == Some(LockMode::Shared)
                {
                    let host = app(s.host, p, Call::Flock { fd, op: LOCK_UN });
                    return Ok(Step { host, result: s.result });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "shared-locks-conflict",
            clause: "flock LOCK_SH",
            f: |h, p, c, o| {
                if let Call::Flock { fd, op } = *c
                    && op & (LOCK_UN | LOCK_EX) == 0
                    && op & LOCK_SH != 0
                    && let Some(e) = h.entry(p, fd)
                    && let Some(n) = h.ofd(e.ofd).and_then(|x| x.node)
                    && h.ofds_on(n).any(|(id, x)| id != e.ofd && x.lock.is_some())
                {
                    if op & LOCK_NB != 0 {
                        return Ok(Step { host: h.clone(), result: Err(Errno::EAGAIN) });
                    }
                    return Err(Refusal::Blocks);
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "flock-decodes-the-op-before-the-kind",
            clause: "flock errno order",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let Call::Flock { op, .. } = *c
                    && op & (LOCK_SH | LOCK_EX | LOCK_UN) == 0
                    && s.result == Err(Errno::ENOTSUP)
                {
                    return Ok(Step { host: s.host, result: Err(Errno::EBADF) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "a-bad-flock-op-is-einval",
            clause: "flock op decoding (Linux reading)",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let Call::Flock { fd, .. } = *c
                    && s.result == Err(Errno::EBADF)
                    && h.entry(p, fd).is_some()
                {
                    return Ok(Step { host: s.host, result: Err(Errno::EINVAL) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "lock-un-does-not-win-over-lock-ex",
            clause: "flock op decoding",
            f: |h, p, c, o| match *c {
                Call::Flock { fd, op } if op & LOCK_UN != 0 && op & LOCK_EX != 0 => {
                    step(h, p, &Call::Flock { fd, op: op & !LOCK_UN }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "a-fifo-takes-flock",
            clause: "flock on a FIFO",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let Call::Flock { fd, .. } = *c
                    && s.result == Err(Errno::ENOTSUP)
                    && h.entry(p, fd).and_then(|e| h.ofd(e.ofd)).is_some_and(|x| x.node.is_some())
                {
                    return Ok(Step { host: s.host, result: Ok(Ret::Int(0)) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "flock-never-conflicts",
            clause: "flock conflicts per node",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if matches!(c, Call::Flock { .. }) && s.result == Err(Errno::EAGAIN) {
                    return Ok(Step { host: s.host, result: Ok(Ret::Int(0)) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "exec-releases-every-lock",
            clause: "exec / flock",
            f: |h, p, c, o| {
                if matches!(c, Call::Exec) {
                    let mut held = h.clone();
                    let fds: Vec<i32> =
                        h.proc(p).map(|x| x.fds().into_iter().collect()).unwrap_or_default();
                    for fd in fds {
                        if lock_of(&held, p, fd).is_some() {
                            held = app(held, p, Call::Flock { fd, op: LOCK_UN });
                        }
                    }
                    return step(&held, p, c, o);
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "open-lock-bits-are-ignored",
            clause: "open O_EXLOCK/O_SHLOCK",
            f: |h, p, c, o| match c {
                Call::OpenPath { at, path, flags } if flags & (O_EXLOCK | O_SHLOCK) != 0 => {
                    let flags = flags & !(O_EXLOCK | O_SHLOCK);
                    step(h, p, &Call::OpenPath { at: *at, path: path.clone(), flags }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "both-lock-bits-take-a-shared-lock",
            clause: "open O_EXLOCK|O_SHLOCK",
            f: |h, p, c, o| match c {
                Call::OpenPath { at, path, flags }
                    if flags & O_EXLOCK != 0 && flags & O_SHLOCK != 0 =>
                {
                    let flags = flags & !O_EXLOCK;
                    step(h, p, &Call::OpenPath { at: *at, path: path.clone(), flags }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "fifo-write-side-opens-without-a-reader",
            clause: "open of a FIFO",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let Call::OpenPath { at, path, flags } = c
                    && s.result == Err(Errno::ENXIO)
                {
                    let flags = (flags & !O_ACCMODE) | O_RDWR;
                    return step(h, p, &Call::OpenPath { at: *at, path: path.clone(), flags }, o);
                }
                Ok(s)
            },
        },
        Mutant {
            name: "openat-reads-its-dirfd-for-an-absolute-path",
            clause: "openat dirfd",
            f: |h, p, c, o| match c {
                Call::OpenPath { at: Some(d), path, .. }
                    if path.starts_with('/') && *d != AT_FDCWD && h.entry(p, *d).is_none() =>
                {
                    Ok(Step { host: h.clone(), result: Err(Errno::EBADF) })
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "openat-checks-the-dirfd-before-the-table",
            clause: "openat errno order",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let Call::OpenPath { at: Some(d), path, .. } = c
                    && !path.starts_with('/')
                    && *d != AT_FDCWD
                    && h.entry(p, *d).is_none()
                    && s.result == Err(Errno::EMFILE)
                {
                    return Ok(Step { host: s.host, result: Err(Errno::EBADF) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "fstat-identity-is-per-description",
            clause: "fstat",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let (Call::Fstat { fd }, Ok(Ret::Stat { ftype, .. })) = (c, s.result)
                    && let Some(e) = h.entry(p, *fd)
                {
                    let node = 1_000_000 + u64::from(e.ofd.0);
                    return Ok(Step { host: s.host, result: Ok(Ret::Stat { node, ftype }) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "o-nofollow-follows",
            clause: "open O_NOFOLLOW",
            f: |h, p, c, o| match c {
                Call::OpenPath { at, path, flags } if flags & O_NOFOLLOW != 0 => {
                    let flags = flags & !O_NOFOLLOW;
                    step(h, p, &Call::OpenPath { at: *at, path: path.clone(), flags }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "creat-through-a-dangling-link-fails",
            clause: "open O_CREAT through a symlink",
            f: |h, p, c, o| {
                if let Call::OpenPath { path, flags, .. } = c
                    && flags & O_CREAT != 0
                    && let Ok(path) = h.canonical_path(path)
                    && let Some(n) = h.name(&path)
                    && let Some(t) = h.node(n).and_then(|x| x.target.clone())
                    && let Ok(t) = h.link_target(&path, &t)
                    && h.name(&t).is_none()
                {
                    return Ok(Step { host: h.clone(), result: Err(Errno::ENOENT) });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "creat-on-a-directory-is-eisdir",
            clause: "open O_CREAT of a directory",
            f: |h, p, c, o| {
                if let Call::OpenPath { path, flags, .. } = c
                    && flags & O_CREAT != 0
                    && h.canonical_path(path)
                        .ok()
                        .and_then(|path| h.name(&path))
                        .and_then(|n| h.node(n))
                        .is_some_and(|x| x.kind == NodeKind::Directory)
                {
                    return Ok(Step { host: h.clone(), result: Err(Errno::EISDIR) });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "unlink-of-a-directory-succeeds",
            clause: "unlink",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if matches!(c, Call::Unlink { .. }) && s.result == Err(Errno::EPERM) {
                    return Ok(Step { host: s.host, result: Ok(Ret::Int(0)) });
                }
                Ok(s)
            },
        },
    ]
}

/// The M2 REVIEW kill matrix (2026-10-01): each mutant is the model before a
/// finding of the M2 model review was fixed — a plausible reading the kernel
/// contradicts. The waiting-call and spawn-window mutants are killed by the
/// multi-threaded checks below ([`spawn_window`], [`waiting_fifo_open`],
/// [`sleeping_flock`], [`create_then_lock`], [`spellings`]); the FIFO and
/// symlink ones by probes.
#[allow(clippy::too_many_lines)]
fn m2_review_mutants() -> Vec<Mutant> {
    use darwin::*;
    vec![
        Mutant {
            name: "posix-spawn-is-one-event",
            clause: "posix_spawn (the copy window)",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if matches!(c, Call::SpawnBegin)
                    && let Some(child) = child_of(&s.result)
                {
                    // The child's copy is already swept: no close-on-exec entry
                    // lives between the halves.
                    let cx: Vec<i32> = s
                        .host
                        .proc(child)
                        .map(|x| {
                            x.table.iter().filter(|(_, e)| e.cloexec).map(|(fd, _)| *fd).collect()
                        })
                        .unwrap_or_default();
                    let mut host = s.host;
                    for fd in cx {
                        host = app(host, child, Call::Close { fd });
                    }
                    return Ok(Step { host, result: s.result });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "a-waiting-fifo-opener-is-not-counted",
            clause: "open of a FIFO (waiting openers)",
            f: |h, p, c, o| {
                if let Call::OpenPath { path, flags, .. } = c
                    && flags & O_ACCMODE == O_WRONLY
                    && let Ok(path) = h.canonical_path(path)
                    && let Some(n) = h.name(&path)
                    && h.node(n).is_some_and(|x| x.kind == NodeKind::Fifo)
                    && !h.ofds_on(n).any(|(_, x)| x.access != Access::WriteOnly)
                {
                    if flags & O_NONBLOCK != 0 {
                        return Ok(Step { host: h.clone(), result: Err(Errno::ENXIO) });
                    }
                    return Err(Refusal::Blocks);
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "a-pending-open-reserves-nothing",
            clause: "open (fdalloc first)",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let (Call::Dup { .. }, Ok(Ret::Int(v))) = (c, s.result)
                    && let Some(n) = (0..).find(|n| h.entry(p, *n).is_none())
                    && i64::from(n) < v
                {
                    return Ok(Step { host: s.host, result: Ok(Ret::Int(i64::from(n))) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "dup2-never-waits",
            clause: "dup2 onto a number in flight",
            f: |h, p, c, o| match (c, step(h, p, c, o)) {
                (Call::Dup2 { to, .. }, Err(Refusal::Blocks)) => {
                    Ok(Step { host: h.clone(), result: Ok(Ret::Int(i64::from(*to))) })
                }
                (_, other) => other,
            },
        },
        Mutant {
            name: "close-never-waits",
            clause: "close of a number a sleeping flock holds",
            f: |h, p, c, o| match (c, step(h, p, c, o)) {
                (Call::Close { .. }, Err(Refusal::Blocks)) => {
                    Ok(Step { host: h.clone(), result: Ok(Ret::Int(0)) })
                }
                (_, other) => other,
            },
        },
        Mutant {
            name: "a-waiting-call-is-never-interrupted",
            clause: "flock / open EINTR",
            f: |h, p, c, o| {
                if matches!(c, Call::Resume { .. }) && o == Oracle::Fail(Errno::EINTR) {
                    return Err(Refusal::InadmissibleOracle { symbol: "resume", oracle: o });
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "create-and-lock-are-one-step",
            clause: "open O_CREAT|O_EXLOCK",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let (Call::OpenPath { .. }, Ok(Ret::Pending { fd })) = (c, s.result)
                    && let Ok(done) = step(&s.host, p, &Call::Resume { fd }, Oracle::Nominal)
                {
                    return Ok(done);
                }
                Ok(s)
            },
        },
        Mutant {
            name: "flock-on-a-fifo-refuses-before-the-op",
            clause: "flock on a FIFO (errno order)",
            f: |h, p, c, o| {
                let s = step(h, p, c, o)?;
                if let Call::Flock { fd, .. } = *c
                    && s.result == Err(Errno::EBADF)
                    && let Some(n) = h.entry(p, fd).and_then(|e| h.ofd(e.ofd)).and_then(|x| x.node)
                    && h.node(n).is_some_and(|x| x.kind == NodeKind::Fifo)
                {
                    return Ok(Step { host: s.host, result: Err(Errno::ENOTSUP) });
                }
                Ok(s)
            },
        },
        Mutant {
            name: "a-relative-link-target-is-a-cwd-name",
            clause: "open through a symlink (relative target)",
            f: |h, p, c, o| {
                if let Call::OpenPath { at, path, flags } = c
                    && flags & O_NOFOLLOW == 0
                    && let Ok(full) = h.canonical_path(path)
                    && let Some(n) = h.name(&full)
                    && let Some(t) = h.node(n).and_then(|x| x.target.clone())
                    && !t.starts_with('/')
                {
                    return step(h, p, &Call::OpenPath { at: *at, path: t, flags: *flags }, o);
                }
                step(h, p, c, o)
            },
        },
        Mutant {
            name: "two-spellings-are-two-files",
            clause: "the namespace's one spelling",
            f: |h, p, c, o| match c {
                Call::OpenPath { at, path, flags }
                    if h.canonical_path(path).is_err() && crate_classify(path) =>
                {
                    let alias: String = path
                        .chars()
                        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
                        .collect();
                    let path = format!("alias_{alias}");
                    step(h, p, &Call::OpenPath { at: *at, path, flags: *flags }, o)
                }
                _ => step(h, p, c, o),
            },
        },
        Mutant {
            name: "ptmx-is-one-node",
            clause: "open of a cloning device",
            f: |h, p, c, o| match c {
                Call::OpenPath { at, path, flags } if path == "/dev/ptmx" => {
                    let path = "/dev/null".to_string();
                    step(h, p, &Call::OpenPath { at: *at, path, flags: *flags }, o)
                }
                _ => step(h, p, c, o),
            },
        },
    ]
}

/// Not an fdesc or refused-device path (the spelling mutant renames only
/// another spelling of a file).
fn crate_classify(path: &str) -> bool {
    matches!(
        trust_platform::symbols::classify_open_path(path),
        trust_platform::symbols::OpenPath::Other
    )
}

// =============================================================================
// Bespoke multi-process checks (the probe grammar has no grandchildren and no
// waiting call)
// =============================================================================

/// THE LOCK OUTLIVES THE PROCESS THAT TOOK IT, held by that process's child:
/// a process P opens a file, takes `LOCK_EX`, forks G (which parks) and
/// EXITS; from outside, `LOCK_EX|LOCK_NB` on another open of the file is
/// `EWOULDBLOCK` while G lives and granted once G is killed. The same steps
/// run on the model (P and G are a child and a grandchild of the script's
/// root) and on every spec mutant; returns the mutants it kills.
fn lock_outlives_its_taker(env: &Env, mutants: &[Mutant]) -> Result<Vec<&'static str>, String> {
    use darwin::*;
    let ns = env.dir.join("ns-orphan");
    let _ = std::fs::create_dir_all(&ns);
    let path = ns.join("m.log");
    let out = env.dir.join("orphan.result");
    // SAFETY: the harness is single-threaded; the child is a fresh process.
    let r = unsafe { libc::fork() };
    if r == 0 {
        let line = orphan_real(&path);
        let _ = std::fs::write(&out, line);
        // SAFETY: leaving the probe process.
        unsafe { libc::_exit(0) };
    }
    let mut st = 0;
    // SAFETY: our own child.
    unsafe { libc::waitpid(r, &mut st, 0) };
    let text = std::fs::read_to_string(&out).map_err(|e| format!("no result: {e}"))?;
    let real: Vec<i32> = text.split_whitespace().filter_map(|v| v.parse().ok()).collect();
    // The model: [0] pipe (the real run's sync pipe), [1] pipe (its death
    // pipe), [2] fork P, [3..] P opens, locks, forks G, exits; the root reaps
    // P, opens, probes, G dies, the root probes again.
    let p = Actor::Child(2);
    let g = Actor::Child(5);
    let prog = vec![
        ProgramStep::root(Call::Pipe),
        ProgramStep::root(Call::Pipe),
        ProgramStep::root(Call::Fork),
        ProgramStep::by(
            p,
            Call::OpenPath {
                at: None,
                path: "m.log".into(),
                flags: O_RDONLY | O_CREAT | O_CLOEXEC,
            },
        ),
        ProgramStep::by(p, Call::Flock { fd: Operand::Ret { step: 3, comp: 0 }, op: LOCK_EX }),
        ProgramStep::by(p, Call::Fork),
        ProgramStep::by(p, Call::Exit { status: 0 }),
        ProgramStep::root(Call::Waitpid { pid: Operand::Ret { step: 2, comp: 0 }, options: 0 }),
        ProgramStep::root(Call::OpenPath { at: None, path: "m.log".into(), flags: O_RDONLY }),
        ProgramStep::root(Call::Flock {
            fd: Operand::Ret { step: 8, comp: 0 },
            op: LOCK_EX | LOCK_NB,
        }),
        ProgramStep::by(g, Call::Exit { status: 137 }),
        ProgramStep::root(Call::Flock {
            fd: Operand::Ret { step: 8, comp: 0 },
            op: LOCK_EX | LOCK_NB,
        }),
    ];
    let observed = [4usize, 9, 11];
    let mut init = Host::new(env.maxfiles);
    init.set_cwd(&canonical_dir(&ns)).map_err(|e| format!("{e:?}"))?;
    let root = init.add_root(Rlimit { soft: PROBE_SOFT, hard: env.hard });
    let null = init
        .install_fresh(root, 0, OfdKind::File, Access::ReadWrite, 0, false)
        .map_err(|e| format!("{e:?}"))?;
    init.install_dup(root, 1, null, false).map_err(|e| format!("{e:?}"))?;
    init.install_dup(root, 2, null, false).map_err(|e| format!("{e:?}"))?;
    let errno_of = |r: &SysResult| match r {
        Ok(_) => 0,
        Err(e) => e.0,
    };
    let run = |sem: &dyn Semantics| -> Result<Vec<i32>, String> {
        let t = script::run(sem, &init, root, &prog, &[]).map_err(|e| format!("{e:?}"))?;
        Ok(observed.iter().map(|i| errno_of(&t[*i].result)).collect())
    };
    let model = run(&Darwin)?;
    if model != real {
        return Err(format!(
            "flock errnos (P's lock, probe while G lives, probe after): model {model:?}, kernel {real:?}"
        ));
    }
    let mut killed = Vec::new();
    for m in mutants {
        if run(m).map_or(true, |v| v != real) {
            killed.push(m.name);
        }
    }
    println!(
        "  lock outlives its taker: P locked and exited; while its child G lived the lock read \
         held ({}), after G died free ({}) — the model agrees",
        real.get(1).copied().unwrap_or(-1),
        real.get(2).copied().unwrap_or(-1)
    );
    Ok(killed)
}

/// The real side of [`lock_outlives_its_taker`], in a fresh process R:
/// errnos of (P's `flock(LOCK_EX)`, R's probe while G lives, R's probe after
/// G died), space-separated.
fn orphan_real(path: &Path) -> String {
    let c = CString::new(path.as_os_str().as_encoded_bytes()).unwrap_or_default();
    let mut sync = [0; 2];
    let mut death = [0; 2];
    // SAFETY (whole function): plain syscalls on this fresh process's own
    // descriptors, and on its own children.
    unsafe {
        libc::pipe(sync.as_mut_ptr());
        libc::pipe(death.as_mut_ptr());
        let p = libc::fork();
        if p == 0 {
            let fd = libc::open(
                c.as_ptr(),
                libc::O_RDONLY | libc::O_CREAT | libc::O_CLOEXEC,
                0o644 as libc::c_uint,
            );
            let rc = if libc::flock(fd, libc::LOCK_EX) == 0 { 0 } else { errno().0 };
            let g = libc::fork();
            if g == 0 {
                // G: holds the copy (and the death pipe's write end) until killed.
                let deadline = Instant::now() + Duration::from_secs(60);
                while Instant::now() < deadline {
                    libc::usleep(100_000);
                }
                libc::_exit(0);
            }
            let msg = [rc, g];
            libc::write(sync[1], msg.as_ptr().cast(), std::mem::size_of_val(&msg));
            libc::_exit(0);
        }
        libc::close(sync[1]);
        libc::close(death[1]);
        let mut msg = [0i32; 2];
        libc::read(sync[0], msg.as_mut_ptr().cast(), std::mem::size_of_val(&msg));
        let mut st = 0;
        libc::waitpid(p, &mut st, 0);
        let [p_rc, g] = msg;
        let a = libc::open(c.as_ptr(), libc::O_RDONLY);
        let while_g =
            if libc::flock(a, libc::LOCK_EX | libc::LOCK_NB) == 0 { 0 } else { errno().0 };
        if g > 0 {
            libc::kill(g, libc::SIGKILL);
        }
        // G's death closes its copy of the death pipe's write end: EOF.
        let mut byte = 0u8;
        libc::read(death[0], (&raw mut byte).cast(), 1);
        let after = if libc::flock(a, libc::LOCK_EX | libc::LOCK_NB) == 0 { 0 } else { errno().0 };
        format!("{p_rc} {while_g} {after}")
    }
}

/// A BLOCKING `LOCK_SH -> LOCK_EX` conversion that must wait releases the
/// shared lock BEFORE it sleeps (the reason the model refuses that call by
/// name instead of executing it as "not enabled"): descriptions a and b hold
/// `LOCK_SH`; a child blocks in `flock(a, LOCK_EX)`; meanwhile b's
/// `LOCK_EX|LOCK_NB` is GRANTED — a's shared lock is gone — and once b lets
/// go the child's conversion completes. Real-only; checks the model refuses
/// the call with that reason.
fn blocking_upgrade_drops_shared_first(env: &Env) -> Result<(), String> {
    use darwin::*;
    let ns = env.dir.join("ns-upgrade");
    let _ = std::fs::create_dir_all(&ns);
    let c = CString::new(ns.join("m.log").as_os_str().as_encoded_bytes()).unwrap_or_default();
    let out = env.dir.join("upgrade.result");
    // SAFETY: as in `lock_outlives_its_taker`.
    let r = unsafe { libc::fork() };
    if r == 0 {
        // SAFETY: plain syscalls in a fresh process.
        let line = unsafe {
            let a = libc::open(c.as_ptr(), libc::O_RDONLY | libc::O_CREAT, 0o644 as libc::c_uint);
            let b = libc::open(c.as_ptr(), libc::O_RDONLY);
            libc::flock(a, libc::LOCK_SH);
            libc::flock(b, libc::LOCK_SH);
            let mut ready = [0; 2];
            libc::pipe(ready.as_mut_ptr());
            let k = libc::fork();
            if k == 0 {
                libc::write(ready[1], b"s".as_ptr().cast(), 1);
                libc::flock(a, libc::LOCK_EX);
                let deadline = Instant::now() + Duration::from_secs(30);
                while Instant::now() < deadline {
                    libc::usleep(100_000);
                }
                libc::_exit(0);
            }
            let mut byte = 0u8;
            libc::read(ready[0], (&raw mut byte).cast(), 1);
            libc::usleep(300_000);
            let granted = libc::flock(b, libc::LOCK_EX | libc::LOCK_NB) == 0;
            libc::flock(b, libc::LOCK_UN);
            libc::usleep(300_000);
            let third = libc::open(c.as_ptr(), libc::O_RDONLY);
            let child_got_ex = libc::flock(third, libc::LOCK_SH | libc::LOCK_NB) != 0;
            libc::kill(k, libc::SIGKILL);
            let mut st = 0;
            libc::waitpid(k, &mut st, 0);
            format!("{} {}", u8::from(granted), u8::from(child_got_ex))
        };
        let _ = std::fs::write(&out, line);
        // SAFETY: leaving the probe process.
        unsafe { libc::_exit(0) };
    }
    let mut st = 0;
    // SAFETY: our own child.
    unsafe { libc::waitpid(r, &mut st, 0) };
    let text = std::fs::read_to_string(&out).map_err(|e| format!("no result: {e}"))?;
    if text.trim() != "1 1" {
        return Err(format!(
            "expected b's LOCK_EX|LOCK_NB granted while a's blocking conversion waits, then a's \
             conversion completing (\"1 1\"); measured {text:?}"
        ));
    }
    let mut h = Host::new(env.maxfiles);
    h.set_cwd(&canonical_dir(&ns)).map_err(|e| format!("{e:?}"))?;
    let p = h.add_root(Rlimit { soft: PROBE_SOFT, hard: env.hard });
    let fd = |h: &mut Host, flags| -> Result<i32, String> {
        let s =
            step(h, p, &Call::OpenPath { at: None, path: "m.log".into(), flags }, Oracle::Nominal)
                .map_err(|e| e.to_string())?;
        *h = s.host;
        match s.result {
            Ok(Ret::Int(v)) => i32::try_from(v).map_err(|e| e.to_string()),
            other => Err(format!("{other:?}")),
        }
    };
    let a = fd(&mut h, O_RDONLY | O_CREAT)?;
    let b = fd(&mut h, O_RDONLY)?;
    for x in [a, b] {
        h = app(h, p, Call::Flock { fd: x, op: LOCK_SH });
    }
    match step(&h, p, &Call::Flock { fd: a, op: LOCK_EX }, Oracle::Nominal) {
        Err(Refusal::Unmodeled { symbol: "flock", detail })
            if detail.contains("releases the shared lock") =>
        {
            println!(
                "  blocking LOCK_SH -> LOCK_EX conversion: the kernel released the shared lock \
                 before sleeping (another description's LOCK_EX|LOCK_NB was granted); the model \
                 refuses that call by name"
            );
            Ok(())
        }
        other => Err(format!("the model should refuse the waiting conversion by name: {other:?}")),
    }
}

/// Darwin 27 made `FD_CLOFORK` a descriptor flag: `F_SETFD` keeps it, `F_GETFD`
/// reads it back, and `fork` drops the descriptor. On Darwin 25.6, where the
/// model was measured, `F_SETFD` kept only `FD_CLOEXEC` and `fork` copied the
/// descriptor. The model has no close-on-fork bit, so on either kernel it
/// refuses an `F_SETFD` that carries one, by name, instead of executing it as
/// if the bit were ignored. Real side: names which of the two kernels this is,
/// and fails on any third behaviour.
fn clofork_is_refused_by_name(env: &Env) -> Result<(), String> {
    use darwin::*;
    let flag = c_int::try_from(FD_CLOFORK).unwrap_or(0);
    // SAFETY: a pipe this function owns; the child calls only `fcntl` and
    // `_exit`, both async-signal-safe.
    let (read_back, child_kept) = unsafe {
        let mut p = [0; 2];
        if libc::pipe(p.as_mut_ptr()) != 0 {
            return Err(format!("pipe: errno {}", errno().0));
        }
        libc::fcntl(p[0], libc::F_SETFD, flag);
        let g = libc::fcntl(p[0], libc::F_GETFD);
        let r = libc::fork();
        if r == 0 {
            libc::_exit(if libc::fcntl(p[0], libc::F_GETFD) == -1 { 0 } else { 1 });
        }
        let mut st = 0;
        libc::waitpid(r, &mut st, 0);
        libc::close(p[0]);
        libc::close(p[1]);
        (g, libc::WIFEXITED(st) && libc::WEXITSTATUS(st) == 1)
    };
    let kernel = match (read_back, child_kept) {
        (2, false) => "F_SETFD keeps it (F_GETFD reads 2) and fork drops the descriptor",
        (0, true) => "F_SETFD ignores it (F_GETFD reads 0) and fork copies the descriptor",
        other => {
            return Err(format!(
                "F_SETFD(FD_CLOFORK), F_GETFD and fork measured (F_GETFD, child kept) = {other:?}, \
                 neither Darwin 27's (2, false) nor Darwin 25.6's (0, true)"
            ));
        }
    };
    let mut h = Host::new(env.maxfiles);
    let p = h.add_root(Rlimit { soft: PROBE_SOFT, hard: env.hard });
    let s = step(&h, p, &Call::Pipe, Oracle::Nominal).map_err(|e| e.to_string())?;
    let Ok(Ret::Pair(rd, _)) = s.result else {
        return Err(format!("the model's pipe: {:?}", s.result));
    };
    let set = Call::Fcntl { fd: rd, cmd: F_SETFD, arg: FD_CLOFORK };
    match step(&s.host, p, &set, Oracle::Nominal) {
        Err(Refusal::Unmodeled { symbol: "fcntl", detail }) if detail.contains("FD_CLOFORK") => {
            println!(
                "  FD_CLOFORK: on this kernel {kernel}; the model refuses F_SETFD with that bit by name"
            );
            Ok(())
        }
        other => Err(format!("the model should refuse F_SETFD(FD_CLOFORK) by name: {other:?}")),
    }
}

/// `open("/dev/fd/N")` of a kqueue: Darwin 25.6 and 27.0 answer `EBADF`,
/// Darwin 27.2 `EACCES`, for every access mode. The model names no kernel
/// release, so it refuses that open by name (PLATFORM-KQUEUE-ALIAS-1). Real
/// side: names which of the two answers this kernel gives, and fails on a
/// third or on an answer that differs between access modes.
fn kqueue_alias_is_refused_by_name(env: &Env) -> Result<(), String> {
    use darwin::*;
    let modes = [O_RDONLY, O_WRONLY, O_RDWR];
    // SAFETY: a kqueue this function owns and closes; each open that
    // succeeds is closed at once.
    let answers: Vec<Result<(), Errno>> = unsafe {
        let kq = libc::kqueue();
        if kq < 0 {
            return Err(format!("kqueue: errno {}", errno().0));
        }
        let path = CString::new(format!("/dev/fd/{kq}")).map_err(|e| e.to_string())?;
        let out = modes
            .iter()
            .map(|&m| {
                let n = libc::open(path.as_ptr(), m);
                if n >= 0 {
                    libc::close(n);
                    Ok(())
                } else {
                    Err(errno())
                }
            })
            .collect();
        libc::close(kq);
        out
    };
    let kernel = match answers.as_slice() {
        [Err(a), Err(b), Err(c)] if a == b && b == c && *a == Errno::EBADF => {
            "EBADF for every access mode (Darwin 25.6 and 27.0)"
        }
        [Err(a), Err(b), Err(c)] if a == b && b == c && *a == Errno::EACCES => {
            "EACCES for every access mode (Darwin 27.2)"
        }
        other => {
            return Err(format!(
                "open(/dev/fd/<kqueue>) with O_RDONLY, O_WRONLY, O_RDWR measured {other:?}, \
                 neither EBADF nor EACCES for every mode"
            ));
        }
    };
    let mut h = Host::new(env.maxfiles);
    let p = h.add_root(Rlimit { soft: PROBE_SOFT, hard: env.hard });
    let s = step(&h, p, &Call::Kqueue, Oracle::Nominal).map_err(|e| e.to_string())?;
    let Ok(Ret::Int(kq)) = s.result else {
        return Err(format!("the model's kqueue: {:?}", s.result));
    };
    let kq = c_int::try_from(kq).map_err(|e| e.to_string())?;
    for flags in modes {
        match step(&s.host, p, &Call::OpenAlias { fd: kq, flags }, Oracle::Nominal) {
            Err(Refusal::Unmodeled { symbol: "open", detail })
                if detail == trust_platform::clauses::KQUEUE_ALIAS => {}
            other => {
                return Err(format!(
                    "the model should refuse open(/dev/fd/<kqueue>, {flags:#x}) by name: {other:?}"
                ));
            }
        }
    }
    println!(
        "  kqueue /dev/fd alias: on this kernel {kernel}; the model refuses that open by name"
    );
    Ok(())
}

/// `F_GETFD` of the descriptor `kqueue()` returns: Darwin 27.2 reads 3
/// (`FD_CLOEXEC|FD_CLOFORK`); Darwin 25.6, which has no `FD_CLOFORK`, reads 1.
/// The model refuses that read by name until an `F_SETFD` sets the flags
/// (PLATFORM-KQUEUE-ALIAS-1). Real side: names which answer this kernel gives
/// and fails on a third.
fn kqueue_getfd_is_refused_by_name(env: &Env) -> Result<(), String> {
    // SAFETY: a kqueue this function owns and closes.
    let read = unsafe {
        let kq = libc::kqueue();
        if kq < 0 {
            return Err(format!("kqueue: errno {}", errno().0));
        }
        let got = libc::fcntl(kq, libc::F_GETFD);
        libc::close(kq);
        got
    };
    let kernel = match read {
        3 => "FD_CLOEXEC|FD_CLOFORK (Darwin 27.2)",
        1 => "FD_CLOEXEC alone (no FD_CLOFORK, as on Darwin 25.6)",
        other => return Err(format!("F_GETFD of a fresh kqueue read {other}, neither 3 nor 1")),
    };
    let mut h = Host::new(env.maxfiles);
    let p = h.add_root(Rlimit { soft: PROBE_SOFT, hard: env.hard });
    let s = step(&h, p, &Call::Kqueue, Oracle::Nominal).map_err(|e| e.to_string())?;
    let Ok(Ret::Int(kq)) = s.result else {
        return Err(format!("the model's kqueue: {:?}", s.result));
    };
    let kq = c_int::try_from(kq).map_err(|e| e.to_string())?;
    let getfd = Call::Fcntl { fd: kq, cmd: darwin::F_GETFD, arg: 0 };
    match step(&s.host, p, &getfd, Oracle::Nominal) {
        Err(Refusal::Unmodeled { symbol: "fcntl", detail })
            if detail == trust_platform::clauses::KQUEUE_GETFD =>
        {
            println!(
                "  kqueue F_GETFD: on this kernel {kernel}; the model refuses that read by name"
            );
            Ok(())
        }
        other => {
            Err(format!("the model should refuse F_GETFD of a fresh kqueue by name: {other:?}"))
        }
    }
}

// =============================================================================
// M2 review: waiting calls and the posix_spawn window. The real side runs in a
// fresh process (stdio on /dev/null, nothing else open) that may start
// threads; the model side is a SCHEDULE of steps by one process, run on
// Darwin and on every spec mutant with no call continued behind its back (a
// refused step, `Blocks` included, is recorded and changes nothing). The
// kernel's observation fixes the outcome of the schedule's observed steps:
// Darwin must produce it, and a mutant that cannot is killed.
// =============================================================================

/// `PROBE_SOFT` table with 0, 1, 2 on one `/dev/null` description, and the
/// working directory `cwd` (canonical) — the fresh process's state.
fn bespoke_host(env: &Env, cwd: &Path) -> Result<(Host, Pid), String> {
    let mut h = Host::new(env.maxfiles);
    h.set_cwd(&canonical_dir(cwd)).map_err(|e| format!("{e:?}"))?;
    let root = h.add_root(Rlimit { soft: PROBE_SOFT, hard: env.hard });
    let null = h
        .install_fresh(root, 0, OfdKind::File, Access::ReadWrite, 0, false)
        .map_err(|e| format!("{e:?}"))?;
    h.install_dup(root, 1, null, false).map_err(|e| format!("{e:?}"))?;
    h.install_dup(root, 2, null, false).map_err(|e| format!("{e:?}"))?;
    h.add_name("/dev/null", NodeKind::CharDevice).map_err(|e| format!("{e:?}"))?;
    Ok((h, root))
}

/// The outcome of every step of `steps` (calls by `pid`, operands resolved
/// against earlier results; a pending call's operand is the number it holds).
fn run_schedule(
    sem: &dyn Semantics,
    h: &Host,
    pid: Pid,
    steps: &[(Call<Operand>, Oracle)],
) -> Vec<String> {
    let mut h = h.clone();
    let mut results: Vec<SysResult> = Vec::new();
    let mut out = Vec::new();
    for (call, o) in steps {
        let Some(call) = resolve_call(call, &results) else {
            out.push("unresolved".to_string());
            results.push(Err(Errno(0)));
            continue;
        };
        match sem.step(&h, pid, &call, *o) {
            Ok(s) => {
                out.push(encode_result(&s.result));
                results.push(s.result);
                h = s.host;
            }
            Err(Refusal::Blocks) => {
                out.push("blocks".to_string());
                results.push(Err(Errno(0)));
            }
            Err(Refusal::Unmodeled { .. }) => {
                out.push("refused".to_string());
                results.push(Err(Errno(0)));
            }
            Err(r) => {
                out.push(format!("declined {r}"));
                results.push(Err(Errno(0)));
            }
        }
    }
    out
}

/// Check a schedule against the kernel: at each `(step, outcome)` of
/// `observed` Darwin must answer `outcome`; returns the mutants that do not.
fn judge(
    what: &str,
    sems: (&dyn Semantics, &[Mutant]),
    h: &Host,
    pid: Pid,
    steps: &[(Call<Operand>, Oracle)],
    observed: &[(usize, String)],
) -> Result<Vec<&'static str>, String> {
    let (darwin, mutants) = sems;
    let fits = |v: &[String]| observed.iter().all(|(i, want)| v.get(*i) == Some(want));
    let model = run_schedule(darwin, h, pid, steps);
    if !fits(&model) {
        return Err(format!(
            "{what}: the kernel observed {observed:?}; the model's schedule gives {model:?}"
        ));
    }
    Ok(mutants.iter().filter(|m| !fits(&run_schedule(*m, h, pid, steps))).map(|m| m.name).collect())
}

/// Run `f` in a fresh process (stdio on /dev/null, every other descriptor
/// closed, soft `RLIMIT_NOFILE` `PROBE_SOFT`) with its own directory; returns
/// the line it wrote.
fn in_fresh_process(env: &Env, name: &str, f: fn(&Path) -> String) -> Result<String, String> {
    let out = env.dir.join(format!("{name}.result"));
    let dir = env.dir.join(format!("ns-{name}"));
    let _ = std::fs::create_dir_all(dir.join("sub"));
    // SAFETY: the harness is single-threaded; the child is a fresh process.
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        // SAFETY: plain descriptor syscalls on this fresh process's own table.
        unsafe {
            let null = CString::new("/dev/null").unwrap_or_default();
            let fd = libc::open(null.as_ptr(), libc::O_RDWR);
            for n in 0..3 {
                if fd != n {
                    libc::dup2(fd, n);
                }
            }
            for f in snapshot() {
                if f.fd > 2 {
                    libc::close(f.fd);
                }
            }
            for n in 0..3 {
                libc::fcntl(n, libc::F_SETFD, 0);
            }
            let rl = libc::rlimit { rlim_cur: PROBE_SOFT, rlim_max: libc::RLIM_INFINITY };
            libc::setrlimit(libc::RLIMIT_NOFILE, &rl);
        }
        let line = f(&dir);
        let _ = std::fs::write(&out, line);
        // SAFETY: leaving the probe process.
        unsafe { libc::_exit(0) };
    }
    if pid < 0 {
        return Err(format!("fork failed: {}", errno()));
    }
    let mut st = 0;
    // SAFETY: our own child.
    unsafe { libc::waitpid(pid, &mut st, 0) };
    std::fs::read_to_string(&out).map_err(|e| format!("{name}: no result ({e}), status {st:#x}"))
}

fn sp1_status_error_channel(env: &Env) -> Result<String, String> {
    fn real(_dir: &Path) -> String {
        use std::os::fd::AsRawFd;
        use std::os::unix::process::CommandExt;
        let (reader, _writer) = match std::io::pipe() {
            Ok(pair) => pair,
            Err(e) => return format!("pipe: {e}"),
        };
        let fd = reader.as_raw_fd();
        let mut original_limit = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
        // SAFETY: a writable rlimit record for this process's own limit.
        if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut original_limit) } != 0 {
            return format!("getrlimit: {}", errno());
        }
        // The fresh process has 0..2 plus this pair at3/4. The status
        // writer starts at6: relocation must protect it from hook target6.
        // Under soft8 relocation cannot allocate: a non-colliding hook at7
        // then checks that the fallback writer still delivers ENOENT.
        for (soft, target) in [(PROBE_SOFT, 6), (8, 7)] {
            let limit = libc::rlimit { rlim_cur: soft, rlim_max: original_limit.rlim_max };
            // SAFETY: only this fresh process's descriptor limit changes.
            if unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &limit) } != 0 {
                return format!("setrlimit: {}", errno());
            }
            let before = snapshot();
            let mut cmd = std::process::Command::new(MISSING);
            // SAFETY: one dup2, integer arguments and no child allocation.
            unsafe {
                cmd.pre_exec(move || {
                    if libc::dup2(fd, target) < 0 {
                        Err(std::io::Error::last_os_error())
                    } else {
                        Ok(())
                    }
                });
            }
            match cmd.spawn() {
                Err(e) if e.raw_os_error() == Some(libc::ENOENT) => {}
                Err(e) => return format!("soft{soft}: missing exec reported {e}"),
                Ok(mut child) => {
                    let _ = child.wait();
                    return format!("soft{soft}: missing exec falsely reported a started child");
                }
            }
            if snapshot() != before {
                return format!("soft{soft}: failed spawn changed the parent's descriptor table");
            }
            let mut status = 0;
            // SAFETY: a nonblocking query for any of this process's children.
            if unsafe { libc::waitpid(-1, &mut status, libc::WNOHANG) } != -1
                || errno() != darwin::Errno::ECHILD
            {
                return format!("soft{soft}: failed spawn did not reap its child");
            }
        }
        "SP1 status errors: relocated and fallback writers deliver ENOENT; parent unchanged and child reaped".to_string()
    }
    let line = in_fresh_process(env, "sp1-status-errors", real)?;
    if line.starts_with("SP1 status errors:") { Ok(line) } else { Err(line) }
}

fn cpath(p: &Path) -> CString {
    CString::new(p.as_os_str().as_encoded_bytes()).unwrap_or_default()
}

/// `r` as `0`/a value, or `-errno`.
fn rc(r: c_int) -> i64 {
    if r < 0 { -i64::from(errno().0) } else { i64::from(r) }
}

/// A thread looping `posix_spawn(exe)` until `stop` (reaping what it spawned).
fn spawner(
    exe: &'static str,
    stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
) -> std::thread::JoinHandle<()> {
    std::thread::spawn(move || {
        let path = CString::new(exe).unwrap_or_default();
        let argv = [path.as_ptr(), std::ptr::null()];
        let envp: [*const c_char; 1] = [std::ptr::null()];
        while !stop.load(std::sync::atomic::Ordering::Relaxed) {
            let mut pid: libc::pid_t = 0;
            // SAFETY: NUL-terminated argv/envp arrays of live C strings.
            let r = unsafe {
                libc::posix_spawn(
                    &mut pid,
                    path.as_ptr(),
                    std::ptr::null(),
                    std::ptr::null(),
                    argv.as_ptr().cast(),
                    envp.as_ptr().cast(),
                )
            };
            if r == 0 {
                let mut st = 0;
                // SAFETY: our own child.
                unsafe { libc::waitpid(pid, &mut st, 0) };
            }
        }
    })
}

/// The real side of [`spawn_window`]: how often (out of at most a few
/// thousand trials, stopping at a few) a close-on-exec `LOCK_EX`'s holder's
/// LAST close left the lock held, beside a thread looping `posix_spawn` of a
/// real image and of a missing one; how often a pipe's reader saw no
/// end-of-file at once after its LAST write end's close.
fn spawn_window_real(dir: &Path) -> String {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};
    let path = cpath(&dir.join("w.lock"));
    let mut seed = 0x2545_f491_4f6c_dd1d_u64;
    let mut jitter = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        u32::try_from(seed % 200).unwrap_or(0)
    };
    // SAFETY (whole block): plain syscalls on this fresh process's own
    // descriptors.
    unsafe {
        libc::close(libc::open(path.as_ptr(), libc::O_RDWR | libc::O_CREAT, 0o644 as libc::c_uint));
        let probe = libc::open(path.as_ptr(), libc::O_RDONLY | libc::O_CLOEXEC);
        let mut held_after = |exe: &'static str, max: u32, enough: u32| -> u32 {
            let stop = Arc::new(AtomicBool::new(false));
            let t = spawner(exe, Arc::clone(&stop));
            let mut held = 0;
            for _ in 0..max {
                if held >= enough {
                    break;
                }
                let l = libc::open(path.as_ptr(), libc::O_RDONLY | libc::O_CLOEXEC);
                while libc::flock(l, libc::LOCK_EX | libc::LOCK_NB) != 0 {
                    libc::usleep(10);
                }
                libc::usleep(jitter());
                libc::close(l);
                if libc::flock(probe, libc::LOCK_EX | libc::LOCK_NB) != 0 {
                    held += 1;
                    while libc::flock(probe, libc::LOCK_EX | libc::LOCK_NB) != 0 {
                        libc::usleep(10);
                    }
                }
                libc::flock(probe, libc::LOCK_UN);
            }
            stop.store(true, Ordering::Relaxed);
            let _ = t.join();
            held
        };
        let ok = held_after("/usr/bin/true", 20_000, 3);
        let failed = held_after(MISSING, 200_000, 1);
        let stop = Arc::new(AtomicBool::new(false));
        let t = spawner("/usr/bin/true", Arc::clone(&stop));
        let mut late = 0;
        for _ in 0..20_000 {
            if late >= 3 {
                break;
            }
            let mut fds = [0; 2];
            libc::pipe(fds.as_mut_ptr());
            libc::ioctl(fds[0], libc::FIOCLEX);
            libc::ioctl(fds[1], libc::FIOCLEX);
            libc::fcntl(fds[0], libc::F_SETFL, libc::O_NONBLOCK);
            libc::usleep(jitter());
            libc::close(fds[1]);
            let mut byte = 0u8;
            if libc::read(fds[0], (&raw mut byte).cast(), 1) < 0 && errno() == Errno::EAGAIN {
                late += 1;
            }
            libc::close(fds[0]);
        }
        stop.store(true, Ordering::Relaxed);
        let _ = t.join();
        format!("{ok} {failed} {late}")
    }
}

/// THE posix_spawn WINDOW (the M2 model review's F1): the new process holds
/// a copy of the caller's whole table, close-on-exec entries included, until
/// its image is activated — or its spawn fails.
fn spawn_window(env: &Env, mutants: &[Mutant]) -> Result<Vec<&'static str>, String> {
    use darwin::*;
    let line = in_fresh_process(env, "spawn-window", spawn_window_real)?;
    let v: Vec<u32> = line.split_whitespace().filter_map(|x| x.parse().ok()).collect();
    let [ok, failed, late] = v.as_slice() else {
        return Err(format!("unreadable: {line:?}"));
    };
    if *ok == 0 || *failed == 0 || *late == 0 {
        return Err(format!(
            "the window was not observed (held after the last close beside a spawn: {ok}; \
             beside a failing spawn: {failed}; late end-of-file: {late})"
        ));
    }
    let (h, root) = bespoke_host(env, &env.dir.join("ns-spawn-window"))?;
    let lock = |end: Oracle| {
        vec![
            (op("w.lock", O_RDONLY | O_CREAT | O_CLOEXEC), Oracle::Nominal),
            (fl(r(0, 0), LOCK_EX), Oracle::Nominal),
            (Call::SpawnBegin, Oracle::Nominal),
            (Call::Close { fd: r(0, 0) }, Oracle::Nominal),
            (op("w.lock", O_RDONLY), Oracle::Nominal),
            (fl(r(4, 0), LOCK_EX | LOCK_NB), Oracle::Nominal),
            (Call::SpawnEnd { child: r(2, 0), actions: Vec::new(), flags: 0 }, end),
            (fl(r(4, 0), LOCK_EX | LOCK_NB), Oracle::Nominal),
        ]
    };
    let held = vec![(5, "err 35".to_string()), (7, "int 0".to_string())];
    let mut killed =
        judge("spawn window", (&Darwin, mutants), &h, root, &lock(Oracle::Nominal), &held)?;
    let fail = lock(Oracle::Fail(Errno::ENOENT));
    killed.extend(judge("failed spawn window", (&Darwin, mutants), &h, root, &fail, &held)?);
    let eof = vec![
        (Call::Pipe, Oracle::Nominal),
        (ioctl(r(0, 0), FIOCLEX, 0), Oracle::Nominal),
        (ioctl(r(0, 1), FIOCLEX, 0), Oracle::Nominal),
        (fcntl(r(0, 0), F_SETFL, i64::from(O_NONBLOCK)), Oracle::Nominal),
        (Call::SpawnBegin, Oracle::Nominal),
        (Call::Close { fd: r(0, 1) }, Oracle::Nominal),
        (Call::ReadSome { fd: r(0, 0) }, Oracle::Nominal),
        (Call::SpawnEnd { child: r(4, 0), actions: Vec::new(), flags: 0 }, Oracle::Nominal),
        (Call::ReadSome { fd: r(0, 0) }, Oracle::Nominal),
    ];
    let seen = vec![(6, "err 35".to_string()), (8, "int 0".to_string())];
    killed.extend(judge("spawn window (pipe EOF)", (&Darwin, mutants), &h, root, &eof, &seen)?);
    println!(
        "  posix_spawn window: a close-on-exec lock outlived its holder's last close beside a \
         spawn ({ok}) and a failing spawn ({failed}); a reader missed end-of-file ({late}) — the \
         model's SpawnBegin/SpawnEnd admit each"
    );
    Ok(killed)
}

/// The real side of [`waiting_fifo_open`]: errno/values while a thread waits
/// in `open(fifo, O_RDONLY)`, then a `dup2` onto the number a waiting open
/// reserved, with its wait in ms.
fn waiting_fifo_real(dir: &Path) -> String {
    let f = cpath(&dir.join("f"));
    let f2 = cpath(&dir.join("f2"));
    // SAFETY (whole block): plain syscalls on this fresh process's own table.
    unsafe {
        libc::mkfifo(f.as_ptr(), 0o600);
        let fa = f.clone();
        let a = std::thread::spawn(move || rc(libc::open(fa.as_ptr(), libc::O_RDONLY)));
        libc::usleep(150_000);
        let g = rc(libc::fcntl(3, libc::F_GETFD));
        let c = rc(libc::close(3));
        let d = rc(libc::dup(0));
        let w = rc(libc::open(f.as_ptr(), libc::O_WRONLY | libc::O_NONBLOCK));
        let av = a.join().unwrap_or(-1);
        for fd in [d, w, av] {
            libc::close(i32::try_from(fd).unwrap_or(-1));
        }
        libc::mkfifo(f2.as_ptr(), 0o600);
        let fb = f2.clone();
        let a2 = std::thread::spawn(move || rc(libc::open(fb.as_ptr(), libc::O_RDONLY)));
        libc::usleep(150_000);
        let helper = libc::fork();
        if helper == 0 {
            libc::usleep(400_000);
            libc::open(f2.as_ptr(), libc::O_WRONLY);
            libc::usleep(200_000);
            libc::_exit(0);
        }
        let t0 = Instant::now();
        let dr = rc(libc::dup2(0, 3));
        let ms = t0.elapsed().as_millis();
        let _ = a2.join();
        let mut st = 0;
        libc::waitpid(helper, &mut st, 0);
        format!("{g} {c} {d} {w} {av} {dr} {ms}")
    }
}

/// A WAITING FIFO OPEN (the M2 model review's F2, F6): its number is reserved
/// (`F_GETFD`/`close` `EBADF`, `dup` skips it, `dup2` onto it waits), and the
/// waiting opener counts as a reader.
fn waiting_fifo_open(env: &Env, mutants: &[Mutant]) -> Result<Vec<&'static str>, String> {
    use darwin::*;
    let line = in_fresh_process(env, "waiting-fifo", waiting_fifo_real)?;
    let v: Vec<i64> = line.split_whitespace().filter_map(|x| x.parse().ok()).collect();
    let [g, c, d, w, av, dr, ms] = v.as_slice() else {
        return Err(format!("unreadable: {line:?}"));
    };
    let val = |x: i64| {
        if x < 0 { format!("err {}", -x) } else { format!("int {x}") }
    };
    let observed = vec![
        (2, val(*g)),
        (3, val(*c)),
        (4, val(*d)),
        (5, val(*w)),
        (6, val(*av)),
        (12, if *ms >= 150 { "blocks".to_string() } else { format!("returned after {ms} ms") }),
        (15, val(*dr)),
    ];
    let (h, root) = bespoke_host(env, &env.dir.join("ns-waiting-fifo"))?;
    let steps = vec![
        (Call::Mkfifo { path: "f".into() }, Oracle::Nominal),
        (op("f", O_RDONLY), Oracle::Nominal),
        (fcntl(lit(3), F_GETFD, 0), Oracle::Nominal),
        (Call::Close { fd: lit(3) }, Oracle::Nominal),
        (Call::Dup { fd: lit(0) }, Oracle::Nominal),
        (op("f", O_WRONLY | O_NONBLOCK), Oracle::Nominal),
        (Call::Resume { fd: r(1, 0) }, Oracle::Nominal),
        (Call::Close { fd: lit(4) }, Oracle::Nominal),
        (Call::Close { fd: lit(5) }, Oracle::Nominal),
        (Call::Close { fd: lit(3) }, Oracle::Nominal),
        (Call::Mkfifo { path: "f2".into() }, Oracle::Nominal),
        (op("f2", O_RDONLY), Oracle::Nominal),
        (Call::Dup2 { from: lit(0), to: lit(3) }, Oracle::Nominal),
        // A writer appears (another process on the kernel; any opener here).
        (op("f2", O_WRONLY), Oracle::Nominal),
        (Call::Resume { fd: r(11, 0) }, Oracle::Nominal),
        (Call::Dup2 { from: lit(0), to: lit(3) }, Oracle::Nominal),
    ];
    let killed = judge("waiting FIFO open", (&Darwin, mutants), &h, root, &steps, &observed)?;
    println!(
        "  waiting FIFO open: its number reserved (F_GETFD {g}, close {c}, dup -> {d}), the \
         waiting reader counted (O_WRONLY|O_NONBLOCK -> {w}), dup2 onto it waited {ms} ms — the \
         model agrees"
    );
    Ok(killed)
}

extern "C" fn on_usr1(_: c_int) {}

/// The real side of [`sleeping_flock`]: a `close` and a `dup2` of a number
/// another thread sleeps in `flock` on (each with its wait in ms), the
/// sleeper's result, then a sleeper interrupted by a signal whose handler
/// was installed without `SA_RESTART`.
fn sleeping_flock_real(dir: &Path) -> String {
    use std::os::unix::thread::JoinHandleExt as _;
    let path = cpath(&dir.join("s.lock"));
    // SAFETY (whole block): plain syscalls on this fresh process's own table.
    unsafe {
        let a = libc::open(path.as_ptr(), libc::O_RDWR | libc::O_CREAT, 0o644 as libc::c_uint);
        let w = libc::open(path.as_ptr(), libc::O_RDONLY);
        let z = libc::open(c"/dev/null".as_ptr(), libc::O_RDONLY);
        libc::flock(a, libc::LOCK_EX);
        let release_later = move || {
            std::thread::spawn(move || {
                libc::usleep(400_000);
                libc::flock(a, libc::LOCK_UN);
            })
        };
        let t = std::thread::spawn(move || rc(libc::flock(w, libc::LOCK_EX)));
        libc::usleep(150_000);
        let rel = release_later();
        let t0 = Instant::now();
        let cr = rc(libc::close(w));
        let close_ms = t0.elapsed().as_millis();
        let trc = t.join().unwrap_or(-1);
        let _ = rel.join();
        let b = libc::open(path.as_ptr(), libc::O_RDONLY);
        let fb = rc(libc::flock(b, libc::LOCK_EX | libc::LOCK_NB));
        libc::close(b);
        libc::flock(a, libc::LOCK_EX);
        let w2 = libc::open(path.as_ptr(), libc::O_RDONLY);
        let t2 = std::thread::spawn(move || rc(libc::flock(w2, libc::LOCK_EX)));
        libc::usleep(150_000);
        let rel = release_later();
        let t0 = Instant::now();
        let dr = rc(libc::dup2(z, w2));
        let dup2_ms = t0.elapsed().as_millis();
        let _ = t2.join();
        let _ = rel.join();
        libc::close(w2);
        let mut sa: libc::sigaction = std::mem::zeroed();
        sa.sa_sigaction = on_usr1 as *const () as usize;
        sa.sa_flags = 0;
        libc::sigemptyset(&mut sa.sa_mask);
        libc::sigaction(libc::SIGUSR1, &sa, std::ptr::null_mut());
        libc::flock(a, libc::LOCK_EX);
        let w3 = libc::open(path.as_ptr(), libc::O_RDONLY);
        let t3 = std::thread::spawn(move || rc(libc::flock(w3, libc::LOCK_EX)));
        libc::usleep(150_000);
        libc::pthread_kill(t3.as_pthread_t(), libc::SIGUSR1);
        let trc3 = t3.join().unwrap_or(-1);
        let nb = rc(libc::flock(w3, libc::LOCK_EX | libc::LOCK_NB));
        format!("{cr} {close_ms} {trc} {fb} {dr} {dup2_ms} {trc3} {nb}")
    }
}

/// A SLEEPING flock (the M2 model review's F5, F7): `close` and `dup2` of its
/// number wait until it returns — `0`, the lock taken — and a signal handler
/// without `SA_RESTART` interrupts it (`EINTR`).
fn sleeping_flock(env: &Env, mutants: &[Mutant]) -> Result<Vec<&'static str>, String> {
    use darwin::*;
    let line = in_fresh_process(env, "sleeping-flock", sleeping_flock_real)?;
    let v: Vec<i64> = line.split_whitespace().filter_map(|x| x.parse().ok()).collect();
    let [cr, close_ms, trc, fb, dr, dup2_ms, trc3, nb] = v.as_slice() else {
        return Err(format!("unreadable: {line:?}"));
    };
    let val = |x: i64| {
        if x < 0 { format!("err {}", -x) } else { format!("int {x}") }
    };
    let waited = |ms: i64| {
        if ms >= 150 { "blocks".to_string() } else { format!("returned after {ms} ms") }
    };
    let observed = vec![
        (5, waited(*close_ms)),
        (7, val(*trc)),
        (8, val(*cr)),
        (10, val(*fb)),
        (15, waited(*dup2_ms)),
        (18, val(*dr)),
        (23, val(*trc3)),
        (24, val(*nb)),
    ];
    let (h, root) = bespoke_host(env, &env.dir.join("ns-sleeping-flock"))?;
    let steps = vec![
        (op("s.lock", O_RDWR | O_CREAT), Oracle::Nominal),
        (op("s.lock", O_RDONLY), Oracle::Nominal),
        (op("/dev/null", O_RDONLY), Oracle::Nominal),
        (fl(lit(3), LOCK_EX), Oracle::Nominal),
        (fl(lit(4), LOCK_EX), Oracle::Nominal),
        (Call::Close { fd: lit(4) }, Oracle::Nominal),
        (fl(lit(3), LOCK_UN), Oracle::Nominal),
        (Call::Resume { fd: r(4, 0) }, Oracle::Nominal),
        (Call::Close { fd: lit(4) }, Oracle::Nominal),
        (op("s.lock", O_RDONLY), Oracle::Nominal),
        (fl(r(9, 0), LOCK_EX | LOCK_NB), Oracle::Nominal),
        (Call::Close { fd: r(9, 0) }, Oracle::Nominal),
        (fl(lit(3), LOCK_EX), Oracle::Nominal),
        (op("s.lock", O_RDONLY), Oracle::Nominal),
        (fl(r(13, 0), LOCK_EX), Oracle::Nominal),
        (Call::Dup2 { from: lit(5), to: r(13, 0) }, Oracle::Nominal),
        (fl(lit(3), LOCK_UN), Oracle::Nominal),
        (Call::Resume { fd: r(14, 0) }, Oracle::Nominal),
        (Call::Dup2 { from: lit(5), to: r(13, 0) }, Oracle::Nominal),
        (Call::Close { fd: r(13, 0) }, Oracle::Nominal),
        (fl(lit(3), LOCK_EX), Oracle::Nominal),
        (op("s.lock", O_RDONLY), Oracle::Nominal),
        (fl(r(21, 0), LOCK_EX), Oracle::Nominal),
        (Call::Resume { fd: r(22, 0) }, Oracle::Fail(Errno::EINTR)),
        (fl(r(21, 0), LOCK_EX | LOCK_NB), Oracle::Nominal),
    ];
    let killed = judge("sleeping flock", (&Darwin, mutants), &h, root, &steps, &observed)?;
    println!(
        "  sleeping flock: close waited {close_ms} ms and dup2 {dup2_ms} ms for it, it returned \
         {trc}; a signal without SA_RESTART interrupted another ({trc3}) — the model agrees"
    );
    Ok(killed)
}

/// The real side of [`create_then_lock`]: `O_CREAT|O_EXCL|O_EXLOCK|O_NONBLOCK`
/// opens of a fresh name against two racers that open it and take its lock;
/// how many failed `EAGAIN` with the file left created, and the tries.
fn create_then_lock_real(dir: &Path) -> String {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};
    let path = cpath(&dir.join("c.lock"));
    let stop = Arc::new(AtomicBool::new(false));
    let racers: Vec<_> = (0..2)
        .map(|_| {
            let stop = Arc::clone(&stop);
            let p = path.clone();
            std::thread::spawn(move || {
                while !stop.load(Ordering::Relaxed) {
                    // SAFETY: plain syscalls on this thread's own descriptor.
                    unsafe {
                        let fd = libc::open(p.as_ptr(), libc::O_RDONLY | libc::O_NONBLOCK);
                        if fd >= 0 {
                            if libc::flock(fd, libc::LOCK_EX | libc::LOCK_NB) == 0 {
                                libc::flock(fd, libc::LOCK_UN);
                            }
                            libc::close(fd);
                        }
                    }
                }
            })
        })
        .collect();
    let deadline = Instant::now() + Duration::from_secs(20);
    let (mut seen, mut tries) = (0u32, 0u32);
    while seen == 0 && tries < 1_000_000 && Instant::now() < deadline {
        tries += 1;
        // SAFETY: plain syscalls; `st` is a live stat buffer.
        unsafe {
            libc::unlink(path.as_ptr());
            let flags =
                libc::O_RDWR | libc::O_CREAT | libc::O_EXCL | libc::O_EXLOCK | libc::O_NONBLOCK;
            let fd = libc::open(path.as_ptr(), flags, 0o600 as libc::c_uint);
            if fd >= 0 {
                libc::close(fd);
            } else if errno() == Errno::EAGAIN {
                let mut st: libc::stat = std::mem::zeroed();
                if libc::stat(path.as_ptr(), &mut st) == 0 {
                    seen += 1;
                }
            }
        }
    }
    stop.store(true, Ordering::Relaxed);
    for t in racers {
        let _ = t.join();
    }
    format!("{seen} {tries}")
}

/// `O_CREAT` WITH A LOCK BIT CREATES, THEN LOCKS (the M2 model review's F4): a
/// racer can lock the new file in between, and the open fails `EAGAIN`
/// leaving the file created.
fn create_then_lock(env: &Env, mutants: &[Mutant]) -> Result<Vec<&'static str>, String> {
    use darwin::*;
    let line = in_fresh_process(env, "create-then-lock", create_then_lock_real)?;
    let v: Vec<u32> = line.split_whitespace().filter_map(|x| x.parse().ok()).collect();
    let [seen, tries] = v.as_slice() else {
        return Err(format!("unreadable: {line:?}"));
    };
    if *seen == 0 {
        return Err(format!("EAGAIN with the file left created not observed in {tries} tries"));
    }
    let (h, root) = bespoke_host(env, &env.dir.join("ns-create-then-lock"))?;
    let steps = vec![
        (op("c.lock", O_RDWR | O_CREAT | O_EXCL | O_EXLOCK | O_NONBLOCK), Oracle::Nominal),
        (op("c.lock", O_RDONLY | O_NONBLOCK), Oracle::Nominal),
        (fl(r(1, 0), LOCK_EX | LOCK_NB), Oracle::Nominal),
        (Call::Resume { fd: r(0, 0) }, Oracle::Nominal),
        (op("c.lock", O_RDWR | O_CREAT | O_EXCL), Oracle::Nominal),
    ];
    let observed = vec![(3, "err 35".to_string()), (4, "err 17".to_string())];
    let killed = judge("create then lock", (&Darwin, mutants), &h, root, &steps, &observed)?;
    println!(
        "  O_CREAT|O_EXLOCK: a racer locked the new file first in {seen} of {tries} tries (EAGAIN, \
         the file left created) — the model's create-then-lock admits it"
    );
    Ok(killed)
}

/// The real side of [`spellings`]: for each other spelling of a locked file,
/// `flock(LOCK_EX|LOCK_NB)` through it and whether it stats as the file;
/// then two `/dev/ptmx` masters' locks.
fn spellings_real(dir: &Path) -> String {
    let canon = canonical_dir(dir);
    let mut out = Vec::new();
    // SAFETY (whole block): plain syscalls on this fresh process's own table.
    unsafe {
        let a = libc::open(
            cpath(&dir.join("Lease.lock")).as_ptr(),
            libc::O_RDWR | libc::O_CREAT,
            0o644 as libc::c_uint,
        );
        libc::flock(a, libc::LOCK_EX);
        let mut sa: libc::stat = std::mem::zeroed();
        libc::fstat(a, &mut sa);
        for alias in spelling_aliases(&canon) {
            let real =
                if alias.starts_with('/') { PathBuf::from(&alias) } else { dir.join(&alias) };
            let b = libc::open(cpath(&real).as_ptr(), libc::O_RDONLY);
            let mut sb: libc::stat = std::mem::zeroed();
            libc::fstat(b, &mut sb);
            let same = b >= 0 && sa.st_dev == sb.st_dev && sa.st_ino == sb.st_ino;
            out.push(format!(
                "{}:{}",
                rc(libc::flock(b, libc::LOCK_EX | libc::LOCK_NB)),
                u8::from(same)
            ));
            libc::close(b);
        }
        let p1 = libc::open(c"/dev/ptmx".as_ptr(), libc::O_RDWR);
        let p2 = libc::open(c"/dev/ptmx".as_ptr(), libc::O_RDWR);
        out.push(format!(
            "{}:{}",
            rc(libc::flock(p1, libc::LOCK_EX | libc::LOCK_NB)),
            rc(libc::flock(p2, libc::LOCK_EX | libc::LOCK_NB))
        ));
    }
    out.join(" ")
}

// The fixture generator is shared with the independently collected cross-root
// regression so a custom TMPDIR cannot silently turn an alias into the target.
#[path = "conformance_darwin/spelling_paths.rs"]
mod spelling_paths;
use spelling_paths::spelling_aliases;

/// ONE FILE, ONE SPELLING (the M2 model review's F3, F10): every other
/// spelling of a file reaches it on Darwin (its lock conflicts), so the flat
/// namespace refuses them by name; two `/dev/ptmx` opens are two devices.
fn spellings(env: &Env, mutants: &[Mutant]) -> Result<Vec<&'static str>, String> {
    use darwin::*;
    let dir = env.dir.join("ns-spellings");
    let line = in_fresh_process(env, "spellings", spellings_real)?;
    let cells: Vec<&str> = line.split_whitespace().collect();
    let aliases = spelling_aliases(&canonical_dir(&dir));
    if cells.len() != aliases.len() + 1 {
        return Err(format!("unreadable: {line:?}"));
    }
    let (h, root) = bespoke_host(env, &dir)?;
    let mut killed = Vec::new();
    for (alias, cell) in aliases.iter().zip(&cells) {
        if *cell != "-35:1" {
            return Err(format!(
                "{alias:?}: expected one node and a conflicting lock, measured {cell}"
            ));
        }
        let steps = vec![
            (op("Lease.lock", O_RDWR | O_CREAT), Oracle::Nominal),
            (fl(lit(3), LOCK_EX), Oracle::Nominal),
            (op(alias, O_RDONLY), Oracle::Nominal),
            (fl(r(2, 0), LOCK_EX | LOCK_NB), Oracle::Nominal),
        ];
        let model = run_schedule(&Darwin, &h, root, &steps);
        if model.get(2).map(String::as_str) != Some("refused") {
            return Err(format!("{alias:?}: the model must refuse another spelling: {model:?}"));
        }
        for m in mutants {
            let v = run_schedule(m, &h, root, &steps);
            if v.get(2).map(String::as_str) != Some("refused")
                && v.get(3).map(String::as_str) != Some("err 35")
            {
                killed.push(m.name);
            }
        }
    }
    let ptmx = cells.last().copied().unwrap_or_default();
    if ptmx != "0:0" {
        return Err(format!("two /dev/ptmx masters: expected two granted locks, measured {ptmx}"));
    }
    let steps = vec![
        (op("/dev/ptmx", O_RDWR), Oracle::Nominal),
        (op("/dev/ptmx", O_RDWR), Oracle::Nominal),
        (fl(r(0, 0), LOCK_EX | LOCK_NB), Oracle::Nominal),
        (fl(r(1, 0), LOCK_EX | LOCK_NB), Oracle::Nominal),
    ];
    let model = run_schedule(&Darwin, &h, root, &steps);
    if model.first().map(String::as_str) != Some("refused") {
        return Err(format!("/dev/ptmx: the model must refuse a cloning device: {model:?}"));
    }
    for m in mutants {
        let v = run_schedule(m, &h, root, &steps);
        if v.first().map(String::as_str) != Some("refused")
            && v.get(3).map(String::as_str) != Some("int 0")
        {
            killed.push(m.name);
        }
    }
    println!(
        "  spellings: {} other spellings of a locked file reached it (its lock conflicted) and two \
         /dev/ptmx masters locked independently — the model refuses each by name",
        aliases.len()
    );
    Ok(killed)
}

// =============================================================================
// Driver
// =============================================================================

fn maxfiles() -> u64 {
    let mut v: c_int = 0;
    let mut sz = std::mem::size_of::<c_int>();
    let name = CString::new("kern.maxfilesperproc").unwrap_or_default();
    // SAFETY: `v` is a live int and `sz` its size.
    let rc = unsafe {
        libc::sysctlbyname(name.as_ptr(), (&raw mut v).cast(), &mut sz, std::ptr::null_mut(), 0)
    };
    if rc == 0 { u64::try_from(v).unwrap_or(0) } else { 0 }
}

/// libc's add-time validation of file actions vs [`file_action_add`]: every
/// mismatch, as a line. Runs in the harness process (no descriptor is
/// opened; each action list is initialised and destroyed).
fn file_action_add_mismatches() -> Vec<String> {
    let cases = [
        FileAction::Close { fd: 10_239 },
        FileAction::Close { fd: 10_240 },
        FileAction::Close { fd: 20_000 },
        FileAction::Close { fd: -1 },
        FileAction::Dup2 { from: 5, to: 7 },
        FileAction::Dup2 { from: 20_000, to: 7 },
        FileAction::Dup2 { from: 5, to: 20_000 },
        FileAction::Open { fd: 9, flags: darwin::O_RDONLY },
        FileAction::Open { fd: 20_000, flags: darwin::O_RDONLY },
        FileAction::Inherit { fd: 10_239 },
        FileAction::Inherit { fd: 10_240 },
        FileAction::Fchdir { fd: 3 },
        FileAction::Fchdir { fd: 20_000 },
    ];
    let devnull = CString::new("/dev/null").unwrap_or_default();
    let mut out = Vec::new();
    for a in cases {
        // SAFETY: a fresh action list, destroyed after one add.
        let rc = unsafe {
            let mut fa: libc::posix_spawn_file_actions_t = std::ptr::null_mut();
            libc::posix_spawn_file_actions_init(&mut fa);
            let rc = match a {
                FileAction::Close { fd } => libc::posix_spawn_file_actions_addclose(&mut fa, fd),
                FileAction::Dup2 { from, to } => {
                    libc::posix_spawn_file_actions_adddup2(&mut fa, from, to)
                }
                FileAction::Open { fd, flags } => {
                    libc::posix_spawn_file_actions_addopen(&mut fa, fd, devnull.as_ptr(), flags, 0)
                }
                FileAction::Inherit { fd } => posix_spawn_file_actions_addinherit_np(&mut fa, fd),
                FileAction::Fchdir { fd } => posix_spawn_file_actions_addfchdir_np(&mut fa, fd),
                FileAction::Chdir => {
                    posix_spawn_file_actions_addchdir_np(&mut fa, devnull.as_ptr())
                }
                FileAction::InheritIf { .. } | FileAction::PlaceStdio { .. } => {
                    panic!("a raw add-time check contains a std builder")
                }
            };
            libc::posix_spawn_file_actions_destroy(&mut fa);
            rc
        };
        let real = if rc == 0 { Ok(()) } else { Err(Errno(rc)) };
        let model = trust_platform::clauses::file_action_add(&a);
        if real != model {
            out.push(format!("{a:?}: libc {real:?}, model {model:?}"));
        }
    }
    out
}

/// The torn table copy (`step_torn`) is a real Darwin outcome: in a fresh
/// process, one thread keeps re-pointing an always-open fd 50 between two
/// descriptions with `dup2` while the main thread forks; a child whose fd 50
/// is closed got a torn copy. Returns `(torn, forks)`. Statistical: it shows
/// the outcome is reachable, never that it is likely.
fn torn_copy_probe(env: &Env) -> Result<(u32, u32), String> {
    let out = env.dir.join("torn.result");
    // SAFETY: the harness is single-threaded; the child is a fresh process
    // that may start threads of its own.
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let (torn, forks) = torn_copy_child();
        let _ = std::fs::write(&out, format!("{torn} {forks}"));
        // SAFETY: leaving the probe process.
        unsafe { libc::_exit(0) };
    }
    if pid < 0 {
        return Err(format!("fork failed: {}", errno()));
    }
    let mut st = 0;
    // SAFETY: our own child.
    unsafe { libc::waitpid(pid, &mut st, 0) };
    let text = std::fs::read_to_string(&out).map_err(|e| format!("no result: {e}"))?;
    let mut it = text.split_whitespace().map(|v| v.parse::<u32>().unwrap_or(0));
    Ok((it.next().unwrap_or(0), it.next().unwrap_or(0)))
}

fn torn_copy_child() -> (u32, u32) {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};
    const FORKS: u32 = 3000;
    let mut fds = [0; 2];
    // SAFETY: plain descriptor syscalls on this fresh process's own table.
    unsafe {
        libc::pipe(fds.as_mut_ptr());
        libc::dup2(fds[0], 50);
    }
    let (a, b) = (fds[0], fds[1]);
    let stop = Arc::new(AtomicBool::new(false));
    let stop2 = Arc::clone(&stop);
    let racer = std::thread::spawn(move || {
        while !stop2.load(Ordering::Relaxed) {
            // SAFETY: fd 50 stays open: each dup2 replaces it atomically.
            unsafe {
                libc::dup2(a, 50);
                libc::dup2(b, 50);
            }
        }
    });
    let mut torn = 0;
    for _ in 0..FORKS {
        // SAFETY: the child only calls fcntl and _exit (async-signal-safe).
        let c = unsafe { libc::fork() };
        if c == 0 {
            // SAFETY: as above.
            let open = unsafe { libc::fcntl(50, libc::F_GETFD) } != -1;
            unsafe { libc::_exit(if open { 0 } else { 1 }) };
        }
        let mut st = 0;
        // SAFETY: our own child.
        unsafe { libc::waitpid(c, &mut st, 0) };
        if libc::WIFEXITED(st) && libc::WEXITSTATUS(st) == 1 {
            torn += 1;
        }
    }
    stop.store(true, Ordering::Relaxed);
    let _ = racer.join();
    (torn, FORKS)
}

/// Runs in the forked probe root. Returns the lines of its result file.
fn probe_root(
    pi: usize,
    probe: &Probe,
    mutants: &[Mutant],
    xmutants: &[x3a::XMutant],
    env: &Env,
) -> Vec<String> {
    // AF_UNIX sockets are bound by a short name relative to the private
    // directory, so no TMPDIR length can overflow `sun_path`.
    if let Err(e) = std::env::set_current_dir(&env.dir) {
        return vec![format!("REALERR\tchdir {}: {e}", env.dir.display())];
    }
    // A known initial table: 0, 1, 2 = one /dev/null description; nothing else.
    // SAFETY: plain descriptor syscalls on this process's own table.
    unsafe {
        let null = CString::new("/dev/null").unwrap_or_default();
        let fd = libc::open(null.as_ptr(), libc::O_RDWR);
        for n in 0..3 {
            if fd != n {
                libc::dup2(fd, n);
            }
        }
        if fd > 2 {
            libc::close(fd);
        }
        for f in snapshot() {
            if f.fd > 2 {
                libc::close(f.fd);
            }
        }
        for n in 0..3 {
            libc::fcntl(n, libc::F_SETFD, 0);
        }
        let rl = libc::rlimit { rlim_cur: PROBE_SOFT, rlim_max: env.hard };
        libc::setrlimit(libc::RLIMIT_NOFILE, &rl);
    }
    let mut init = Host::new(env.maxfiles);
    let root = init.add_root(Rlimit { soft: PROBE_SOFT, hard: env.hard });
    let null =
        init.install_fresh(root, 0, OfdKind::File, Access::ReadWrite, 0, false).expect("fd 0");
    init.install_dup(root, 1, null, false).expect("fd 1");
    init.install_dup(root, 2, null, false).expect("fd 2");
    // The namespace (M2): `/dev/null`, and this probe's own directory with one
    // subdirectory `dir` in it. The model's working directory is that
    // directory's canonical spelling (relative model names resolve there, as
    // the real calls' `ns.join(path)` do).
    let ns = env.dir.join(format!("ns{pi}"));
    let _ = std::fs::create_dir_all(ns.join("dir"));
    init.set_cwd(&canonical_dir(&ns)).expect("the probe directory's canonical spelling");
    init.add_name("/dev/null", NodeKind::CharDevice).expect("/dev/null");
    init.add_name("dir", NodeKind::Directory).expect("dir");
    let init_real = snapshot();

    let sock = PathBuf::from(format!("p{pi}.sock"));
    let n = probe.steps.len();
    let real = Real {
        pi,
        probe,
        env,
        results: vec![Err(Errno(0)); n],
        recs: vec![Rec::default(); n],
        sock,
        ns,
    };
    let recs = real.run();

    let mut lines = Vec::new();
    for (i, rec) in recs.iter().enumerate() {
        if let Some(e) = &rec.error {
            lines.push(format!("REALERR\tstep {i}: {e}"));
        }
    }
    let darwin: &dyn Spec = &Darwin;
    let mut specs: Vec<(&str, &dyn Spec)> = vec![("Darwin", darwin)];
    for m in mutants {
        specs.push((m.name, m));
    }
    for m in xmutants {
        specs.push((m.name, m));
    }
    for (name, sem) in specs {
        match replay(sem, &init, root, probe, &init_real, &recs) {
            Ok(r) => lines.push(format!("PASS\t{name}\t{}\t{}", r.steps, r.observations)),
            Err(e) => lines.push(format!("FAIL\t{name}\t{}", e.replace(['\t', '\n'], " "))),
        }
    }
    lines
}

fn run_probe(
    pi: usize,
    probe: &Probe,
    mutants: &[Mutant],
    xmutants: &[x3a::XMutant],
    env: &Env,
) -> Vec<String> {
    let result = env.dir.join(format!("p{pi}.result"));
    // SAFETY: the harness is single-threaded.
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let lines = probe_root(pi, probe, mutants, xmutants, env);
        let _ = std::fs::write(&result, lines.join("\n"));
        // SAFETY: leaving the probe root.
        unsafe { libc::_exit(0) };
    }
    if pid < 0 {
        return vec![format!("REALERR\tfork failed: {}", errno())];
    }
    let mut st = 0;
    // SAFETY: our own child.
    unsafe { libc::waitpid(pid, &mut st, 0) };
    match std::fs::read_to_string(&result) {
        Ok(s) => s.lines().map(str::to_string).collect(),
        Err(_) => vec![format!("REALERR\tprobe root died (wait status {st:#x})")],
    }
}

fn reporter(path: &str, park: bool) -> c_int {
    let fds = snapshot();
    let mut out = String::new();
    for f in &fds {
        out.push_str("H ");
        out.push_str(&f.encode());
        out.push('\n');
    }
    let tmp = format!("{path}.tmp");
    if std::fs::write(&tmp, out).is_ok() {
        let _ = std::fs::rename(&tmp, path);
    }
    if park {
        // An image that lives on with every descriptor its exec kept, until
        // the probe root kills it (bounded: a forgotten parker exits).
        let deadline = Instant::now() + Duration::from_secs(60);
        while Instant::now() < deadline {
            // SAFETY: plain sleep.
            unsafe { libc::usleep(100_000) };
        }
    }
    // SAFETY: leaving without running anything else.
    unsafe { libc::_exit(0) }
}

/// # Safety
/// Called by the C runtime with a valid `argv` of `argc` C strings.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args: Vec<String> = (0..usize::try_from(argc).unwrap_or(0))
        // SAFETY: the C runtime passes `argc` valid NUL-terminated strings.
        .map(|i| unsafe { CStr::from_ptr(*argv.add(i)) }.to_string_lossy().into_owned())
        .collect();
    if args.get(1).map(String::as_str) == Some(REPORTER_FLAG) {
        return reporter(args.get(2).map_or("", String::as_str), false);
    }
    if args.get(1).map(String::as_str) == Some(REPORTER_PARK_FLAG) {
        return reporter(args.get(2).map_or("", String::as_str), true);
    }
    if args.get(1).map(String::as_str) == Some(x3a::LONG_TMPDIR_FLAG) {
        return x3a::long_tmpdir_run();
    }
    harness()
}

/// The run's environment: a fresh private directory under `TMPDIR` (made
/// absolute, and unique by pid and time so an earlier run's leftovers are
/// never reused), the host's limits, this binary's path.
fn make_env() -> Env {
    let exe = std::env::current_exe().expect("current_exe");
    let base = std::path::absolute(std::env::temp_dir()).unwrap_or_else(|_| PathBuf::from("/tmp"));
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.subsec_nanos());
    let dir = base.join(format!("tpconf-{}-{nanos}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let mut rl = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
    // SAFETY: live rlimit buffer.
    unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut rl) };
    Env {
        maxfiles: maxfiles(),
        hard: rl.rlim_max,
        exe: CString::new(exe.as_os_str().as_encoded_bytes()).expect("exe path"),
        dir,
    }
}

// Trust: independently check both real policies without changing model selection.
fn check_std_inheritance_policy(env: &Env) -> Result<&'static str, String> {
    use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::process::CommandExt;
    let mut fds = [-1; 2];
    // SAFETY: a live pair buffer; each returned descriptor gets one owner.
    if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
        return Err(format!("inheritance control pipe: {}", errno()));
    }
    let owned = fds.map(|fd| unsafe { OwnedFd::from_raw_fd(fd) });
    if owned.iter().any(|fd| fd.as_raw_fd() <= 2) {
        return Err("inheritance control needs two descriptors above stdio".to_string());
    }
    for explicit in [false, true] {
        let report = env.dir.join(format!("inheritance-{explicit}.report"));
        let exe = std::ffi::OsStr::from_bytes(env.exe.as_bytes());
        let mut cmd = std::process::Command::new(exe);
        cmd.arg(REPORTER_FLAG).arg(&report);
        if explicit {
            cmd.inherit_all_fds();
        }
        let status = cmd.status().map_err(|e| format!("inheritance reporter: {e}"))?;
        if !status.success() {
            return Err(format!("inheritance reporter exited {status}"));
        }
        let text = std::fs::read_to_string(report).map_err(|e| e.to_string())?;
        let table: Vec<RealFd> =
            text.lines().filter_map(|s| s.strip_prefix("H ")).filter_map(RealFd::decode).collect();
        if table.is_empty() {
            return Err("inheritance reporter wrote no table".to_string());
        }
        for fd in &owned {
            let present = table.iter().any(|f| f.fd == fd.as_raw_fd());
            if present != explicit {
                return Err(format!(
                    "fd {}: inherit_all_fds={explicit}, inherited={present}",
                    fd.as_raw_fd()
                ));
            }
        }
    }
    Ok(
        "P-STD-POLICIES: real default SP-1 excludes the same two unflagged descriptors that explicit inherit_all_fds carries; paired native check, not a proof of the summaries",
    )
}

fn harness() -> c_int {
    let started = Instant::now();
    let env = make_env();
    let dir = env.dir.clone();
    let mut probes = probes(&env);
    probes.extend(m2_probes(&env));
    let mut mutants = mutants();
    mutants.extend(m2_mutants());
    mutants.extend(m2_review_mutants());
    let xmutants = x3a::mutants();
    let mut failed = false;
    match check_std_inheritance_policy(&env) {
        Ok(msg) => println!("  {msg}"),
        Err(error) => {
            println!("  std inheritance policy FAILED: {error}");
            failed = true;
        }
    }
    match std_model::check(&env) {
        Ok(msg) => println!("  {msg}"),
        Err(e) => {
            println!("  P-STD-MODEL premise FAILED: {e}");
            failed = true;
        }
    }
    match x3a::std_file_lock_is_flock(&env) {
        Ok(msg) => println!("  {msg}"),
        Err(e) => {
            println!("  STD-FILE-LOCK premise FAILED: {e}");
            failed = true;
        }
    }
    match x3a::long_tmpdir_check(&env) {
        Ok(msg) => println!("  {msg}"),
        Err(e) => {
            println!("  long TMPDIR FAILED: {e}");
            failed = true;
        }
    }
    let add_mismatches = file_action_add_mismatches();
    for m in &add_mismatches {
        println!("  posix_spawn_file_actions_add* MISMATCH: {m}");
        failed = true;
    }
    if add_mismatches.is_empty() {
        println!(
            "  posix_spawn_file_actions_add*: libc's add-time OPEN_MAX check matches the model"
        );
    }
    match torn_copy_probe(&env) {
        Ok((torn, forks)) if torn > 0 => println!(
            "  torn table copy: {torn} of {forks} fork children lacked an always-open fd that \
             another thread kept dup2-ing (step_torn's outcome is real)"
        ),
        Ok((_, forks)) => {
            println!("  torn table copy: NOT observed in {forks} forks (step_torn unconfirmed)");
            failed = true;
        }
        Err(e) => {
            println!("  torn table copy probe failed: {e}");
            failed = true;
        }
    }
    for p in &probes {
        if let Err(e) = validate(p) {
            println!("INVALID PROBE {}: {e}", p.name);
            failed = true;
        }
    }
    let orphan_kills = match lock_outlives_its_taker(&env, &mutants) {
        Ok(k) => k,
        Err(e) => {
            println!("  lock-outlives-its-taker check FAILED: {e}");
            failed = true;
            Vec::new()
        }
    };
    if let Err(e) = blocking_upgrade_drops_shared_first(&env) {
        println!("  blocking-upgrade check FAILED: {e}");
        failed = true;
    }
    if let Err(e) = clofork_is_refused_by_name(&env) {
        println!("  FD_CLOFORK check FAILED: {e}");
        failed = true;
    }
    if let Err(e) = kqueue_alias_is_refused_by_name(&env) {
        println!("  kqueue /dev/fd alias check FAILED: {e}");
        failed = true;
    }
    if let Err(e) = kqueue_getfd_is_refused_by_name(&env) {
        println!("  kqueue F_GETFD check FAILED: {e}");
        failed = true;
    }
    match sp1_status_error_channel(&env) {
        Ok(line) => println!("  {line}"),
        Err(e) => {
            println!("  SP1 status error-channel check FAILED: {e}");
            failed = true;
        }
    }
    type Check = fn(&Env, &[Mutant]) -> Result<Vec<&'static str>, String>;
    let review_checks: [(&str, Check); 5] = [
        ("spawn-window", spawn_window),
        ("waiting-fifo-open", waiting_fifo_open),
        ("sleeping-flock", sleeping_flock),
        ("create-then-lock", create_then_lock),
        ("spellings", spellings),
    ];
    let mut review_kills: Vec<(&str, Vec<&'static str>)> = Vec::new();
    for (name, check) in review_checks {
        match check(&env, &mutants) {
            Ok(k) => review_kills.push((name, k)),
            Err(e) => {
                println!("  {name} check FAILED: {e}");
                failed = true;
            }
        }
    }
    if failed {
        let _ = std::fs::remove_dir_all(&dir);
        return 1;
    }
    println!(
        "trust-platform conformance on {} (kern.maxfilesperproc={}, hard RLIMIT_NOFILE={}): {} probes x (Darwin + {} spec mutants)",
        trust_platform::PLATFORM_SPEC,
        env.maxfiles,
        env.hard,
        probes.len(),
        mutants.len() + xmutants.len()
    );
    let all: Vec<(&'static str, &'static str)> = mutants
        .iter()
        .map(|m| (m.name, m.clause))
        .chain(xmutants.iter().map(|m| (m.name, m.clause)))
        .collect();
    let mut killed_by: BTreeMap<&'static str, Vec<String>> =
        all.iter().map(|(name, _)| (*name, Vec::new())).collect();
    for name in orphan_kills {
        if let Some(v) = killed_by.get_mut(name) {
            v.push("lock-outlives-its-taker".to_string());
        }
    }
    for (check, names) in review_kills {
        for name in names {
            if let Some(v) = killed_by.get_mut(name) {
                v.push(format!("{check} check"));
            }
        }
    }
    let (mut steps, mut observations) = (0usize, 0usize);
    for (pi, p) in probes.iter().enumerate() {
        let lines = run_probe(pi, p, &mutants, &xmutants, &env);
        let darwin_passed = lines.iter().any(|l| l.starts_with("PASS\tDarwin\t"))
            && !lines.iter().any(|l| l.starts_with("REALERR"));
        let mut darwin_ok = false;
        for line in &lines {
            let cols: Vec<&str> = line.splitn(4, '\t').collect();
            match cols.as_slice() {
                ["REALERR", msg] => {
                    println!("  REAL-RUN ERROR in {}: {msg}", p.name);
                    failed = true;
                }
                ["PASS", "Darwin", s, o] => {
                    darwin_ok = true;
                    steps += s.parse::<usize>().unwrap_or(0);
                    observations += o.parse::<usize>().unwrap_or(0);
                    println!(
                        "  probe {:<26} Darwin PASS ({s} steps, {o} table observations)",
                        p.name
                    );
                }
                ["FAIL", "Darwin", msg] => {
                    println!("  probe {:<26} Darwin FAIL: {msg}", p.name);
                    failed = true;
                }
                // A kill counts only on a probe the real spec passes.
                ["FAIL", name, msg] if darwin_passed => {
                    if let Some(v) = killed_by.get_mut(*name) {
                        v.push(format!("{}: {msg}", p.name));
                    }
                }
                _ => {}
            }
        }
        if !darwin_ok && !lines.iter().any(|l| l.starts_with("FAIL\tDarwin")) {
            println!("  probe {:<26} produced no Darwin verdict: {lines:?}", p.name);
            failed = true;
        }
    }
    println!("spec-mutant kill matrix:");
    let mut survivors = 0;
    for (name, clause) in &all {
        let kills = &killed_by[name];
        match kills.first() {
            Some(first) => {
                println!(
                    "  KILLED   {name:<36} [{clause}] by {} probe(s); first: {first}",
                    kills.len()
                );
            }
            None => {
                survivors += 1;
                println!("  SURVIVED {name:<36} [{clause}]");
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
    println!(
        "summary: {} probes, {steps} steps, {observations} table observations; {} of {} mutants killed; {:.1}s",
        probes.len(),
        all.len() - survivors,
        all.len(),
        started.elapsed().as_secs_f64()
    );
    if failed || survivors > 0 {
        println!("conformance FAILED");
        1
    } else {
        println!("conformance ok");
        0
    }
}
