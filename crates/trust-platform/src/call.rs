//! The event vocabulary: what a process asks the platform ([`Call`]), what it
//! gets back ([`SysResult`]), which environment choice resolved any
//! nondeterminism ([`Oracle`]), and how the model declines what it does not
//! model ([`Refusal`]).

use crate::darwin::Errno;
use crate::host::{Host, Pid};
use crate::introspect::ListedFd;

/// A spawn file-action entry or a std builder that resolves to an entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FileAction<V = i32> {
    /// `posix_spawn_file_actions_addclose(fd)`.
    Close { fd: V },
    /// `posix_spawn_file_actions_adddup2(from, to)`.
    Dup2 { from: V, to: V },
    /// `posix_spawn_file_actions_addopen(fd, path, oflag, mode)`; the path is
    /// not modeled (the spawn's oracle decides whether the open succeeds).
    Open { fd: V, flags: i32 },
    /// `posix_spawn_file_actions_addinherit_np(fd)` (Darwin).
    Inherit { fd: V },
    /// std's conditional inherited-stdio action. `enabled` is the captured
    /// result of `StdPassesExec`, before the spawn copies the table.
    InheritIf { fd: V, enabled: V },
    /// std places owned stdio with addinherit_np when source == target;
    /// otherwise it uses adddup2. Resolved before the raw Darwin operation.
    PlaceStdio { from: V, to: V },
    /// `posix_spawn_file_actions_addchdir(_np)(path)`: a working-directory
    /// change in the child; no descriptor effect, but its path resolution
    /// can fail the spawn (the spawn's oracle: `ENOENT`, `ENOTDIR`, …).
    Chdir,
    /// `posix_spawn_file_actions_addfchdir(_np)(fd)`. MEASURED: fails the
    /// spawn with `EBADF` on a closed descriptor, `EINVAL` on a kqueue,
    /// `ENOTDIR` on a regular file.
    Fchdir { fd: V },
}

impl<V> FileAction<V> {
    /// Every descriptor operand of the action (what libc validates at add
    /// time against `OPEN_MAX`).
    pub fn fds(&self) -> Vec<&V> {
        match self {
            FileAction::Close { fd }
            | FileAction::Open { fd, .. }
            | FileAction::Inherit { fd }
            | FileAction::InheritIf { fd, .. }
            | FileAction::Fchdir { fd } => vec![fd],
            FileAction::Dup2 { from, to } | FileAction::PlaceStdio { from, to } => vec![from, to],
            FileAction::Chdir => Vec::new(),
        }
    }

    /// Map every operand.
    pub fn map<W>(&self, mut f: impl FnMut(&V) -> W) -> FileAction<W> {
        match self {
            FileAction::Close { fd } => FileAction::Close { fd: f(fd) },
            FileAction::Dup2 { from, to } => {
                let from = f(from);
                FileAction::Dup2 { from, to: f(to) }
            }
            FileAction::Open { fd, flags } => FileAction::Open { fd: f(fd), flags: *flags },
            FileAction::Inherit { fd } => FileAction::Inherit { fd: f(fd) },
            FileAction::InheritIf { fd, enabled } => {
                let fd = f(fd);
                FileAction::InheritIf { fd, enabled: f(enabled) }
            }
            FileAction::PlaceStdio { from, to } => {
                let from = f(from);
                FileAction::PlaceStdio { from, to: f(to) }
            }
            FileAction::Chdir => FileAction::Chdir,
            FileAction::Fchdir { fd } => FileAction::Fchdir { fd: f(fd) },
        }
    }
}

/// A platform call, made by one process.
///
/// `V` is the type of descriptor (and pid) operands: `i32` for a concrete
/// call, [`crate::script::Operand`] in a script or std summary whose operands
/// name earlier results.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Call<V = i32> {
    /// `pipe(2)`. Darwin has no `pipe2`.
    Pipe,
    /// `socketpair(2)`. Darwin has no `SOCK_CLOEXEC`.
    Socketpair { domain: i32, ty: i32, protocol: i32 },
    /// `socket(2)`. Darwin has no `SOCK_CLOEXEC`.
    Socket { domain: i32, ty: i32, protocol: i32 },
    /// A socket operation with no descriptor-table effect (`bind`, `listen`,
    /// `connect`, `shutdown`, `setsockopt`, `getsockopt`, `getsockname`,
    /// `getpeername`): `EBADF`/`ENOTSOCK` are decided here, everything else
    /// by the oracle.
    SocketOp { fd: V, op: SocketOp },
    /// `accept(2)`. Darwin has no `accept4`.
    Accept { fd: V },
    /// `open(2)` of a path that names a FRESH vnode: a regular file, a
    /// directory, or a device that does not block on open (`/dev/null`). The
    /// path itself is not modeled (the oracle decides whether it resolves);
    /// the census must classify it ([`crate::symbols::classify_open_path`]):
    /// an fdesc alias (`/dev/fd/N`, `/dev/std{in,out,err}`) is
    /// [`Call::OpenAlias`], and a FIFO (whose open blocks for a peer) is not
    /// modeled. Bits outside [`crate::darwin::OPEN_MODELED_MASK`] are
    /// refused by name. `openat` (a `dirfd`) is not this clause.
    Open { flags: i32 },
    /// `open("/dev/fd/N")` (and `/dev/stdin|stdout|stderr` = N 0|1|2):
    /// Darwin's fdesc. MEASURED: a new descriptor for the SAME open file
    /// description as `fd` (`F_SETFL` through one is seen through the other;
    /// the original's close does not end the description), `FD_CLOEXEC` set
    /// iff the source's is or `O_CLOEXEC` is asked, the requested access must
    /// be within the description's
    /// (`EACCES` otherwise), status and creation bits are ignored, a closed
    /// `fd` is `EBADF`. A kqueue's alias is refused by name: Darwin 27.2
    /// answers `EACCES` where 25.6 and 27.0 answered `EBADF`
    /// ([`crate::clauses::KQUEUE_ALIAS`]).
    OpenAlias { fd: V, flags: i32 },
    /// `kqueue(2)`.
    Kqueue,
    /// `fcntl(2)`, split by command; only F_DUPFD, F_DUPFD_CLOEXEC, F_GETFD,
    /// F_SETFD, F_GETFL and F_SETFL are executed, every other command is
    /// refused by name.
    Fcntl { fd: V, cmd: i32, arg: i64 },
    /// `dup(2)`.
    Dup { fd: V },
    /// `dup2(2)`.
    Dup2 { from: V, to: V },
    /// Trust std's do_exec stdio placement: clear CLOEXEC on a same-number
    /// source, otherwise dup2. A modeled std composition, not a raw syscall.
    StdPlaceFd { from: V, to: V },
    /// Trust std's clear_cloexec, retaining every other descriptor flag.
    StdClearCloexec { fd: V },
    /// Capture std's passes_exec predicate as Int(0/1), including closed fds.
    StdPassesExec { fd: V },
    /// Trust std's child-only SP1 strip: mark every live fd >= 3 CLOEXEC.
    /// Only a single-threaded caller is modeled; no descriptor is closed.
    StdMarkCloexec,
    /// Move a pre_exec status writer above the conventional slots, retaining
    /// its original number when it is already high or duplication fails.
    StdStatusFd { fd: V },
    /// Drop the old status writer only when relocation succeeded. A
    /// separate event retains the parent's dup-then-close copy window.
    StdCloseMovedStatus { old: V, new: V },
    /// `close(2)` (and `close$NOCANCEL`).
    Close { fd: V },
    /// `ioctl(2)`: FIOCLEX, FIONCLEX and FIONBIO (`arg` is the `int` it
    /// points at); every other request is refused by name.
    Ioctl { fd: V, request: u64, arg: i32 },
    /// `fork(2)`.
    Fork,
    /// `execve(2)` / `execv` / `execvp` (the image is not modeled; the oracle
    /// decides success).
    Exec,
    /// `posix_spawn(2)` / `posix_spawnp`.
    Spawn { actions: Vec<FileAction<V>>, flags: i32 },
    /// `getrlimit(2)`.
    Getrlimit { resource: i32 },
    /// `setrlimit(2)`.
    Setrlimit { resource: i32, soft: u64, hard: u64 },
    /// `proc_pidinfo(getpid(), PROC_PIDLISTFDS, _, buf, bytes)` with a
    /// non-NULL `buf` of at least `bytes` bytes: the caller's own descriptor
    /// listing ([`crate::introspect::listing`], [`Semantics::listing`]);
    /// `Ret::Int` is the byte count written (8 per entry). Changes nothing.
    /// The census emits it only when the pid operand is `getpid()`'s result;
    /// another pid, a NULL buffer (a size query) or another flavor is
    /// refused.
    ListOwnFds { bytes: i32 },
    /// `sysctlbyname(name, old, &oldlen, NULL, 0)` with a non-NULL `old` of
    /// `oldlen` bytes: a read of one integer sysctl; `Ret::Int` is the value
    /// written to `*old` (and `*oldlen` becomes 4). Only
    /// `kern.maxfilesperproc` is modeled ([`crate::introspect`]); a write
    /// (`new` non-NULL) is refused by the census. Changes nothing.
    Sysctl { name: String, oldlen: u64 },
    /// `_exit(2)` / `exit(3)` / death by a fatal signal.
    Exit { status: i32 },
    /// `waitpid(2)`: `pid > 0` one child, `pid == -1` any child; `options`
    /// is 0 or `WNOHANG` (anything else, and process-group waits, are
    /// refused by name).
    Waitpid { pid: V, options: i32 },
    /// `pthread_create(3)`.
    ThreadCreate,
    /// A `read(2)` on a pipe or socketpair end whose data the model
    /// abstracts to "some bytes are pending" (std's spawn status pipe).
    /// Returns `Int(1)` ("n >= 1 bytes", consuming them) when the peer wrote
    /// ([`Call::WriteSome`]), `Int(0)` (end-of-file) when nothing is pending
    /// and the peer description is gone, and is not enabled
    /// ([`Refusal::Blocks`]) otherwise. Byte counts and contents are not
    /// modeled: `read` in general is NOT this clause (it stays an unmodeled
    /// platform effect until M2).
    ReadSome { fd: V },
    /// A `write(2)` of a small (`<= PIPE_BUF`), nonzero byte count to a pipe
    /// write end or a connected socket: marks the peer description's data
    /// pending (std's child reporting an exec error on the status pipe).
    WriteSome { fd: V },
    /// `flock(2)`: `op` is `LOCK_SH`/`LOCK_EX`/`LOCK_UN`, optionally `|
    /// LOCK_NB`. The lock lives on the open file DESCRIPTION
    /// ([`crate::Ofd::lock`]); see [`crate::clauses`] for the measured rules.
    Flock { fd: V, op: i32 },
    /// `open(2)` (`at: None`) or `openat(2)` (`at: Some(dirfd)`) of a path
    /// the model's flat namespace resolves ([`crate::Host::name`]): a
    /// regular file, a directory, a character device, a FIFO, through
    /// symlinks. Two opens of one name reach one node — what `flock`
    /// conflicts and `fstat` identity are computed over. Bits outside
    /// [`crate::darwin::OPEN_NAMED_MODELED_MASK`] are refused by name; an fdesc
    /// path (`/dev/fd/N`) is [`Call::OpenAlias`], not this.
    OpenPath { at: Option<V>, path: String, flags: i32 },
    /// `fstat(2)`: the identity (`dev`, `ino`) and file type of the node the
    /// descriptor's description is open on ([`Ret::Stat`]).
    Fstat { fd: V },
    /// `mkfifo(3)`: a named pipe at `path`.
    Mkfifo { path: String },
    /// `unlink(2)`: remove `path`'s name (the node lives on while open).
    Unlink { path: String },
    /// `symlink(2)`: a link at `path` to `target`.
    Symlink { target: String, path: String },
    /// `posix_spawn(2)`'s FIRST half (M2 review, MEASURED Darwin 25.6): the
    /// new process exists, holding a copy of the caller's WHOLE table —
    /// `FD_CLOEXEC` entries included, kqueues excluded — while its file
    /// actions run and its image is activated; the caller's other threads act
    /// meanwhile (a close-on-exec lock the parent's last close "released"
    /// stays held for tens of microseconds). The result is the in-progress
    /// child's pid ([`crate::Phase::Spawning`]); the caller's call has not
    /// returned until [`Call::SpawnEnd`]. [`Call::Spawn`] is the two halves
    /// with nothing between them.
    SpawnBegin,
    /// `posix_spawn(2)`'s SECOND half, by the caller: the file actions run in
    /// `child` (the process [`Call::SpawnBegin`] created), then the image:
    /// on success the close-on-exec sweep (and `CLOEXEC_DEFAULT`'s) and the
    /// child's pid; on failure (an action's errno or the oracle's) the child
    /// is torn down — its copies dropped — and the spawn returns the errno.
    SpawnEnd { child: V, actions: Vec<FileAction<V>>, flags: i32 },
    /// Continue a call that has not returned ([`Ret::Pending`]): an `open`
    /// that waits (a FIFO's peer, an `O_EXLOCK`/`O_SHLOCK` lock, or the lock
    /// of an open that has just created its file) or a `flock` that sleeps,
    /// holding descriptor number `fd` ([`crate::InFlight`]). Not enabled
    /// ([`Refusal::Blocks`]) while it still waits; the oracle may interrupt a
    /// wait with `EINTR`.
    Resume { fd: V },
    /// Trust std's descriptor strip in a forked child (`FdStrip::apply`,
    /// `library/std/src/sys/process/unix/inherit.rs`; DECISION_QUEUE SP-1):
    /// `proc_pidinfo(PROC_PIDLISTFDS)` of the caller's own table, then
    /// `fcntl(F_GETFD)` and, where `FD_CLOEXEC` is clear, `fcntl(F_SETFD,
    /// flags | FD_CLOEXEC)` on every listed descriptor from `first` up. ONE
    /// event: the table is a single-threaded process's own, which nothing
    /// else changes meanwhile, so a caller with another thread is refused by
    /// name. Never closes anything; `Int(0)`.
    CloexecFrom { first: i32 },
}

/// The socket operations [`Call::SocketOp`] covers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SocketOp {
    Bind,
    Listen,
    Connect,
    Shutdown,
    Setsockopt,
    Getsockopt,
    Getsockname,
    Getpeername,
}

impl<V> Call<V> {
    /// The libc symbol (or family) this call stands for.
    #[must_use]
    pub fn symbol(&self) -> &'static str {
        match self {
            Call::Pipe => "pipe",
            Call::Socketpair { .. } => "socketpair",
            Call::Socket { .. } => "socket",
            Call::SocketOp { op, .. } => match op {
                SocketOp::Bind => "bind",
                SocketOp::Listen => "listen",
                SocketOp::Connect => "connect",
                SocketOp::Shutdown => "shutdown",
                SocketOp::Setsockopt => "setsockopt",
                SocketOp::Getsockopt => "getsockopt",
                SocketOp::Getsockname => "getsockname",
                SocketOp::Getpeername => "getpeername",
            },
            Call::Accept { .. } => "accept",
            Call::Open { .. } | Call::OpenAlias { .. } => "open",
            Call::Kqueue => "kqueue",
            Call::Fcntl { .. } => "fcntl",
            Call::Dup { .. } => "dup",
            Call::Dup2 { .. } => "dup2",
            Call::StdPlaceFd { .. } => "std::process::place_stdio",
            Call::StdClearCloexec { .. } => "std::process::clear_cloexec",
            Call::StdPassesExec { .. } => "std::process::passes_exec",
            Call::StdMarkCloexec => "std::process::mark_cloexec",
            Call::StdStatusFd { .. } => "std::process::status_fd",
            Call::StdCloseMovedStatus { .. } => "std::process::close_moved_status",
            Call::Close { .. } => "close",
            Call::Ioctl { .. } => "ioctl",
            Call::Fork => "fork",
            Call::Exec => "execve",
            Call::Spawn { .. } => "posix_spawn",
            Call::Getrlimit { .. } => "getrlimit",
            Call::Setrlimit { .. } => "setrlimit",
            Call::ListOwnFds { .. } => "proc_pidinfo",
            Call::Sysctl { .. } => "sysctlbyname",
            Call::Exit { .. } => "_exit",
            Call::Waitpid { .. } => "waitpid",
            Call::ThreadCreate => "pthread_create",
            Call::ReadSome { .. } => "read",
            Call::WriteSome { .. } => "write",
            Call::Flock { .. } => "flock",
            Call::OpenPath { at: None, .. } => "open",
            Call::OpenPath { at: Some(_), .. } => "openat",
            Call::Fstat { .. } => "fstat",
            Call::Mkfifo { .. } => "mkfifo",
            Call::Unlink { .. } => "unlink",
            Call::Symlink { .. } => "symlink",
            Call::SpawnBegin | Call::SpawnEnd { .. } => "posix_spawn",
            Call::Resume { .. } => "resume",
            Call::CloexecFrom { .. } => "fcntl",
        }
    }

    /// Map every operand.
    pub fn map<W>(&self, mut f: impl FnMut(&V) -> W) -> Call<W> {
        match self {
            Call::Pipe => Call::Pipe,
            Call::Socketpair { domain, ty, protocol } => {
                Call::Socketpair { domain: *domain, ty: *ty, protocol: *protocol }
            }
            Call::Socket { domain, ty, protocol } => {
                Call::Socket { domain: *domain, ty: *ty, protocol: *protocol }
            }
            Call::SocketOp { fd, op } => Call::SocketOp { fd: f(fd), op: *op },
            Call::Accept { fd } => Call::Accept { fd: f(fd) },
            Call::Open { flags } => Call::Open { flags: *flags },
            Call::OpenAlias { fd, flags } => Call::OpenAlias { fd: f(fd), flags: *flags },
            Call::Kqueue => Call::Kqueue,
            Call::Fcntl { fd, cmd, arg } => Call::Fcntl { fd: f(fd), cmd: *cmd, arg: *arg },
            Call::Dup { fd } => Call::Dup { fd: f(fd) },
            Call::Dup2 { from, to } => {
                let from = f(from);
                Call::Dup2 { from, to: f(to) }
            }
            Call::StdPlaceFd { from, to } => {
                let from = f(from);
                Call::StdPlaceFd { from, to: f(to) }
            }
            Call::StdClearCloexec { fd } => Call::StdClearCloexec { fd: f(fd) },
            Call::StdPassesExec { fd } => Call::StdPassesExec { fd: f(fd) },
            Call::StdMarkCloexec => Call::StdMarkCloexec,
            Call::StdStatusFd { fd } => Call::StdStatusFd { fd: f(fd) },
            Call::StdCloseMovedStatus { old, new } => {
                let old = f(old);
                Call::StdCloseMovedStatus { old, new: f(new) }
            }
            Call::Close { fd } => Call::Close { fd: f(fd) },
            Call::Ioctl { fd, request, arg } => {
                Call::Ioctl { fd: f(fd), request: *request, arg: *arg }
            }
            Call::Fork => Call::Fork,
            Call::Exec => Call::Exec,
            Call::Spawn { actions, flags } => Call::Spawn {
                actions: actions.iter().map(|a| a.map(&mut f)).collect(),
                flags: *flags,
            },
            Call::Getrlimit { resource } => Call::Getrlimit { resource: *resource },
            Call::Setrlimit { resource, soft, hard } => {
                Call::Setrlimit { resource: *resource, soft: *soft, hard: *hard }
            }
            Call::ListOwnFds { bytes } => Call::ListOwnFds { bytes: *bytes },
            Call::Sysctl { name, oldlen } => Call::Sysctl { name: name.clone(), oldlen: *oldlen },
            Call::Exit { status } => Call::Exit { status: *status },
            Call::Waitpid { pid, options } => Call::Waitpid { pid: f(pid), options: *options },
            Call::ThreadCreate => Call::ThreadCreate,
            Call::ReadSome { fd } => Call::ReadSome { fd: f(fd) },
            Call::WriteSome { fd } => Call::WriteSome { fd: f(fd) },
            Call::Flock { fd, op } => Call::Flock { fd: f(fd), op: *op },
            Call::OpenPath { at, path, flags } => {
                Call::OpenPath { at: at.as_ref().map(&mut f), path: path.clone(), flags: *flags }
            }
            Call::Fstat { fd } => Call::Fstat { fd: f(fd) },
            Call::Mkfifo { path } => Call::Mkfifo { path: path.clone() },
            Call::Unlink { path } => Call::Unlink { path: path.clone() },
            Call::Symlink { target, path } => {
                Call::Symlink { target: target.clone(), path: path.clone() }
            }
            Call::SpawnBegin => Call::SpawnBegin,
            Call::SpawnEnd { child, actions, flags } => Call::SpawnEnd {
                child: f(child),
                actions: actions.iter().map(|a| a.map(&mut f)).collect(),
                flags: *flags,
            },
            Call::Resume { fd } => Call::Resume { fd: f(fd) },
            Call::CloexecFrom { first } => Call::CloexecFrom { first: *first },
        }
    }
}

/// A successful return.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Ret {
    /// An `int`-returning call: a descriptor, a flag word, a pid, or 0.
    Int(i64),
    /// `pipe` / `socketpair`: the two new descriptors.
    Pair(i32, i32),
    /// `getrlimit`.
    Rlimit { soft: u64, hard: u64 },
    /// `fstat`: the node's identity (the model's [`crate::NodeId`], standing for
    /// `dev`, `ino`: equal exactly when the nodes are one) and its file type
    /// (`st_mode & S_IFMT`).
    Stat { node: u64, ftype: i32 },
    /// `execve` (success) and `_exit` do not return.
    NoReturn,
    /// The call has NOT returned: it waits holding descriptor number `fd`
    /// (an `open` that reserved `fd`, a `flock` that sleeps on `fd`); the
    /// process's [`crate::Proc::inflight`] names it, and the caller continues
    /// with [`Call::Resume`].
    Pending { fd: i32 },
}

impl Ret {
    /// Component `i` as an `i32` operand (`Int` is component 0; `Pair` has 0
    /// and 1; a `Pending` call's component 0 is the number it holds).
    #[must_use]
    pub fn component(&self, i: u8) -> Option<i32> {
        match (self, i) {
            (Ret::Int(v), 0) => i32::try_from(*v).ok(),
            (Ret::Pending { fd }, 0) => Some(*fd),
            (Ret::Pair(a, _), 0) => Some(*a),
            (Ret::Pair(_, b), 1) => Some(*b),
            _ => None,
        }
    }
}

/// What the call returned: a value, or `-1` with this `errno`.
pub type SysResult = Result<Ret, Errno>;

/// The environment's resolution of a call's nondeterminism.
///
/// Everything the model can decide from the host state (EBADF, EMFILE,
/// EINVAL, lowest-free numbering, …) it decides; what depends on the world
/// outside the descriptor model (does the path exist? is a connection
/// pending? is the system file table full?) is an explicit choice here. A
/// choice outside [`crate::clauses::admissible_failures`] is refused, so an
/// oracle can never invent a behaviour the clause does not allow.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Oracle {
    /// The world cooperates: the path exists, the image execs, a connection
    /// is pending, the system tables have room.
    Nominal,
    /// The world refuses with this errno (no descriptor-table effect).
    Fail(Errno),
}

/// The model declines to say what happens.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Refusal {
    /// The platform behaviour is not modeled: an unmodeled `fcntl` command or
    /// `ioctl` request, a socket domain/type the model does not cover, a
    /// spawn flag with a descriptor effect the model does not know. NEVER a
    /// silent no-op: a caller must surface it (I-FD-SPECIFIED).
    Unmodeled { symbol: &'static str, detail: String },
    /// No such process in the host.
    NoSuchProcess(Pid),
    /// The process cannot act (it has exited).
    NotLive(Pid),
    /// The call does not complete in this state (`waitpid` on a live child,
    /// a read with nothing pending and the peer still open); the step is not
    /// enabled.
    Blocks,
    /// The oracle chose a failure this clause does not admit.
    InadmissibleOracle { symbol: &'static str, oracle: Oracle },
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Refusal::Unmodeled { symbol, detail } => {
                write!(f, "unmodeled platform effect: {symbol} {detail}")
            }
            Refusal::NoSuchProcess(p) => write!(f, "no such process {p:?}"),
            Refusal::NotLive(p) => write!(f, "process {p:?} has exited"),
            Refusal::Blocks => write!(f, "call blocks in this state"),
            Refusal::InadmissibleOracle { symbol, oracle } => {
                write!(f, "oracle {oracle:?} is not admissible for {symbol}")
            }
        }
    }
}

/// The outcome of one platform event.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub host: Host,
    pub result: SysResult,
}

/// A platform semantics: the one function every consumer evaluates.
///
/// [`crate::Darwin`] is THE definition; the trait exists so the conformance
/// suite can run deliberately wrong variants (spec mutants) through the same
/// probes and show each one is caught.
pub trait Semantics {
    /// The primitive platform clause hook. Std compositions dispatch their
    /// constituent calls through `step`, retaining the selected semantics.
    fn step_raw(&self, host: &Host, pid: Pid, call: &Call, oracle: Oracle)
    -> Result<Step, Refusal>;

    fn step(&self, host: &Host, pid: Pid, call: &Call, oracle: Oracle) -> Result<Step, Refusal> {
        crate::std_execution::step(self, host, pid, call, oracle)
    }

    /// The entries a successful [`Call::ListOwnFds`] by `pid` writes into its
    /// buffer, read from `host` BEFORE the call (the step's result is only
    /// their byte count). [`crate::Darwin`]'s answer is
    /// [`crate::introspect::listing`]; the conformance suite compares it with
    /// the kernel's listing entry by entry, so a spec mutant overrides it.
    fn listing(
        &self,
        host: &Host,
        pid: Pid,
        bytes: i32,
    ) -> Result<Result<Vec<ListedFd>, Errno>, Refusal> {
        crate::introspect::listing(host, pid, bytes)
    }
}
