//! The Darwin clauses: one pure function per platform call,
//! `Host × args × oracle → Host × result`.
//!
//! Every behaviour below that a conformance probe exercises is compared with
//! the real kernel on every run of `tests/conformance_darwin.rs`. The
//! behaviours that CONTRADICT the M1 plan's sketch, or that the plan marked
//! as recollection (\[K\]), were measured on Darwin 25.6 (2026-09-30) and are
//! marked MEASURED where they are implemented.

use std::collections::{BTreeMap, BTreeSet};

use crate::call::{Call, FileAction, Oracle, Refusal, Ret, Semantics, SocketOp, Step, SysResult};
use crate::darwin::{self, Errno};
use crate::host::{
    Access, Entry, Host, InFlight, LockMode, Node, NodeId, NodeKind, Ofd, OfdId, OfdKind, Peer,
    Phase, Pid, Proc, Rlimit,
};

/// The Darwin platform semantics: the single definition.
#[derive(Clone, Copy, Debug, Default)]
pub struct Darwin;

impl Semantics for Darwin {
    fn step_raw(
        &self,
        host: &Host,
        pid: Pid,
        call: &Call,
        oracle: Oracle,
    ) -> Result<Step, Refusal> {
        primitive_step_torn(host, pid, call, oracle, &BTreeSet::new())
    }
}

/// Which environment failures an [`Oracle::Fail`] may choose for a call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Admits {
    /// None: the call is fully determined by the host state.
    Nothing,
    /// Exactly these errnos.
    Only(&'static [Errno]),
    /// Any errno other than the ones the model decides itself (`SocketOp`:
    /// the network namespace is outside the model).
    AnyExcept(&'static [Errno]),
}

impl Admits {
    #[must_use]
    pub fn admits(self, e: Errno) -> bool {
        match self {
            Admits::Nothing => false,
            Admits::Only(set) => set.contains(&e),
            Admits::AnyExcept(set) => !set.contains(&e),
        }
    }
}

const PATH_ERRNOS: &[Errno] = &[
    Errno::ENOENT,
    Errno::EACCES,
    Errno::EEXIST,
    Errno::ENOTDIR,
    Errno::EISDIR,
    Errno::ELOOP,
    Errno::ENAMETOOLONG,
    Errno::ENXIO,
    Errno::EROFS,
    Errno::EPERM,
    Errno::ETXTBSY,
    Errno::EINTR,
    Errno::EIO,
    Errno::EAGAIN,
    Errno::ENFILE,
];

/// The environment failures of an open the namespace resolves
/// ([`Call::OpenPath`]): permissions, the file system, signals, the system
/// table. NOT `ENOENT`, `EEXIST`, `ELOOP`, `ENXIO`, `EISDIR`, `ENOTDIR`,
/// `ENOTSUP` or `EAGAIN`: the namespace and the node decide those.
const NAMED_OPEN_ERRNOS: &[Errno] = &[
    Errno::EACCES,
    Errno::EINTR,
    Errno::EIO,
    Errno::ENFILE,
    Errno::ENAMETOOLONG,
    Errno::ENOSPC,
    Errno::EPERM,
    Errno::EROFS,
    Errno::ETXTBSY,
];

/// The environment failures of a namespace edit (`mkfifo`, `unlink`,
/// `symlink`); `EEXIST`/`ENOENT` are the namespace's.
const NAME_EDIT_ERRNOS: &[Errno] = &[
    Errno::EACCES,
    Errno::EBUSY,
    Errno::EIO,
    Errno::ENAMETOOLONG,
    Errno::ENOSPC,
    Errno::EPERM,
    Errno::EROFS,
];

const EXEC_ERRNOS: &[Errno] = &[
    Errno::E2BIG,
    Errno::EACCES,
    Errno::EFAULT,
    Errno::EIO,
    Errno::ELOOP,
    Errno::ENAMETOOLONG,
    Errno::ENOENT,
    Errno::ENOEXEC,
    Errno::ENOMEM,
    Errno::ENOTDIR,
    Errno::ETXTBSY,
    Errno::EPERM,
    Errno::EBADARCH,
    Errno::EBADEXEC,
    Errno::EBADMACHO,
];

const SPAWN_ERRNOS: &[Errno] = &[
    // exec stage
    Errno::E2BIG,
    Errno::EACCES,
    Errno::EFAULT,
    Errno::EIO,
    Errno::ELOOP,
    Errno::ENAMETOOLONG,
    Errno::ENOENT,
    Errno::ENOEXEC,
    Errno::ENOMEM,
    Errno::ENOTDIR,
    Errno::ETXTBSY,
    Errno::EPERM,
    Errno::EBADARCH,
    Errno::EBADEXEC,
    Errno::EBADMACHO,
    // process creation, addopen path resolution
    Errno::EAGAIN,
    Errno::EEXIST,
    Errno::EISDIR,
    Errno::ENXIO,
    Errno::EROFS,
    Errno::EINTR,
    Errno::ENFILE,
];

/// The failures the environment may choose for `call` ([`Oracle::Fail`]).
#[must_use]
pub fn admissible_failures<V>(call: &Call<V>) -> Admits {
    match call {
        Call::Pipe => Admits::Only(&[Errno::ENFILE]),
        // Reads of this process's own state (X3a, `crate::introspect`).
        Call::ListOwnFds { .. }
        | Call::Sysctl { .. }
        | Call::StdPlaceFd { .. }
        | Call::StdClearCloexec { .. }
        | Call::StdPassesExec { .. }
        | Call::StdMarkCloexec
        | Call::StdStatusFd { .. }
        | Call::StdCloseMovedStatus { .. } => Admits::Nothing,
        // The explicit strip clause ignores per-descriptor errors.
        Call::CloexecFrom { .. } => Admits::Nothing,
        Call::Socketpair { .. } | Call::Socket { .. } => {
            Admits::Only(&[Errno::ENFILE, Errno::ENOBUFS, Errno::ENOMEM, Errno::EACCES])
        }
        Call::SocketOp { .. } => Admits::AnyExcept(&[Errno::EBADF, Errno::ENOTSOCK]),
        // EINVAL (not listening) and EOPNOTSUPP (a datagram socket) are the
        // model's to decide, from the description.
        Call::Accept { .. } => Admits::Only(&[
            Errno::EAGAIN,
            Errno::ECONNABORTED,
            Errno::EINTR,
            Errno::ENFILE,
            Errno::ENOMEM,
            Errno::ENOBUFS,
        ]),
        Call::Open { .. } => Admits::Only(PATH_ERRNOS),
        Call::OpenPath { .. } => Admits::Only(NAMED_OPEN_ERRNOS),
        Call::Mkfifo { .. } | Call::Unlink { .. } | Call::Symlink { .. } => {
            Admits::Only(NAME_EDIT_ERRNOS)
        }
        Call::Kqueue => Admits::Only(&[Errno::ENFILE, Errno::ENOMEM]),
        Call::Fork => Admits::Only(&[Errno::EAGAIN, Errno::ENOMEM]),
        Call::Exec => Admits::Only(EXEC_ERRNOS),
        Call::Spawn { .. } | Call::SpawnEnd { .. } => Admits::Only(SPAWN_ERRNOS),
        // fork1's failure: no process, no copy; the spawn returns at once.
        Call::SpawnBegin => Admits::Only(&[Errno::EAGAIN, Errno::ENOMEM]),
        // A waiting call interrupted by a signal whose handler was installed
        // without SA_RESTART (MEASURED for flock, the M2 model review's p7).
        Call::Resume { .. } => Admits::Only(&[Errno::EINTR]),
        Call::ThreadCreate => Admits::Only(&[Errno::EAGAIN, Errno::ENOMEM]),
        Call::Fcntl { .. }
        | Call::Dup { .. }
        | Call::Dup2 { .. }
        | Call::Close { .. }
        | Call::Ioctl { .. }
        | Call::Getrlimit { .. }
        | Call::Setrlimit { .. }
        | Call::Exit { .. }
        | Call::Waitpid { .. }
        | Call::OpenAlias { .. }
        | Call::ReadSome { .. }
        | Call::WriteSome { .. }
        | Call::Flock { .. }
        | Call::Fstat { .. } => Admits::Nothing,
    }
}

/// Every oracle choice admissible for `call`, for an exploration that must
/// cover them all (`AnyExcept` is enumerated as one representative failure).
#[must_use]
pub fn oracle_space<V>(call: &Call<V>) -> Vec<Oracle> {
    let mut out = vec![Oracle::Nominal];
    match admissible_failures(call) {
        Admits::Nothing => {}
        Admits::Only(set) => out.extend(set.iter().map(|e| Oracle::Fail(*e))),
        Admits::AnyExcept(_) => out.push(Oracle::Fail(Errno::EINVAL)),
    }
    out
}

/// libc's add-time validation of a `posix_spawn_file_actions_add*` call.
/// MEASURED (Darwin 25.6): every descriptor operand must be in
/// `[0, OPEN_MAX)` (`OPEN_MAX` = 10240), else the add fails `EBADF` and the
/// action is NOT recorded — although the kernel allocates descriptors up to
/// `kern.maxfilesperproc`. The spawn clause refuses an action list that
/// holds an action this check rejects: such an action cannot have been
/// added, and whether the program then spawns without it is a property of
/// its return-code handling, which the action list does not record.
pub fn file_action_add(action: &FileAction) -> Result<(), Errno> {
    if matches!(action, FileAction::InheritIf { enabled, .. } if *enabled != 0 && *enabled != 1) {
        return Err(Errno::EINVAL);
    }
    if matches!(action, FileAction::InheritIf { enabled: 0, .. }) {
        return Ok(());
    }
    if action.fds().into_iter().any(|fd| *fd < 0 || *fd >= darwin::OPEN_MAX) {
        return Err(Errno::EBADF);
    }
    Ok(())
}

/// Apply `call`, made by `pid`, under `oracle`. THE Darwin clause set.
pub fn step(host: &Host, pid: Pid, call: &Call, oracle: Oracle) -> Result<Step, Refusal> {
    Darwin.step(host, pid, call, oracle)
}

/// [`step`] for a `fork` or `posix_spawn` whose descriptor-table copy MISSED
/// the slots in `missed` (each must be open in the caller's table).
///
/// MEASURED (Darwin 25.6, the adversarial review's probes p7/p8): XNU copies
/// a table without a snapshot of it. A slot a concurrent `dup2` is replacing
/// is reserved — absent — while it is replaced (2985 of 20000 `fork`
/// children and 859 of 5000 `posix_spawn` children lacked an always-open fd
/// 50 that another thread kept `dup2`-ing onto); a description another
/// thread moves (`F_DUPFD` above the table end read at the start of the
/// copy, then `close` of the old slot) can land in neither slot (1406 of
/// 20000). The child's table is therefore a SUBSET of an atomic snapshot,
/// never more: an empty `missed` is the atomic copy. Which slots a racing
/// thread can make the copy miss is the caller's to say (it knows the other
/// threads' pending events); this clause only executes the outcome.
pub fn step_torn(
    host: &Host,
    pid: Pid,
    call: &Call,
    oracle: Oracle,
    missed: &BTreeSet<i32>,
) -> Result<Step, Refusal> {
    if missed.is_empty() && crate::std_execution::is_composite(call) {
        return Darwin.step(host, pid, call, oracle);
    }
    let expanded = match call {
        Call::Spawn { actions, flags } => {
            Call::Spawn { actions: crate::std_execution::actions(actions)?, flags: *flags }
        }
        Call::SpawnEnd { child, actions, flags } => Call::SpawnEnd {
            child: *child,
            actions: crate::std_execution::actions(actions)?,
            flags: *flags,
        },
        _ => call.clone(),
    };
    primitive_step_torn(host, pid, &expanded, oracle, missed)
}

fn primitive_step_torn(
    host: &Host,
    pid: Pid,
    call: &Call,
    oracle: Oracle,
    missed: &BTreeSet<i32>,
) -> Result<Step, Refusal> {
    let proc = host.proc(pid).ok_or(Refusal::NoSuchProcess(pid))?;
    if !proc.is_live() {
        return Err(Refusal::NotLive(pid));
    }
    if let Oracle::Fail(e) = oracle
        && !admissible_failures(call).admits(e)
    {
        return Err(Refusal::InadmissibleOracle { symbol: call.symbol(), oracle });
    }
    if !missed.is_empty() {
        if !matches!(call, Call::Fork | Call::Spawn { .. } | Call::SpawnBegin) {
            return Err(Refusal::Unmodeled {
                symbol: call.symbol(),
                detail: "a torn table copy applies only to fork and posix_spawn".to_string(),
            });
        }
        if let Some(fd) = missed.iter().find(|fd| !proc.table.contains_key(fd)) {
            return Err(Refusal::Unmodeled {
                symbol: call.symbol(),
                detail: format!("a torn copy cannot miss fd {fd}: it is not open"),
            });
        }
    }
    let mut h = host.clone();
    let result = match call {
        Call::StdPlaceFd { .. }
        | Call::StdClearCloexec { .. }
        | Call::StdPassesExec { .. }
        | Call::StdMarkCloexec
        | Call::StdStatusFd { .. }
        | Call::StdCloseMovedStatus { .. } => {
            return Err(Refusal::Unmodeled {
                symbol: call.symbol(),
                detail: "a std composition must use the shared semantics executor".to_string(),
            });
        }
        Call::Pipe => pipe(&mut h, pid, oracle),
        Call::Socketpair { domain, ty, protocol } => {
            socketpair(&mut h, pid, *domain, *ty, *protocol, oracle)?
        }
        Call::Socket { domain, ty, protocol } => {
            socket(&mut h, pid, *domain, *ty, *protocol, oracle)?
        }
        Call::SocketOp { fd, op } => socket_op(&mut h, pid, *fd, *op, oracle)?,
        Call::Accept { fd } => accept(&mut h, pid, *fd, oracle)?,
        Call::Open { flags } => open(&mut h, pid, *flags, oracle)?,
        Call::OpenAlias { fd, flags } => open_alias(&mut h, pid, *fd, *flags)?,
        Call::Kqueue => kqueue(&mut h, pid, oracle),
        Call::Fcntl { fd, cmd, arg } => fcntl(&mut h, pid, *fd, *cmd, *arg)?,
        Call::Dup { fd } => dup(&mut h, pid, *fd),
        Call::Dup2 { from, to } => dup2(&mut h, pid, *from, *to)?,
        Call::Close { fd } => close(&mut h, pid, *fd)?,
        Call::Ioctl { fd, request, arg } => ioctl(&mut h, pid, *fd, *request, *arg)?,
        Call::Fork => fork(&mut h, pid, oracle, missed),
        Call::Exec => exec(&mut h, pid, oracle),
        Call::Spawn { actions, flags } => spawn(&mut h, pid, actions, *flags, oracle, missed)?,
        Call::Getrlimit { resource } => getrlimit(&h, pid, *resource)?,
        Call::ListOwnFds { bytes } => crate::introspect::list_own_fds(&h, pid, *bytes)?,
        Call::Sysctl { name, oldlen } => crate::introspect::sysctl(&h, name, *oldlen)?,
        Call::Setrlimit { resource, soft, hard } => {
            setrlimit(&mut h, pid, *resource, *soft, *hard)?
        }
        Call::Exit { status } => exit(&mut h, pid, *status),
        Call::Waitpid { pid: child, options } => waitpid(&mut h, pid, *child, *options)?,
        Call::ThreadCreate => thread_create(&mut h, pid, oracle),
        Call::ReadSome { fd } => read_some(&mut h, pid, *fd)?,
        Call::WriteSome { fd } => write_some(&mut h, pid, *fd)?,
        Call::Flock { fd, op } => flock(&mut h, pid, *fd, *op)?,
        Call::OpenPath { at, path, flags } => open_path(&mut h, pid, *at, path, *flags, oracle)?,
        Call::Fstat { fd } => fstat(&h, pid, *fd)?,
        Call::Mkfifo { path } => mkfifo(&mut h, path, oracle)?,
        Call::Unlink { path } => unlink(&mut h, path, oracle)?,
        Call::Symlink { target, path } => symlink(&mut h, target, path, oracle)?,
        Call::SpawnBegin => spawn_begin(&mut h, pid, oracle, missed),
        Call::SpawnEnd { child, actions, flags } => {
            let child = Pid(u32::try_from(*child).map_err(|_| Refusal::Unmodeled {
                symbol: "posix_spawn",
                detail: format!("child pid {child}"),
            })?);
            spawn_end(&mut h, pid, child, actions, *flags, oracle)?
        }
        Call::Resume { fd } => resume(&mut h, pid, *fd, oracle)?,
        Call::CloexecFrom { first } => cloexec_from(&mut h, pid, *first)?,
    };
    Ok(Step { host: h, result })
}

// ---- helpers ------------------------------------------------------------------

fn entry(h: &Host, pid: Pid, fd: i32) -> Result<Entry, Errno> {
    if fd < 0 {
        return Err(Errno::EBADF);
    }
    h.entry(pid, fd).ok_or(Errno::EBADF)
}

fn table_mut(h: &mut Host, pid: Pid) -> &mut BTreeMap<i32, Entry> {
    // The caller was checked live at the top of `step`, and no clause
    // removes the caller before using this.
    &mut h.proc_mut(pid).expect("caller exists").table
}

fn fail_or<T>(oracle: Oracle, ok: impl FnOnce() -> T) -> Result<T, Errno> {
    match oracle {
        Oracle::Nominal => Ok(ok()),
        Oracle::Fail(e) => Err(e),
    }
}

/// Allocate two fresh descriptors at the two lowest free numbers, or EMFILE
/// with no change (MEASURED: with exactly one free slot, `pipe` and
/// `socketpair` fail EMFILE and the slot stays free).
fn two_lowest(h: &Host, pid: Pid) -> Result<(i32, i32), Errno> {
    let a = h.lowest_free(pid, 0).ok_or(Errno::EMFILE)?;
    let proc = h.proc(pid).ok_or(Errno::EMFILE)?;
    let limit = h.alloc_limit(pid);
    let mut b = a + 1;
    loop {
        if i64::from(b) >= limit {
            return Err(Errno::EMFILE);
        }
        if !proc.table.contains_key(&b) {
            return Ok((a, b));
        }
        b += 1;
    }
}

fn install(h: &mut Host, pid: Pid, fd: i32, ofd: OfdId, cloexec: bool) {
    table_mut(h, pid).insert(fd, Entry { ofd, cloexec, clofork: false });
}

// ---- creation ---------------------------------------------------------------------

/// `pipe(2)`: two fresh descriptions (read end, write end) at the two lowest
/// free numbers, both `FD_CLOEXEC` clear. Darwin has no `pipe2`.
fn pipe(h: &mut Host, pid: Pid, oracle: Oracle) -> SysResult {
    let (r, w) = two_lowest(h, pid)?;
    fail_or(oracle, || ())?;
    let ro = h.mint_ofd(Ofd::fresh(OfdKind::PipeRead, Access::ReadOnly, 0));
    let wo = h.mint_ofd(Ofd::fresh(OfdKind::PipeWrite, Access::WriteOnly, 0));
    link(h, ro, wo);
    install(h, pid, r, ro, false);
    install(h, pid, w, wo, false);
    Ok(Ret::Pair(r, w))
}

fn link(h: &mut Host, a: OfdId, b: OfdId) {
    if let Some(o) = h.ofd_mut(a) {
        o.peer = Peer::Open(b);
    }
    if let Some(o) = h.ofd_mut(b) {
        o.peer = Peer::Open(a);
    }
}

/// The domain/type/protocol check `socreate` makes, shared by `socket` and
/// `socketpair`. MEASURED: a type carrying Linux's `SOCK_CLOEXEC` bit
/// (0x80000), AF_UNIX `SOCK_SEQPACKET`, and a non-zero AF_UNIX protocol all
/// fail `EPROTONOSUPPORT`.
fn socreate_check(
    symbol: &'static str,
    domain: i32,
    ty: i32,
    protocol: i32,
) -> Result<Result<(), Errno>, Refusal> {
    let unmodeled = || Refusal::Unmodeled {
        symbol,
        detail: format!("domain={domain} type={ty:#x} protocol={protocol}"),
    };
    match domain {
        darwin::AF_UNIX => {
            if ty & darwin::LINUX_SOCK_CLOEXEC != 0 {
                return Ok(Err(Errno::EPROTONOSUPPORT));
            }
            match ty {
                darwin::SOCK_STREAM | darwin::SOCK_DGRAM => {
                    if protocol == 0 {
                        Ok(Ok(()))
                    } else {
                        Ok(Err(Errno::EPROTONOSUPPORT))
                    }
                }
                darwin::SOCK_SEQPACKET => Ok(Err(Errno::EPROTONOSUPPORT)),
                _ => Err(unmodeled()),
            }
        }
        darwin::AF_INET | darwin::AF_INET6 => match (ty, protocol) {
            (darwin::SOCK_STREAM | darwin::SOCK_DGRAM, 0) => Ok(Ok(())),
            _ => Err(unmodeled()),
        },
        _ => Err(unmodeled()),
    }
}

/// `socketpair(2)`: two connected fresh descriptions, `FD_CLOEXEC` clear on
/// both. Darwin has no `SOCK_CLOEXEC`. MEASURED order (XNU `socketpair`:
/// `socreate` x2, `falloc` x2, `soconnect2`): the type check first (an
/// AF_UNIX `SOCK_STREAM|0x80000` pair is `EPROTONOSUPPORT` even at a full
/// table), then allocation (`EMFILE`; an AF_INET pair at a full table is
/// `EMFILE`), then the connect (`socketpair(AF_INET, …)` is `EOPNOTSUPP`).
fn socketpair(
    h: &mut Host,
    pid: Pid,
    domain: i32,
    ty: i32,
    protocol: i32,
    oracle: Oracle,
) -> Result<SysResult, Refusal> {
    if let Err(e) = socreate_check("socketpair", domain, ty, protocol)? {
        return Ok(Err(e));
    }
    let (a, b) = match two_lowest(h, pid) {
        Ok(p) => p,
        Err(e) => return Ok(Err(e)),
    };
    match domain {
        darwin::AF_UNIX => {}
        darwin::AF_INET => return Ok(Err(Errno::EOPNOTSUPP)),
        _ => {
            return Err(Refusal::Unmodeled {
                symbol: "socketpair",
                detail: format!("domain={domain} type={ty:#x}"),
            });
        }
    }
    if let Oracle::Fail(e) = oracle {
        return Ok(Err(e));
    }
    let kind = OfdKind::Socket { domain, ty };
    let ao = h.mint_ofd(Ofd::fresh(kind, Access::ReadWrite, 0));
    let bo = h.mint_ofd(Ofd::fresh(kind, Access::ReadWrite, 0));
    link(h, ao, bo);
    install(h, pid, a, ao, false);
    install(h, pid, b, bo, false);
    Ok(Ok(Ret::Pair(a, b)))
}

/// `socket(2)`: one fresh description at the lowest free number,
/// `FD_CLOEXEC` clear. MEASURED order (XNU `socket`: `falloc` before
/// `socreate`): at a full table every shape — even one `socreate` rejects —
/// fails `EMFILE`.
fn socket(
    h: &mut Host,
    pid: Pid,
    domain: i32,
    ty: i32,
    protocol: i32,
    oracle: Oracle,
) -> Result<SysResult, Refusal> {
    let Some(fd) = h.lowest_free(pid, 0) else {
        return Ok(Err(Errno::EMFILE));
    };
    if let Err(e) = socreate_check("socket", domain, ty, protocol)? {
        return Ok(Err(e));
    }
    if let Oracle::Fail(e) = oracle {
        return Ok(Err(e));
    }
    let o = h.mint_ofd(Ofd::fresh(OfdKind::Socket { domain, ty }, Access::ReadWrite, 0));
    install(h, pid, fd, o, false);
    Ok(Ok(Ret::Int(i64::from(fd))))
}

/// The kind of the description `e` names, refusing a description whose kind
/// RL-INIT left unknown when the outcome depends on it.
fn known_kind(h: &Host, e: Entry, symbol: &'static str) -> Result<OfdKind, Refusal> {
    match h.ofd(e.ofd).map(|o| o.kind) {
        Some(OfdKind::Opaque) => Err(Refusal::Unmodeled {
            symbol,
            detail: "the description's kind is unknown (an environment-provided descriptor)"
                .to_string(),
        }),
        Some(k) => Ok(k),
        None => Err(Refusal::Unmodeled { symbol, detail: "dangling entry".to_string() }),
    }
}

/// A socket operation with no descriptor-table effect. `listen` on a
/// datagram socket is `EOPNOTSUPP` (XNU `solisten`: no `PR_CONNREQUIRED`);
/// a `listen` that succeeds marks the description listening, which `accept`
/// requires.
fn socket_op(
    h: &mut Host,
    pid: Pid,
    fd: i32,
    op: SocketOp,
    oracle: Oracle,
) -> Result<SysResult, Refusal> {
    let e = match entry(h, pid, fd) {
        Ok(e) => e,
        Err(err) => return Ok(Err(err)),
    };
    let kind = known_kind(h, e, op_symbol(op))?;
    let OfdKind::Socket { ty, .. } = kind else {
        return Ok(Err(Errno::ENOTSOCK));
    };
    if op == SocketOp::Listen && ty == darwin::SOCK_DGRAM {
        return Ok(Err(Errno::EOPNOTSUPP));
    }
    if let Oracle::Fail(err) = oracle {
        return Ok(Err(err));
    }
    if op == SocketOp::Listen
        && let Some(o) = h.ofd_mut(e.ofd)
    {
        o.listening = true;
    }
    Ok(Ok(Ret::Int(0)))
}

fn op_symbol(op: SocketOp) -> &'static str {
    Call::<i32>::SocketOp { fd: 0, op }.symbol()
}

/// `accept(2)`: a fresh description (of the listener's kind) at the lowest
/// free number, `FD_CLOEXEC` clear (Darwin has no `accept4`). The new
/// description inherits the listener's status flags (`O_NONBLOCK`, …) —
/// BSD behaviour, checked by the conformance suite. Its peer (the
/// connecting socket) is not tracked. MEASURED: a datagram socket is
/// `EOPNOTSUPP` and a socket that is not listening is `EINVAL`, whatever the
/// environment does.
fn accept(h: &mut Host, pid: Pid, fd: i32, oracle: Oracle) -> Result<SysResult, Refusal> {
    let e = match entry(h, pid, fd) {
        Ok(e) => e,
        Err(err) => return Ok(Err(err)),
    };
    let kind = known_kind(h, e, "accept")?;
    let listener = *h
        .ofd(e.ofd)
        .ok_or(Refusal::Unmodeled { symbol: "accept", detail: "dangling entry".to_string() })?;
    let OfdKind::Socket { ty, .. } = kind else {
        return Ok(Err(Errno::ENOTSOCK));
    };
    if ty == darwin::SOCK_DGRAM {
        return Ok(Err(Errno::EOPNOTSUPP));
    }
    if !listener.listening {
        return Ok(Err(Errno::EINVAL));
    }
    if let Oracle::Fail(err) = oracle {
        return Ok(Err(err));
    }
    let Some(new_fd) = h.lowest_free(pid, 0) else {
        return Ok(Err(Errno::EMFILE));
    };
    let o = h.mint_ofd(Ofd::fresh(listener.kind, Access::ReadWrite, listener.status));
    install(h, pid, new_fd, o, false);
    Ok(Ok(Ret::Int(i64::from(new_fd))))
}

/// The access mode of an `open`, refusing an unknown mode or any bit outside
/// [`darwin::OPEN_MODELED_MASK`] by name (`O_EXLOCK`, `O_EVTONLY`, the
/// private close-on-fork bit, …).
fn open_access(symbol: &'static str, flags: i32) -> Result<Access, Refusal> {
    if let Some(names) = darwin::unmodeled_open_bits(flags) {
        return Err(Refusal::Unmodeled { symbol, detail: format!("open flags {names}") });
    }
    Access::from_open_flags(flags).ok_or_else(|| Refusal::Unmodeled {
        symbol,
        detail: format!("access mode {:#x}", flags & darwin::O_ACCMODE),
    })
}

/// `open(2)` of a fresh vnode: allocation is decided FIRST — MEASURED: at a
/// full table even a path that does not exist fails `EMFILE`, not `ENOENT` —
/// then the oracle decides the path. `O_CLOEXEC` sets `FD_CLOEXEC`
/// atomically.
fn open(h: &mut Host, pid: Pid, flags: i32, oracle: Oracle) -> Result<SysResult, Refusal> {
    let access = open_access("open", flags)?;
    let Some(fd) = h.lowest_free(pid, 0) else {
        return Ok(Err(Errno::EMFILE));
    };
    if let Oracle::Fail(e) = oracle {
        return Ok(Err(e));
    }
    let o = h.mint_ofd(Ofd::fresh(OfdKind::File, access, flags & darwin::OPEN_STATUS_MASK));
    install(h, pid, fd, o, flags & darwin::O_CLOEXEC != 0);
    Ok(Ok(Ret::Int(i64::from(fd))))
}

/// The refusal of `open("/dev/fd/N")` when N names a kqueue
/// (PLATFORM-KQUEUE-ALIAS-1): the kernels the model was measured on disagree.
pub const KQUEUE_ALIAS: &str =
    "/dev/fd/N of a kqueue (Darwin 25.6 and 27.0 answer EBADF, Darwin 27.2 EACCES)";

/// The refusal of `F_GETFD` of the descriptor `kqueue()` returned, until an
/// `F_SETFD` sets its flags (PLATFORM-KQUEUE-ALIAS-1): Darwin 27.2 sets
/// `FD_CLOFORK` on it as well as `FD_CLOEXEC`, and Darwin 25.6 has no such bit.
pub const KQUEUE_GETFD: &str = "F_GETFD of the descriptor kqueue() returned (Darwin 27.2 reads \
     FD_CLOEXEC|FD_CLOFORK, 3; Darwin 25.6, which has no FD_CLOFORK, reads 1)";

/// `open("/dev/fd/N")` — Darwin's fdesc (MEASURED, Darwin 25.6): the new
/// descriptor (lowest free; allocation first, as for every `open`) names
/// the SAME description as `fd`; `FD_CLOEXEC` is set iff `fd`'s is set OR
/// the open asked for `O_CLOEXEC` (XNU `dupfdopen` copies the source slot's
/// flags; MEASURED all three cases); the requested
/// access must lie within the description's (`O_WRONLY` or `O_RDWR` on a
/// pipe's read end, `O_WRONLY` on a read-only `/dev/null`: `EACCES`); the
/// status and creation bits (`O_NONBLOCK`, `O_APPEND`, `O_CREAT`,
/// `O_TRUNC`) are ignored — the shared description's flags do not change; a
/// closed `fd` is `EBADF`. A kqueue's alias is refused by name
/// (PLATFORM-KQUEUE-ALIAS-1): Darwin 25.6 and 27.0 answer `EBADF`, Darwin
/// 27.2 `EACCES` for every access mode (MEASURED), and the model names no
/// kernel release, so it gives neither answer. A full table is still `EMFILE`
/// first (MEASURED on 27.2 too).
fn open_alias(h: &mut Host, pid: Pid, fd: i32, flags: i32) -> Result<SysResult, Refusal> {
    let want = open_access("open", flags)?;
    let Some(new_fd) = h.lowest_free(pid, 0) else {
        return Ok(Err(Errno::EMFILE));
    };
    let e = match entry(h, pid, fd) {
        Ok(e) => e,
        Err(err) => return Ok(Err(err)),
    };
    let kind = known_kind(h, e, "open")?;
    if kind == OfdKind::Kqueue {
        return Err(Refusal::Unmodeled { symbol: "open", detail: KQUEUE_ALIAS.to_string() });
    }
    let have = h.ofd(e.ofd).map_or(Access::ReadOnly, |o| o.access);
    let within = match want {
        Access::ReadOnly => matches!(have, Access::ReadOnly | Access::ReadWrite),
        Access::WriteOnly => matches!(have, Access::WriteOnly | Access::ReadWrite),
        Access::ReadWrite => have == Access::ReadWrite,
    };
    if !within {
        return Ok(Err(Errno::EACCES));
    }
    install(h, pid, new_fd, e.ofd, e.cloexec || flags & darwin::O_CLOEXEC != 0);
    Ok(Ok(Ret::Int(i64::from(new_fd))))
}

/// `kqueue(2)`. MEASURED: the new descriptor has `FD_CLOEXEC` SET, and
/// `F_GETFL` answers `O_RDWR`. On Darwin 27.2 it has `FD_CLOFORK` set too
/// (`F_GETFD` reads 3; its `dup`, `dup2` and `F_DUPFD_CLOEXEC` do not carry
/// the bit, and an `F_SETFD` sets the flags exactly; MEASURED). That changes
/// nothing the model runs, since `fork` and `posix_spawn` never copy a
/// kqueue's entry, but it changes what `F_GETFD` reads, so the entry is marked
/// `clofork` and [`fcntl`] refuses that read by name ([`KQUEUE_GETFD`]).
fn kqueue(h: &mut Host, pid: Pid, oracle: Oracle) -> SysResult {
    let fd = h.lowest_free(pid, 0).ok_or(Errno::EMFILE)?;
    fail_or(oracle, || ())?;
    let o = h.mint_ofd(Ofd::fresh(OfdKind::Kqueue, Access::ReadWrite, 0));
    table_mut(h, pid).insert(fd, Entry { ofd: o, cloexec: true, clofork: true });
    Ok(Ret::Int(i64::from(fd)))
}

// ---- descriptor operations ----------------------------------------------------------

/// The `F_GETFL` bits `F_SETFL` cannot clear: `FWASWRITTEN` and `FHASLOCK`
/// (MEASURED: `F_SETFL(0)` after a write or a granted `flock` keeps them).
const STICKY_STATUS: i32 = darwin::FWASWRITTEN | darwin::FHASLOCK;

/// `fcntl(2)`, split by command.
fn fcntl(h: &mut Host, pid: Pid, fd: i32, cmd: i32, arg: i64) -> Result<SysResult, Refusal> {
    match cmd {
        darwin::F_GETFD => match entry(h, pid, fd) {
            Ok(e) if e.clofork => {
                Err(Refusal::Unmodeled { symbol: "fcntl", detail: KQUEUE_GETFD.to_string() })
            }
            other => Ok(other.map(|e| Ret::Int(i64::from(e.cloexec)))),
        },
        darwin::F_SETFD => {
            if let Err(err) = entry(h, pid, fd) {
                return Ok(Err(err));
            }
            // FD_CLOEXEC is the only descriptor flag the model has. Darwin 27
            // keeps FD_CLOFORK too (MEASURED: F_SETFD(3) reads back 3 and
            // `fork` drops the descriptor; Darwin 25.6 read back 1), so a call
            // carrying it is refused by name rather than run as if the bit were
            // ignored. Every higher bit is ignored on both (MEASURED).
            if arg & darwin::FD_CLOFORK != 0 {
                return Err(Refusal::Unmodeled {
                    symbol: "fcntl",
                    detail: "F_SETFD with FD_CLOFORK (the model has no close-on-fork flag)"
                        .to_string(),
                });
            }
            if let Some(e) = table_mut(h, pid).get_mut(&fd) {
                e.cloexec = arg & darwin::FD_CLOEXEC != 0;
                // The flags are set exactly: a kqueue's FD_CLOFORK goes too.
                e.clofork = false;
            }
            Ok(Ok(Ret::Int(0)))
        }
        darwin::F_GETFL => Ok(entry(h, pid, fd).and_then(|e| {
            h.ofd(e.ofd).map(|o| Ret::Int(i64::from(o.getfl()))).ok_or(Errno::EBADF)
        })),
        darwin::F_SETFL => {
            let e = match entry(h, pid, fd) {
                Ok(e) => e,
                Err(err) => return Ok(Err(err)),
            };
            let kind = known_kind(h, e, "fcntl")?;
            let bits = i32::try_from(arg & i64::from(darwin::SETFL_MASK)).unwrap_or(0);
            // XNU's F_SETFL stores the bits on the description, THEN asks the
            // object to apply FIONBIO (and FIOASYNC). MEASURED: a kqueue
            // answers FIONBIO with ENOTTY, so F_SETFL on a kqueue fails ENOTTY
            // for EVERY argument (0 included) while the bits stay changed.
            if kind == OfdKind::Kqueue {
                if let Some(o) = h.ofd_mut(e.ofd) {
                    o.status = bits | (o.status & STICKY_STATUS);
                }
                return Ok(Err(Errno::ENOTTY));
            }
            // O_ASYNC is MEASURED accepted on a pipe; on a vnode it reaches
            // the object's FIOASYNC handler, which the model does not know for
            // every device — refuse rather than guess.
            if bits & darwin::O_ASYNC != 0
                && !matches!(kind, OfdKind::PipeRead | OfdKind::PipeWrite | OfdKind::Socket { .. })
            {
                return Err(Refusal::Unmodeled {
                    symbol: "fcntl",
                    detail: format!("F_SETFL O_ASYNC on {kind:?}"),
                });
            }
            if let Some(o) = h.ofd_mut(e.ofd) {
                o.status = bits | (o.status & STICKY_STATUS);
            }
            Ok(Ok(Ret::Int(0)))
        }
        darwin::F_DUPFD | darwin::F_DUPFD_CLOEXEC => {
            Ok(dupfd(h, pid, fd, arg, cmd == darwin::F_DUPFD_CLOEXEC))
        }
        other => Err(Refusal::Unmodeled {
            symbol: "fcntl",
            detail: darwin::fcntl_name(other)
                .map_or_else(|| format!("cmd={other}"), str::to_string),
        }),
    }
}

/// `F_DUPFD(floor)` / `F_DUPFD_CLOEXEC(floor)`: lowest free number `>= floor`
/// naming the same description; `FD_CLOEXEC` clear / set. MEASURED:
/// `floor < 0` or `floor >= limit` is `EINVAL`; a source above the limit
/// (left open by a lowering `setrlimit`) is a valid source.
fn dupfd(h: &mut Host, pid: Pid, fd: i32, floor: i64, cloexec: bool) -> SysResult {
    let e = entry(h, pid, fd)?;
    if floor < 0 || floor >= h.alloc_limit(pid) {
        return Err(Errno::EINVAL);
    }
    let floor = i32::try_from(floor).map_err(|_| Errno::EINVAL)?;
    let new_fd = h.lowest_free(pid, floor).ok_or(Errno::EMFILE)?;
    install(h, pid, new_fd, e.ofd, cloexec);
    Ok(Ret::Int(i64::from(new_fd)))
}

/// `dup(2)`: lowest free number, same description, `FD_CLOEXEC` clear.
fn dup(h: &mut Host, pid: Pid, fd: i32) -> SysResult {
    let e = entry(h, pid, fd)?;
    let new_fd = h.lowest_free(pid, 0).ok_or(Errno::EMFILE)?;
    install(h, pid, new_fd, e.ofd, false);
    Ok(Ret::Int(i64::from(new_fd)))
}

/// `dup2(2)`. MEASURED order: `to < 0` or `to >= limit` is `EBADF` even when
/// `from == to` (a self-copy of a descriptor left above a lowered limit
/// fails); then `from == to` is a no-op that KEEPS `FD_CLOEXEC`; otherwise
/// `to` is closed (its description dropped iff that was the last reference)
/// and re-pointed at `from`'s description with `FD_CLOEXEC` clear, atomically.
fn dup2(h: &mut Host, pid: Pid, from: i32, to: i32) -> Result<SysResult, Refusal> {
    let e = match entry(h, pid, from) {
        Ok(e) => e,
        Err(err) => return Ok(Err(err)),
    };
    if to < 0 || i64::from(to) >= h.alloc_limit(pid) {
        return Ok(Err(Errno::EBADF));
    }
    if from == to {
        return Ok(Ok(Ret::Int(i64::from(to))));
    }
    // MEASURED (the M2 model review's P3c, P18): `dup2` onto a number an
    // `open` reserved, or onto one a sleeping `flock` holds, waits until that
    // call returns (1003 ms, 810 ms), then replaces the descriptor.
    if h.proc(pid).is_some_and(|p| p.inflight.contains_key(&to)) {
        return Err(Refusal::Blocks);
    }
    dup2_unchecked(h, pid, e.ofd, to);
    Ok(Ok(Ret::Int(i64::from(to))))
}

fn dup2_unchecked(h: &mut Host, pid: Pid, ofd: OfdId, to: i32) {
    let old = table_mut(h, pid).insert(to, Entry { ofd, cloexec: false, clofork: false });
    if let Some(old) = old {
        h.collect(old.ofd);
    }
}

/// `close(2)`: remove the entry; the description — and with it its `flock`
/// lock — is dropped only when no entry in ANY process names it (MEASURED:
/// closing one of two `dup`s keeps the lock; a `fork` child's copy keeps it
/// after the parent's last close, and after the parent's exit).
///
/// MEASURED (the M2 model review's P7, P18): `close` of a number another
/// thread's sleeping `flock` holds waits until that `flock` returns (1003 ms;
/// 2004 ms while the holder kept its lock) — not enabled
/// ([`Refusal::Blocks`]) while the flock is in flight. A number an `open`
/// reserved is not open: `EBADF` (P3).
fn close(h: &mut Host, pid: Pid, fd: i32) -> Result<SysResult, Refusal> {
    if let Err(err) = entry(h, pid, fd) {
        return Ok(Err(err));
    }
    if h.proc(pid).is_some_and(|p| matches!(p.inflight.get(&fd), Some(InFlight::Flock { .. }))) {
        return Err(Refusal::Blocks);
    }
    h.remove_entry(pid, fd);
    Ok(Ok(Ret::Int(0)))
}

/// `ioctl(2)`: FIOCLEX / FIONCLEX set / clear the entry's `FD_CLOEXEC`
/// (std's `set_cloexec` on Darwin); FIONBIO sets / clears the description's
/// `O_NONBLOCK`. Every other request is refused by name.
fn ioctl(h: &mut Host, pid: Pid, fd: i32, request: u64, arg: i32) -> Result<SysResult, Refusal> {
    match request {
        darwin::FIOCLEX | darwin::FIONCLEX => Ok(entry(h, pid, fd).map(|_| {
            if let Some(e) = table_mut(h, pid).get_mut(&fd) {
                e.cloexec = request == darwin::FIOCLEX;
            }
            Ret::Int(0)
        })),
        darwin::FIONBIO => {
            let e = match entry(h, pid, fd) {
                Ok(e) => e,
                Err(err) => return Ok(Err(err)),
            };
            let kind = h.ofd(e.ofd).map(|o| o.kind);
            if !matches!(
                kind,
                Some(OfdKind::PipeRead | OfdKind::PipeWrite | OfdKind::Socket { .. })
            ) {
                return Err(Refusal::Unmodeled {
                    symbol: "ioctl",
                    detail: format!("FIONBIO on {kind:?}"),
                });
            }
            if let Some(o) = h.ofd_mut(e.ofd) {
                if arg != 0 {
                    o.status |= darwin::O_NONBLOCK;
                } else {
                    o.status &= !darwin::O_NONBLOCK;
                }
            }
            Ok(Ok(Ret::Int(0)))
        }
        other => Err(Refusal::Unmodeled {
            symbol: "ioctl",
            detail: darwin::ioctl_name(other)
                .map_or_else(|| format!("request={other:#x}"), str::to_string),
        }),
    }
}

// ---- processes ------------------------------------------------------------------------

/// The table a `fork` (or `posix_spawn`) child starts from: a snapshot of the
/// parent's whole table, minus every entry naming a kqueue (MEASURED), minus
/// the slots a torn copy `missed` ([`step_torn`]).
fn fork_snapshot(h: &Host, parent: Pid, missed: &BTreeSet<i32>) -> BTreeMap<i32, Entry> {
    let Some(p) = h.proc(parent) else {
        return BTreeMap::new();
    };
    p.table
        .iter()
        .filter(|(fd, _)| !missed.contains(fd))
        .filter(|(_, e)| h.ofd(e.ofd).is_some_and(|o| o.kind.inherited_by_fork()))
        .map(|(fd, e)| (*fd, *e))
        .collect()
}

/// `fork(2)`: one event. The child's table is a snapshot of the parent's
/// (every description's reference count goes up by the copies) — minus any
/// slot a torn copy missed — it has one thread, the parent's limits, and
/// phase `ForkedPreExec`.
fn fork(h: &mut Host, pid: Pid, oracle: Oracle, missed: &BTreeSet<i32>) -> SysResult {
    fail_or(oracle, || ())?;
    let parent = h.proc(pid).cloned().ok_or(Errno::EAGAIN)?;
    let table = fork_snapshot(h, pid, missed);
    let child = h.mint_pid();
    h.insert_proc(
        child,
        Proc {
            table,
            phase: Phase::ForkedPreExec { parent_threads: parent.threads },
            threads: 1,
            nofile: parent.nofile,
            parent: Some(pid),
            inflight: BTreeMap::new(),
        },
    );
    Ok(Ret::Int(i64::from(child.0)))
}

/// The exec sweep: drop every `FD_CLOEXEC` entry and every kqueue entry
/// (MEASURED: a kqueue with `FD_CLOEXEC` clear does not survive `execve`).
fn exec_sweep(h: &mut Host, pid: Pid) {
    let doomed: Vec<i32> = h
        .proc(pid)
        .map(|p| {
            p.table
                .iter()
                .filter(|(_, e)| e.cloexec || !h.ofd(e.ofd).is_some_and(|o| o.kind.survives_exec()))
                .map(|(fd, _)| *fd)
                .collect()
        })
        .unwrap_or_default();
    for fd in doomed {
        h.remove_entry(pid, fd);
    }
}

/// `execve(2)` and the `exec*` family: on success the cloexec entries are
/// dropped, the process becomes one-threaded and `Execd`; on failure NOTHING
/// changes. The image is not modeled and is NOT set-id: XNU reopens a closed
/// 0, 1 or 2 on `/dev/null` when it execs a setuid/setgid image (from the
/// XNU source, not measured here); an image the oracle cannot name cannot be
/// one.
fn exec(h: &mut Host, pid: Pid, oracle: Oracle) -> SysResult {
    fail_or(oracle, || ())?;
    // The other threads, and the calls they had in flight, are gone.
    cancel_inflight(h, pid);
    exec_sweep(h, pid);
    if let Some(p) = h.proc_mut(pid) {
        p.phase = Phase::Execd;
        p.threads = 1;
    }
    Ok(Ret::NoReturn)
}

/// Abandon every call `pid`'s threads have in flight (its exit or exec ends
/// them): reserved numbers are free again, a pending open's node is let go.
fn cancel_inflight(h: &mut Host, pid: Pid) {
    let nodes: Vec<NodeId> = h
        .proc(pid)
        .map(|p| {
            p.inflight
                .values()
                .filter_map(|f| match f {
                    InFlight::Open { ofd, .. } => ofd.node,
                    InFlight::Flock { .. } => None,
                })
                .collect()
        })
        .unwrap_or_default();
    if let Some(p) = h.proc_mut(pid) {
        p.inflight.clear();
    }
    for n in nodes {
        h.collect_node(n);
    }
}

/// `posix_spawn(2)` / `posix_spawnp` as ONE event: [`spawn_begin`] then
/// [`spawn_end`] with nothing between them (an M1 program's spawn; a
/// derivation that interleaves the window uses [`Call::SpawnBegin`] and
/// [`Call::SpawnEnd`]). A failed spawn leaves the host as it was.
fn spawn(
    h: &mut Host,
    pid: Pid,
    actions: &[FileAction],
    flags: i32,
    oracle: Oracle,
    missed: &BTreeSet<i32>,
) -> Result<SysResult, Refusal> {
    if let Some(r) = spawn_refusal(actions, flags) {
        return Err(r);
    }
    // The two halves with nothing between them, on a scratch host so a
    // failed spawn leaves `h` untouched (counters included).
    let mut scratch = h.clone();
    let child = match spawn_begin(&mut scratch, pid, Oracle::Nominal, missed) {
        Ok(Ret::Int(c)) => Pid(u32::try_from(c).unwrap_or(0)),
        other => {
            return Err(Refusal::Unmodeled {
                symbol: "posix_spawn",
                detail: format!("the copy step answered {other:?}"),
            });
        }
    };
    match spawn_end(&mut scratch, pid, child, actions, flags, oracle)? {
        Ok(r) => {
            *h = scratch;
            Ok(Ok(r))
        }
        Err(e) => Ok(Err(e)),
    }
}

/// Why the model refuses a `posix_spawn` with these file actions and
/// attribute flags (before any process exists), if it does.
#[must_use]
pub fn spawn_refusal(actions: &[FileAction], flags: i32) -> Option<Refusal> {
    for a in actions {
        if file_action_add(a).is_err() {
            return Some(Refusal::Unmodeled {
                symbol: "posix_spawn_file_actions_add",
                detail: format!(
                    "{a:?}: libc rejects a descriptor >= OPEN_MAX ({}) with EBADF when the \
                     action is ADDED, so it cannot be in the list; whether the program spawns \
                     without it depends on its return-code handling",
                    darwin::OPEN_MAX
                ),
            });
        }
    }
    if flags & darwin::POSIX_SPAWN_SETEXEC != 0 {
        return Some(Refusal::Unmodeled {
            symbol: "posix_spawn",
            detail: "POSIX_SPAWN_SETEXEC".to_string(),
        });
    }
    let unknown = flags & !(darwin::SPAWN_FD_NEUTRAL_FLAGS | darwin::POSIX_SPAWN_CLOEXEC_DEFAULT);
    if unknown != 0 {
        return Some(Refusal::Unmodeled {
            symbol: "posix_spawn",
            detail: format!("attribute flags {unknown:#x}"),
        });
    }
    None
}

/// [`Call::SpawnBegin`]: the new process, holding the fork snapshot of the
/// caller's table (every entry but kqueues and the slots a torn copy
/// `missed` — `FD_CLOEXEC` ones INCLUDED), phase
/// [`Phase::Spawning`]. MEASURED (Darwin 25.6, the M2 model review's p4/p4b,
/// re-run 2026-10-01): after the parent closed its ONLY reference to a
/// close-on-exec locked description, another open's `LOCK_EX|LOCK_NB` was
/// refused in 3626 of 20000 trials beside a thread looping `posix_spawn`
/// (3102 with `POSIX_SPAWN_CLOEXEC_DEFAULT`; 0 of 5000 with no spawner); a
/// pipe's reader saw no end-of-file at once in 260 of 5000 (0 without).
/// The oracle's `EAGAIN`/`ENOMEM` is fork1's failure: no process, no copy.
fn spawn_begin(h: &mut Host, pid: Pid, oracle: Oracle, missed: &BTreeSet<i32>) -> SysResult {
    fail_or(oracle, || ())?;
    let parent = h.proc(pid).cloned().ok_or(Errno::EAGAIN)?;
    let table = fork_snapshot(h, pid, missed);
    let child = h.mint_pid();
    h.insert_proc(
        child,
        Proc {
            table,
            phase: Phase::Spawning { parent_threads: parent.threads },
            threads: 1,
            nofile: parent.nofile,
            parent: Some(pid),
            inflight: BTreeMap::new(),
        },
    );
    Ok(Ret::Int(i64::from(child.0)))
}

/// [`Call::SpawnEnd`]: the second half of `posix_spawn(2)` / `posix_spawnp`.
///
/// 1. The file actions run in order, in the child, with the syscalls' own
///    semantics: `addclose` closes (`EBADF` if not open); `adddup2(a, b)` is
///    `dup2` (so `a == b` keeps `FD_CLOEXEC` — MEASURED, Darwin does not
///    implement POSIX-2024's "clears FD_CLOEXEC" for that case); `addopen(fd)`
///    opens at the lowest free number with its own `O_CLOEXEC` and, when that
///    is not `fd`, `dup2`s it there (clearing `FD_CLOEXEC`) and closes the
///    temporary; `addinherit_np(fd)` clears `FD_CLOEXEC` (`EBADF` if not open);
///    `addchdir` has no descriptor effect (its path is the oracle's);
///    `addfchdir(fd)` is `EBADF` on a closed descriptor, `EINVAL` on a kqueue
///    (MEASURED: although the kqueue is not copied, fchdir sees the parent's
///    kqueue) or on a pipe or socket (not a vnode), and the oracle's
///    `ENOTDIR` on a vnode that is not a directory.
///    Any action error fails the whole spawn. An action libc rejects at add
///    time ([`file_action_add`]: a descriptor `>= OPEN_MAX`) is refused: it
///    cannot be in the list.
/// 2. A failure (an action's errno, or the oracle's) tears the child down:
///    every copy it held is dropped (a lock its copy kept ends there) and the
///    spawn returns the errno. MEASURED (P21): a spawn of a missing image
///    held a close-on-exec lock past the parent's last close (19 of 20000).
/// 3. Success: the exec sweep keeps an entry iff `FD_CLOEXEC` is clear, it is
///    not a kqueue, and — under `POSIX_SPAWN_CLOEXEC_DEFAULT` — its number
///    was the target of an `adddup2`, `addopen` or `addinherit_np` action.
///
/// MEASURED (13 cases, Darwin 25.6): this survives-iff-(not cloexec) AND
/// (no CLOEXEC_DEFAULT or named) rule; the plan's "CLOEXEC_DEFAULT marks
/// every unnamed fd" is right in effect, but marking before the actions is
/// NOT (`adddup2(1,1)` keeps a non-cloexec fd 1 under CLOEXEC_DEFAULT).
fn spawn_end(
    h: &mut Host,
    pid: Pid,
    child: Pid,
    actions: &[FileAction],
    flags: i32,
    oracle: Oracle,
) -> Result<SysResult, Refusal> {
    if let Some(r) = spawn_refusal(actions, flags) {
        return Err(r);
    }
    let in_progress = h
        .proc(child)
        .is_some_and(|c| c.parent == Some(pid) && matches!(c.phase, Phase::Spawning { .. }));
    if !in_progress {
        return Err(Refusal::Unmodeled {
            symbol: "posix_spawn",
            detail: format!("{child:?} is not a spawn in progress of {pid:?}"),
        });
    }
    let cloexec_default = flags & darwin::POSIX_SPAWN_CLOEXEC_DEFAULT != 0;
    let mut named: BTreeSet<i32> = BTreeSet::new();
    for action in actions {
        let r = match *action {
            FileAction::Close { fd } => close(h, child, fd)?.map(|_| ()),
            FileAction::Dup2 { from, to } => {
                named.insert(to);
                dup2(h, child, from, to)?.map(|_| ())
            }
            FileAction::Open { fd, flags: oflags } => {
                named.insert(fd);
                spawn_open(h, child, fd, oflags)?
            }
            FileAction::Inherit { fd } => {
                named.insert(fd);
                entry(h, child, fd).map(|_| {
                    if let Some(e) = table_mut(h, child).get_mut(&fd) {
                        e.cloexec = false;
                    }
                })
            }
            FileAction::Chdir => Ok(()),
            FileAction::Fchdir { fd } => spawn_fchdir(h, pid, child, fd)?,
            FileAction::InheritIf { .. } | FileAction::PlaceStdio { .. } => {
                return Err(Refusal::Unmodeled {
                    symbol: "posix_spawn",
                    detail: "unresolved std file-action builder".to_string(),
                });
            }
        };
        if let Err(e) = r {
            teardown(h, child);
            return Ok(Err(e));
        }
    }
    if let Oracle::Fail(e) = oracle {
        teardown(h, child);
        return Ok(Err(e));
    }
    if cloexec_default {
        let unnamed: Vec<i32> = h
            .proc(child)
            .map(|p| p.table.keys().filter(|fd| !named.contains(fd)).copied().collect())
            .unwrap_or_default();
        for fd in unnamed {
            h.remove_entry(child, fd);
        }
    }
    exec_sweep(h, child);
    if let Some(p) = h.proc_mut(child) {
        p.phase = Phase::Execd;
    }
    Ok(Ok(Ret::Int(i64::from(child.0))))
}

/// A failed spawn's child goes: every copy it held is dropped, then the
/// process (posix_spawn reaps it; the caller never sees its pid).
fn teardown(h: &mut Host, child: Pid) {
    let fds: Vec<i32> =
        h.proc(child).map(|p| p.table.keys().copied().collect()).unwrap_or_default();
    for fd in fds {
        h.remove_entry(child, fd);
    }
    h.remove_proc(child);
}

/// `posix_spawn_file_actions_addfchdir(fd)` inside the spawn.
fn spawn_fchdir(h: &Host, parent: Pid, child: Pid, fd: i32) -> Result<Result<(), Errno>, Refusal> {
    let Ok(e) = entry(h, child, fd) else {
        let parent_kq = h
            .entry(parent, fd)
            .and_then(|e| h.ofd(e.ofd))
            .is_some_and(|o| o.kind == OfdKind::Kqueue);
        return Ok(Err(if parent_kq { Errno::EINVAL } else { Errno::EBADF }));
    };
    match known_kind(h, e, "posix_spawn_file_actions_addfchdir")? {
        OfdKind::File => Ok(Ok(())),
        _ => Ok(Err(Errno::EINVAL)),
    }
}

/// `posix_spawn_file_actions_addopen` inside the spawn (path success is the
/// spawn oracle's to refuse).
fn spawn_open(
    h: &mut Host,
    child: Pid,
    fd: i32,
    oflags: i32,
) -> Result<Result<(), Errno>, Refusal> {
    let access = open_access("posix_spawn_file_actions_addopen", oflags)?;
    if fd < 0 || i64::from(fd) >= h.alloc_limit(child) {
        return Ok(Err(Errno::EBADF));
    }
    let Some(tmp) = h.lowest_free(child, 0) else {
        return Ok(Err(Errno::EMFILE));
    };
    let o = h.mint_ofd(Ofd::fresh(OfdKind::File, access, oflags & darwin::OPEN_STATUS_MASK));
    install(h, child, tmp, o, oflags & darwin::O_CLOEXEC != 0);
    if tmp != fd {
        dup2_unchecked(h, child, o, fd);
        h.remove_entry(child, tmp);
    }
    Ok(Ok(()))
}

/// `getrlimit(2)`; only `RLIMIT_NOFILE` is modeled.
fn getrlimit(h: &Host, pid: Pid, resource: i32) -> Result<SysResult, Refusal> {
    if resource != darwin::RLIMIT_NOFILE {
        return Err(unmodeled_rlimit("getrlimit", resource));
    }
    let p = h.proc(pid).ok_or(Refusal::NoSuchProcess(pid))?;
    Ok(Ok(Ret::Rlimit { soft: p.nofile.soft, hard: p.nofile.hard }))
}

fn unmodeled_rlimit(symbol: &'static str, resource: i32) -> Refusal {
    Refusal::Unmodeled {
        symbol,
        detail: darwin::rlimit_name(resource)
            .map_or_else(|| format!("resource={resource}"), str::to_string),
    }
}

/// `setrlimit(2)` for `RLIMIT_NOFILE`. `soft > hard` is `EINVAL`; raising
/// the hard limit is `EPERM` (the model is of an unprivileged process).
/// MEASURED: Darwin 25.6 accepts a soft limit above `kern.maxfilesperproc`,
/// even `RLIM_INFINITY`, unclamped (the SDK man page's "EINVAL for
/// RLIM_INFINITY" note is stale). Lowering NEVER closes a descriptor.
fn setrlimit(
    h: &mut Host,
    pid: Pid,
    resource: i32,
    soft: u64,
    hard: u64,
) -> Result<SysResult, Refusal> {
    if resource != darwin::RLIMIT_NOFILE {
        return Err(unmodeled_rlimit("setrlimit", resource));
    }
    let p = h.proc_mut(pid).ok_or(Refusal::NoSuchProcess(pid))?;
    if soft > hard {
        return Ok(Err(Errno::EINVAL));
    }
    if hard > p.nofile.hard {
        return Ok(Err(Errno::EPERM));
    }
    p.nofile = Rlimit { soft, hard };
    Ok(Ok(Ret::Int(0)))
}

/// `_exit(2)`: every descriptor is closed (descriptions dropped at zero
/// references, peers see end-of-file); the process stays a zombie until
/// reaped.
fn exit(h: &mut Host, pid: Pid, status: i32) -> SysResult {
    cancel_inflight(h, pid);
    let fds: Vec<i32> = h.proc(pid).map(|p| p.table.keys().copied().collect()).unwrap_or_default();
    for fd in fds {
        h.remove_entry(pid, fd);
    }
    if let Some(p) = h.proc_mut(pid) {
        p.phase = Phase::Exited { status };
        p.threads = 0;
    }
    Ok(Ret::NoReturn)
}

/// `waitpid(2)`. `pid > 0`: `ECHILD` unless it is the caller's child;
/// `pid == -1`: any child of the caller (`ECHILD` if it has none). An exited
/// eligible child is reaped and its pid returned; with none exited, `WNOHANG`
/// returns 0 at once and a blocking wait is not enabled
/// ([`Refusal::Blocks`]). Refused by name: process-group waits (`pid == 0`,
/// `pid < -1`: groups are not modeled), options other than `WNOHANG`
/// (`WUNTRACED`, `WCONTINUED`: stops are not modeled), and a `-1` wait that
/// could reap either of several exited children (which one is not modeled).
fn waitpid(h: &mut Host, pid: Pid, child: i32, options: i32) -> Result<SysResult, Refusal> {
    if options & !darwin::WNOHANG != 0 {
        return Err(Refusal::Unmodeled {
            symbol: "waitpid",
            detail: format!("options {options:#x} (only WNOHANG is modeled)"),
        });
    }
    let eligible: Vec<Pid> = match child {
        -1 => h.procs().filter(|(_, p)| p.parent == Some(pid)).map(|(c, _)| c).collect(),
        c if c > 0 => {
            let cpid = Pid(u32::try_from(c).unwrap_or(0));
            match h.proc(cpid) {
                Some(p) if p.parent == Some(pid) => vec![cpid],
                _ => Vec::new(),
            }
        }
        other => {
            return Err(Refusal::Unmodeled {
                symbol: "waitpid",
                detail: format!("pid {other}: process-group waits are not modeled"),
            });
        }
    };
    if eligible.is_empty() {
        return Ok(Err(Errno::ECHILD));
    }
    let exited: Vec<Pid> =
        eligible.iter().copied().filter(|c| h.proc(*c).is_some_and(|p| !p.is_live())).collect();
    match exited.as_slice() {
        [] if options & darwin::WNOHANG != 0 => Ok(Ok(Ret::Int(0))),
        [] => Err(Refusal::Blocks),
        [one] => {
            h.remove_proc(*one);
            Ok(Ok(Ret::Int(i64::from(one.0))))
        }
        _ => Err(Refusal::Unmodeled {
            symbol: "waitpid",
            detail: format!("which of {} exited children waitpid(-1) reaps", exited.len()),
        }),
    }
}

/// `pthread_create(3)`.
/// [`Call::CloexecFrom`]: `FD_CLOEXEC` on every entry from `first` up.
fn cloexec_from(h: &mut Host, pid: Pid, first: i32) -> Result<SysResult, Refusal> {
    let threads = h.proc(pid).map_or(0, |p| p.threads);
    if threads != 1 {
        return Err(Refusal::Unmodeled {
            symbol: "fcntl",
            detail: format!(
                "std's descriptor strip in a process of {threads} threads: one event only while \
                 no other thread can change the table (a forked child)"
            ),
        });
    }
    for (_, e) in table_mut(h, pid).range_mut(first..) {
        e.cloexec = true;
    }
    Ok(Ok(Ret::Int(0)))
}

fn thread_create(h: &mut Host, pid: Pid, oracle: Oracle) -> SysResult {
    fail_or(oracle, || ())?;
    if let Some(p) = h.proc_mut(pid) {
        p.threads += 1;
    }
    Ok(Ret::Int(0))
}

/// [`Call::ReadSome`]: data the peer wrote is consumed (`Int(1)`: "some
/// bytes"); with nothing pending, end-of-file (`Int(0)`) once the peer
/// description is gone; otherwise `EAGAIN` on a non-blocking description and
/// not enabled on a blocking one. A write-only description is `EBADF`.
fn read_some(h: &mut Host, pid: Pid, fd: i32) -> Result<SysResult, Refusal> {
    let e = match entry(h, pid, fd) {
        Ok(e) => e,
        Err(err) => return Ok(Err(err)),
    };
    known_kind(h, e, "read")?;
    let Some(o) = h.ofd(e.ofd).copied() else {
        return Ok(Err(Errno::EBADF));
    };
    if o.access == Access::WriteOnly {
        return Ok(Err(Errno::EBADF));
    }
    if o.unread {
        if let Some(m) = h.ofd_mut(e.ofd) {
            m.unread = false;
        }
        return Ok(Ok(Ret::Int(1)));
    }
    match o.peer {
        Peer::Closed => Ok(Ok(Ret::Int(0))),
        Peer::Open(_) if o.status & darwin::O_NONBLOCK != 0 => Ok(Err(Errno::EAGAIN)),
        Peer::Open(_) => Err(Refusal::Blocks),
        Peer::None => Err(Refusal::Unmodeled {
            symbol: "read",
            detail: "a description with no tracked peer".to_string(),
        }),
    }
}

/// [`Call::WriteSome`]: a small write to a pipe write end or a connected
/// socket marks the peer description's data pending and the written
/// description [`darwin::FWASWRITTEN`] (MEASURED). A read-only
/// description is `EBADF`. A write whose peer is gone raises `SIGPIPE` (by
/// default fatal) or fails `EPIPE`: refused, not modeled.
fn write_some(h: &mut Host, pid: Pid, fd: i32) -> Result<SysResult, Refusal> {
    let e = match entry(h, pid, fd) {
        Ok(e) => e,
        Err(err) => return Ok(Err(err)),
    };
    known_kind(h, e, "write")?;
    let Some(o) = h.ofd(e.ofd).copied() else {
        return Ok(Err(Errno::EBADF));
    };
    if o.access == Access::ReadOnly {
        return Ok(Err(Errno::EBADF));
    }
    match o.peer {
        Peer::Open(peer) => {
            if let Some(p) = h.ofd_mut(peer) {
                p.unread = true;
            }
            if let Some(me) = h.ofd_mut(e.ofd) {
                me.status |= darwin::FWASWRITTEN;
            }
            Ok(Ok(Ret::Int(1)))
        }
        Peer::Closed => Err(Refusal::Unmodeled {
            symbol: "write",
            detail: "a write whose reader is gone (SIGPIPE / EPIPE)".to_string(),
        }),
        Peer::None => Err(Refusal::Unmodeled {
            symbol: "write",
            detail: "a description with no tracked peer".to_string(),
        }),
    }
}

// ---- M2: flock, the namespace, node identity ------------------------------------------

/// What `flock` (or a lock bit of an open) acts on.
enum LockTarget {
    /// A lockable vnode: a regular file, a directory, a character device.
    Lockable,
    /// Not a vnode — a pipe, a socket, a kqueue: `ENOTSUP` BEFORE `op` is
    /// decoded (MEASURED: `flock(pipe, 0)` is `ENOTSUP`).
    NotVnode,
    /// A vnode that takes no lock — a FIFO: `op` is decoded FIRST (MEASURED,
    /// the M2 model review's P1: `flock(fifo, 0)`, `LOCK_NB` alone and `16` are
    /// `EBADF`; `LOCK_UN` and `LOCK_EX` are `ENOTSUP`).
    NotLockable,
}

/// The target of `flock` (or a lock bit) on the description `e` names, or a
/// refusal for a description whose file the model does not know.
fn lock_target(h: &Host, e: Entry, symbol: &'static str) -> Result<LockTarget, Refusal> {
    let o = h.ofd(e.ofd).ok_or(Refusal::Unmodeled { symbol, detail: "dangling entry".into() })?;
    match o.kind {
        OfdKind::PipeRead | OfdKind::PipeWrite | OfdKind::Socket { .. } | OfdKind::Kqueue => {
            return Ok(LockTarget::NotVnode);
        }
        OfdKind::Opaque => {
            return Err(Refusal::Unmodeled {
                symbol,
                detail: "the description's kind is unknown (an environment-provided descriptor)"
                    .to_string(),
            });
        }
        OfdKind::File => {}
    }
    let Some(n) = o.node else {
        return Err(Refusal::Unmodeled {
            symbol,
            detail: "a description whose file the model does not know (an anonymous open): flock \
                     conflicts are per file, and two such opens may be one file (MEASURED: two \
                     opens of /dev/null conflict)"
                .to_string(),
        });
    };
    match h.node(n).map(|node| node.kind) {
        Some(k) if k.lockable() => Ok(LockTarget::Lockable),
        Some(NodeKind::Fifo) => Ok(LockTarget::NotLockable),
        other => {
            Err(Refusal::Unmodeled { symbol, detail: format!("a description open on {other:?}") })
        }
    }
}

/// Give description `ofd` the lock `mode` (and its sticky `FHASLOCK`).
fn grant(h: &mut Host, ofd: OfdId, mode: LockMode) {
    if let Some(o) = h.ofd_mut(ofd) {
        o.lock = Some(mode);
        o.status |= darwin::FHASLOCK;
    }
}

/// `flock(2)`. MEASURED (Darwin 25.6, 2026-10-01; each rule a conformance
/// probe):
///
/// * a closed descriptor is `EBADF`; a pipe, socket or kqueue is `ENOTSUP` —
///   before `op` is looked at (`flock(pipe, 0)` is `ENOTSUP`);
/// * `LOCK_UN` anywhere in `op` wins: the DESCRIPTION's lock is released,
///   whoever else holds a reference to it (a `dup`, a `fork` child's copy);
///   unlocking an unlocked description is `0`;
/// * otherwise `LOCK_EX` anywhere in `op` asks for an exclusive lock, else
///   `LOCK_SH` a shared one, else `EBADF` (`op` 0, `LOCK_NB` alone, an unknown
///   bit);
/// * a FIFO is a vnode that takes no lock: its `op` is decoded first (a bad
///   one is `EBADF`), then every request — `LOCK_UN` included — is `ENOTSUP`;
/// * the request is granted iff no OTHER description open on the node holds a
///   conflicting lock (exclusive conflicts with any lock); a granted request
///   REPLACES the description's own lock (an upgrade or a downgrade) and sets
///   `FHASLOCK` in `F_GETFL`;
/// * a request a conflict refuses: under `LOCK_NB`, `EWOULDBLOCK` (= `EAGAIN`)
///   with the description's own lock KEPT — a failed `LOCK_SH -> LOCK_EX|LOCK_NB`
///   upgrade still holds `LOCK_SH` (Linux drops it; Darwin does not); without
///   `LOCK_NB` the call SLEEPS: it returns [`Ret::Pending`] and its number is
///   in flight ([`InFlight::Flock`]: `close`/`dup2` of it wait until it
///   returns, MEASURED) until [`Call::Resume`] finds the lock free (or a
///   signal interrupts it, `EINTR`) — except a `LOCK_SH -> LOCK_EX`
///   conversion, which XNU makes by releasing the shared lock BEFORE it sleeps
///   (MEASURED: another description's `LOCK_EX|LOCK_NB` is granted while the
///   conversion waits; interrupted, it has lost `LOCK_SH`) — refused by name.
fn flock(h: &mut Host, pid: Pid, fd: i32, op: i32) -> Result<SysResult, Refusal> {
    let e = match entry(h, pid, fd) {
        Ok(e) => e,
        Err(err) => return Ok(Err(err)),
    };
    let target = lock_target(h, e, "flock")?;
    if matches!(target, LockTarget::NotVnode) {
        return Ok(Err(Errno::ENOTSUP));
    }
    let want = if op & darwin::LOCK_UN != 0 {
        None
    } else if op & darwin::LOCK_EX != 0 {
        Some(LockMode::Exclusive)
    } else if op & darwin::LOCK_SH != 0 {
        Some(LockMode::Shared)
    } else {
        return Ok(Err(Errno::EBADF));
    };
    if matches!(target, LockTarget::NotLockable) {
        return Ok(Err(Errno::ENOTSUP));
    }
    let Some(want) = want else {
        if let Some(o) = h.ofd_mut(e.ofd) {
            o.lock = None;
        }
        return Ok(Ok(Ret::Int(0)));
    };
    if h.lock_blocker(e.ofd, want).is_none() {
        grant(h, e.ofd, want);
        return Ok(Ok(Ret::Int(0)));
    }
    if op & darwin::LOCK_NB != 0 {
        return Ok(Err(Errno::EAGAIN));
    }
    if h.ofd(e.ofd).and_then(|o| o.lock) == Some(LockMode::Shared) && want == LockMode::Exclusive {
        return Err(Refusal::Unmodeled {
            symbol: "flock",
            detail: "a blocking LOCK_SH -> LOCK_EX conversion that must wait: XNU releases the \
                     shared lock before it sleeps (MEASURED), a host change the model has no \
                     waiting-call state for"
                .to_string(),
        });
    }
    if h.proc(pid).is_some_and(|p| p.inflight.contains_key(&fd)) {
        return Err(Refusal::Unmodeled {
            symbol: "flock",
            detail: format!("a second call in flight on descriptor {fd}"),
        });
    }
    table_proc_mut(h, pid).inflight.insert(fd, InFlight::Flock { ofd: e.ofd, want });
    Ok(Ok(Ret::Pending { fd }))
}

fn table_proc_mut(h: &mut Host, pid: Pid) -> &mut Proc {
    // The caller was checked live at the top of `step`.
    h.proc_mut(pid).expect("caller exists")
}

/// The node a canonical `path` resolves to for an open with `flags`,
/// following symlinks (MEASURED: `open` follows a symlink, `O_NOFOLLOW` on
/// one fails `ELOOP`; a relative target names a file in the LINK's
/// directory). `Ok(Ok((None, name)))`: the name is absent, so an `O_CREAT`
/// open creates `name` (a dangling symlink's target: MEASURED, `O_CREAT`
/// through a dangling link creates its target).
fn resolve(
    h: &Host,
    path: &str,
    flags: i32,
    symbol: &'static str,
) -> Result<Result<(Option<NodeId>, String), Errno>, Refusal> {
    let mut name = path.to_string();
    for hop in 0..32 {
        let Some(n) = h.name(&name) else {
            return Ok(Ok((None, name)));
        };
        let Some(node) = h.node(n) else {
            return Ok(Err(Errno::ENOENT));
        };
        if node.kind != NodeKind::Symlink {
            return Ok(Ok((Some(n), name)));
        }
        if hop == 0 && flags & darwin::O_NOFOLLOW != 0 {
            return Ok(Err(Errno::ELOOP));
        }
        let target = node.target.clone().unwrap_or_default();
        name = h.link_target(&name, &target).map_err(|d| Refusal::Unmodeled {
            symbol,
            detail: format!("the target of the symlink {name:?}: {d}"),
        })?;
    }
    Ok(Err(Errno::ELOOP))
}

/// The canonical spelling of a path a namespace call names, or the
/// refusal ([`Host::canonical_path`]).
fn named(h: &Host, path: &str, symbol: &'static str) -> Result<String, Refusal> {
    h.canonical_path(path).map_err(|detail| Refusal::Unmodeled { symbol, detail })
}

/// `open(2)` / `openat(2)` of a NAMED path ([`Call::OpenPath`]). MEASURED
/// (Darwin 25.6), in this order:
///
/// 1. bits outside [`darwin::OPEN_NAMED_MODELED_MASK`], fdesc paths and the
///    cloning devices are refused (an fdesc open is [`Call::OpenAlias`]);
/// 2. allocation: a full table is `EMFILE` before anything else is looked at
///    (a missing path, a bad `dirfd`, a FIFO with no reader, a lock conflict);
/// 3. `openat`'s `dirfd`, for a RELATIVE path only (an absolute path ignores
///    it, even a closed one): closed is `EBADF`, a pipe/socket/kqueue
///    `ENOTSUP`, a non-directory `ENOTDIR`; resolution relative to a real
///    directory is refused — the namespace is flat;
/// 4. the path's one spelling ([`Host::canonical_path`]; refused otherwise);
/// 5. the environment's failures (the oracle: permissions, the file system);
/// 6. the namespace: `O_CREAT|O_EXCL` on an existing name (a symlink
///    included) is `EEXIST`; symlinks are followed (`O_NOFOLLOW`: `ELOOP`);
///    an absent name is `ENOENT` unless `O_CREAT` creates a regular file;
/// 7. the node: a directory opened for writing or with `O_TRUNC` is `EISDIR`
///    (`O_CREAT` alone opens it); `O_DIRECTORY` on anything else is
///    `ENOTDIR`; a FIFO opened read-only waits for a writer and write-only
///    for a reader (`O_NONBLOCK`: the read side opens at once, the write side
///    fails `ENXIO`), read-write never waits — and a WAITING opener already
///    counts as a reader (writer) of the FIFO;
/// 8. `O_EXLOCK` / `O_SHLOCK` (both: exclusive) take the `flock` lock as part
///    of the open: `ENOTSUP` on a FIFO (after its `ENXIO`, or its wait), and
///    on an existing file a conflict fails `EAGAIN` under `O_NONBLOCK` with
///    NO descriptor allocated, or waits;
/// 9. the new description (the number allocated in 2, `FD_CLOEXEC` =
///    `O_CLOEXEC`) is open on the node, with the lock and `FHASLOCK` when one
///    was taken.
///
/// A call that does not return at once returns [`Ret::Pending`] with its
/// number RESERVED ([`InFlight::Open`]): a FIFO open waiting for its peer, a
/// lock open waiting for the lock, and an `O_CREAT` lock open that CREATED
/// the file — Darwin creates it and then takes the lock, so a racer can lock
/// the new file in between (MEASURED, 46 of 20000: `EAGAIN` with the file
/// left created). [`Call::Resume`] finishes it.
fn open_path(
    h: &mut Host,
    pid: Pid,
    at: Option<i32>,
    path: &str,
    flags: i32,
    oracle: Oracle,
) -> Result<SysResult, Refusal> {
    let symbol = if at.is_some() { "openat" } else { "open" };
    if let Some(names) = darwin::unmodeled_open_bits_in(flags, darwin::OPEN_NAMED_MODELED_MASK) {
        return Err(Refusal::Unmodeled { symbol, detail: format!("open flags {names}") });
    }
    let access = Access::from_open_flags(flags).ok_or_else(|| Refusal::Unmodeled {
        symbol,
        detail: format!("access mode {:#x}", flags & darwin::O_ACCMODE),
    })?;
    match crate::symbols::classify_open_path(path) {
        crate::symbols::OpenPath::FdAlias(n) => {
            return Err(Refusal::Unmodeled {
                symbol,
                detail: format!("{path:?} is fdesc's alias of descriptor {n} (Call::OpenAlias)"),
            });
        }
        crate::symbols::OpenPath::Refused(why) => {
            return Err(Refusal::Unmodeled { symbol, detail: format!("{path:?}: {why}") });
        }
        crate::symbols::OpenPath::DevNull | crate::symbols::OpenPath::Other => {}
    }
    let Some(fd) = h.lowest_free(pid, 0) else {
        return Ok(Err(Errno::EMFILE));
    };
    let relative_to_dirfd = at.is_some_and(|d| d != darwin::AT_FDCWD) && !path.starts_with('/');
    if let Some(d) = at
        && relative_to_dirfd
    {
        let e = match entry(h, pid, d) {
            Ok(e) => e,
            Err(err) => return Ok(Err(err)),
        };
        let o = h.ofd(e.ofd).ok_or(Refusal::Unmodeled { symbol, detail: "dangling".into() })?;
        match o.kind {
            OfdKind::PipeRead | OfdKind::PipeWrite | OfdKind::Socket { .. } | OfdKind::Kqueue => {
                return Ok(Err(Errno::ENOTSUP));
            }
            OfdKind::Opaque => {
                return Err(Refusal::Unmodeled {
                    symbol,
                    detail: "a dirfd of unknown kind (an environment-provided descriptor)".into(),
                });
            }
            OfdKind::File => match o.node.and_then(|n| h.node(n)).map(|n| n.kind) {
                Some(NodeKind::Directory) => {
                    return Err(Refusal::Unmodeled {
                        symbol,
                        detail: "resolution relative to a directory descriptor: the model's \
                                 namespace is flat"
                            .to_string(),
                    });
                }
                Some(_) => return Ok(Err(Errno::ENOTDIR)),
                None => {
                    return Err(Refusal::Unmodeled {
                        symbol,
                        detail: "a dirfd whose file the model does not know (an anonymous open)"
                            .to_string(),
                    });
                }
            },
        }
    }
    let path = named(h, path, symbol)?;
    if let Oracle::Fail(err) = oracle {
        return Ok(Err(err));
    }
    let creat = flags & darwin::O_CREAT != 0;
    if creat && flags & darwin::O_EXCL != 0 && h.name(&path).is_some() {
        return Ok(Err(Errno::EEXIST));
    }
    let (found, name) = match resolve(h, &path, flags, symbol)? {
        Ok(r) => r,
        Err(err) => return Ok(Err(err)),
    };
    let kind = match found {
        Some(n) => h.node(n).map_or(NodeKind::Regular, |node| node.kind),
        None if creat => NodeKind::Regular,
        None => return Ok(Err(Errno::ENOENT)),
    };
    let writes = access != Access::ReadOnly;
    if kind == NodeKind::Directory && (writes || flags & darwin::O_TRUNC != 0) {
        return Ok(Err(Errno::EISDIR));
    }
    if kind != NodeKind::Directory && flags & darwin::O_DIRECTORY != 0 {
        return Ok(Err(Errno::ENOTDIR));
    }
    let nonblock = flags & darwin::O_NONBLOCK != 0;
    let mut waits_for_peer = false;
    if kind == NodeKind::Fifo
        && let Some(n) = found
    {
        let (readers, writers) = h.fifo_parties(n, None);
        match access {
            Access::ReadOnly if !nonblock && !writers => waits_for_peer = true,
            Access::WriteOnly if !readers => {
                if nonblock {
                    return Ok(Err(Errno::ENXIO));
                }
                waits_for_peer = true;
            }
            _ => {}
        }
    }
    let lock = if flags & darwin::O_EXLOCK != 0 {
        Some(LockMode::Exclusive)
    } else if flags & darwin::O_SHLOCK != 0 {
        Some(LockMode::Shared)
    } else {
        None
    };
    if lock.is_some() && !kind.lockable() && !waits_for_peer {
        return Ok(Err(Errno::ENOTSUP));
    }
    let conflict = |h: &Host, n: NodeId| {
        lock.is_some_and(|want| h.ofds_on(n).any(|(_, o)| o.lock.is_some_and(|m| m.blocks(want))))
    };
    if let Some(n) = found
        && !waits_for_peer
        && nonblock
        && conflict(h, n)
    {
        return Ok(Err(Errno::EAGAIN));
    }
    let created = found.is_none();
    let node = match found {
        Some(n) => n,
        None => {
            let n = h.mint_node(Node { kind: NodeKind::Regular, target: None });
            h.bind_name(&name, n);
            n
        }
    };
    let mut o = Ofd::fresh(OfdKind::File, access, flags & darwin::OPEN_STATUS_MASK);
    o.node = Some(node);
    let cloexec = flags & darwin::O_CLOEXEC != 0;
    if waits_for_peer || (lock.is_some() && (created || conflict(h, node))) {
        table_proc_mut(h, pid)
            .inflight
            .insert(fd, InFlight::Open { ofd: o, cloexec, lock, nonblock });
        return Ok(Ok(Ret::Pending { fd }));
    }
    let id = h.mint_ofd(o);
    install(h, pid, fd, id, cloexec);
    if let Some(mode) = lock {
        grant(h, id, mode);
    }
    Ok(Ok(Ret::Int(i64::from(fd))))
}

/// End the in-flight call on `pid`'s `fd` without its effect (an `EINTR`, a
/// failed lock): a reserved number is free again, a pending open's node is
/// let go when nothing else keeps it.
fn abandon(h: &mut Host, pid: Pid, fd: i32) {
    let gone = h.proc_mut(pid).and_then(|p| p.inflight.remove(&fd));
    if let Some(InFlight::Open { ofd, .. }) = gone
        && let Some(n) = ofd.node
    {
        h.collect_node(n);
    }
}

/// [`Call::Resume`]: continue the call `pid`'s thread has in flight on `fd`.
///
/// * a FIFO open returns once the FIFO has its peer (a description or
///   another waiting open of the other side; the asker itself not counted),
///   then — with a lock bit — fails `ENOTSUP`;
/// * a lock open takes the lock: a conflict fails `EAGAIN` under
///   `O_NONBLOCK` (the number freed; a file the open created STAYS), else
///   waits;
/// * then the description is installed at the reserved number (with its
///   lock) and the number returned;
/// * a sleeping `flock` returns `0` once the lock is free, granting it on the
///   description it slept on.
///
/// The oracle's `EINTR` (a signal handler without `SA_RESTART`) ends a call
/// that still waits, with nothing changed but its reservation (MEASURED for
/// `flock`, the M2 model review's p7); a call that no longer waits cannot
/// take it ([`Refusal::Blocks`]: not this outcome here).
fn resume(h: &mut Host, pid: Pid, fd: i32, oracle: Oracle) -> Result<SysResult, Refusal> {
    let Some(f) = h.proc(pid).and_then(|p| p.inflight.get(&fd)).copied() else {
        return Err(Refusal::Unmodeled {
            symbol: "resume",
            detail: format!("no call of {pid:?} is in flight on descriptor {fd}"),
        });
    };
    let interrupted = oracle == Oracle::Fail(Errno::EINTR);
    match f {
        InFlight::Open { ofd, cloexec, lock, nonblock } => {
            let n = ofd.node.ok_or(Refusal::Unmodeled {
                symbol: "open",
                detail: "a pending open on no node".to_string(),
            })?;
            let kind = h.node(n).map(|x| x.kind).ok_or(Refusal::Unmodeled {
                symbol: "open",
                detail: "a pending open on a dropped node".to_string(),
            })?;
            if kind == NodeKind::Fifo {
                let (readers, writers) = h.fifo_parties(n, Some((pid, fd)));
                let ready = match ofd.access {
                    Access::ReadOnly => writers,
                    Access::WriteOnly => readers,
                    Access::ReadWrite => true,
                };
                if !ready {
                    if interrupted {
                        abandon(h, pid, fd);
                        return Ok(Err(Errno::EINTR));
                    }
                    return Err(Refusal::Blocks);
                }
                if lock.is_some() {
                    abandon(h, pid, fd);
                    return Ok(Err(Errno::ENOTSUP));
                }
            }
            if let Some(want) = lock
                && h.ofds_on(n).any(|(_, o)| o.lock.is_some_and(|m| m.blocks(want)))
            {
                if nonblock {
                    abandon(h, pid, fd);
                    return Ok(Err(Errno::EAGAIN));
                }
                if interrupted {
                    abandon(h, pid, fd);
                    return Ok(Err(Errno::EINTR));
                }
                return Err(Refusal::Blocks);
            }
            if interrupted {
                return Err(Refusal::Blocks);
            }
            table_proc_mut(h, pid).inflight.remove(&fd);
            let id = h.mint_ofd(ofd);
            install(h, pid, fd, id, cloexec);
            if let Some(mode) = lock {
                grant(h, id, mode);
            }
            Ok(Ok(Ret::Int(i64::from(fd))))
        }
        InFlight::Flock { ofd, want } => {
            if h.lock_blocker(ofd, want).is_some() {
                if interrupted {
                    abandon(h, pid, fd);
                    return Ok(Err(Errno::EINTR));
                }
                return Err(Refusal::Blocks);
            }
            if interrupted {
                return Err(Refusal::Blocks);
            }
            table_proc_mut(h, pid).inflight.remove(&fd);
            grant(h, ofd, want);
            Ok(Ok(Ret::Int(0)))
        }
    }
}

/// `fstat(2)`: the identity and file type of the node a named open reached
/// (MEASURED: two opens of one path, a `dup`, a `fork` child's copy and both
/// ends of a named FIFO stat alike; an unlinked file still stats). The
/// identity of a description the model has no node for is refused by name.
fn fstat(h: &Host, pid: Pid, fd: i32) -> Result<SysResult, Refusal> {
    let e = match entry(h, pid, fd) {
        Ok(e) => e,
        Err(err) => return Ok(Err(err)),
    };
    let o =
        h.ofd(e.ofd).ok_or(Refusal::Unmodeled { symbol: "fstat", detail: "dangling".into() })?;
    let why = match (o.kind, o.node) {
        (OfdKind::File, Some(n)) => {
            let node = h
                .node(n)
                .ok_or(Refusal::Unmodeled { symbol: "fstat", detail: "dropped node".into() })?;
            return Ok(Ok(Ret::Stat { node: u64::from(n.0), ftype: node.kind.mode() }));
        }
        (OfdKind::File, None) => {
            "a description whose file the model does not know (an anonymous open): two such \
             opens may be one node"
        }
        (OfdKind::PipeRead | OfdKind::PipeWrite, _) => "a pipe end's identity is not tracked",
        (OfdKind::Socket { .. }, _) => {
            "a socket's identity is not tracked (MEASURED: every AF_INET socket stats (dev, 0))"
        }
        (OfdKind::Kqueue, _) => "every kqueue stats as (0, 0) (MEASURED); not modeled",
        (OfdKind::Opaque, _) => "the description's kind is unknown",
    };
    Err(Refusal::Unmodeled { symbol: "fstat", detail: why.to_string() })
}

/// `mkfifo(3)`: `EEXIST` on an existing name (a symlink included); else a
/// fresh FIFO node under `path`.
fn mkfifo(h: &mut Host, path: &str, oracle: Oracle) -> Result<SysResult, Refusal> {
    let path = named(h, path, "mkfifo")?;
    if let Oracle::Fail(e) = oracle {
        return Ok(Err(e));
    }
    if h.name(&path).is_some() {
        return Ok(Err(Errno::EEXIST));
    }
    let n = h.mint_node(Node { kind: NodeKind::Fifo, target: None });
    h.bind_name(&path, n);
    Ok(Ok(Ret::Int(0)))
}

/// `unlink(2)`: `ENOENT` on an absent name, `EPERM` on a directory
/// (MEASURED); else the name goes and the node lives on while a description
/// is open on it (MEASURED: an unlinked FIFO's ends still stat alike, a new
/// open of the name is `ENOENT`). A symlink's own name is removed, not its
/// target's.
fn unlink(h: &mut Host, path: &str, oracle: Oracle) -> Result<SysResult, Refusal> {
    let path = named(h, path, "unlink")?;
    if let Oracle::Fail(e) = oracle {
        return Ok(Err(e));
    }
    let Some(n) = h.name(&path) else {
        return Ok(Err(Errno::ENOENT));
    };
    if h.node(n).is_some_and(|node| node.kind == NodeKind::Directory) {
        return Ok(Err(Errno::EPERM));
    }
    h.unbind_name(&path);
    Ok(Ok(Ret::Int(0)))
}

/// `symlink(2)`: `EEXIST` on an existing name; else a link node under `path`
/// whose target is `target`, kept as written (it need not exist; a relative
/// target is resolved against the link's directory when the link is
/// followed).
fn symlink(h: &mut Host, target: &str, path: &str, oracle: Oracle) -> Result<SysResult, Refusal> {
    let path = named(h, path, "symlink")?;
    if let Oracle::Fail(e) = oracle {
        return Ok(Err(e));
    }
    if h.name(&path).is_some() {
        return Ok(Err(Errno::EEXIST));
    }
    let n = h.mint_node(Node { kind: NodeKind::Symlink, target: Some(target.to_string()) });
    h.bind_name(&path, n);
    Ok(Ok(Ret::Int(0)))
}
