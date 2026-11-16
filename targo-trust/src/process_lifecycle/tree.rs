//! Process facts the stop path reads: the process tree under a root, the
//! members of a process group, and a process's identity (its start time, and
//! whether it is a zombie); and, for a bounded probe's streams, whether a
//! process holds a pipe's write end.
//!
//! The tree walk moved here from `pipeline/run.rs` with T5a (DECISION_QUEUE
//! "T5a"), unchanged, because the stop path is now its other reader: the CPU
//! sampler of the compiler watchdog still reads it from there.
//!
//! Every reader here answers from the KERNEL's record (`proc_pidinfo`,
//! `proc_pidfdinfo`, `proc_listchildpids`, `proc_listpgrppids` on macOS;
//! `/proc` on Linux).
//! Other targets have no walk and no identity, and the stop path degrades as
//! [`super::stop_tree`] documents.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#[cfg(any(target_os = "macos", target_os = "linux"))]
use std::ffi::OsStr;
#[cfg(any(target_os = "macos", target_os = "linux"))]
use std::path::Path;

/// Whether every required kernel observation completed. Zero observed members
/// says nothing when an observation failed or reached a bounded buffer.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum Observation {
    Complete,
    #[default]
    Unknown,
    Exhausted,
}

impl Observation {
    pub(crate) fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::Exhausted, _) | (_, Self::Exhausted) => Self::Exhausted,
            _ => Self::Complete,
        }
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReadKind {
    Identity,
    Tree,
    Group,
    Image,
}

#[cfg(test)]
thread_local! {
    static READ_FAULT: std::cell::Cell<Option<(ReadKind, Observation)>> = const { std::cell::Cell::new(None) };
}

/// Thread-local OS-observation fault; it never changes signal or ownership facts.
#[cfg(test)]
pub(crate) fn with_read_fault<T>(
    kind: ReadKind,
    fault: Observation,
    action: impl FnOnce() -> T,
) -> T {
    struct Reset(Option<(ReadKind, Observation)>);
    impl Drop for Reset {
        fn drop(&mut self) {
            READ_FAULT.with(|slot| slot.set(self.0));
        }
    }
    let _reset = Reset(READ_FAULT.with(|slot| slot.replace(Some((kind, fault)))));
    action()
}

#[cfg(test)]
fn injected(kind: ReadKind) -> Option<Observation> {
    READ_FAULT.with(|slot| slot.get().filter(|(read, _)| *read == kind).map(|(_, fault)| fault))
}

pub(crate) fn observe_group_leader(pid: u32) -> Result<bool, Observation> {
    #[cfg(unix)]
    {
        let pid =
            libc::pid_t::try_from(pid).ok().filter(|pid| *pid > 0).ok_or(Observation::Unknown)?;
        let group = unsafe { libc::getpgid(pid) };
        if group > 0 {
            return Ok(group == pid);
        }
        if std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH) {
            return Ok(false);
        }
    }
    #[cfg(not(unix))]
    let _ = pid;
    Err(Observation::Unknown)
}

/// True when `pid` leads a process group of its own -- the invariant
/// [`super::configure_own_group`] installs on every child this process owns.
///
/// It is checked in two places, for two different reasons.
///
/// Sampling: a child that failed to become group-leading would have inherited
/// OUR group, so the guard's whole model of the child is wrong, and the honest
/// reading is "no reading". It fails closed, which degrades to exactly the
/// output-only guard that shipped before.
///
/// Killing: `kill(-pgid, ...)` may only be aimed at a group LEADER's pid.
/// Pointed at a pid that merely belongs to a group it would signal whatever
/// group that pid happens to sit in -- including this process's own.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn leads_own_process_group(pgid: u32) -> bool {
    observe_group_leader(pgid).unwrap_or(false)
}

/// Every other target keeps exactly today's output-only behaviour, so it never
/// samples and never needs the invariant.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn leads_own_process_group(_pgid: u32) -> bool {
    false
}

/// Upper bound on the number of processes one sample or one kill will touch.
///
/// One `trustc` per job slot, plus whatever a compiler shells out to; 512 is
/// far past any real `-j`. Both the walk and the kill are bounded by it, so
/// neither can be made unbounded by a runaway fork inside the tree.
pub(crate) const MAX_PROCESS_TREE_MEMBERS: usize = 512;

/// The executable file name of the machine-wide memory-coordination daemon.
const TRUST_MEMORY_DAEMON_EXECUTABLE: &str = "trustd";

/// True when `pid` must never be sampled as compiler work or reached by the
/// stop path ([`super::stop_tree`]): it is (or may be) the machine-wide `trustd`.
///
/// `trustd` is the memory authority for EVERY verified build on the host. On
/// 2026-09-22 a group-directed signal killed it mid-epoch, its crash epoch was
/// left DIRTY, and every verified gate on the machine refused to start until an
/// operator recovered it. Since 41f912aa5f it is spawned into a process group
/// of its own, so no group kill here can reach it. The tree walk is different:
/// it follows parent edges across group boundaries on purpose, because cargo
/// puts every compiler in a group of its own. `targo trust` starts the daemon
/// itself, as a sibling of the driver, so the normal gate never meets it
/// inside the tree; a NESTED `targo trust` (a build script, a test) that
/// starts it would make it a descendant, and the walk would then have killed
/// the host's authority. So the walk neither includes it nor descends past it.
///
/// Identity is the KERNEL's record of the executable image (`proc_pidpath`,
/// `/proc/<pid>/exe`), never argv or `comm`, which a process sets for itself.
/// A process whose image cannot be read is treated as the daemon too: the
/// hard constraint is that no stop ever reaches `trustd`, and a same-user
/// descendant's image is always readable while it runs, so what this excludes
/// in practice is a process that has already exited.
#[cfg(target_os = "macos")]
pub(crate) fn observe_daemon(pid: u32) -> Result<bool, Observation> {
    use std::os::unix::ffi::OsStrExt as _;
    #[cfg(test)]
    if let Some(fault) = injected(ReadKind::Image) {
        return Err(fault);
    }
    let pid = libc::pid_t::try_from(pid).map_err(|_| Observation::Unknown)?;
    let mut path = [0u8; libc::PROC_PIDPATHINFO_MAXSIZE as usize];
    let capacity = u32::try_from(path.len()).map_err(|_| Observation::Unknown)?;
    let written = unsafe { libc::proc_pidpath(pid, path.as_mut_ptr().cast(), capacity) };
    let written = usize::try_from(written).map_err(|_| Observation::Unknown)?;
    if written >= path.len() {
        return Err(Observation::Exhausted);
    }
    if written == 0 || written > path.len() {
        return match observe_identity(pid as u32)? {
            None => Ok(true),
            Some(identity) if identity.zombie => Ok(true),
            _ => Err(Observation::Unknown),
        };
    }
    Ok(executable_is_trust_memory_daemon(std::path::Path::new(std::ffi::OsStr::from_bytes(
        &path[..written],
    ))))
}

#[cfg(target_os = "linux")]
pub(crate) fn observe_daemon(pid: u32) -> Result<bool, Observation> {
    #[cfg(test)]
    if let Some(fault) = injected(ReadKind::Image) {
        return Err(fault);
    }
    match std::fs::read_link(format!("/proc/{pid}/exe")) {
        Ok(image) => Ok(executable_is_trust_memory_daemon(&image)),
        Err(_) => match observe_identity(pid)? {
            None => Ok(true),
            Some(identity) if identity.zombie => Ok(true),
            _ => Err(Observation::Unknown),
        },
    }
}

#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn is_trust_memory_daemon(pid: u32) -> bool {
    observe_daemon(pid).unwrap_or(true)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn observe_daemon(_pid: u32) -> Result<bool, Observation> {
    Err(Observation::Unknown)
}

/// `/proc/<pid>/exe` renders a replaced image as `<path> (deleted)`; an
/// upgraded toolchain whose running `trustd` was unlinked is still the daemon.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn executable_is_trust_memory_daemon(image: &Path) -> bool {
    image.file_name().and_then(OsStr::to_str).is_some_and(|name| {
        name == TRUST_MEMORY_DAEMON_EXECUTABLE
            || name
                .strip_suffix(" (deleted)")
                .is_some_and(|name| name == TRUST_MEMORY_DAEMON_EXECUTABLE)
    })
}

/// Observe the process tree rooted at `root`, root first, breadth-first.
/// Incomplete observations retain any safely identified partial members for
/// cleanup. The machine-wide `trustd` and its subtree remain excluded.
///
/// `proc_listchildpids` is one syscall per visited process rather than the one
/// syscall `proc_listpgrppids` needed for a group, so this is O(processes in
/// the tree) instead of O(1). Measured against a live verified check on
/// 2026-09-09 with a 19-process tree: 143.1us min / 228.9us mean / 364.7us max
/// per sample over 200 repetitions, against 12.6us min / 13.9us mean for the
/// one-syscall group walk it replaces -- about 12us per member. At the shipped
/// 30s sampling interval that is 0.0008% of one core.
#[cfg(target_os = "macos")]
pub(crate) fn observe_process_tree(root: u32, out: &mut Vec<u32>) -> Observation {
    out.clear();
    #[cfg(test)]
    if let Some(fault) = injected(ReadKind::Tree) {
        return fault;
    }
    let Ok(root_pid) = libc::pid_t::try_from(root) else { return Observation::Unknown };
    if root_pid <= 0 {
        return Observation::Unknown;
    }
    out.push(root);
    // 2 KiB on the caller's stack, reused for every level of the walk, so an
    // enumeration allocates nothing beyond `out`'s own growth.
    let mut children = [0 as libc::pid_t; MAX_PROCESS_TREE_MEMBERS];
    let Ok(capacity) = libc::c_int::try_from(std::mem::size_of_val(&children)) else {
        return Observation::Unknown;
    };
    // Breadth-first over `out` itself: every pid appended is a pid still to be
    // asked for its children, so no second queue is needed. The cap bounds the
    // walk, and the duplicate check keeps a pid that appears twice -- which a
    // reparent racing the walk can produce -- from being expanded twice.
    let mut expanded = 0;
    while expanded < out.len() {
        let Ok(parent) = libc::pid_t::try_from(out[expanded]) else {
            return Observation::Unknown;
        };
        expanded += 1;
        children.fill(0);
        // Measured to return entries, not bytes. A full buffer or unexpected
        // entry is incomplete evidence, never an apparently empty tail.
        unsafe {
            *libc::__error() = 0;
        }
        let listed =
            unsafe { libc::proc_listchildpids(parent, children.as_mut_ptr().cast(), capacity) };
        let errno = std::io::Error::last_os_error().raw_os_error().unwrap_or(0);
        let mut listed_children = Vec::new();
        let observed = decode_pid_list(listed, errno, &children, &mut listed_children);
        for child in listed_children {
            let daemon = match observe_daemon(child) {
                Ok(daemon) => daemon,
                Err(fault) => return fault,
            };
            if !out.contains(&child) && !daemon {
                if out.len() >= MAX_PROCESS_TREE_MEMBERS {
                    return Observation::Exhausted;
                }
                out.push(child);
            }
        }
        if observed != Observation::Complete {
            return observed;
        }
    }
    Observation::Complete
}

/// The same walk over `/proc`. No syscall enumerates children here, so one
/// pass recovers every `(pid, ppid)` edge and the tree is walked over that
/// snapshot -- the scan, which is the expensive part, happens exactly once per
/// sample rather than once per level.
#[cfg(target_os = "linux")]
pub(crate) fn observe_process_tree(root: u32, out: &mut Vec<u32>) -> Observation {
    out.clear();
    #[cfg(test)]
    if let Some(fault) = injected(ReadKind::Tree) {
        return fault;
    }
    if root == 0 {
        return Observation::Unknown;
    }
    let Ok(entries) = std::fs::read_dir("/proc") else { return Observation::Unknown };
    let mut edges: Vec<(u32, u32)> = Vec::new();
    for entry in entries {
        let Ok(entry) = entry else { return Observation::Unknown };
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        if name.is_empty() || !name.bytes().all(|byte| byte.is_ascii_digit()) {
            continue;
        }
        let Ok(pid) = name.parse::<u32>() else { return Observation::Unknown };
        match read_linux_stat(pid) {
            Ok(Some(stat)) => edges.push((pid, stat.ppid)),
            Ok(None) => {}
            Err(fault) => return fault,
        }
    }
    out.push(root);
    let mut expanded = 0;
    while expanded < out.len() {
        let parent = out[expanded];
        expanded += 1;
        for &(pid, ppid) in &edges {
            if ppid == parent && pid > 0 && !out.contains(&pid) {
                match observe_daemon(pid) {
                    Ok(true) => continue,
                    Ok(false) => {}
                    Err(fault) => return fault,
                }
                if out.len() >= MAX_PROCESS_TREE_MEMBERS {
                    return Observation::Exhausted;
                }
                out.push(pid);
            }
        }
    }
    Observation::Complete
}

/// Windows would need `GetProcessTimes` plus a job-object or toolhelp walk to
/// recover the tree, and the remaining BSDs need a `sysctl` MIB this crate does
/// not model. None of that is added by this change, and "no reading" degrades
/// safely.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn observe_process_tree(_root: u32, out: &mut Vec<u32>) -> Observation {
    out.clear();
    Observation::Unknown
}

/// Compatibility readers receive no partial sample; cleanup uses the explicit
/// observation and may still stop the positively identified partial members.
pub(crate) fn collect_process_tree(root: u32, out: &mut Vec<u32>) -> bool {
    let complete = observe_process_tree(root, out) == Observation::Complete;
    if !complete {
        out.clear();
    }
    complete
}

/// What the kernel says about one process: when it started, and whether it has
/// already exited and waits to be reaped.
///
/// The start time is what makes a pid safe to signal later: a pid is recycled
/// once its process is reaped, and the recycled one has a later start. Every
/// signal the stop path sends to a process it did not just read is preceded by
/// a fresh read that must agree ([`still_running`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Identity {
    /// Microseconds since the epoch on macOS (`pbi_start_tvsec/usec`), clock
    /// ticks since boot on Linux (`/proc/<pid>/stat` field 22). Only ever
    /// compared with another reading of the same kind on the same host.
    pub(crate) start: u64,
    /// The process has exited and is not yet reaped: it can no longer run, so
    /// the stop path never counts it as running.
    pub(crate) zombie: bool,
}

/// Read a kernel identity. Only ESRCH/NotFound is absence; failed, partial or
/// unsupported reads are explicitly unknown, never evidence of an exited task.
#[cfg(target_os = "macos")]
pub(crate) fn observe_identity(pid: u32) -> Result<Option<Identity>, Observation> {
    #[cfg(test)]
    if let Some(fault) = injected(ReadKind::Identity) {
        return Err(fault);
    }
    let pid = libc::c_int::try_from(pid).ok().filter(|pid| *pid > 0).ok_or(Observation::Unknown)?;
    // SAFETY: `proc_bsdinfo` is a plain C struct of integers and byte arrays,
    // for which all-zero is a valid value.
    let mut info: libc::proc_bsdinfo = unsafe { std::mem::zeroed() };
    let size = libc::c_int::try_from(std::mem::size_of::<libc::proc_bsdinfo>())
        .map_err(|_| Observation::Unknown)?;
    // SAFETY: `info` is exactly `size` bytes, which is what PROC_PIDTBSDINFO
    // writes. The flavor also answers for a zombie (with `pbi_status` SZOMB),
    // which is how an exited, unreaped child is told apart from a running one.
    unsafe {
        *libc::__error() = 0;
    }
    let written =
        unsafe { libc::proc_pidinfo(pid, libc::PROC_PIDTBSDINFO, 0, (&raw mut info).cast(), size) };
    if written != size || info.pbi_pid != pid as u32 {
        return if written <= 0
            && std::io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH)
        {
            Ok(None)
        } else {
            Err(Observation::Unknown)
        };
    }
    Ok(Some(Identity {
        start: info.pbi_start_tvsec.saturating_mul(1_000_000).saturating_add(info.pbi_start_tvusec),
        zombie: info.pbi_status == libc::SZOMB,
    }))
}

#[cfg(target_os = "linux")]
pub(crate) fn observe_identity(pid: u32) -> Result<Option<Identity>, Observation> {
    #[cfg(test)]
    if let Some(fault) = injected(ReadKind::Identity) {
        return Err(fault);
    }
    Ok(read_linux_stat(pid)?.map(|stat| Identity { start: stat.start, zombie: stat.zombie }))
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn observe_identity(_pid: u32) -> Result<Option<Identity>, Observation> {
    Err(Observation::Unknown)
}

/// Existing diagnostic/sampling readers keep their optional reading API.
pub(crate) fn identity(pid: u32) -> Option<Identity> {
    observe_identity(pid).ok().flatten()
}

/// True when `pid` is a running process (not a zombie) whose start is
/// `expected_start`, or any start when that is `None`.
pub(crate) fn still_running(pid: u32, expected_start: Option<u64>) -> bool {
    observe_running(pid, expected_start).unwrap_or(false)
}

pub(crate) fn observe_running(pid: u32, expected_start: Option<u64>) -> Result<bool, Observation> {
    Ok(observe_identity(pid)?.is_some_and(|now| {
        !now.zombie && expected_start.is_none_or(|expected| expected == now.start)
    }))
}

/// Observe group members (including zombies), with explicit enumeration status.
#[cfg(target_os = "macos")]
pub(crate) fn observe_process_group(pgid: u32, out: &mut Vec<u32>) -> Observation {
    out.clear();
    #[cfg(test)]
    if let Some(fault) = injected(ReadKind::Group) {
        return fault;
    }
    let Ok(pgid) = libc::pid_t::try_from(pgid) else { return Observation::Unknown };
    if pgid <= 0 {
        return Observation::Unknown;
    }
    let mut members = [0 as libc::pid_t; MAX_PROCESS_TREE_MEMBERS];
    let Ok(capacity) = libc::c_int::try_from(std::mem::size_of_val(&members)) else {
        return Observation::Unknown;
    };
    // SAFETY: `members` is `capacity` bytes, which bounds what the call writes.
    unsafe {
        *libc::__error() = 0;
    }
    let listed = unsafe { libc::proc_listpgrppids(pgid, members.as_mut_ptr().cast(), capacity) };
    decode_pid_list(
        listed,
        std::io::Error::last_os_error().raw_os_error().unwrap_or(0),
        &members,
        out,
    )
}

#[cfg(target_os = "linux")]
pub(crate) fn observe_process_group(pgid: u32, out: &mut Vec<u32>) -> Observation {
    out.clear();
    #[cfg(test)]
    if let Some(fault) = injected(ReadKind::Group) {
        return fault;
    }
    linux_members(out, |stat| stat.pgrp == pgid)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn observe_process_group(_pgid: u32, out: &mut Vec<u32>) -> Observation {
    out.clear();
    Observation::Unknown
}

pub(crate) fn collect_process_group(pgid: u32, out: &mut Vec<u32>) -> bool {
    let complete = observe_process_group(pgid, out) == Observation::Complete;
    if !complete {
        out.clear();
    }
    complete
}

/// Every child of `parent`, exited-and-unreaped ones included, which
/// [`collect_process_tree`] leaves out (a zombie's image cannot be read, so
/// the walk treats it as the daemon; measured on macOS 26.6: `proc_pidpath`
/// and `PROC_PIDTBSDINFO` both answer ESRCH for a zombie). A reader's listing,
/// never a stop's: a bounded probe reads the groups these lead. `false` means
/// the children could not be listed.
#[cfg(target_os = "macos")]
fn observe_children(parent: u32, out: &mut Vec<u32>) -> Observation {
    out.clear();
    let Ok(parent) = libc::pid_t::try_from(parent) else { return Observation::Unknown };
    if parent <= 0 {
        return Observation::Unknown;
    }
    let mut children = [0 as libc::pid_t; MAX_PROCESS_TREE_MEMBERS];
    let Ok(capacity) = libc::c_int::try_from(std::mem::size_of_val(&children)) else {
        return Observation::Unknown;
    };
    // SAFETY: `children` is `capacity` bytes, which bounds what the call writes.
    unsafe {
        *libc::__error() = 0;
    }
    let listed =
        unsafe { libc::proc_listchildpids(parent, children.as_mut_ptr().cast(), capacity) };
    decode_pid_list(
        listed,
        std::io::Error::last_os_error().raw_os_error().unwrap_or(0),
        &children,
        out,
    )
}

#[cfg(target_os = "linux")]
fn observe_children(parent: u32, out: &mut Vec<u32>) -> Observation {
    out.clear();
    linux_members(out, |stat| stat.ppid == parent)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn observe_children(_parent: u32, out: &mut Vec<u32>) -> Observation {
    out.clear();
    Observation::Unknown
}

pub(crate) fn collect_children(parent: u32, out: &mut Vec<u32>) -> bool {
    let complete = observe_children(parent, out) == Observation::Complete;
    if !complete {
        out.clear();
    }
    complete
}

#[cfg(any(target_os = "macos", test))]
fn decode_pid_list(
    listed: i32,
    errno: i32,
    raw: &[libc::pid_t],
    out: &mut Vec<u32>,
) -> Observation {
    out.clear();
    if listed <= 0 {
        return if (listed == 0 && errno == 0) || errno == libc::ESRCH {
            Observation::Complete
        } else {
            Observation::Unknown
        };
    }
    let Ok(listed) = usize::try_from(listed) else { return Observation::Unknown };
    for &pid in &raw[..listed.min(raw.len())] {
        if pid == 0 {
            return Observation::Unknown;
        }
        let Ok(pid) = u32::try_from(pid) else { return Observation::Unknown };
        out.push(pid);
    }
    if listed >= raw.len() { Observation::Exhausted } else { Observation::Complete }
}

/// The write end of a pipe this process reads, as the kernel names it in
/// every process that holds it: what [`holds_pipe_writer`] looks for.
///
/// On macOS it is the write end's kernel handle, one value in every process
/// (`PROC_PIDFDPIPEINFO`: the read end's `pipe_peerhandle` is the write end's
/// `pipe_handle`). On Linux it is the pipe's `/proc/<pid>/fd` link,
/// `pipe:[<inode>]`, which both ends share; an end's access mode tells the
/// write end apart. Elsewhere no pipe end can be named, and the type has no
/// value.
#[derive(Debug)]
pub(crate) enum PipeWriter {
    #[cfg(target_os = "macos")]
    Handle(u64),
    #[cfg(target_os = "linux")]
    Link(std::path::PathBuf),
}

/// `struct pipe_fdinfo` (`<sys/proc_info.h>`), what `PROC_PIDFDPIPEINFO`
/// writes: the `proc_fileinfo` it opens with is read as opaque bytes.
#[cfg(target_os = "macos")]
#[repr(C)]
#[derive(Clone, Copy)]
struct PipeFdinfo {
    _pfi: [u64; 3],
    _pipe_stat: libc::vinfo_stat,
    pipe_handle: u64,
    pipe_peerhandle: u64,
    _pipe_status: libc::c_int,
    _rfu_1: libc::c_int,
}

/// `PROC_PIDFDPIPEINFO_SIZE` in the SDK: the layout above is the kernel's.
#[cfg(target_os = "macos")]
const _: () = assert!(std::mem::size_of::<PipeFdinfo>() == 184);

/// `<sys/proc_info.h>`: the flavor of `proc_pidfdinfo` that reads a pipe end.
#[cfg(target_os = "macos")]
const PROC_PIDFDPIPEINFO: libc::c_int = 6;

/// Descriptor `fd` of process `pid`, read as a pipe end; `None` when it is
/// not one or cannot be read.
#[cfg(target_os = "macos")]
fn pipe_fdinfo(pid: u32, fd: libc::c_int) -> Option<PipeFdinfo> {
    let pid = libc::c_int::try_from(pid).ok().filter(|pid| *pid > 0)?;
    // SAFETY: a plain C struct of integers, for which all-zero is valid.
    let mut info: PipeFdinfo = unsafe { std::mem::zeroed() };
    let size = libc::c_int::try_from(std::mem::size_of::<PipeFdinfo>()).ok()?;
    // SAFETY: `info` is exactly `size` bytes, which is what the flavor writes.
    let written =
        unsafe { libc::proc_pidfdinfo(pid, fd, PROC_PIDFDPIPEINFO, (&raw mut info).cast(), size) };
    (written == size).then_some(info)
}

/// The write end of the pipe whose read end this process holds as `read_end`;
/// `None` when it is no pipe or cannot be read.
#[cfg(target_os = "macos")]
pub(crate) fn pipe_writer_of(read_end: std::os::fd::RawFd) -> Option<PipeWriter> {
    let info = pipe_fdinfo(std::process::id(), read_end)?;
    Some(PipeWriter::Handle(info.pipe_peerhandle))
}

#[cfg(target_os = "linux")]
pub(crate) fn pipe_writer_of(read_end: std::os::fd::RawFd) -> Option<PipeWriter> {
    let link = std::fs::read_link(format!("/proc/self/fd/{read_end}")).ok()?;
    link.to_str()?.starts_with("pipe:[").then_some(PipeWriter::Link(link))
}

#[cfg(all(unix, not(any(target_os = "macos", target_os = "linux"))))]
pub(crate) fn pipe_writer_of(_read_end: std::os::fd::RawFd) -> Option<PipeWriter> {
    None
}

/// Whether process `pid` holds `writer` open now, read from its descriptor
/// table: `Some(false)` for a process that no longer runs (an exited process
/// holds nothing), `None` when a running one's table cannot be read in full.
#[cfg(target_os = "macos")]
pub(crate) fn holds_pipe_writer(pid: u32, writer: &PipeWriter) -> Option<bool> {
    let PipeWriter::Handle(handle) = *writer;
    let Ok(target) = libc::c_int::try_from(pid) else { return None };
    if target <= 0 {
        return None;
    }
    let entry = std::mem::size_of::<libc::proc_fdinfo>();
    // SAFETY: a null buffer of size 0 asks only for the size the listing needs.
    let needed =
        unsafe { libc::proc_pidinfo(target, libc::PROC_PIDLISTFDS, 0, std::ptr::null_mut(), 0) };
    let Some(room) = usize::try_from(needed).ok().filter(|&needed| needed > 0) else {
        return unreadable(pid);
    };
    // Room for descriptors opened between the two calls.
    let room = room / entry + 64;
    let mut entries = vec![libc::proc_fdinfo { proc_fd: -1, proc_fdtype: 0 }; room];
    let bytes = libc::c_int::try_from(room * entry).ok()?;
    // SAFETY: `entries` is `bytes` long, which bounds what the call writes.
    let written = unsafe {
        libc::proc_pidinfo(target, libc::PROC_PIDLISTFDS, 0, entries.as_mut_ptr().cast(), bytes)
    };
    let Some(listed) = usize::try_from(written).ok().filter(|&written| written > 0) else {
        return unreadable(pid);
    };
    let listed = listed / entry;
    if listed >= room {
        // Possibly cut off at the buffer's end: not a full listing.
        return None;
    }
    let pipe = u32::try_from(libc::PROX_FDTYPE_PIPE).ok()?;
    // A pipe end whose own read fails (closed since the listing, or the
    // process gone) proves nothing: the answer is then unknown while the
    // process runs, unless another entry is the write end.
    let mut unread = false;
    for entry in entries[..listed].iter().filter(|entry| entry.proc_fdtype == pipe) {
        match pipe_fdinfo(pid, entry.proc_fd) {
            Some(info) if info.pipe_handle == handle => return Some(true),
            Some(_) => {}
            None => unread = true,
        }
    }
    if unread { unreadable(pid) } else { Some(false) }
}

#[cfg(target_os = "linux")]
pub(crate) fn holds_pipe_writer(pid: u32, writer: &PipeWriter) -> Option<bool> {
    let PipeWriter::Link(pipe) = writer;
    let Ok(entries) = std::fs::read_dir(format!("/proc/{pid}/fd")) else {
        return unreadable(pid);
    };
    let mut unread = false;
    for entry in entries.flatten() {
        if std::fs::read_link(entry.path()).ok().as_ref() != Some(pipe) {
            continue;
        }
        // Both ends share the link: the end's `flags:` (octal) tell them
        // apart, O_WRONLY or O_RDWR in the access-mode bits being a writer.
        let flags = std::fs::read_to_string(format!(
            "/proc/{pid}/fdinfo/{}",
            entry.file_name().to_string_lossy()
        ))
        .ok()
        .and_then(|fdinfo| {
            fdinfo.lines().find_map(|line| {
                line.strip_prefix("flags:")
                    .and_then(|flags| u32::from_str_radix(flags.trim(), 8).ok())
            })
        });
        match flags {
            Some(flags) if flags & 0o3 != 0 => return Some(true),
            Some(_) => {}
            None => unread = true,
        }
    }
    (!unread).then_some(false)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn holds_pipe_writer(_pid: u32, writer: &PipeWriter) -> Option<bool> {
    match *writer {}
}

/// A process whose descriptors could not be listed: one that no longer runs
/// holds nothing; of one that runs, nothing can be said.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn unreadable(pid: u32) -> Option<bool> {
    (!still_running(pid, None)).then_some(false)
}

#[cfg(target_os = "linux")]
struct LinuxStat {
    ppid: u32,
    pgrp: u32,
    start: u64,
    zombie: bool,
}

/// `/proc/<pid>/stat`, read past the parenthesised `comm` (which may itself
/// contain spaces and `)`): field 3 state, 4 ppid, 5 pgrp, 22 starttime.
#[cfg(target_os = "linux")]
fn read_linux_stat(pid: u32) -> Result<Option<LinuxStat>, Observation> {
    if pid == 0 {
        return Err(Observation::Unknown);
    }
    let stat = match std::fs::read_to_string(format!("/proc/{pid}/stat")) {
        Ok(stat) => stat,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(_) => return Err(Observation::Unknown),
    };
    let tail = stat.rfind(')').and_then(|end| stat.get(end + 1..)).ok_or(Observation::Unknown)?;
    let fields: Vec<&str> = tail.split_ascii_whitespace().collect();
    let state = *fields.first().ok_or(Observation::Unknown)?;
    Ok(Some(LinuxStat {
        ppid: fields
            .get(1)
            .ok_or(Observation::Unknown)?
            .parse()
            .map_err(|_| Observation::Unknown)?,
        pgrp: fields
            .get(2)
            .ok_or(Observation::Unknown)?
            .parse()
            .map_err(|_| Observation::Unknown)?,
        start: fields
            .get(19)
            .ok_or(Observation::Unknown)?
            .parse()
            .map_err(|_| Observation::Unknown)?,
        zombie: matches!(state, "Z" | "X" | "x"),
    }))
}

#[cfg(target_os = "linux")]
fn linux_members(out: &mut Vec<u32>, include: impl Fn(&LinuxStat) -> bool) -> Observation {
    let Ok(entries) = std::fs::read_dir("/proc") else { return Observation::Unknown };
    for entry in entries {
        let Ok(entry) = entry else { return Observation::Unknown };
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        if name.is_empty() || !name.bytes().all(|byte| byte.is_ascii_digit()) {
            continue;
        }
        let Ok(pid) = name.parse() else { return Observation::Unknown };
        match read_linux_stat(pid) {
            Ok(Some(stat)) if include(&stat) => {
                if out.len() >= MAX_PROCESS_TREE_MEMBERS {
                    return Observation::Exhausted;
                }
                out.push(pid);
            }
            Ok(_) => {}
            Err(fault) => return fault,
        }
    }
    Observation::Complete
}

#[cfg(test)]
mod observation_tests {
    use super::*;

    #[test]
    fn failed_and_full_kernel_lists_are_not_complete_empty_observations() {
        let raw = [41, 42];
        let mut out = Vec::new();
        assert_eq!(decode_pid_list(-1, libc::EACCES, &raw, &mut out), Observation::Unknown);
        assert_eq!(decode_pid_list(0, libc::EPERM, &raw, &mut out), Observation::Unknown);
        assert_eq!(decode_pid_list(0, 0, &raw, &mut out), Observation::Complete);
        assert_eq!(decode_pid_list(0, libc::ESRCH, &raw, &mut out), Observation::Complete);
        assert_eq!(decode_pid_list(2, 0, &raw, &mut out), Observation::Exhausted);
        assert_eq!(out, [41, 42], "partial identities remain available for safe cleanup");
        assert_eq!(decode_pid_list(3, 0, &raw, &mut out), Observation::Exhausted);
        assert_eq!(decode_pid_list(1, 0, &[-1, 0], &mut out), Observation::Unknown);
    }

    #[test]
    fn unreadable_identity_is_distinct_from_absence_and_legacy_samples_refuse_partial_lists() {
        with_read_fault(ReadKind::Identity, Observation::Unknown, || {
            assert_eq!(observe_identity(std::process::id()), Err(Observation::Unknown));
            assert_eq!(observe_running(std::process::id(), None), Err(Observation::Unknown));
        });
        for fault in [Observation::Unknown, Observation::Exhausted] {
            with_read_fault(ReadKind::Group, fault, || {
                let mut out = vec![123];
                assert!(!collect_process_group(std::process::id(), &mut out));
                assert!(out.is_empty());
            });
        }
    }
}
