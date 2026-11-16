//! Native process observations. No interpreter, ps, pgrep or lsof subprocesses.

use std::ffi::OsString;
use std::io;
use std::path::PathBuf;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Process {
    pub pid: u32,
    pub parent: u32,
    pub group: u32,
    pub uid: u32,
    pub birth: u64,
    pub epoch_seconds: u64,
    pub name: OsString,
    pub zombie: bool,
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

/// Trust (TBT-WRITER-CENSUS-ARGV-EIO-1): an argv or cwd observation error
/// names the native call that failed, so a census refusal shows whether the
/// identity read around the query or the query itself refused. The error
/// kind is kept, and the errno stays with the inner error.
#[cfg(target_os = "macos")]
#[derive(Debug)]
struct Observed {
    call: &'static str,
    error: io::Error,
}

#[cfg(target_os = "macos")]
impl std::fmt::Display for Observed {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{}: {}", self.call, self.error)
    }
}

#[cfg(target_os = "macos")]
impl std::error::Error for Observed {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

#[cfg(target_os = "macos")]
fn in_call(call: &'static str) -> impl FnOnce(io::Error) -> io::Error {
    move |error| io::Error::new(error.kind(), Observed { call, error })
}

/// `proc_pidinfo` returns the bytes it wrote, or 0 with errno set. A short
/// positive count sets no errno, so it is its own error: reading errno then
/// would report whatever an earlier call left there. Every fixed-size
/// `proc_pidinfo` call `trust_repo_lock::management` makes itself outside
/// tests is decided here. The readers in the crates `trust-build-tree` links
/// under `machine-admission` and `native-exec` (`trust-resource-provenance`,
/// `jobserver_utils`, `trust-build-cpu`) decide their own counts, and none of
/// them reads errno after a short one.
#[cfg(target_os = "macos")]
pub(super) fn proc_info_count(
    count: libc::c_int,
    size: libc::c_int,
    incomplete: &'static str,
) -> io::Result<()> {
    if count == size {
        Ok(())
    } else if count <= 0 {
        Err(io::Error::last_os_error())
    } else {
        Err(invalid(incomplete))
    }
}

pub(crate) fn present(pid: u32) -> io::Result<bool> {
    let pid = i32::try_from(pid)
        .ok()
        .filter(|pid| *pid > 0)
        .ok_or_else(|| invalid("invalid positive process ID"))?;
    // SAFETY: signal zero observes existence without sending a signal.
    if unsafe { libc::kill(pid, 0) } == 0 {
        return Ok(true);
    }
    match io::Error::last_os_error().raw_os_error() {
        Some(libc::ESRCH) => Ok(false),
        Some(libc::EPERM) => Ok(true),
        _ => Err(io::Error::last_os_error()),
    }
}

/// A writer is gone only after confirmed absence or a current native zombie
/// observation. Holder/seed liveness has its separate actual-reap contract.
pub(crate) fn writer_gone(pid: u32) -> io::Result<bool> {
    if !present(pid)? {
        return Ok(true);
    }
    #[cfg(all(target_os = "macos", target_pointer_width = "64"))]
    {
        Ok(native_writer_state(pid)?.is_none_or(|(zombie, _)| zombie))
    }
    #[cfg(target_os = "linux")]
    {
        read(pid).map(|process| process.zombie)
    }
    #[cfg(not(any(target_os = "linux", all(target_os = "macos", target_pointer_width = "64"))))]
    {
        Err(io::Error::new(io::ErrorKind::Unsupported, "native writer state is unsupported"))
    }
}

/// Test-only faults, per thread and keyed by PID, so one test can fault several
/// processes. Installing one replaces that PID's fault until its guard drops,
/// which restores the previous one.
#[cfg(all(test, target_os = "macos"))]
mod fault {
    use std::cell::RefCell;
    use std::thread::LocalKey;

    pub(crate) type Table<T> = RefCell<Vec<(u32, T)>>;

    pub(crate) struct Guard<T: Copy + 'static> {
        table: &'static LocalKey<Table<T>>,
        pid: u32,
        previous: Option<T>,
    }

    pub(crate) fn install<T: Copy>(
        table: &'static LocalKey<Table<T>>,
        pid: u32,
        fault: T,
    ) -> Guard<T> {
        Guard { table, pid, previous: set(table, pid, Some(fault)) }
    }

    fn set<T: Copy>(table: &'static LocalKey<Table<T>>, pid: u32, fault: Option<T>) -> Option<T> {
        table.with_borrow_mut(|faults| {
            let previous = faults
                .iter()
                .position(|(expected, _)| *expected == pid)
                .map(|at| faults.remove(at).1);
            faults.extend(fault.map(|fault| (pid, fault)));
            previous
        })
    }

    /// This PID's answer from its fault, which `answer` may advance.
    pub(crate) fn answer<T: Copy, R>(
        table: &'static LocalKey<Table<T>>,
        pid: u32,
        answer: impl FnOnce(&mut T) -> Option<R>,
    ) -> Option<R> {
        table.with_borrow_mut(|faults| {
            faults.iter_mut().find(|(expected, _)| *expected == pid).and_then(|(_, at)| answer(at))
        })
    }

    impl<T: Copy + 'static> Drop for Guard<T> {
        fn drop(&mut self) {
            set(self.table, self.pid, self.previous);
        }
    }
}

/// How long a faulted PID reports exiting before it reports a zombie.
#[cfg(all(test, target_os = "macos", target_pointer_width = "64"))]
#[derive(Clone, Copy)]
pub(crate) enum Exiting {
    Reports(usize),
    Forever,
    /// From its first report.
    For(std::time::Duration, Option<std::time::Instant>),
}

#[cfg(all(test, target_os = "macos", target_pointer_width = "64"))]
thread_local! {
    static EXITING_FAULT: fault::Table<Exiting> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Test-only: on this thread, Darwin's state reads report `pid` exiting, then a
/// zombie.
#[cfg(all(test, target_os = "macos", target_pointer_width = "64"))]
pub(crate) type ExitingFault = fault::Guard<Exiting>;

/// A zombie after `exiting` reports, or never when `exiting` is `None`.
#[cfg(all(test, target_os = "macos", target_pointer_width = "64"))]
pub(crate) fn exiting_fault(pid: u32, exiting: Option<usize>) -> ExitingFault {
    fault::install(&EXITING_FAULT, pid, exiting.map_or(Exiting::Forever, Exiting::Reports))
}

/// A zombie once `span` has passed since the first report.
#[cfg(all(test, target_os = "macos", target_pointer_width = "64"))]
pub(crate) fn exiting_for(pid: u32, span: std::time::Duration) -> ExitingFault {
    fault::install(&EXITING_FAULT, pid, Exiting::For(span, None))
}

/// Darwin's exit state of a present PID: `None` once it is absent, else
/// (zombie, exiting). `exiting` is P_WEXIT, "working on exiting" in the public
/// <sys/proc.h>: the kernel has begun the exit, which a zombie has finished.
#[cfg(all(target_os = "macos", target_pointer_width = "64"))]
fn native_writer_state(pid: u32) -> io::Result<Option<(bool, bool)>> {
    const P_WEXIT: libc::c_int = 0x0000_2000;
    #[cfg(test)]
    if let Some(zombie) = fault::answer(&EXITING_FAULT, pid, |exiting| {
        Some(match exiting {
            Exiting::Forever => false,
            Exiting::Reports(0) => true,
            Exiting::Reports(left) => {
                *left -= 1;
                false
            }
            Exiting::For(span, first) => {
                first.get_or_insert_with(std::time::Instant::now).elapsed() >= *span
            }
        })
    }) {
        return Ok(Some((zombie, true)));
    }
    // Darwin libproc refuses both BSD-info flavors for unreaped zombies,
    // even while signal zero reports present. KERN_PROC_PID exports the
    // public <sys/proc.h> extern_proc prefix (also on x86_64).
    #[repr(C)]
    struct Prefix {
        _start_or_links: [u64; 2],
        _vmspace: usize,
        _sigacts: usize,
        flags: libc::c_int,
        state: libc::c_char,
        pid: libc::pid_t,
        _original_parent: libc::pid_t,
    }
    const { assert!(std::mem::size_of::<Prefix>() == 48) };
    let raw = i32::try_from(pid).map_err(|_| invalid("invalid writer PID"))?;
    let mut mib = [libc::CTL_KERN, libc::KERN_PROC, libc::KERN_PROC_PID, raw];
    let mut bytes = [0_u8; 65_536];
    let mut length = bytes.len();
    // SAFETY: writable bounded output and four initialized selector ints.
    let result = unsafe {
        libc::sysctl(
            mib.as_mut_ptr(),
            4,
            bytes.as_mut_ptr().cast(),
            &mut length,
            std::ptr::null_mut(),
            0,
        )
    };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    if length < std::mem::size_of::<Prefix>() || length > bytes.len() {
        return if !present(pid)? {
            Ok(None)
        } else {
            Err(invalid("native writer state is unavailable"))
        };
    }
    // SAFETY: sysctl initialized at least the public prefix. Copy without
    // alignment assumptions; all fields are plain integers, never pointers
    // we dereference or owner tokens reconstructed from kernel addresses.
    let prefix = unsafe { std::ptr::read_unaligned(bytes.as_ptr().cast::<Prefix>()) };
    if prefix.pid != raw {
        return Err(invalid("native writer state names a different PID"));
    }
    Ok(Some((prefix.state as u32 == libc::SZOMB, prefix.flags & P_WEXIT != 0)))
}

/// How long one writer census may spend, in all, waiting for exits Darwin
/// reports in progress. MEASURED on macOS (2026-11-09, Python test processes
/// and a Rust test binary, single runs): such exits took 0.3-1.7 ms bare, 22-38
/// ms with 2000 threads, under 130 ms with 8000; only an exit the kernel itself
/// held open (a socket lingering in close) took longer.
pub(crate) const CENSUS_EXIT_SETTLE: std::time::Duration = std::time::Duration::from_secs(2);

/// The exit wait one census has left. The census passes the same budget to
/// every `census_gone` it makes, which spends only the time it actually waits:
/// however many PIDs or observations are exiting, the census waits at most its
/// budget (plus one poll), and reading the PIDs it does not wait for spends none.
pub(crate) struct CensusSettle(std::cell::Cell<std::time::Duration>);

impl CensusSettle {
    /// A writer census's budget, `CENSUS_EXIT_SETTLE`.
    pub(crate) fn new() -> Self {
        Self::within(CENSUS_EXIT_SETTLE)
    }

    pub(crate) fn within(budget: std::time::Duration) -> Self {
        Self(std::cell::Cell::new(budget))
    }
}

/// Trust (LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)): a census's answer for a PID
/// whose observation failed. It omits a process exactly when `writer_gone`
/// does: confirmed absence or a native zombie. A process Darwin marks exiting
/// (P_WEXIT) but not yet a zombie is never omitted while it exits, since another
/// of its threads may still finish an in-kernel write; its exit is waited for
/// within the census's `settle` budget and judged by `writer_gone` again, so an
/// exit still in progress when the budget is spent stays unknown. MEASURED on
/// macOS (2026-11-09) for processes sampled after their one exec: under process
/// churn every BSD-info refusal of a present, non-zombie PID was such an exit
/// (a refusal during an exec was not sampled), and the census refused it when
/// the exit outlasted its identity retries (`native process identity <pid>: No
/// such process`). Adoption never sleeps and keeps `writer_gone`.
pub(crate) fn census_gone(pid: u32, settle: &CensusSettle) -> bool {
    if writer_gone(pid).unwrap_or(false) {
        return true;
    }
    #[cfg(all(target_os = "macos", target_pointer_width = "64"))]
    {
        let mut since = std::time::Instant::now();
        let mut spend = || {
            let now = std::time::Instant::now();
            let left = settle.0.get().saturating_sub(now - since);
            since = now;
            settle.0.set(left);
            left
        };
        while matches!(native_writer_state(pid), Ok(Some((false, true)))) {
            let left = spend();
            if left.is_zero() {
                return false;
            }
            std::thread::sleep(left.min(std::time::Duration::from_millis(1)));
        }
        spend();
        writer_gone(pid).unwrap_or(false)
    }
    #[cfg(not(all(target_os = "macos", target_pointer_width = "64")))]
    {
        let _ = settle;
        false
    }
}

/// A non-authoritative writer-census observation. Holder and seed identity
/// still use `read` and retain their separate actual-reap contracts.
pub(super) fn writer_identity(pid: u32, settle: &CensusSettle) -> io::Result<Option<Process>> {
    // Full BSD identity and the independent native liveness query are not
    // one atomic snapshot. After an exhausted identity read and a still-live
    // observation, obtain one fresh identity for this same PID. A new birth
    // is an ordinary current census entry, never the old holder's authority.
    // Persistent uncertainty is still an error; only positive native absence
    // or zombie state can omit an entry. Do not extend holder/seed semantics.
    for observation in 0..2 {
        match read(pid) {
            Ok(identity) => return Ok((!identity.zombie).then_some(identity)),
            Err(_) if census_gone(pid, settle) => return Ok(None),
            Err(error) if observation == 1 => return Err(error),
            Err(_) => {}
        }
    }
    unreachable!()
}

/// Final census bookend after argv/cwd. Only an independently observed absent
/// or zombie process is omitted; a changed/live-unknown original stays an error.
pub(super) fn writer_recheck(original: &Process, settle: &CensusSettle) -> io::Result<bool> {
    match writer_identity(original.pid, settle)? {
        None => Ok(false),
        Some(current) if current == *original => Ok(true),
        Some(_) => Err(invalid("writer changed during discovery")),
    }
}

#[cfg(target_os = "macos")]
pub(crate) fn read(pid: u32) -> io::Result<Process> {
    // A process transitioning through exec/exit can briefly deny BSD-info
    // observation while signal-zero still reports it present. Reobserve the
    // SAME native PID; never treat denied access as absence or skip it. A
    // persistent refusal remains an error and retains the original holder.
    for attempt in 0..3 {
        let observed = read_native(pid);
        if attempt == 2
            || !matches!(
                observed.as_ref().err().and_then(io::Error::raw_os_error),
                Some(libc::EPERM | libc::EACCES | libc::ESRCH | libc::ENOENT | libc::EIO)
            )
        {
            return observed;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    unreachable!()
}

/// Public process name/state for readiness, never a holder/birth identity.
/// Darwin intentionally exposes SHORTBSDINFO for processes whose full BSD
/// identity is protected. Request this limited observation directly, without
/// probing their argv, cwd, full birth record or debug/task information.
#[cfg(all(target_os = "macos", feature = "machine-admission"))]
pub(crate) fn readiness_name(pid: u32) -> io::Result<(OsString, bool)> {
    // A PID can be visible while exec/exit temporarily withholds short BSD
    // info. Reobserve that SAME PID, as the full identity reader already does.
    // Only an actual successful final kernel response yields name/state.
    for attempt in 0..3 {
        let observed = readiness_name_native(pid);
        if attempt == 2
            || !matches!(
                observed.as_ref().err().and_then(io::Error::raw_os_error),
                Some(libc::EPERM | libc::EACCES | libc::ESRCH | libc::ENOENT | libc::EIO)
            )
        {
            return observed;
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    unreachable!()
}

#[cfg(all(target_os = "macos", feature = "machine-admission"))]
fn readiness_name_native(pid: u32) -> io::Result<(OsString, bool)> {
    use std::os::unix::ffi::OsStringExt;
    #[cfg(test)]
    if let Some(errno) = fault::answer(&READY_FAULT, pid, |(remaining, errno)| {
        (*remaining != 0).then(|| {
            *remaining -= 1;
            *errno
        })
    }) {
        return Err(io::Error::from_raw_os_error(errno));
    }
    // Public sys/proc_info.h ABI. The leaf's pinned libc 0.2.186 predates
    // these bindings. All fields are fixed-width integers; no kernel address
    // or undocumented prefix is involved. Keep the complete 64-byte buffer.
    #[repr(C)]
    struct ShortBsdInfo {
        pid: u32,
        _parent: u32,
        _group: u32,
        status: u32,
        comm: [u8; 16],
        _flags_and_ids: [u32; 8],
    }
    const {
        assert!(std::mem::size_of::<ShortBsdInfo>() == 64);
        assert!(std::mem::align_of::<ShortBsdInfo>() == 4);
        assert!(std::mem::offset_of!(ShortBsdInfo, comm) == 16);
    }
    const SHORT_BSD_INFO: libc::c_int = 13;
    let raw = i32::try_from(pid)
        .ok()
        .filter(|pid| *pid > 0)
        .ok_or_else(|| invalid("invalid readiness PID"))?;
    let mut info = std::mem::MaybeUninit::<ShortBsdInfo>::zeroed();
    let size = std::mem::size_of::<ShortBsdInfo>() as i32;
    // SAFETY: exactly one writable public short-info structure; no pointers
    // from the record are followed and no stronger identity is reconstructed.
    let count =
        unsafe { libc::proc_pidinfo(raw, SHORT_BSD_INFO, 0, info.as_mut_ptr().cast(), size) };
    proc_info_count(count, size, "incomplete native readiness process observation")?;
    // SAFETY: the successful exact-size native call initialized every field.
    let info = unsafe { info.assume_init() };
    if info.pid != pid {
        return Err(invalid("native readiness process ID changed"));
    }
    let name = info.comm.into_iter().take_while(|byte| *byte != 0).collect();
    Ok((OsString::from_vec(name), info.status == libc::SZOMB))
}

#[cfg(all(test, target_os = "macos", feature = "machine-admission"))]
thread_local! {
    static READY_FAULT: fault::Table<(usize, i32)> = const { std::cell::RefCell::new(Vec::new()) };
}

#[cfg(all(test, target_os = "macos", feature = "machine-admission"))]
pub(crate) type ReadyFault = fault::Guard<(usize, i32)>;

#[cfg(all(test, target_os = "macos", feature = "machine-admission"))]
pub(crate) fn readiness_fault(pid: u32, attempts: usize, errno: i32) -> ReadyFault {
    fault::install(&READY_FAULT, pid, (attempts, errno))
}

#[cfg(all(target_os = "linux", feature = "machine-admission"))]
pub(crate) fn readiness_name(pid: u32) -> io::Result<(OsString, bool)> {
    read(pid).map(|process| (process.name, process.zombie))
}

// A PID's identity-read fault: reads to let through first, then reads to
// refuse with the errno.
#[cfg(all(test, target_os = "macos"))]
thread_local! {
    static READ_FAULT: fault::Table<(usize, usize, i32)> = const { std::cell::RefCell::new(Vec::new()) };
}

#[cfg(all(test, target_os = "macos"))]
pub(super) type ReadFault = fault::Guard<(usize, usize, i32)>;

#[cfg(all(test, target_os = "macos"))]
pub(super) fn read_fault(pid: u32, attempts: usize) -> ReadFault {
    read_errno_fault(pid, attempts, libc::EPERM)
}

#[cfg(all(test, target_os = "macos"))]
pub(super) fn read_errno_fault(pid: u32, attempts: usize, errno: i32) -> ReadFault {
    fault::install(&READ_FAULT, pid, (0, attempts, errno))
}

/// A PID's `proc_pidinfo` count fault: the next calls' counts, after the real
/// call, become `count`, with errno preset, so a test reaches the count rule
/// through the reader that calls it.
#[cfg(all(test, target_os = "macos"))]
type CountFault = fault::Table<(usize, libc::c_int, i32)>;

#[cfg(all(test, target_os = "macos"))]
thread_local! {
    static READ_COUNT_FAULT: CountFault = const { std::cell::RefCell::new(Vec::new()) };
    static CWD_COUNT_FAULT: CountFault = const { std::cell::RefCell::new(Vec::new()) };
}

#[cfg(all(test, target_os = "macos"))]
fn faulted_count(
    table: &'static std::thread::LocalKey<CountFault>,
    pid: u32,
) -> Option<libc::c_int> {
    fault::answer(table, pid, |(remaining, count, errno)| {
        (*remaining != 0).then(|| {
            *remaining -= 1;
            // SAFETY: __error returns this thread's errno location.
            unsafe { *libc::__error() = *errno };
            *count
        })
    })
}

#[cfg(target_os = "macos")]
fn read_native(pid: u32) -> io::Result<Process> {
    #[cfg(test)]
    if let Some(errno) = fault::answer(&READ_FAULT, pid, |(skip, remaining, errno)| {
        if *skip != 0 {
            *skip -= 1;
            return None;
        }
        (*remaining != 0).then(|| {
            *remaining -= 1;
            *errno
        })
    }) {
        return Err(io::Error::from_raw_os_error(errno));
    }
    use std::os::unix::ffi::OsStringExt;
    let raw = i32::try_from(pid)
        .ok()
        .filter(|pid| *pid > 0)
        .ok_or_else(|| invalid("invalid process ID"))?;
    let mut info = std::mem::MaybeUninit::<libc::proc_bsdinfo>::zeroed();
    let size = std::mem::size_of::<libc::proc_bsdinfo>() as i32;
    // SAFETY: the kernel receives exactly the writable BSD-info structure size.
    let count = unsafe {
        libc::proc_pidinfo(raw, libc::PROC_PIDTBSDINFO, 0, info.as_mut_ptr().cast(), size)
    };
    #[cfg(test)]
    let count = faulted_count(&READ_COUNT_FAULT, pid).unwrap_or(count);
    proc_info_count(count, size, "incomplete native process observation")?;
    // SAFETY: proc_pidinfo initialized the complete plain-data structure.
    let info = unsafe { info.assume_init() };
    if info.pbi_pid != pid {
        return Err(invalid("native process ID changed"));
    }
    let birth = info
        .pbi_start_tvsec
        .checked_mul(1_000_000)
        .and_then(|seconds| seconds.checked_add(info.pbi_start_tvusec))
        .filter(|birth| *birth != 0)
        .ok_or_else(|| invalid("invalid process birth"))?;
    Ok(Process {
        pid,
        parent: info.pbi_ppid,
        group: info.pbi_pgid,
        uid: info.pbi_uid,
        birth,
        epoch_seconds: info.pbi_start_tvsec,
        name: OsString::from_vec(
            info.pbi_comm.iter().map(|byte| *byte as u8).take_while(|byte| *byte != 0).collect(),
        ),
        zombie: info.pbi_status == libc::SZOMB,
    })
}

#[cfg(target_os = "macos")]
pub(super) fn all_pids() -> io::Result<Vec<u32>> {
    list_pids(Some(unsafe { libc::geteuid() }))
}

/// System PID census for readiness. This exposes no other account's argv/cwd.
#[cfg(all(target_os = "macos", feature = "machine-admission"))]
pub(crate) fn system_pids() -> io::Result<Vec<u32>> {
    list_pids(None)
}

#[cfg(target_os = "macos")]
fn list_pids(uid: Option<u32>) -> io::Result<Vec<u32>> {
    // PROC_UID_ONLY=4 and PROC_ALL_PIDS=1 are the public libproc ABI. Holder
    // discovery stays account-scoped; readiness lists only global PID/name
    // observations and never reads another account's argv/cwd.
    let (selector, argument) = uid.map_or((1, 0), |uid| (4, uid));
    list_selected_pids(selector, argument, true)
}

#[cfg(all(target_os = "macos", feature = "machine-admission"))]
pub(crate) fn group_pids(group: u32) -> io::Result<Vec<u32>> {
    if group == 0 || group > i32::MAX as u32 {
        return Err(invalid("invalid positive process group"));
    }
    // PROC_PGRP_ONLY=2 requests only public PID membership, never argv/cwd.
    list_selected_pids(2, group, false)
}

#[cfg(target_os = "macos")]
mod pid_list;
#[cfg(target_os = "macos")]
use pid_list::list_selected_pids;

#[cfg(target_os = "macos")]
pub(super) fn args(pid: u32) -> io::Result<Vec<OsString>> {
    let identity = read(pid).map_err(in_call("identity before argv"))?;
    for attempt in 0..3 {
        let observed = args_native(pid);
        let after = read(pid).map_err(in_call("identity after argv"))?;
        if identity.birth != after.birth || identity.uid != after.uid || after.zombie {
            return Err(invalid("process changed during native argv observation"));
        }
        if attempt == 2
            || !matches!(
                observed.as_ref().err().and_then(io::Error::raw_os_error),
                // KERN_PROCARGS2 can also return EINVAL across exec. Retry
                // only within this same bounded birth/UID-checked observation.
                Some(libc::EIO | libc::EPERM | libc::EACCES | libc::EINVAL)
            )
        {
            return observed.map_err(in_call("KERN_PROCARGS2"));
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    unreachable!()
}

#[cfg(all(test, target_os = "macos"))]
thread_local! {
    static ARGS_FAULT: std::cell::Cell<Option<(u32, usize, i32)>> = const { std::cell::Cell::new(None) };
}

#[cfg(all(test, target_os = "macos"))]
pub(super) struct ArgsFault(Option<(u32, usize, i32)>);
#[cfg(all(test, target_os = "macos"))]
pub(super) fn args_fault(pid: u32, attempts: usize, errno: i32) -> ArgsFault {
    ArgsFault(ARGS_FAULT.with(|fault| fault.replace(Some((pid, attempts, errno)))))
}
#[cfg(all(test, target_os = "macos"))]
impl Drop for ArgsFault {
    fn drop(&mut self) {
        ARGS_FAULT.with(|fault| fault.set(self.0));
    }
}

#[cfg(target_os = "macos")]
fn args_native(pid: u32) -> io::Result<Vec<OsString>> {
    #[cfg(test)]
    if let Some(errno) = ARGS_FAULT.with(|fault| match fault.get() {
        Some((expected, remaining, errno)) if expected == pid && remaining != 0 => {
            fault.set(Some((expected, remaining - 1, errno)));
            Some(errno)
        }
        _ => None,
    }) {
        return Err(io::Error::from_raw_os_error(errno));
    }
    use std::os::unix::ffi::OsStringExt;
    let raw = i32::try_from(pid).map_err(|_| invalid("invalid process ID"))?;
    let mut mib = [libc::CTL_KERN, libc::KERN_PROCARGS2, raw];
    let mut bytes = vec![0_u8; 1024 * 1024];
    let mut length = bytes.len();
    // SAFETY: mib has three elements; bytes is writable for length bytes.
    let result = unsafe {
        libc::sysctl(
            mib.as_mut_ptr(),
            3,
            bytes.as_mut_ptr().cast(),
            &mut length,
            std::ptr::null_mut(),
            0,
        )
    };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    bytes.truncate(length);
    parse_macos_args(&bytes).map(|args| args.into_iter().map(OsString::from_vec).collect())
}

#[cfg(any(target_os = "macos", test))]
fn parse_macos_args(bytes: &[u8]) -> io::Result<Vec<Vec<u8>>> {
    let count = i32::from_ne_bytes(
        bytes.get(..4).ok_or_else(|| invalid("missing argc"))?.try_into().unwrap(),
    );
    if !(1..=65536).contains(&count) {
        return Err(invalid("invalid native argc"));
    }
    let mut at = 4;
    let executable_end = bytes
        .get(at..)
        .and_then(|rest| rest.iter().position(|byte| *byte == 0))
        .ok_or_else(|| invalid("unterminated native executable"))?;
    at += executable_end;
    while bytes.get(at) == Some(&0) {
        at += 1;
    }
    let mut args = Vec::new();
    for _ in 0..count {
        let end = bytes
            .get(at..)
            .and_then(|rest| rest.iter().position(|byte| *byte == 0))
            .ok_or_else(|| invalid("truncated native argument vector"))?;
        args.push(bytes[at..at + end].to_vec());
        at += end + 1;
    }
    Ok(args)
}

#[cfg(target_os = "macos")]
pub(crate) fn cwd(pid: u32) -> io::Result<PathBuf> {
    // A vnode-query refusal does not establish that a live writer exited.
    // Reobserve only the same native PID/birth/UID, as argv already does.
    // No failed query is absence; persistent or changed identity still fails.
    let original = read(pid).map_err(in_call("identity before cwd"))?;
    for attempt in 0..3 {
        let observed = cwd_native(pid);
        let after = read(pid).map_err(in_call("identity after cwd"))?;
        if original.birth != after.birth || original.uid != after.uid || after.zombie {
            return Err(invalid("process changed during native cwd observation"));
        }
        if attempt == 2
            || !matches!(
                observed.as_ref().err().and_then(io::Error::raw_os_error),
                Some(libc::ESRCH | libc::ENOENT | libc::EIO | libc::EPERM | libc::EACCES)
            )
        {
            return observed.map_err(in_call("PROC_PIDVNODEPATHINFO"));
        }
        std::thread::sleep(std::time::Duration::from_millis(10));
    }
    unreachable!()
}

#[cfg(target_os = "macos")]
fn cwd_native(pid: u32) -> io::Result<PathBuf> {
    #[cfg(test)]
    if let Some(errno) = CWD_FAULT.with(|fault| match fault.get() {
        Some((expected, remaining, errno)) if expected == pid && remaining != 0 => {
            fault.set(Some((expected, remaining - 1, errno)));
            Some(errno)
        }
        _ => None,
    }) {
        return Err(io::Error::from_raw_os_error(errno));
    }
    use std::os::unix::ffi::OsStringExt;
    let raw = i32::try_from(pid).map_err(|_| invalid("invalid process ID"))?;
    let mut info = std::mem::MaybeUninit::<libc::proc_vnodepathinfo>::zeroed();
    let size = std::mem::size_of::<libc::proc_vnodepathinfo>() as i32;
    // SAFETY: the entire vnode-path structure is writable for size bytes.
    let count = unsafe {
        libc::proc_pidinfo(raw, libc::PROC_PIDVNODEPATHINFO, 0, info.as_mut_ptr().cast(), size)
    };
    #[cfg(test)]
    let count = faulted_count(&CWD_COUNT_FAULT, pid).unwrap_or(count);
    proc_info_count(count, size, "incomplete native working-directory observation")?;
    // SAFETY: proc_pidinfo initialized the full plain-data record.
    let info = unsafe { info.assume_init() };
    let bytes: Vec<u8> = info
        .pvi_cdir
        .vip_path
        .iter()
        .flatten()
        .map(|byte| *byte as u8)
        .take_while(|byte| *byte != 0)
        .collect();
    if bytes.is_empty() {
        return Err(invalid("native working directory is unavailable"));
    }
    Ok(PathBuf::from(OsString::from_vec(bytes)))
}

#[cfg(all(test, target_os = "macos"))]
thread_local! {
    static CWD_FAULT: std::cell::Cell<Option<(u32, usize, i32)>> = const { std::cell::Cell::new(None) };
}

#[cfg(all(test, target_os = "macos"))]
pub(super) struct CwdFault(Option<(u32, usize, i32)>);
#[cfg(all(test, target_os = "macos"))]
impl CwdFault {
    pub(super) fn install(pid: u32, remaining: usize, errno: i32) -> Self {
        Self(CWD_FAULT.with(|fault| fault.replace(Some((pid, remaining, errno)))))
    }
}
#[cfg(all(test, target_os = "macos"))]
impl Drop for CwdFault {
    fn drop(&mut self) {
        CWD_FAULT.with(|fault| fault.set(self.0));
    }
}

#[cfg(target_os = "linux")]
pub(crate) fn read(pid: u32) -> io::Result<Process> {
    use std::os::unix::ffi::OsStringExt;
    use std::os::unix::fs::MetadataExt;
    let bytes = std::fs::read(format!("/proc/{pid}/stat"))?;
    let left =
        bytes.iter().position(|byte| *byte == b'(').ok_or_else(|| invalid("invalid proc stat"))?;
    let right =
        bytes.iter().rposition(|byte| *byte == b')').ok_or_else(|| invalid("invalid proc stat"))?;
    let fields: Vec<&str> = std::str::from_utf8(&bytes[right + 1..])
        .map_err(|_| invalid("invalid proc fields"))?
        .split_whitespace()
        .collect();
    let number = |index: usize| -> io::Result<u64> {
        fields
            .get(index)
            .and_then(|value| value.parse().ok())
            .ok_or_else(|| invalid("missing proc field"))
    };
    let birth = number(19)?;
    let stat = std::fs::read_to_string("/proc/stat")?;
    let boot: u64 = stat
        .lines()
        .find_map(|line| line.strip_prefix("btime "))
        .and_then(|value| value.parse().ok())
        .ok_or_else(|| invalid("missing kernel boot time"))?;
    // SAFETY: sysconf reads the kernel clock-tick frequency.
    let ticks = unsafe { libc::sysconf(libc::_SC_CLK_TCK) };
    if ticks <= 0 {
        return Err(invalid("invalid kernel clock ticks"));
    }
    Ok(Process {
        pid,
        parent: number(1)?.try_into().map_err(|_| invalid("invalid parent"))?,
        group: number(2)?.try_into().map_err(|_| invalid("invalid group"))?,
        uid: std::fs::metadata(format!("/proc/{pid}"))?.uid(),
        birth,
        epoch_seconds: boot
            .checked_add(birth / ticks as u64)
            .ok_or_else(|| invalid("invalid start time"))?,
        name: OsString::from_vec(bytes[left + 1..right].to_vec()),
        zombie: fields.first() == Some(&"Z"),
    })
}

#[cfg(target_os = "linux")]
pub(super) fn all_pids() -> io::Result<Vec<u32>> {
    list_pids(Some(unsafe { libc::geteuid() }))
}

#[cfg(all(target_os = "linux", feature = "machine-admission"))]
pub(crate) fn system_pids() -> io::Result<Vec<u32>> {
    list_pids(None)
}

#[cfg(target_os = "linux")]
fn list_pids(uid: Option<u32>) -> io::Result<Vec<u32>> {
    use std::os::unix::fs::MetadataExt;
    let mut pids = Vec::new();
    for entry in std::fs::read_dir("/proc")? {
        let entry = entry?;
        if let Some(pid) = entry.file_name().to_str().and_then(|name| name.parse::<u32>().ok()) {
            let metadata = match std::fs::metadata(entry.path()) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
                Err(error) => return Err(error),
            };
            if uid.is_some_and(|uid| metadata.uid() != uid) {
                continue;
            }
            pids.push(pid);
            if pids.len() > 1_000_000 {
                return Err(invalid("native process table exceeds its bound"));
            }
        }
    }
    if !pids.contains(&std::process::id()) {
        return Err(invalid("native account process table omitted the observer"));
    }
    Ok(pids)
}

#[cfg(all(target_os = "linux", feature = "machine-admission"))]
pub(crate) fn group_pids(group: u32) -> io::Result<Vec<u32>> {
    if group == 0 || group > i32::MAX as u32 {
        return Err(invalid("invalid positive process group"));
    }
    let mut members = Vec::new();
    for pid in system_pids()? {
        match read(pid) {
            Ok(process) if process.group == group => members.push(pid),
            Ok(_) => {}
            Err(error) => {
                if present(pid)? {
                    return Err(error);
                }
            }
        }
    }
    Ok(members)
}

#[cfg(target_os = "linux")]
pub(super) fn args(pid: u32) -> io::Result<Vec<OsString>> {
    use std::io::Read;
    use std::os::unix::ffi::OsStringExt;
    let mut bytes = Vec::new();
    std::fs::File::open(format!("/proc/{pid}/cmdline"))?
        .take(1024 * 1024 + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() > 1024 * 1024 || bytes.last() != Some(&0) {
        return Err(invalid("native argv is unavailable or exceeds its bound"));
    }
    bytes.pop();
    Ok(bytes.split(|byte| *byte == 0).map(|arg| OsString::from_vec(arg.to_vec())).collect())
}

#[cfg(target_os = "linux")]
pub(crate) fn cwd(pid: u32) -> io::Result<PathBuf> {
    std::fs::read_link(format!("/proc/{pid}/cwd"))
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn read(_: u32) -> io::Result<Process> {
    Err(unsupported())
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(super) fn all_pids() -> io::Result<Vec<u32>> {
    Err(unsupported())
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(super) fn args(_: u32) -> io::Result<Vec<OsString>> {
    Err(unsupported())
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
pub(crate) fn cwd(_: u32) -> io::Result<PathBuf> {
    Err(unsupported())
}
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn unsupported() -> io::Error {
    io::Error::new(io::ErrorKind::Unsupported, "native build-tree process reader is unavailable")
}

/// Identity used by the existing build-slot adoption records. Exec and UID
/// changes do not retire a birth. An unavailable native observation is an
/// error; only a zombie or independently confirmed absence is gone.
#[cfg(any(target_os = "macos", target_os = "linux"))]
pub(crate) fn live_adoption_birth(pid: u32) -> io::Result<Option<String>> {
    // Admission holds original path/queue locks. Never use the writer
    // observer's sleeping startup retry here: an unavailable snapshot retains
    // debt immediately and the coordinator releases its partial claim.
    #[cfg(target_os = "macos")]
    let observe = read_native;
    #[cfg(target_os = "linux")]
    let observe = read;
    let before = match observe(pid) {
        Ok(process) => process,
        Err(error) => return if writer_gone(pid).unwrap_or(false) { Ok(None) } else { Err(error) },
    };
    if before.zombie {
        return Ok(None);
    }
    #[cfg(target_os = "macos")]
    let birth = format!("darwin:{}:{}", before.birth / 1_000_000, before.birth % 1_000_000);
    #[cfg(target_os = "linux")]
    let birth = {
        use std::io::Read;
        let mut bytes = Vec::new();
        std::fs::File::open("/proc/sys/kernel/random/boot_id")?
            .take(129)
            .read_to_end(&mut bytes)?;
        let boot =
            std::str::from_utf8(&bytes).map_err(|_| invalid("invalid kernel boot ID"))?.trim();
        if boot.len() != 36
            || !boot.bytes().enumerate().all(|(i, byte)| {
                if [8, 13, 18, 23].contains(&i) { byte == b'-' } else { byte.is_ascii_hexdigit() }
            })
        {
            return Err(invalid("invalid kernel boot ID"));
        }
        format!("linux:{boot}:{}", before.birth)
    };
    let after = match observe(pid) {
        Ok(process) => process,
        Err(error) => return if writer_gone(pid).unwrap_or(false) { Ok(None) } else { Err(error) },
    };
    if after.zombie {
        return Ok(None);
    }
    if before.birth != after.birth || before.uid != after.uid {
        return Err(invalid("process changed during native adoption observation"));
    }
    Ok(Some(birth))
}

pub(super) fn utc_start(seconds: u64) -> io::Result<String> {
    let seconds: libc::time_t = seconds.try_into().map_err(|_| invalid("invalid epoch"))?;
    let mut time = std::mem::MaybeUninit::<libc::tm>::zeroed();
    // SAFETY: gmtime_r writes one tm for the provided representable epoch.
    if unsafe { libc::gmtime_r(&seconds, time.as_mut_ptr()) }.is_null() {
        return Err(invalid("unrepresentable UTC process start"));
    }
    // SAFETY: successful gmtime_r initialized time.
    let time = unsafe { time.assume_init() };
    let day = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
        .get(time.tm_wday as usize)
        .ok_or_else(|| invalid("invalid weekday"))?;
    let month =
        ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
            .get(time.tm_mon as usize)
            .ok_or_else(|| invalid("invalid month"))?;
    Ok(format!(
        "{day} {month} {:2} {:02}:{:02}:{:02} {}",
        time.tm_mday,
        time.tm_hour,
        time.tm_min,
        time.tm_sec,
        time.tm_year + 1900
    ))
}

pub(super) fn descendant(child: &Process, ancestor: &Process) -> io::Result<bool> {
    let mut current = child.clone();
    let mut seen = std::collections::BTreeSet::new();
    for _ in 0..64 {
        if current.pid == ancestor.pid {
            return Ok(current.birth == ancestor.birth);
        }
        if current.parent <= 1 || !seen.insert(current.pid) {
            return Ok(false);
        }
        let parent = read(current.parent)?;
        if read(current.pid)? != current || parent.epoch_seconds > current.epoch_seconds {
            return Err(invalid("process ancestry changed during observation"));
        }
        current = parent;
    }
    Err(invalid("process ancestry exceeds its observation bound"))
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, Instant};

    use super::*;

    /// The native call an argv or cwd observation error names, and its error.
    #[cfg(target_os = "macos")]
    fn named(error: &io::Error) -> (&'static str, &io::Error) {
        let observed = error
            .get_ref()
            .and_then(|inner| inner.downcast_ref::<Observed>())
            .unwrap_or_else(|| panic!("names no native call: {error}"));
        assert_eq!(error.kind(), observed.error.kind());
        assert_eq!(error.to_string(), format!("{}: {}", observed.call, observed.error));
        (observed.call, &observed.error)
    }

    /// The native call an argv or cwd observation error names, and its errno.
    #[cfg(target_os = "macos")]
    fn call_and_errno(error: &io::Error) -> (&'static str, i32) {
        let (call, inner) = named(error);
        (call, inner.raw_os_error().expect("an errno"))
    }

    #[cfg(target_os = "macos")]
    fn read_errno_fault_after(pid: u32, skip: usize, attempts: usize, errno: i32) -> ReadFault {
        fault::install(&READ_FAULT, pid, (skip, attempts, errno))
    }

    /// Trust (TBT-WRITER-CENSUS-ARGV-EIO-1): through the identity and cwd
    /// readers, a short count is an error with no errno, though errno holds a
    /// value both retry; it is not retried, since the retry would see the full
    /// count and succeed.
    #[cfg(target_os = "macos")]
    #[test]
    fn a_short_count_through_the_identity_and_cwd_readers_is_no_errno_and_no_retry() {
        let pid = std::process::id();
        {
            let _fault = fault::install(&READ_COUNT_FAULT, pid, (1, 16, libc::EIO));
            let error = read(pid).unwrap_err();
            assert_eq!((error.kind(), error.raw_os_error()), (io::ErrorKind::InvalidData, None));
            assert_eq!(error.to_string(), "incomplete native process observation");
        }
        {
            let _fault = fault::install(&CWD_COUNT_FAULT, pid, (1, 16, libc::EIO));
            let error = cwd(pid).unwrap_err();
            let (call, inner) = named(&error);
            assert_eq!(call, "PROC_PIDVNODEPATHINFO");
            assert_eq!((inner.kind(), inner.raw_os_error()), (io::ErrorKind::InvalidData, None));
            assert_eq!(inner.to_string(), "incomplete native working-directory observation");
        }
        assert!(read(pid).is_ok() && cwd(pid).is_ok());
    }

    /// Trust (TBT-WRITER-CENSUS-ARGV-EIO-1): the identity read after the argv
    /// or cwd query names itself, apart from the read before it.
    #[cfg(target_os = "macos")]
    #[test]
    fn argv_and_cwd_errors_name_the_identity_read_after_the_query() {
        let pid = std::process::id();
        {
            let _fault = read_errno_fault_after(pid, 1, 3, libc::EIO);
            let error = args(pid).unwrap_err();
            assert_eq!(call_and_errno(&error), ("identity after argv", libc::EIO));
        }
        {
            let _fault = read_errno_fault_after(pid, 1, 3, libc::EIO);
            let error = cwd(pid).unwrap_err();
            assert_eq!(call_and_errno(&error), ("identity after cwd", libc::EIO));
        }
        assert!(args(pid).is_ok() && cwd(pid).is_ok());
    }

    /// Trust (TBT-WRITER-CENSUS-ARGV-EIO-1): a short positive `proc_pidinfo`
    /// count sets no errno, so it must not report the errno an earlier call
    /// left; a zero count reports errno, and the full size is success.
    #[cfg(target_os = "macos")]
    #[test]
    fn a_short_proc_info_count_never_reports_a_stale_errno() {
        // SAFETY: __error returns this thread's errno location.
        unsafe { *libc::__error() = libc::EIO };
        let short = proc_info_count(16, 64, "incomplete test observation").unwrap_err();
        assert_eq!(short.raw_os_error(), None);
        assert_eq!(short.kind(), io::ErrorKind::InvalidData);
        assert_eq!(short.to_string(), "incomplete test observation");
        // SAFETY: as above.
        unsafe { *libc::__error() = libc::EIO };
        assert_eq!(proc_info_count(0, 64, "unused").unwrap_err().raw_os_error(), Some(libc::EIO));
        assert!(proc_info_count(64, 64, "unused").is_ok());
    }

    /// Trust (TBT-WRITER-CENSUS-ARGV-EIO-1): a persistent identity refusal
    /// around the argv or cwd query is told apart from the query's own.
    #[cfg(target_os = "macos")]
    #[test]
    fn argv_and_cwd_errors_name_the_identity_read_that_refused() {
        let pid = std::process::id();
        for errno in [libc::EIO, libc::EPERM] {
            {
                let _fault = read_errno_fault(pid, 3, errno);
                let error = args(pid).unwrap_err();
                assert_eq!(call_and_errno(&error), ("identity before argv", errno));
            }
            {
                let _fault = read_errno_fault(pid, 3, errno);
                let error = cwd(pid).unwrap_err();
                assert_eq!(call_and_errno(&error), ("identity before cwd", errno));
            }
        }
        assert!(args(pid).is_ok() && cwd(pid).is_ok());
    }
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn actual_native_zombie_is_not_a_writer_but_remains_present_until_reaped() {
        use std::time::{Duration, Instant};
        struct Owned(std::process::Child);
        impl Drop for Owned {
            fn drop(&mut self) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
        assert!(!writer_gone(std::process::id()).unwrap());
        let mut child = Owned(std::process::Command::new("/usr/bin/true").spawn().unwrap());
        let pid = child.0.id();
        let deadline = Instant::now() + Duration::from_secs(5);
        while !writer_gone(pid).unwrap() {
            assert!(Instant::now() < deadline, "owned child never became a native zombie");
            std::thread::sleep(Duration::from_millis(1));
        }
        assert!(present(pid).unwrap(), "unreaped child is still present");
        assert!(live_adoption_birth(pid).unwrap().is_none());
        assert!(child.0.wait().unwrap().success());
        assert!(!present(pid).unwrap());
    }
    #[cfg(target_os = "macos")]
    #[test]
    fn native_identity_transient_absence_is_reobserved_and_persistent_refusal_is_not_death() {
        let pid = std::process::id();
        let original = read(pid).unwrap();
        for errno in [libc::ESRCH, libc::ENOENT, libc::EIO, libc::EPERM, libc::EACCES] {
            {
                let _fault = read_errno_fault(pid, 2, errno);
                assert_eq!(read(pid).unwrap(), original);
            }
            {
                let _fault = read_errno_fault(pid, 3, errno);
                assert_eq!(read(pid).unwrap_err().raw_os_error(), Some(errno));
                assert!(present(pid).unwrap());
            }
        }
    }

    /// Trust (LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)): runs `check` on an actual
    /// child (this test binary, re-run as the test named `test`) while Darwin
    /// holds its exit open. The kernel's exit closes a TCP socket that has
    /// unsent data and SO_LINGER ("in ticks" per <sys/socket.h>; a tick is
    /// 1/hz s, 10 ms at this kernel's hz of 100), so the child stays exiting
    /// (P_WEXIT, not a zombie, its BSD identity refused) for about `ticks`
    /// ticks (MEASURED on macOS 2026-11-09: 20 ms for 2, and 1.0 s with
    /// SO_LINGER_SEC 1 in 20 of 20 runs). Keep it short and opt-in: every
    /// census on this machine meets the held exit, and one older than this
    /// fix refuses it. In that child this is the actor, and it does not return.
    #[cfg(all(target_os = "macos", target_pointer_width = "64"))]
    fn with_held_exit(test: &str, ticks: libc::c_int, check: impl FnOnce(u32)) {
        use std::io::Write;
        use std::os::fd::AsRawFd;
        const ROLE: &str = "TRUST_BUILD_TREE_HELD_EXIT_ACTOR";
        if let Some(port) = std::env::var_os(ROLE) {
            let port: u16 = port.to_str().unwrap().parse().unwrap();
            let mut stream = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
            stream.set_nonblocking(true).unwrap();
            let chunk = [0_u8; 65_536];
            let mut fill = || {
                let mut sent = 0;
                loop {
                    match stream.write(&chunk) {
                        Ok(written) => sent += written,
                        Err(error) if error.kind() == io::ErrorKind::WouldBlock => return sent,
                        Err(error) => panic!("held-exit actor write: {error}"),
                    }
                }
            };
            // Fill until a write after a pause makes no progress: the peer's
            // window is closed and data stays unsent (MEASURED: a single fill
            // let the exit end without lingering in 2 of 20 runs).
            fill();
            loop {
                std::thread::sleep(Duration::from_millis(20));
                if fill() == 0 {
                    break;
                }
            }
            stream.set_nonblocking(false).unwrap();
            let value = libc::linger { l_onoff: 1, l_linger: ticks };
            // SAFETY: an open socket and one initialized linger of its size.
            let result = unsafe {
                libc::setsockopt(
                    stream.as_raw_fd(),
                    libc::SOL_SOCKET,
                    libc::SO_LINGER,
                    (&raw const value).cast(),
                    std::mem::size_of::<libc::linger>() as libc::socklen_t,
                )
            };
            assert_eq!(result, 0, "held-exit actor linger: {}", io::Error::last_os_error());
            // The socket stays open: the kernel's exit closes it and lingers.
            std::process::exit(0);
        }
        struct Owned(std::process::Child);
        impl Drop for Owned {
            fn drop(&mut self) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
        // The peer never reads, and its fixed receive buffer (no autotuning)
        // fills, so the actor's data stays unsent.
        let listener = std::net::TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let receive: libc::c_int = 8192;
        // SAFETY: an open socket and one initialized c_int of its size.
        let result = unsafe {
            libc::setsockopt(
                listener.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_RCVBUF,
                (&raw const receive).cast(),
                std::mem::size_of::<libc::c_int>() as libc::socklen_t,
            )
        };
        assert_eq!(result, 0, "held-exit peer buffer: {}", io::Error::last_os_error());
        let port = listener.local_addr().unwrap().port();
        let mut child = Owned(
            std::process::Command::new(std::env::current_exe().unwrap())
                // The test this re-runs is ignored by default.
                .args(["--exact", test, "--include-ignored", "--test-threads=1"])
                .env(ROLE, port.to_string())
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .spawn()
                .unwrap(),
        );
        let pid = child.0.id();
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            assert!(Instant::now() < deadline, "actor {pid} never began its held exit");
            match native_writer_state(pid).unwrap() {
                Some((false, true)) if read_native(pid).is_err() => break,
                Some((false, _)) => std::thread::sleep(Duration::from_millis(1)),
                state => panic!("actor {pid} ended its exit unobserved: {state:?}"),
            }
        }
        check(pid);
        assert!(child.0.wait().unwrap().success());
        drop(listener);
    }

    #[cfg(all(target_os = "macos", target_pointer_width = "64"))]
    #[test]
    fn writer_census_waits_out_an_exit_and_omits_only_its_zombie() {
        // The census refused a PID whose exit outlasted its identity retries
        // (lease acquisition failed: `native process identity <pid>: No such
        // process`). Here the identity read keeps failing while Darwin reports
        // the child exiting, then a zombie: the census waits and omits it.
        with_live_census_child(|pid| {
            {
                let _identity = read_errno_fault(pid, 6, libc::ESRCH);
                let _exiting = exiting_fault(pid, Some(5));
                assert!(!writer_gone(pid).unwrap(), "an exiting process is not gone");
                assert_eq!(writer_identity(pid, &CensusSettle::new()).unwrap(), None);
                assert!(writer_gone(pid).unwrap(), "it was omitted only as a zombie");
            }
            // Without the faults: the actual live child is present and counted.
            assert!(present(pid).unwrap() && !writer_gone(pid).unwrap());
            assert!(writer_identity(pid, &CensusSettle::new()).unwrap().is_some());
        });
    }

    #[cfg(all(target_os = "macos", target_pointer_width = "64"))]
    #[test]
    fn writer_census_keeps_an_exit_that_outlasts_its_wait_unknown() {
        // One census waits at most its budget in all, across both identity
        // observations; an exit still in progress then stays an error, never
        // absence. A budget per observation waits twice, which the upper bound
        // (timed on the census thread, with the budget's own length as slack
        // for a loaded machine) refutes. The never-ending exit is a fault on
        // the helper thread only, and a census that hangs fails here.
        const BUDGET: Duration = Duration::from_secs(5);
        with_live_census_child(|pid| {
            let (sender, receiver) = std::sync::mpsc::channel();
            std::thread::spawn(move || {
                let _identity = read_errno_fault(pid, 6, libc::ESRCH);
                let _exiting = exiting_fault(pid, None);
                let started = Instant::now();
                let result = writer_identity(pid, &CensusSettle::within(BUDGET));
                let _ =
                    sender.send((result.map_err(|error| error.raw_os_error()), started.elapsed()));
            });
            let (result, elapsed) =
                receiver.recv_timeout(Duration::from_secs(60)).expect("the census hung");
            assert_eq!(result, Err(Some(libc::ESRCH)), "an unfinished exit stays unknown");
            assert!(elapsed >= BUDGET, "it waited for the exit: {elapsed:?}");
            assert!(elapsed < 2 * BUDGET, "one budget, not one per observation: {elapsed:?}");
            // Without the faults: the actual live child is present and not gone.
            assert!(present(pid).unwrap() && !writer_gone(pid).unwrap());
        });
    }

    #[cfg(all(target_os = "macos", target_pointer_width = "64"))]
    #[test]
    #[ignore = "holds an actual exit open 300 ms, which every census on this machine meets; \
                one without census_gone refuses it. Run with --ignored to qualify the faults."]
    fn writer_census_waits_out_an_actual_exit_and_omits_only_its_zombie() {
        // Qualifies the fault tests above against Darwin: an actual exit held
        // open is refused to the identity read, reported exiting, then a zombie.
        with_held_exit(
            "trust_repo_lock::management::process::tests::writer_census_waits_out_an_actual_exit_and_omits_only_its_zombie",
            30,
            |pid| {
                assert!(read_native(pid).is_err(), "an exiting identity is refused");
                assert!(!writer_gone(pid).unwrap(), "an exiting process is not gone");
                assert_eq!(writer_identity(pid, &CensusSettle::new()).unwrap(), None);
                assert!(writer_gone(pid).unwrap(), "only once it is a zombie");
                assert!(present(pid).unwrap(), "which is still unreaped");
            },
        );
    }

    #[cfg(target_os = "macos")]
    fn with_live_census_child(check: impl FnOnce(u32)) {
        struct Owned(std::process::Child);
        impl Drop for Owned {
            fn drop(&mut self) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
        let child = Owned(
            std::process::Command::new("/bin/cat")
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .spawn()
                .unwrap(),
        );
        check(child.0.id());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn live_writer_cwd_transient_refusal_requires_actual_same_birth_reobservation() {
        with_live_census_child(|pid| {
            let original = read(pid).unwrap();
            let expected = cwd(pid).unwrap();
            for errno in [libc::ESRCH, libc::ENOENT, libc::EIO, libc::EPERM, libc::EACCES] {
                let _fault = CwdFault::install(pid, 2, errno);
                assert_eq!(cwd(pid).expect("fresh native cwd of the same live writer"), expected);
            }
            assert_eq!(read(pid).unwrap(), original);
            assert!(present(pid).unwrap());
        });
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn persistent_live_writer_cwd_refusal_remains_unknown_and_never_absence() {
        with_live_census_child(|pid| {
            let original = read(pid).unwrap();
            for errno in [libc::ESRCH, libc::ENOENT, libc::EIO, libc::EPERM, libc::EACCES] {
                let _fault = CwdFault::install(pid, 3, errno);
                assert_eq!(
                    call_and_errno(&cwd(pid).unwrap_err()),
                    ("PROC_PIDVNODEPATHINFO", errno)
                );
                assert!(present(pid).unwrap());
                assert!(!writer_gone(pid).unwrap());
            }
            assert_eq!(read(pid).unwrap(), original);
        });
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn writer_census_reobserves_actual_live_child_after_exhausted_initial_identity() {
        with_live_census_child(|pid| {
            let original = read(pid).unwrap();
            let _fault = read_errno_fault(pid, 3, libc::ESRCH);
            let observed = writer_identity(pid, &CensusSettle::new())
                .expect("a fresh census observation must resolve the actual live child")
                .expect("a present live child must never be skipped as gone");
            assert_eq!(observed.pid, pid);
            assert_eq!(observed.birth, original.birth);
            assert_eq!(observed.uid, original.uid);
            assert!(!observed.zombie);
            assert!(present(pid).unwrap());
        });
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn writer_census_persistent_live_refusal_never_becomes_absence() {
        with_live_census_child(|pid| {
            let original = read(pid).unwrap();
            {
                let _fault = read_errno_fault(pid, 6, libc::ESRCH);
                assert_eq!(
                    writer_identity(pid, &CensusSettle::new()).unwrap_err().raw_os_error(),
                    Some(libc::ESRCH)
                );
                assert!(present(pid).unwrap());
                assert!(!writer_gone(pid).unwrap());
            }
            assert_eq!(read(pid).unwrap().birth, original.birth);
        });
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn final_writer_bookend_reobserves_live_refusal_and_rejects_changed_identity() {
        with_live_census_child(|pid| {
            let original = read(pid).unwrap();
            {
                let _fault = read_errno_fault(pid, 3, libc::ESRCH);
                assert!(writer_recheck(&original, &CensusSettle::new()).unwrap());
            }
            {
                let _fault = read_errno_fault(pid, 6, libc::ESRCH);
                assert_eq!(
                    writer_recheck(&original, &CensusSettle::new()).unwrap_err().raw_os_error(),
                    Some(libc::ESRCH)
                );
                assert!(present(pid).unwrap());
                assert!(!writer_gone(pid).unwrap());
            }
            let mut changed = original.clone();
            changed.birth += 1;
            assert!(writer_recheck(&changed, &CensusSettle::new()).is_err());
            assert!(writer_recheck(&original, &CensusSettle::new()).unwrap());
        });
    }

    #[test]
    fn final_writer_bookend_observes_actual_exit_without_reaping_original_child() {
        struct Owned(std::process::Child);
        impl Drop for Owned {
            fn drop(&mut self) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
        let mut child = Owned(
            std::process::Command::new("/bin/cat")
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .spawn()
                .unwrap(),
        );
        let original = read(child.0.id()).unwrap();
        assert!(writer_recheck(&original, &CensusSettle::new()).unwrap());
        drop(child.0.stdin.take());
        let deadline = Instant::now() + Duration::from_secs(60);
        while writer_recheck(&original, &CensusSettle::new()).unwrap() {
            assert!(Instant::now() < deadline, "actual child did not exit");
            std::thread::sleep(Duration::from_millis(1));
        }
        assert!(present(child.0.id()).unwrap(), "census must not reap original child");
        assert!(child.0.wait().unwrap().success());
    }

    #[test]
    fn writer_census_skips_only_a_native_observed_nonwriter_without_reaping_it() {
        struct Owned(std::process::Child);
        impl Drop for Owned {
            fn drop(&mut self) {
                let _ = self.0.kill();
                let _ = self.0.wait();
            }
        }
        let mut child = Owned(std::process::Command::new("/usr/bin/true").spawn().unwrap());
        let pid = child.0.id();
        let deadline = Instant::now() + Duration::from_secs(60);
        while writer_identity(pid, &CensusSettle::new()).unwrap().is_some() {
            assert!(Instant::now() < deadline, "owned child never became a native nonwriter");
            std::thread::sleep(Duration::from_millis(1));
        }
        assert!(present(pid).unwrap(), "writer census must not reap the original child");
        assert!(child.0.wait().unwrap().success());
        assert!(!present(pid).unwrap());
    }
    #[cfg(target_os = "macos")]
    #[test]
    fn native_argv_transient_retry_requires_same_birth_and_persistent_refusal_stays_unknown() {
        let pid = std::process::id();
        let original = args(pid).unwrap();
        let identity = read(pid).unwrap();
        assert!(!identity.zombie);
        for errno in [libc::EIO, libc::EPERM, libc::EACCES, libc::EINVAL] {
            {
                let _fault = args_fault(pid, 2, errno);
                assert_eq!(args(pid).unwrap(), original, "transient errno {errno}");
            }
            {
                let _fault = args_fault(pid, 3, errno);
                assert_eq!(call_and_errno(&args(pid).unwrap_err()), ("KERN_PROCARGS2", errno));
            }
            let after = read(pid).unwrap();
            assert_eq!(
                (after.pid, after.birth, after.uid),
                (identity.pid, identity.birth, identity.uid)
            );
            assert!(!after.zombie);
        }
        assert_eq!(args(pid).unwrap(), original);
    }
    #[test]
    fn real_current_process_has_kernel_parent_group_argv_and_cwd() {
        let process = read(std::process::id()).unwrap();
        assert_eq!(process.parent, unsafe { libc::getppid() } as u32);
        assert_eq!(process.group, unsafe { libc::getpgrp() } as u32);
        assert!(all_pids().unwrap().contains(&process.pid));
        assert_eq!(cwd(process.pid).unwrap(), std::env::current_dir().unwrap());
        assert_eq!(args(process.pid).unwrap(), std::env::args_os().collect::<Vec<_>>());
        let observed = std::process::Command::new("/bin/ps")
            .args(["-o", "lstart=", "-p", &process.pid.to_string()])
            .env("LC_ALL", "C")
            .env("TZ", "UTC0")
            .output()
            .unwrap();
        assert!(observed.status.success());
        assert_eq!(
            utc_start(process.epoch_seconds).unwrap(),
            String::from_utf8(observed.stdout).unwrap().trim()
        );
    }
    #[test]
    fn native_argv_parser_preserves_empty_arguments_without_reading_environment() {
        let mut bytes = 3_i32.to_ne_bytes().to_vec();
        bytes.extend_from_slice(b"/bin/program\0\0program\0\0last arg\0SECRET_ENV=excluded\0");
        assert_eq!(
            parse_macos_args(&bytes).unwrap(),
            [b"program".to_vec(), vec![], b"last arg".to_vec()]
        );
        for length in 0..bytes.iter().position(|byte| *byte == b'S').unwrap() {
            assert!(parse_macos_args(&bytes[..length]).is_err());
        }
    }
}
