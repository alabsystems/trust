//! Bounded, read-only activity of an original process and its current descendants.
//! Observations confer no execution, cancellation, or resource authority. An
//! incomplete sweep is an error, never evidence of zero CPU, I/O, or memory.

use std::collections::{BTreeMap, BTreeSet};
use std::io;
use std::time::{Duration, Instant};

use super::{Identity, ObservedIdentity, Presence, observe_identity, presence, refused};

const MAX_MEMBERS: usize = 4096;

#[derive(Clone, Copy, Debug)]
struct TreeMemberUsage {
    cpu_nanoseconds: u64,
    io_bytes: u64,
    resident_bytes: u64,
}

/// One complete identity-bookended observation. This is not a frozen process
/// tree: descendants may start or finish between observations. A later member
/// is charged its whole counters; a departed member cannot subtract activity.
#[derive(Debug)]
pub struct TreeActivity {
    original: Identity,
    members: BTreeMap<(u32, u64, u64), TreeMemberUsage>,
    resident_bytes: u64,
}

#[derive(Debug)]
pub enum TreeActivityObservation {
    Active(TreeActivity),
    /// Positive native terminal observation of the original incarnation.
    /// This neither reaps nor grants a caller permission to signal a PID.
    Exited,
    /// The original's native record vanished. This is NOT a terminal proof:
    /// only its actual unreaped Child owner may confirm exit or refuse it.
    OriginalUnavailable(io::Error),
}

enum AttemptFailure {
    Churn,
    Exited,
    OriginalUnavailable(io::Error),
    Integrity(io::Error),
}
impl From<io::Error> for AttemptFailure {
    fn from(error: io::Error) -> Self {
        Self::Integrity(error)
    }
}

impl TreeActivity {
    pub fn read(
        pid: u32,
        expected: Option<Identity>,
        deadline: Instant,
    ) -> io::Result<TreeActivityObservation> {
        let observed = match observe_identity(pid) {
            Ok(observed) => observed,
            Err(error) if vanished(&error) => {
                return Ok(TreeActivityObservation::OriginalUnavailable(error));
            }
            Err(error) => return Err(error),
        };
        let original = observed.identity();
        if expected.is_some_and(|expected| !same_incarnation(original, expected)) {
            return Err(refused("process activity original incarnation changed"));
        }
        if matches!(observed, ObservedIdentity::Exited(_)) {
            return Ok(TreeActivityObservation::Exited);
        }
        // Natural population churn has its own cause, never a generic I/O
        // retry. Every attempt retains the SAME root and original deadline.
        for _ in 0..64 {
            if Instant::now() >= deadline {
                break;
            }
            match Self::attempt(original, deadline) {
                Ok(sample) => return Ok(TreeActivityObservation::Active(sample)),
                Err(AttemptFailure::Exited) => return Ok(TreeActivityObservation::Exited),
                Err(AttemptFailure::OriginalUnavailable(error)) => {
                    return Ok(TreeActivityObservation::OriginalUnavailable(error));
                }
                Err(AttemptFailure::Integrity(error)) => return Err(error),
                Err(AttemptFailure::Churn) => {
                    let remaining = deadline.saturating_duration_since(Instant::now());
                    if remaining.is_zero() {
                        break;
                    }
                    std::thread::sleep(remaining.min(Duration::from_millis(1)));
                }
            }
        }
        Err(io::Error::new(
            io::ErrorKind::TimedOut,
            "process activity population remained unstable within its original observation deadline",
        ))
    }

    fn attempt(original: Identity, deadline: Instant) -> Result<Self, AttemptFailure> {
        let mut pending = vec![original];
        let mut seen = BTreeSet::new();
        let mut members = BTreeMap::new();
        let mut resident_bytes = 0_u64;
        while let Some(identity) = pending.pop() {
            if Instant::now() >= deadline {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "process activity observation expired",
                )
                .into());
            }
            if !seen.insert(identity.pid) || seen.len() > MAX_MEMBERS {
                return Err(
                    refused("process activity tree exceeds bound or repeats a member").into()
                );
            }
            if !live_member(identity, original)? {
                continue;
            }
            let mut original_children = children(identity.pid, deadline)
                .map_err(|error| member_error(identity, original, error))?;
            original_children.sort_unstable();
            original_children.dedup();
            let usage = usage(identity).map_err(|error| member_error(identity, original, error))?;
            for &pid in &original_children {
                let child = match observe_identity(pid) {
                    Ok(ObservedIdentity::Live(child)) => child,
                    Ok(ObservedIdentity::Exited(_)) => continue,
                    Err(error) if vanished(&error) && presence(pid) == Presence::Absent => {
                        return Err(AttemptFailure::Churn);
                    }
                    Err(error) => return Err(AttemptFailure::Integrity(error)),
                };
                if child.parent != identity.pid
                    || (child.parent_unique_id != 0 && child.parent_unique_id != identity.unique_id)
                {
                    return Err(AttemptFailure::Churn);
                }
                pending.push(child);
                if pending.len() + seen.len() > MAX_MEMBERS {
                    return Err(refused("process activity tree exceeds member bound").into());
                }
            }
            if !live_member(identity, original)? {
                return Err(AttemptFailure::Churn);
            }
            let mut current_children = children(identity.pid, deadline)
                .map_err(|error| member_error(identity, original, error))?;
            current_children.sort_unstable();
            current_children.dedup();
            if current_children != original_children {
                return Err(AttemptFailure::Churn);
            }
            resident_bytes = resident_bytes
                .checked_add(usage.resident_bytes)
                .ok_or_else(|| refused("process activity resident sum overflow"))?;
            members.insert((identity.pid, identity.birth, identity.unique_id), usage);
        }
        live_member(original, original)?;
        if Instant::now() >= deadline {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "process activity observation expired before its final bookend",
            )
            .into());
        }
        Ok(Self { original, members, resident_bytes })
    }

    pub fn original(&self) -> Identity {
        self.original
    }

    pub fn resident_bytes(&self) -> u64 {
        self.resident_bytes
    }

    pub fn advanced_since(&self, previous: &Self) -> bool {
        self.members.iter().any(|(key, now)| match previous.members.get(key) {
            Some(before) => {
                now.cpu_nanoseconds > before.cpu_nanoseconds || now.io_bytes > before.io_bytes
            }
            None => now.cpu_nanoseconds != 0 || now.io_bytes != 0,
        })
    }
}

fn vanished(error: &io::Error) -> bool {
    matches!(error.raw_os_error(), Some(libc::ESRCH | libc::ENOENT))
}

fn live_member(identity: Identity, root: Identity) -> Result<bool, AttemptFailure> {
    match observe_identity(identity.pid) {
        Ok(observed) => {
            if !same_incarnation(observed.identity(), identity) {
                return if identity.pid == root.pid {
                    Err(refused("process activity root incarnation changed").into())
                } else {
                    Err(AttemptFailure::Churn)
                };
            }
            match observed {
                ObservedIdentity::Live(_) => Ok(true),
                ObservedIdentity::Exited(_) if identity.pid == root.pid => {
                    Err(AttemptFailure::Exited)
                }
                ObservedIdentity::Exited(_) => Ok(false),
            }
        }
        Err(error) => Err(member_error(identity, root, error)),
    }
}

fn member_error(identity: Identity, root: Identity, error: io::Error) -> AttemptFailure {
    if vanished(&error) {
        if identity.pid == root.pid {
            // Darwin may hide a zombie's complete native record. Observation
            // cannot establish termination; return to the same actual Child
            // owner for its unreaped WNOWAIT confirmation, never zero usage.
            return AttemptFailure::OriginalUnavailable(error);
        }
        match observe_identity(identity.pid) {
            Ok(ObservedIdentity::Exited(actual)) if same_incarnation(actual, identity) => {
                return if identity.pid == root.pid {
                    AttemptFailure::Exited
                } else {
                    AttemptFailure::Churn
                };
            }
            Ok(observed)
                if identity.pid != root.pid && !same_incarnation(observed.identity(), identity) =>
            {
                return AttemptFailure::Churn;
            }
            Err(next)
                if vanished(&next)
                    && identity.pid != root.pid
                    && presence(identity.pid) == Presence::Absent =>
            {
                return AttemptFailure::Churn;
            }
            _ => {}
        }
    }
    AttemptFailure::Integrity(error)
}

fn same_incarnation(left: Identity, right: Identity) -> bool {
    // An exec may legitimately change image/version within the same owned
    // child. Activity observations neither authenticate nor authorize images.
    (left.pid, left.birth, left.unique_id) == (right.pid, right.birth, right.unique_id)
}

#[cfg(target_os = "macos")]
fn usage(identity: Identity) -> io::Result<TreeMemberUsage> {
    // SAFETY: this kernel ABI record consists entirely of integers.
    let mut info: libc::rusage_info_v4 = unsafe { std::mem::zeroed() };
    // SAFETY: the correctly sized V4 record is writable for this synchronous call.
    let result = unsafe {
        libc::proc_pid_rusage(identity.pid as i32, 4, (&raw mut info).cast::<libc::rusage_info_t>())
    };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(TreeMemberUsage {
        cpu_nanoseconds: info.ri_user_time.saturating_add(info.ri_system_time),
        io_bytes: info.ri_diskio_bytesread.saturating_add(info.ri_diskio_byteswritten),
        resident_bytes: info.ri_resident_size,
    })
}

#[cfg(target_os = "macos")]
fn children(pid: u32, _deadline: Instant) -> io::Result<Vec<u32>> {
    #[link(name = "proc")]
    unsafe extern "C" {
        fn proc_listchildpids(
            pid: libc::c_int,
            buffer: *mut libc::c_void,
            size: libc::c_int,
        ) -> libc::c_int;
    }
    let mut children = vec![0_i32; MAX_MEMBERS + 1];
    let bytes = std::mem::size_of_val(children.as_slice()) as i32;
    // SAFETY: the vector supplies the complete stated writable PID buffer;
    // errno belongs to this thread and is captured immediately after the call.
    let (count, errno) = unsafe {
        *libc::__error() = 0;
        let count = proc_listchildpids(pid as i32, children.as_mut_ptr().cast(), bytes);
        (count, *libc::__error())
    };
    let count = usize::try_from(count).map_err(|_| io::Error::from_raw_os_error(errno))?;
    if errno != 0 {
        return Err(io::Error::from_raw_os_error(errno));
    }
    if count >= children.len() {
        return Err(refused("process child list exceeds bound"));
    }
    children.truncate(count);
    children
        .into_iter()
        .map(|pid| {
            u32::try_from(pid)
                .ok()
                .filter(|pid| *pid > 1)
                .ok_or_else(|| refused("invalid process child PID"))
        })
        .collect()
}

#[cfg(target_os = "linux")]
fn usage(identity: Identity) -> io::Result<TreeMemberUsage> {
    let dir = super::ProcDir::open(identity.pid)?;
    let bytes = dir.read(c"stat")?;
    let text = std::str::from_utf8(&bytes).map_err(|_| refused("invalid process activity stat"))?;
    let end = text.rfind(')').ok_or_else(|| refused("invalid process activity name"))?;
    let fields: Vec<_> = text[end + 1..].split_whitespace().collect();
    let value = |index: usize| {
        fields
            .get(index)
            .and_then(|value| value.parse::<u64>().ok())
            .ok_or_else(|| refused("incomplete process activity stat"))
    };
    // SAFETY: sysconf reads the kernel's tick and page conversion constants.
    let ticks = unsafe { libc::sysconf(libc::_SC_CLK_TCK) };
    // SAFETY: as above; no pointer or mutable state is supplied.
    let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
    if ticks <= 0 || page <= 0 {
        return Err(refused("process activity conversion unavailable"));
    }
    let cpu = (u128::from(value(11)?.saturating_add(value(12)?)) * 1_000_000_000 / ticks as u128)
        .try_into()
        .map_err(|_| refused("process activity CPU overflow"))?;
    let io = dir.read(c"io")?;
    let io = std::str::from_utf8(&io).map_err(|_| refused("invalid process I/O counters"))?;
    let counter = |key: &str| {
        io.lines()
            .find_map(|line| line.strip_prefix(key))
            .and_then(|value| value.trim().parse::<u64>().ok())
            .ok_or_else(|| refused("process I/O counter unavailable"))
    };
    Ok(TreeMemberUsage {
        cpu_nanoseconds: cpu,
        io_bytes: counter("read_bytes:")?.saturating_add(counter("write_bytes:")?),
        resident_bytes: value(21)?
            .checked_mul(page as u64)
            .ok_or_else(|| refused("process resident bytes overflow"))?,
    })
}

#[cfg(target_os = "linux")]
fn children(pid: u32, deadline: Instant) -> io::Result<Vec<u32>> {
    use std::os::fd::AsRawFd;
    let dir = super::ProcDir::open(pid)?;
    let mut children = BTreeSet::new();
    for (index, task) in
        std::fs::read_dir(format!("/proc/self/fd/{}/task", dir.0.as_raw_fd()))?.enumerate()
    {
        if Instant::now() >= deadline {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "process thread activity observation expired",
            ));
        }
        if index >= MAX_MEMBERS {
            return Err(refused("process thread list exceeds bound"));
        }
        let name = task?.file_name();
        let tid = name
            .to_str()
            .and_then(|name| name.parse::<u32>().ok())
            .ok_or_else(|| refused("invalid process thread ID"))?;
        let name = std::ffi::CString::new(format!("task/{tid}/children"))
            .map_err(|_| refused("invalid child list name"))?;
        let bytes = dir.read(&name)?;
        for word in std::str::from_utf8(&bytes)
            .map_err(|_| refused("invalid process child list"))?
            .split_whitespace()
        {
            children.insert(
                word.parse::<u32>()
                    .ok()
                    .filter(|pid| *pid > 1)
                    .ok_or_else(|| refused("invalid process child PID"))?,
            );
            if children.len() > MAX_MEMBERS {
                return Err(refused("process child list exceeds bound"));
            }
        }
    }
    Ok(children.into_iter().collect())
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn usage(_: Identity) -> io::Result<TreeMemberUsage> {
    Err(io::Error::new(io::ErrorKind::Unsupported, "process activity unsupported"))
}
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn children(_: u32, _: Instant) -> io::Result<Vec<u32>> {
    Err(io::Error::new(io::ErrorKind::Unsupported, "process activity unsupported"))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn observation(birth: u64, cpu: u64, io: u64, resident: u64) -> TreeActivity {
        TreeActivity {
            original: Identity {
                pid: 42,
                parent: 1,
                birth,
                unique_id: birth,
                parent_unique_id: 0,
                exec_version: 0,
            },
            members: [(
                (42, birth, birth),
                TreeMemberUsage { cpu_nanoseconds: cpu, io_bytes: io, resident_bytes: resident },
            )]
            .into_iter()
            .collect(),
            resident_bytes: resident,
        }
    }

    #[test]
    fn io_without_cpu_counts_as_activity_and_memory_alone_does_not() {
        let original = observation(1, 100, 200, 300);
        assert!(observation(1, 100, 201, 300).advanced_since(&original));
        assert!(!observation(1, 100, 200, 301).advanced_since(&original));
    }

    #[test]
    fn a_recycled_descendant_pid_keeps_its_new_incarnations_activity() {
        let old_process = observation(1, 1000, 2000, 3000);
        assert!(observation(2, 1, 0, 30).advanced_since(&old_process));
        assert!(!observation(1, 1, 0, 30).advanced_since(&old_process));
    }
}
