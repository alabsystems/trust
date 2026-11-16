//! Local original-group custody using the shared streaming lifecycle.
//! A watcher handles leader exit even while a descendant holds a capture pipe.
//! Escaped sessions need the separate native workload/containment protocol.

use std::io;
use std::os::unix::process::CommandExt;
use std::process::{Child, ChildStderr, ChildStdin, ChildStdout, Command, ExitStatus};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use trust_resource_provenance::process::{ChildSignalLease, pending_child_signal};

#[derive(Clone, Copy, Debug)]
enum Retirement {
    Owned,
    Observed,
    Reaped(ExitStatus),
    Retired(ExitStatus),
    Lost,
}

pub struct InheritedChild {
    child: Child,
    cancel: Arc<AtomicBool>,
    observer: Option<JoinHandle<io::Result<()>>>,
    state: Retirement,
    signals: ChildSignalLease,
    #[cfg(test)]
    fail_group_absence: bool,
}
impl InheritedChild {
    pub(super) fn spawn(command: &mut Command) -> io::Result<Self> {
        // Autoreaping or another SIGCHLD owner would invalidate WNOWAIT's PID
        // anchor; refuse before creating the child instead of racing a reaper.
        let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
        if unsafe { libc::sigaction(libc::SIGCHLD, std::ptr::null(), &mut action) } != 0 {
            return Err(io::Error::last_os_error());
        }
        if action.sa_sigaction != libc::SIG_DFL || action.sa_flags & libc::SA_NOCLDWAIT != 0 {
            return Err(io::Error::other("inherited child requires default waitable SIGCHLD"));
        }
        let signals = ChildSignalLease::install(true)?.expect("enabled inherited-child signals");
        if pending_child_signal() != 0 {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                "inherited child cancelled before spawn",
            ));
        }
        command.process_group(0);
        let child = command.spawn()?;
        let cancel = Arc::new(AtomicBool::new(false));
        let pid = child.id() as libc::pid_t;
        let observer_cancel = Arc::clone(&cancel);
        let mut owned = Self {
            child,
            cancel,
            observer: None,
            state: Retirement::Owned,
            signals,
            #[cfg(test)]
            fail_group_absence: false,
        };
        owned.observer = Some(
            thread::Builder::new()
                .name("compiletest-child-custody".into())
                .spawn(move || observe(pid, &observer_cancel))?,
        );
        Ok(owned)
    }
    pub fn id(&self) -> u32 {
        self.child.id()
    }
    pub fn take_stdin(&mut self) -> Option<ChildStdin> {
        self.child.stdin.take()
    }
    pub fn take_stdout(&mut self) -> Option<ChildStdout> {
        self.child.stdout.take()
    }
    pub fn take_stderr(&mut self) -> Option<ChildStderr> {
        self.child.stderr.take()
    }
    pub fn wait(&mut self) -> io::Result<ExitStatus> {
        let status = self.finish()?;
        if pending_child_signal() != 0 {
            return Err(io::Error::new(io::ErrorKind::Interrupted, "inherited child interrupted"));
        }
        Ok(status)
    }
    pub(super) fn finish_callback(&mut self) -> io::Result<()> {
        if !matches!(self.state, Retirement::Retired(_)) {
            self.cancel.store(true, Ordering::Release);
        }
        self.finish()?;
        self.signals.restore()
    }
    fn finish(&mut self) -> io::Result<ExitStatus> {
        match self.state {
            Retirement::Retired(status) => return Ok(status),
            Retirement::Lost => {
                return Err(io::Error::other("original child wait custody was lost"));
            }
            Retirement::Reaped(status) => {
                // No waitid, group signal, or owning wait is legal after reap.
                self.require_group_absent()?;
                self.state = Retirement::Retired(status);
                return Ok(status);
            }
            Retirement::Owned => {
                // Any failed observation is terminal. Drop must not retry a
                // numeric PID after a stolen wait or another custody failure.
                self.state = Retirement::Lost;
                if let Some(observer) = self.observer.take() {
                    observer.join().unwrap_or_else(|_| std::process::abort())?;
                } else {
                    // Only possible while unwinding a failed observer spawn;
                    // the actual direct Child has not had another waiter.
                    observe(self.child.id() as libc::pid_t, &self.cancel)?;
                }
                self.state = Retirement::Observed;
            }
            Retirement::Observed => {}
        }
        // Only successful WNOWAIT/group cleanup authorizes the sole reap.
        self.state = Retirement::Lost;
        let status = self.child.wait()?;
        self.state = Retirement::Reaped(status);
        self.require_group_absent()?;
        self.state = Retirement::Retired(status);
        Ok(status)
    }
    fn require_group_absent(&self) -> io::Result<()> {
        #[cfg(test)]
        if self.fail_group_absence {
            return Err(io::Error::other("intentional post-reap group absence failure"));
        }
        group_absence(self.child.id() as libc::pid_t, Duration::from_secs(10))
    }
}
impl Drop for InheritedChild {
    fn drop(&mut self) {
        if let Err(error) = self.finish_callback()
            && !matches!(self.state, Retirement::Retired(_))
        {
            eprintln!("inherited child retirement failed: {error}");
            std::process::abort();
        }
    }
}

/// Observation only after reap: a reused numeric group is NEVER signalled.
/// Uncertain absence retains custody by refusing release; only `ESRCH` releases.
/// Darwin answers `EPERM` for a group whose remaining members are exiting or
/// zombies awaiting their reaper (launchd, once the leader is reaped), which is
/// the window right after the observer's SIGKILL (COMPILETEST-GROUP-EPERM-1).
/// `EPERM` therefore keeps custody and keeps polling within the same patience,
/// as a live member does; it is never read as absence. The refusal names the
/// group's visible members and their states.
fn group_absence(pgid: libc::pid_t, patience: Duration) -> io::Result<()> {
    let until = Instant::now() + patience;
    let refusal = loop {
        let observed = if unsafe { libc::kill(-pgid, 0) } == 0 {
            io::Error::other("inherited child group retirement is unresolved")
        } else {
            let error = io::Error::last_os_error();
            match error.raw_os_error() {
                Some(libc::ESRCH) => return Ok(()),
                Some(libc::EPERM) => error,
                _ => break error,
            }
        };
        if Instant::now() >= until {
            break observed;
        }
        thread::sleep(Duration::from_millis(5));
    };
    Err(io::Error::new(refusal.kind(), format!("{refusal}; {}", group_census(pgid))))
}

/// The members of process group `pgid` this runner can see, beside its own uid.
/// Diagnostic only: nothing listed here is signalled, waited on or trusted for
/// custody, and a member that is reaped mid-listing is simply not named.
fn group_census(pgid: libc::pid_t) -> String {
    let runner = unsafe { libc::getuid() };
    match group_members(pgid) {
        Ok(members) if members.is_empty() => {
            format!("process group {pgid} lists no member (runner uid {runner})")
        }
        Ok(members) => {
            let named: Vec<String> = members
                .iter()
                .map(|member| match member.uid {
                    Some(uid) => {
                        format!(
                            "pid {} uid {uid} `{}` {}",
                            member.pid, member.command, member.state
                        )
                    }
                    None => format!("pid {} `{}` {}", member.pid, member.command, member.state),
                })
                .collect();
            format!("process group {pgid} members (runner uid {runner}): {}", named.join(", "))
        }
        Err(error) => {
            format!(
                "process group {pgid} members could not be listed: {error} (runner uid {runner})"
            )
        }
    }
}

struct GroupMember {
    pid: libc::pid_t,
    uid: Option<libc::uid_t>,
    command: String,
    state: String,
}

/// How one member's short BSD record read went.
#[cfg(any(target_os = "macos", test))]
#[derive(Debug)]
enum MemberRecord {
    Read,
    /// It exited between the listing and the read: not a member to name.
    Gone,
    Unreadable(io::Error),
}

/// `proc_pidinfo` answers the bytes it wrote, or 0 with the refusal in
/// `errno`; the caller clears `errno` before the call and passes it here. A
/// short positive count sets no `errno`, so it is its own error: read then,
/// `errno` would be whatever an earlier call left, and a stale ESRCH would drop
/// a live member from the census.
#[cfg(any(target_os = "macos", test))]
fn member_record(read: libc::c_int, size: libc::c_int, errno: libc::c_int) -> MemberRecord {
    if read == size {
        MemberRecord::Read
    } else if read > 0 {
        MemberRecord::Unreadable(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("short BSD record of {read} of {size} bytes"),
        ))
    } else if errno == libc::ESRCH {
        MemberRecord::Gone
    } else {
        MemberRecord::Unreadable(io::Error::from_raw_os_error(if errno != 0 {
            errno
        } else {
            libc::EIO
        }))
    }
}

/// libproc's listing answers 0, never -1, when the kernel refuses it, and keeps
/// that refusal in `errno`; the caller clears `errno` before the call.
#[cfg(any(target_os = "macos", test))]
fn listed_pid_count(count: libc::c_int, errno: libc::c_int) -> io::Result<usize> {
    if count < 0 || (count == 0 && errno != 0) {
        return Err(io::Error::from_raw_os_error(if errno != 0 { errno } else { libc::EIO }));
    }
    Ok(count as usize)
}

#[cfg(target_os = "macos")]
fn group_members(pgid: libc::pid_t) -> io::Result<Vec<GroupMember>> {
    use std::mem::size_of;
    // libproc already divides the kernel's byte length, so the answer is a pid
    // count; a group can grow between calls, so a full buffer is retried larger.
    let mut capacity = 64usize;
    let pids = loop {
        let mut pids = vec![0 as libc::pid_t; capacity];
        let count = unsafe {
            *libc::__error() = 0;
            let count = libc::proc_listpgrppids(
                pgid,
                pids.as_mut_ptr().cast(),
                (capacity * size_of::<libc::pid_t>()) as libc::c_int,
            );
            listed_pid_count(count, *libc::__error())?
        };
        if count < capacity || capacity >= 1 << 16 {
            pids.truncate(count);
            break pids;
        }
        capacity *= 4;
    };
    let mut members = Vec::new();
    for pid in pids.into_iter().filter(|&pid| pid > 0) {
        // The short BSD record is the flavour macOS serves for another user's
        // process; argument 1 also serves an exiting or zombie member, which is
        // exactly the group Darwin answers EPERM for.
        let mut info: libc::proc_bsdshortinfo = unsafe { std::mem::zeroed() };
        let size = size_of::<libc::proc_bsdshortinfo>() as libc::c_int;
        let record = unsafe {
            *libc::__error() = 0;
            let read = libc::proc_pidinfo(
                pid,
                libc::PROC_PIDT_SHORTBSDINFO,
                1,
                (&raw mut info).cast(),
                size,
            );
            member_record(read, size, *libc::__error())
        };
        match record {
            MemberRecord::Read => {}
            MemberRecord::Gone => continue,
            MemberRecord::Unreadable(error) => {
                members.push(GroupMember {
                    pid,
                    uid: None,
                    command: format!("unreadable: {error}"),
                    state: "unknown".to_string(),
                });
                continue;
            }
        }
        if info.pbsi_pgid != pgid as u32 {
            continue;
        }
        let comm: Vec<u8> =
            info.pbsi_comm.iter().take_while(|&&c| c != 0).map(|&c| c as u8).collect();
        let state = match info.pbsi_status {
            libc::SIDL => "starting".to_string(),
            libc::SRUN => "runnable".to_string(),
            libc::SSLEEP => "sleeping".to_string(),
            libc::SSTOP => "stopped".to_string(),
            libc::SZOMB => "zombie".to_string(),
            other => format!("status {other}"),
        };
        members.push(GroupMember {
            pid,
            uid: Some(info.pbsi_uid),
            command: String::from_utf8_lossy(&comm).into_owned(),
            state,
        });
    }
    Ok(members)
}

/// One `/proc/<pid>/stat` record: `pid (comm) state ppid pgrp ...`. comm is raw
/// bytes (it may hold spaces, parentheses or a cut multibyte character), so the
/// record is decoded lossily and split at the LAST `)`.
#[cfg(any(target_os = "linux", test))]
fn parse_stat(stat: &[u8]) -> Option<(libc::pid_t, String, String)> {
    let stat = String::from_utf8_lossy(stat);
    let (open, close) = (stat.find('(')?, stat.rfind(')')?);
    let mut fields = stat.get(close + 1..)?.split_whitespace();
    let state = match fields.next()? {
        "R" => "runnable".to_string(),
        "S" | "D" | "I" => "sleeping".to_string(),
        "T" | "t" => "stopped".to_string(),
        "Z" => "zombie".to_string(),
        "X" => "dead".to_string(),
        other => format!("state {other}"),
    };
    let pgrp = fields.nth(1)?.parse().ok()?;
    Some((pgrp, stat.get(open + 1..close)?.to_string(), state))
}

#[cfg(target_os = "linux")]
fn group_members(pgid: libc::pid_t) -> io::Result<Vec<GroupMember>> {
    let mut members = Vec::new();
    for entry in std::fs::read_dir("/proc")? {
        let Ok(entry) = entry else { continue };
        let Some(pid) = entry.file_name().to_str().and_then(|name| name.parse().ok()) else {
            continue;
        };
        // A process reaped mid-scan is no member.
        let Ok(stat) = std::fs::read(format!("/proc/{pid}/stat")) else { continue };
        let Some((pgrp, command, state)) = parse_stat(&stat) else { continue };
        if pgrp != pgid {
            continue;
        }
        let uid = std::fs::read(format!("/proc/{pid}/status")).ok().and_then(|status| {
            String::from_utf8_lossy(&status)
                .lines()
                .find_map(|line| line.strip_prefix("Uid:"))?
                .split_whitespace()
                .next()?
                .parse()
                .ok()
        });
        members.push(GroupMember { pid, uid, command, state });
    }
    Ok(members)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn group_members(_pgid: libc::pid_t) -> io::Result<Vec<GroupMember>> {
    Err(io::Error::new(io::ErrorKind::Unsupported, "no process-group listing on this platform"))
}

fn observe(pid: libc::pid_t, cancel: &AtomicBool) -> io::Result<()> {
    // SAFETY: this watcher owns no reap operation; InheritedChild retains its
    // original direct child and new process group until this watcher joins.
    let result = unsafe {
        trust_resource_provenance::process::observe_owned_group_exit(pid, || {
            cancel.load(Ordering::Acquire) || pending_child_signal() != 0
        })
    };
    if !result.exited {
        return Err(result
            .error
            .unwrap_or_else(|| io::Error::other("inherited child custody was lost")));
    }
    result.error.map_or(Ok(()), Err)
}

/// Test-only: `ChildSignalLease` is ONE process-wide signal epoch, so a test that
/// raises a real owned-group signal cancels every concurrent leaseholder in the
/// test binary, as production intends for one compiletest process. That test
/// takes this exclusively; every other test that spawns an `InheritedChild`
/// shares it, so no test reads another test's signal as its own.
#[cfg(test)]
pub(super) static SIGNAL_EPOCH: std::sync::RwLock<()> = std::sync::RwLock::new(());

#[cfg(test)]
pub(super) fn shared_signal_epoch() -> std::sync::RwLockReadGuard<'static, ()> {
    SIGNAL_EPOCH.read().unwrap_or_else(std::sync::PoisonError::into_inner)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn post_reap_absence_failure_never_reobserves_or_resignals_the_pid() {
        let _epoch = shared_signal_epoch();
        let mut child = InheritedChild::spawn(&mut Command::new("/usr/bin/true")).unwrap();
        child.fail_group_absence = true;
        for _ in 0..2 {
            assert!(child.finish().unwrap_err().to_string().contains("post-reap"));
            assert!(matches!(child.state, Retirement::Reaped(_)));
        }
        let mut status = 0;
        assert_eq!(unsafe { libc::waitpid(child.id() as i32, &mut status, libc::WNOHANG) }, -1);
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ECHILD));
        child.fail_group_absence = false;
        assert!(child.finish().unwrap().success());
        assert!(matches!(child.state, Retirement::Retired(_)));
    }

    /// Block until `pid` has exited, leaving it unreaped (a zombie).
    fn wait_until_zombie(pid: libc::pid_t) {
        let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
        let flags = libc::WEXITED | libc::WNOWAIT;
        assert_eq!(unsafe { libc::waitid(libc::P_PID, pid as libc::id_t, &mut info, flags) }, 0);
    }

    #[test]
    fn a_group_of_only_zombies_is_awaited_until_reaped_not_refused() {
        // COMPILETEST-GROUP-EPERM-1: right after the observer's SIGKILL a group holds only
        // exiting or zombie members, and Darwin answers EPERM for it. Absence is awaited.
        let mut leader = Command::new("/bin/sleep").arg("30").process_group(0).spawn().unwrap();
        let pgid = leader.id() as libc::pid_t;
        leader.kill().unwrap();
        wait_until_zombie(pgid);
        #[cfg(target_os = "macos")]
        {
            assert_eq!(unsafe { libc::kill(-pgid, 0) }, -1);
            assert_eq!(
                io::Error::last_os_error().raw_os_error(),
                Some(libc::EPERM),
                "the premise moved: Darwin no longer answers EPERM for a zombie-only group"
            );
        }
        let reaper = thread::spawn(move || {
            thread::sleep(Duration::from_millis(100));
            leader.wait().unwrap()
        });
        group_absence(pgid, Duration::from_secs(10)).unwrap();
        assert!(!reaper.join().unwrap().success());
    }

    #[test]
    fn an_unreaped_zombie_member_is_named_as_one() {
        let mut leader = Command::new("/bin/sleep").arg("30").process_group(0).spawn().unwrap();
        let pgid = leader.id() as libc::pid_t;
        leader.kill().unwrap();
        wait_until_zombie(pgid);
        let refusal = group_absence(pgid, Duration::from_millis(20)).unwrap_err().to_string();
        leader.wait().unwrap();
        let uid = unsafe { libc::getuid() };
        assert!(
            refusal.contains(&format!("pid {pgid} uid {uid} `sleep` zombie")),
            "the refusal does not name the zombie member: {refusal}"
        );
        group_absence(pgid, Duration::from_secs(10)).unwrap();
    }

    #[test]
    fn a_refused_listing_is_an_error_not_an_empty_group() {
        assert_eq!(listed_pid_count(3, 0).unwrap(), 3);
        assert_eq!(listed_pid_count(0, 0).unwrap(), 0);
        let refused = listed_pid_count(0, libc::ENOMEM).unwrap_err();
        assert_eq!(refused.raw_os_error(), Some(libc::ENOMEM));
        assert!(listed_pid_count(-1, 0).is_err());
    }

    #[test]
    fn a_short_member_record_is_unreadable_never_a_stale_errno() {
        assert!(matches!(member_record(64, 64, libc::ESRCH), MemberRecord::Read));
        // A short positive count sets no errno: a stale ESRCH must not drop
        // the member as gone, and no errno is reported for it.
        let MemberRecord::Unreadable(short) = member_record(16, 64, libc::ESRCH) else {
            panic!("a short record was not unreadable");
        };
        assert_eq!(short.raw_os_error(), None, "{short}");
        assert_eq!(short.to_string(), "short BSD record of 16 of 64 bytes");
        assert!(matches!(member_record(0, 64, libc::ESRCH), MemberRecord::Gone));
        let MemberRecord::Unreadable(refused) = member_record(0, 64, libc::EPERM) else {
            panic!("a refusal was not unreadable");
        };
        assert_eq!(refused.raw_os_error(), Some(libc::EPERM));
        let MemberRecord::Unreadable(silent) = member_record(0, 64, 0) else {
            panic!("a zero count without errno was not unreadable");
        };
        assert_eq!(silent.raw_os_error(), Some(libc::EIO));
    }

    #[test]
    fn a_stat_record_keeps_a_member_whose_comm_is_not_utf8() {
        // comm cut mid-character, holding `) (`: split at the LAST `)`, decode lossily.
        let mut stat = b"4242 (".to_vec();
        stat.extend_from_slice(&[0xd0, 0xba, b')', b' ', b'(', 0xd0]);
        stat.extend_from_slice(b") Z 1 4240 4240 0 -1");
        let (pgrp, command, state) = parse_stat(&stat).unwrap();
        assert_eq!((pgrp, state.as_str()), (4240, "zombie"));
        assert!(command.starts_with("\u{43a}) ("), "{command}");
        let plain = parse_stat(b"4242 (sh) S 1 77 77").unwrap();
        assert_eq!(plain, (77, "sh".to_string(), "sleeping".to_string()));
    }

    #[test]
    fn unresolved_group_refusal_names_each_member_and_the_runner_uid() {
        // COMPILETEST-GROUP-EPERM-1: the refusal that aborts a run says whose group it is.
        let mut leader = Command::new("/bin/sleep").arg("30").process_group(0).spawn().unwrap();
        let pgid = leader.id() as libc::pid_t;
        let refusal = group_absence(pgid, Duration::from_millis(20)).unwrap_err().to_string();
        leader.kill().unwrap();
        leader.wait().unwrap();
        let uid = unsafe { libc::getuid() };
        assert!(
            refusal.starts_with("inherited child group retirement is unresolved; "),
            "the refusal lost its cause: {refusal}"
        );
        assert!(
            refusal.contains(&format!("process group {pgid} members (runner uid {uid}): ")),
            "the refusal does not compare against the runner's uid: {refusal}"
        );
        assert!(
            refusal.contains(&format!("pid {pgid} uid {uid} `sleep`")),
            "the refusal does not name the live member: {refusal}"
        );
        // Retiring the group releases custody exactly as before.
        group_absence(pgid, Duration::from_secs(10)).unwrap();
    }
}
