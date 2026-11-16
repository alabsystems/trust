use std::fs::File;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::net::UnixStream;
use std::ptr;

use trust_process_isolation::{Budget, Charge};

use super::custody::Custody;
use super::tree::Tree;
use super::{PreparedStaticWorker, checked, contract};
mod birth;
use birth::contained_clone;

use crate::{Error, system};

#[derive(Debug)]
pub(crate) struct Child {
    pub pid: libc::pid_t,
    pub pidfd: Option<OwnedFd>,
    pub reaped: bool,
    pub budget: Budget,
}
impl Child {
    pub fn exited(&self) -> Result<bool, Error> {
        Ok(self.successful_exit()?.is_some())
    }
    /// A process observation only: the held child still reserves its PID, and
    /// a zero exit grants no protocol, macro or proof authority.
    pub(crate) fn successful_exit(&self) -> Result<Option<bool>, Error> {
        let mut info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
        // SAFETY: the live owned child PID is never reaped by another owner;
        // waitid writes a complete siginfo_t and WNOWAIT reserves its identity.
        if unsafe {
            libc::waitid(
                libc::P_PID,
                self.pid as u32,
                info.as_mut_ptr(),
                libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
            )
        } != 0
        {
            return Err(system("worker waitid"));
        }
        // SAFETY: successful waitid initialized the complete output record.
        let info = unsafe { info.assume_init() };
        // SAFETY: waitid initialized this status union. WEXITED excludes stop
        // events; si_pid distinguishes the no-event result under WNOHANG.
        Ok(if unsafe { info.si_pid() } == self.pid {
            Some(info.si_code == libc::CLD_EXITED && unsafe { info.si_status() } == 0)
        } else {
            None
        })
    }
    /// Signal cleanup before any wait. A multi-process owner signals every
    /// owned leader before it enters an opaque reap interval for either one.
    /// The exclusive unreaped guard reserves the PID/PGID throughout this call.
    pub fn request_stop(&self) {
        if self.reaped || self.pid <= 0 {
            return;
        }
        // SAFETY: the leader is still unreaped and reserves its PID/PGID. A
        // failed pre-setpgid setup may lack that group, so kill leader as well.
        unsafe {
            libc::kill(-self.pid, libc::SIGKILL);
            if let Some(fd) = &self.pidfd {
                libc::syscall(
                    libc::SYS_pidfd_send_signal,
                    fd.as_raw_fd(),
                    libc::SIGKILL,
                    ptr::null::<libc::siginfo_t>(),
                    0u32,
                );
            }
            libc::kill(self.pid, libc::SIGKILL);
        }
    }
    pub fn stop_and_reap(&mut self) -> Result<i32, Error> {
        if self.reaped {
            return Err(contract("worker already reaped"));
        }
        if self.pid <= 0 {
            return Err(contract("worker PID must be positive"));
        }
        self.request_stop();
        let mut status = 0;
        loop {
            // SAFETY: only this owner reaps its positive PID, with writable
            // status storage. Cleanup deliberately does not charge a dead grant.
            let got = unsafe { libc::waitpid(self.pid, &mut status, 0) };
            if got == self.pid {
                self.reaped = true;
                return Ok(status);
            }
            if got < 0 && std::io::Error::last_os_error().raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            return Err(system("worker reap"));
        }
    }
}
impl Drop for Child {
    fn drop(&mut self) {
        if !self.reaped {
            self.budget.cancel();
            let _ = self.stop_and_reap();
        }
    }
}

pub(super) struct Channels {
    pub child: Custody,
    pub stdout: File,
    pub stderr: File,
    pub control: UnixStream,
    pub status: File,
}
pub(crate) struct NativeChannels {
    pub child: Child,
    pub stdout: File,
    pub stderr: File,
    pub control: UnixStream,
    pub status: File,
}
fn pipe() -> Result<(File, File), Error> {
    let mut fds = [-1; 2];
    // SAFETY: pipe2 writes two fresh descriptors to the full live array.
    if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
        return Err(system("worker pipe"));
    }
    // SAFETY: successful pipe2 yielded two distinct uniquely owned descriptors.
    Ok(unsafe { (File::from_raw_fd(fds[0]), File::from_raw_fd(fds[1])) })
}
fn high(fd: RawFd) -> Result<OwnedFd, Error> {
    // SAFETY: F_DUPFD_CLOEXEC copies a live borrowed source to a fresh FD above
    // every dense destination, avoiding child dup cycles and accidental aliases.
    let copy = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 64) };
    if copy < 0 {
        return Err(system("worker high FD"));
    }
    // SAFETY: successful duplication returned a new uniquely owned descriptor.
    Ok(unsafe { OwnedFd::from_raw_fd(copy) })
}
fn nonblocking(fd: RawFd) -> Result<(), Error> {
    // SAFETY: scalar flag operations address a trusted, exclusively held
    // channel before launch. No concurrent alias may mutate its status flags.
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
        return Err(system("worker channel nonblocking"));
    }
    // SAFETY: F_GETFL only observes the same still-live channel.
    let verified = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if verified < 0 || verified & libc::O_NONBLOCK == 0 {
        return Err(contract("worker channel remains blocking"));
    }
    Ok(())
}

pub(super) fn spawn(
    p: &PreparedStaticWorker,
    args: &[&str],
    scratch: RawFd,
) -> Result<Channels, Error> {
    spawn_inner(p, args, scratch, None, None)
}

/// Retain one authenticated native-entry socket above the dense input bank.
/// The pinned trusted executable receives its exact slot as the last argument;
/// it must rendezvous with the owning parent before any untrusted entry.
pub(crate) fn spawn_native(
    p: &PreparedStaticWorker,
    args: &[&str],
    scratch: RawFd,
    transfer: RawFd,
) -> Result<NativeChannels, Error> {
    let Channels { child, stdout, stderr, control, status } =
        spawn_inner(p, args, scratch, None, Some(transfer))?;
    let child = child.into_legacy()?;
    Ok(NativeChannels { child, stdout, stderr, control, status })
}

pub(super) fn spawn_contained(
    p: &PreparedStaticWorker,
    args: &[&str],
    scratch: RawFd,
    tree: Tree,
) -> Result<Channels, Error> {
    spawn_inner(p, args, scratch, Some(tree), None)
}

fn spawn_inner(
    p: &PreparedStaticWorker,
    args: &[&str],
    scratch: RawFd,
    mut tree: Option<Tree>,
    transfer: Option<RawFd>,
) -> Result<Channels, Error> {
    checked(&p.budget)?;
    if args.len() + usize::from(transfer.is_some()) > 8 {
        return Err(contract("worker argument count"));
    }
    // All duplicates are made before fork. The retained high socket is not
    // remapped into another high source, avoiding exec/status/transfer cycles.
    let transfer = transfer.map(high).transpose()?;
    let transfer_fd = transfer.as_ref().map(AsRawFd::as_raw_fd);
    if transfer_fd.is_some_and(|fd| !(64..=4096).contains(&fd)) {
        return Err(contract("native transfer slot"));
    }
    let transfer_argument = if let Some(fd) = transfer_fd {
        p.budget
            .charge(Charge { allocation_bytes: 32, work: 32, ..Charge::default() })
            .map_err(Error::Budget)?;
        let argument = fd.to_string();
        if argument.capacity() > 32 {
            return Err(contract("native transfer argument capacity"));
        }
        Some(argument)
    } else {
        None
    };
    let mut argv: [Option<Vec<u8>>; 10] = std::array::from_fn(|_| None);
    let mut total = 0usize;
    for (at, arg) in std::iter::once("trust-static-worker")
        .chain(args.iter().copied())
        .chain(transfer_argument.as_deref())
        .enumerate()
    {
        let length = arg.len().checked_add(1).ok_or_else(|| contract("argument overflow"))?;
        total = total.checked_add(length).ok_or_else(|| contract("argument overflow"))?;
        if total > 8192 {
            return Err(contract("worker argument bytes"));
        }
        p.budget
            .charge(Charge {
                allocation_bytes: (arg.len() + 1) as u64,
                work: 2 * arg.len() as u64,
                ..Charge::default()
            })
            .map_err(Error::Budget)?;
        if arg.as_bytes().contains(&0) {
            return Err(contract("worker argument NUL"));
        }
        let mut bytes = Vec::new();
        bytes.try_reserve_exact(arg.len() + 1).map_err(|_| {
            Error::Budget(p.budget.refuse(trust_process_isolation::Error::Allocation))
        })?;
        let slack = bytes.capacity().saturating_sub(arg.len() + 1);
        p.budget
            .charge(Charge { allocation_bytes: slack as u64, ..Charge::default() })
            .map_err(Error::Budget)?;
        bytes.extend_from_slice(arg.as_bytes());
        bytes.push(0);
        argv[at] = Some(bytes);
    }
    let mut pointers = [ptr::null(); 11];
    for (at, arg) in argv.iter().enumerate() {
        if let Some(arg) = arg {
            pointers[at] = arg.as_ptr().cast();
        }
    }
    let (stdout, out) = pipe()?;
    let (stderr, err) = pipe()?;
    let (status, status_write) = pipe()?;
    let (control, worker_control) =
        UnixStream::pair().map_err(|e| Error::System("worker control", e))?;
    // Configure the worker open-file description before high copies/remapping
    // and exec. Entry authenticates it and independently sets/verifies this
    // invariant before filtering; post-entry F_SETFL/dup/close stay forbidden.
    nonblocking(worker_control.as_raw_fd())?;
    let null = File::open("/dev/null").map_err(|e| Error::System("worker null", e))?;
    let mut sources: [Option<OwnedFd>; 32] = std::array::from_fn(|_| None);
    for (at, fd) in
        [null.as_raw_fd(), out.as_raw_fd(), err.as_raw_fd(), worker_control.as_raw_fd(), scratch]
            .into_iter()
            .enumerate()
    {
        sources[at] = Some(high(fd)?);
    }
    for at in 0..p.count {
        sources[5 + at] = Some(high(
            p.inputs[at].as_ref().ok_or_else(|| contract("input slot"))?.file.as_raw_fd(),
        )?);
    }
    let executable = high(p.worker.file.as_raw_fd())?;
    let exec_status = high(status_write.as_raw_fd())?;
    let mut remap = [-1; 32];
    for (at, fd) in sources.iter().enumerate() {
        if let Some(fd) = fd {
            remap[at] = fd.as_raw_fd();
        }
    }
    let executable_fd = executable.as_raw_fd();
    let status_fd = exec_status.as_raw_fd();
    for fd in [stdout.as_raw_fd(), stderr.as_raw_fd(), status.as_raw_fd(), control.as_raw_fd()] {
        nonblocking(fd)?;
    }
    let kernel = p.limits.kernel;
    // SAFETY: getpid is a scalar observation of this authoritative parent.
    let parent = unsafe { libc::getpid() };
    checked(&p.budget)?;
    let mut birth_pidfd = -1;
    let group = match tree.as_mut() {
        Some(tree) => Some(tree.arm_birth(&p.budget)?),
        None => None,
    };
    // SAFETY: all allocations/FD plans precede the fork-equivalent syscall.
    // There is no shared VM/stack. Child setup calls only async-signal-safe
    // operations and _exit/execveat; parent constructs exclusive custody next.
    let pid = match group {
        Some(group) => unsafe { contained_clone(group, &mut birth_pidfd) },
        None => unsafe { libc::fork() },
    };
    if pid < 0 {
        return Err(system("worker fork"));
    }
    if pid == 0 {
        // SAFETY: this is the newly forked child; prepared pointers and FD table
        // stay live until exec or _exit and setup performs no heap operations.
        unsafe {
            setup(
                &remap,
                5 + p.count,
                executable_fd,
                status_fd,
                transfer_fd,
                pointers.as_ptr(),
                parent,
                kernel,
            )
        };
    }
    let child = birth::transfer(pid, birth_pidfd, tree, &p.budget)?;
    checked(&p.budget)?;
    Ok(Channels { child, stdout, stderr, control, status })
}

unsafe fn failed(fd: RawFd, stage: u32) -> ! {
    // SAFETY: __errno_location returns this child thread's live errno storage.
    let errno = unsafe { *libc::__errno_location() };
    let mut bytes = [0; 8];
    bytes[..4].copy_from_slice(&stage.to_le_bytes());
    bytes[4..].copy_from_slice(&errno.to_le_bytes());
    // SAFETY: failure is child-only, fd is the preserved status pipe. This
    // fixed record cannot exceed PIPE_BUF; _exit avoids post-fork destructors.
    unsafe {
        libc::write(fd, bytes.as_ptr().cast(), 8);
        libc::_exit(120)
    }
}
unsafe fn setup(
    remap: &[RawFd; 32],
    count: usize,
    exec: RawFd,
    status: RawFd,
    transfer: Option<RawFd>,
    argv: *const *const libc::c_char,
    parent: libc::pid_t,
    kernel: crate::KernelLimits,
) -> ! {
    // SAFETY: all calls operate only on this child and prepared live scalars.
    unsafe {
        if libc::setpgid(0, 0) != 0 {
            failed(status, 1);
        }
        if libc::prctl(
            libc::PR_SET_PDEATHSIG,
            libc::SIGKILL as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
        ) != 0
            || libc::getppid() != parent
        {
            failed(status, 2);
        }
        for (at, source) in remap[..count].iter().enumerate() {
            if libc::dup2(*source, at as i32) < 0 {
                failed(status, 3);
            }
        }
        // A fixed stack plan preserves exactly exec, status and optional H.
        // Every source is a distinct high duplicate above the dense remaps.
        let mut kept = [exec as u32, status as u32, u32::MAX];
        let keep_count = if let Some(fd) = transfer {
            kept[2] = fd as u32;
            3
        } else {
            2
        };
        kept[..keep_count].sort_unstable();
        let mut next = count as u32;
        for fd in &kept[..keep_count] {
            if next < *fd && libc::syscall(libc::SYS_close_range, next, *fd - 1, 0u32) != 0 {
                failed(status, 4);
            }
            next = *fd + 1;
        }
        if libc::syscall(libc::SYS_close_range, next, u32::MAX, 0u32) != 0 {
            failed(status, 4);
        }
        if transfer.is_some_and(|fd| libc::fcntl(fd, libc::F_SETFD, 0) != 0) {
            failed(status, 4);
        }
        for (resource, limit) in [
            (libc::RLIMIT_CORE, 0),
            (libc::RLIMIT_AS, kernel.address_space_bytes),
            (libc::RLIMIT_STACK, kernel.stack_bytes),
            (libc::RLIMIT_FSIZE, kernel.file_bytes),
            (libc::RLIMIT_NOFILE, kernel.descriptors as u64),
        ] {
            let value = libc::rlimit { rlim_cur: limit, rlim_max: limit };
            if libc::setrlimit(resource, &value) != 0 {
                failed(status, 5);
            }
        }
        if libc::prctl(
            libc::PR_SET_NO_NEW_PRIVS,
            1 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
            0 as libc::c_ulong,
        ) != 0
        {
            failed(status, 6);
        }
        let env = [ptr::null::<libc::c_char>()];
        libc::syscall(
            libc::SYS_execveat,
            exec,
            c"".as_ptr(),
            argv,
            env.as_ptr(),
            libc::AT_EMPTY_PATH,
        );
        failed(status, 7)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Read;
    use std::time::{Duration, Instant};

    use trust_process_isolation::Limits;

    use super::*;
    #[test]
    fn preserved_cloexec_status_pipe_reports_actual_exec_failure()
    -> Result<(), Box<dyn std::error::Error>> {
        let budget = Budget::new(
            Limits {
                frame_bytes: 1024,
                wire_bytes: 4096,
                allocation_bytes: 4096,
                values: 100,
                work: 100000,
                calls: 10,
                live_handles: 2,
                depth: 8,
            },
            Instant::now() + Duration::from_secs(5),
        )?;
        let executable = File::open("/dev/null")?;
        let exec = high(executable.as_raw_fd())?;
        let (mut status, write) = pipe()?;
        let failure = high(write.as_raw_fd())?;
        nonblocking(status.as_raw_fd())?;
        // SAFETY: scalar parent identity observed before fork; the child below
        // performs only setup syscalls and terminal exec/_exit with live scalars.
        let parent = unsafe { libc::getpid() };
        let remap = [-1; 32];
        let argv = [c"fixture".as_ptr(), ptr::null()];
        // SAFETY: no allocation/locking occurs in the child after fork.
        let pid = unsafe { libc::fork() };
        if pid < 0 {
            return Err(system("fixture fork").into());
        }
        if pid == 0 {
            // SAFETY: prepared fixed FD/pointer data stays valid until _exit.
            unsafe {
                setup(
                    &remap,
                    0,
                    exec.as_raw_fd(),
                    failure.as_raw_fd(),
                    None,
                    argv.as_ptr(),
                    parent,
                    crate::KernelLimits {
                        address_space_bytes: 256 * 1024 * 1024,
                        stack_bytes: 8 * 1024 * 1024,
                        file_bytes: 1024 * 1024,
                        descriptors: 64,
                    },
                )
            }
        }
        let mut child = Child { pid, pidfd: None, reaped: false, budget: budget.clone() };
        drop(write);
        drop(failure);
        drop(exec);
        let mut bytes = [0; 8];
        let mut got = 0;
        while got < bytes.len() {
            budget.check()?;
            match status.read(&mut bytes[got..]) {
                Ok(0) => return Err(contract("missing fixture exec failure").into()),
                Ok(n) => got += n,
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                    std::thread::sleep(Duration::from_millis(1))
                }
                Err(e) => return Err(e.into()),
            }
        }
        let stage = u32::from_le_bytes(bytes[..4].try_into()?);
        let errno = i32::from_le_bytes(bytes[4..].try_into()?);
        assert_eq!(stage, 7);
        assert!(matches!(errno, libc::EACCES | libc::ENOEXEC));
        let status = child.stop_and_reap()?;
        assert!(child.reaped);
        assert!(libc::WIFEXITED(status));
        assert_eq!(libc::WEXITSTATUS(status), 120);
        Ok(())
    }
}

#[cfg(test)]
mod tree_tests;
