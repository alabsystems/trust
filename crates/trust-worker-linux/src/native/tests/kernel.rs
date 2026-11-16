//! Real kernel service only, not a production launcher or native-load test.
//! The diagnostic forks a trusted single-thread entry, without a new exec mm;
//! B3a's separately tested sealed exec and root's retained-mm probe cover those
//! distinct boundaries. No DSO is loaded here.
use std::fs::File;
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, BorrowedFd, FromRawFd, OwnedFd};
use std::os::unix::net::UnixStream;
use std::time::{Duration, Instant};

use super::super::bootstrap;
use super::super::kernel::Service;
use super::{budget, closure};
use crate::launcher::child::Child;
use crate::{KernelLimits, Profile};

mod control;

struct Fixture {
    child: Child,
    control: UnixStream,
    bootstrap: File,
    memory: File,
}
struct Directory(std::path::PathBuf);
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir(&self.0);
    }
}
fn pair(kind: i32) -> (File, File) {
    let mut fds = [-1; 2];
    // SAFETY: one complete writable pair; successful socketpair owns both FDs.
    assert_eq!(
        unsafe { libc::socketpair(libc::AF_UNIX, kind | libc::SOCK_CLOEXEC, 0, fds.as_mut_ptr()) },
        0
    );
    // SAFETY: the successful syscall returned two fresh unique owned FDs.
    unsafe { (File::from_raw_fd(fds[0]), File::from_raw_fd(fds[1])) }
}
fn pipe() -> (File, File) {
    let mut fds = [-1; 2];
    // SAFETY: pipe2 writes exactly two fresh owned descriptors.
    assert_eq!(unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) }, 0);
    // SAFETY: the successful syscall returned two fresh unique owned FDs.
    unsafe { (File::from_raw_fd(fds[0]), File::from_raw_fd(fds[1])) }
}
fn high(fd: i32) -> OwnedFd {
    // SAFETY: duplicate live fixture-only sources above dense targets.
    let copy = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 64) };
    assert!((64..128).contains(&copy));
    // SAFETY: the successful duplicate is a fresh unique owned descriptor.
    unsafe { OwnedFd::from_raw_fd(copy) }
}
fn wait(fd: i32, b: &trust_process_isolation::Budget) {
    loop {
        b.check().unwrap();
        let mut p = libc::pollfd { fd, events: libc::POLLIN, revents: 0 };
        // SAFETY: one writable poll record, finite1ms wait, no retained pointer.
        let n = unsafe { libc::poll(&mut p, 1, 1) };
        assert!(n >= 0);
        if n == 1 {
            assert_eq!(p.revents, libc::POLLIN);
            return;
        }
    }
}
fn handoff(f: &mut Fixture, b: &trust_process_isolation::Budget) {
    loop {
        b.check().unwrap();
        let mut p = libc::pollfd { fd: f.bootstrap.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        // SAFETY: one bounded fixture poll record with a finite wait.
        let n = unsafe { libc::poll(&mut p, 1, 1) };
        assert!(n >= 0);
        if n == 1 {
            // SOCK_SEQPACKET preserves the complete queued handoff after the
            // child closes its one-shot sender. POLLIN|POLLHUP is expected; the
            // receiver still validates exact bytes, credentials and one FD.
            if p.revents & libc::POLLIN == 0 || p.revents & !(libc::POLLIN | libc::POLLHUP) != 0 {
                let status = f.child.stop_and_reap().unwrap();
                panic!(
                    "trusted entry stopped before handoff: events={} status={} exit={} signal={}",
                    p.revents,
                    status,
                    libc::WEXITSTATUS(status),
                    libc::WTERMSIG(status)
                );
            }
            let mut installed = [0u8; 1];
            f.control.read_exact(&mut installed).unwrap();
            assert_eq!(
                &installed, b"I",
                "fixed entry continuation requires installed restrictions"
            );
            return;
        }
    }
}
fn start(mode: u8, b: trust_process_isolation::Budget) -> (Fixture, Directory) {
    let (mut control, peer) = UnixStream::pair().unwrap();
    control.set_read_timeout(Some(Duration::from_secs(2))).unwrap();
    if mode == 17 {
        let size = 1024i32;
        // SAFETY: fixed fixture-owned socket and exact initialized integer;
        // trusted setup only, before fork, authentication and filter install.
        assert_eq!(
            unsafe {
                libc::setsockopt(
                    peer.as_raw_fd(),
                    libc::SOL_SOCKET,
                    libc::SO_SNDBUF,
                    (&size as *const i32).cast(),
                    std::mem::size_of_val(&size) as libc::socklen_t,
                )
            },
            0
        );
    }
    let (boot, bootpeer) = pair(libc::SOCK_SEQPACKET);
    bootstrap::configure(&boot, &b).unwrap();
    let (_out, out) = pipe();
    let (_err, err) = pipe();
    let null = File::open("/dev/null").unwrap();
    let path = std::env::temp_dir().join(format!(
        "trust-native-scratch-{}-{}",
        std::process::id(),
        super::SEQUENCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    let c = std::ffi::CString::new(path.as_os_str().as_encoded_bytes()).unwrap();
    // SAFETY: the terminated fixture-owned path is read-only O_PATH.
    let scratchfd = unsafe { libc::open(c.as_ptr(), libc::O_PATH | libc::O_CLOEXEC) };
    assert!(scratchfd >= 0);
    // SAFETY: successful open returned one fresh unique owned descriptor.
    let scratch = unsafe { File::from_raw_fd(scratchfd) };
    let sources = [
        high(null.as_raw_fd()),
        high(out.as_raw_fd()),
        high(err.as_raw_fd()),
        high(peer.as_raw_fd()),
        high(scratch.as_raw_fd()),
        high(bootpeer.as_raw_fd()),
    ];
    // SAFETY: this test's trusted child runs only the fixed diagnostic entry;
    // no production fork-only startup or constructor-safety claim is made.
    let pid = unsafe { libc::fork() };
    assert!(pid >= 0);
    if pid == 0 {
        child(&sources, mode, &b);
    }
    let child = Child { pid, pidfd: None, reaped: false, budget: b.clone() };
    drop(peer);
    drop(bootpeer);
    drop(sources);
    let mut marker = [0; 1];
    control.read_exact(&mut marker).unwrap();
    assert_eq!(marker, [b'M']);
    // The direct parent opens exactly its unreaped trusted child before the
    // clamp. It is the current post-fork mm; no further exec is allowed here.
    let memory = File::open(format!("/proc/{pid}/mem")).unwrap();
    control.write_all(b"A").unwrap();
    (Fixture { child, control, bootstrap: boot, memory }, Directory(path))
}
fn child(sources: &[OwnedFd; 6], mode: u8, b: &trust_process_isolation::Budget) -> ! {
    // SAFETY: fixed trusted fixture setup changes only this child. High copies
    // prevent dup cycles, parent-death cleanup is armed, no user code exists.
    unsafe {
        if libc::setpgid(0, 0) != 0
            || libc::prctl(libc::PR_SET_PDEATHSIG, libc::SIGKILL, 0, 0, 0) != 0
        {
            libc::_exit(100);
        }
        for (n, fd) in sources[..5].iter().enumerate() {
            if libc::dup2(fd.as_raw_fd(), n as i32) < 0 {
                libc::_exit(101);
            }
        }
        if libc::dup2(sources[5].as_raw_fd(), 128) < 0
            || libc::syscall(libc::SYS_close_range, 5u32, 127u32, 0u32) != 0
            || libc::syscall(libc::SYS_close_range, 129u32, u32::MAX, 0u32) != 0
        {
            libc::_exit(102);
        }
        libc::clearenv();
        if libc::write(3, b"M".as_ptr().cast(), 1) != 1 {
            libc::_exit(103);
        }
        let mut ack = 0u8;
        if libc::read(3, (&mut ack as *mut u8).cast(), 1) != 1 || ack != b'A' {
            libc::_exit(104);
        }
    }
    if mode == 4 {
        // SAFETY: a zeroed native sigaction is initialized with a fixed trusted
        // handler and empty mask; no untrusted code or alternate stack exists.
        unsafe {
            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = interrupted as *const () as usize;
            if libc::sigemptyset(&mut action.sa_mask) != 0
                || libc::sigaction(libc::SIGUSR1, &action, std::ptr::null_mut()) != 0
            {
                libc::_exit(116);
            }
        }
    }
    if mode == 15 || mode == 16 {
        // SAFETY: trusted fixture entry sets an explicit tested SIGPIPE
        // disposition and unblocks it before installing the unchanged filter.
        unsafe {
            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = if mode == 15 { libc::SIG_DFL } else { libc::SIG_IGN };
            let mut signals: libc::sigset_t = std::mem::zeroed();
            if libc::sigemptyset(&mut action.sa_mask) != 0
                || libc::sigaction(libc::SIGPIPE, &action, std::ptr::null_mut()) != 0
                || libc::sigemptyset(&mut signals) != 0
                || libc::sigaddset(&mut signals, libc::SIGPIPE) != 0
                || libc::sigprocmask(libc::SIG_UNBLOCK, &signals, std::ptr::null_mut()) != 0
            {
                libc::_exit(116);
            }
        }
    }
    // SAFETY: getppid is a scalar fixture observation before restrictions.
    let parent = unsafe { libc::getppid() };
    let limits = KernelLimits {
        address_space_bytes: 256 << 20,
        stack_bytes: 8 << 20,
        file_bytes: 1 << 20,
        descriptors: if mode == 9 { 63 } else { 64 },
    };
    let profile = Profile { parent_pid: parent, inputs: &[], limits };
    if mode == 5 {
        // SAFETY: replace the fixture-owned transfer slot with its validated
        // null stdin before entry; admission must reject this descriptor role.
        if unsafe { libc::dup2(0, 128) } != 128 {
            exit(118);
        }
    } else if mode == 6 {
        // SAFETY: a preexisting ambient listener-slot descriptor is deliberate;
        // installation must close it and acquire the exact free listener slot.
        if unsafe { libc::dup2(0, 5) } != 5 {
            exit(118);
        }
    } else if mode == 7 {
        // SAFETY: deliberately clear the fixture's parent-death restriction;
        // the native entry must refuse before its fixed continuation marker.
        if unsafe { libc::prctl(libc::PR_SET_PDEATHSIG, 0, 0, 0, 0) } != 0 {
            exit(118);
        }
    } else if mode == 8 {
        b.cancel();
    }
    // SAFETY: setup owns live FD128. Its borrow lasts through entry admission;
    // no untrusted handler, thread or constructor can replace it in this test.
    let transfer = unsafe { BorrowedFd::borrow_raw(128) };
    let mut installed = match crate::restriction::install_native(&profile, b, transfer) {
        Ok(installed) => installed,
        Err(_) => {
            if b.check().is_ok() {
                exit(119);
            }
            // SAFETY: before or after a partial clamp, the parent-bound stream
            // permits this one-byte refusal diagnostic. No entry follows it.
            unsafe { libc::write(3, b"R".as_ptr().cast(), 1) };
            exit(117);
        }
    };
    if installed.restrictions.landlock_abi() < 3 || installed.listener.as_raw_fd() != 5 {
        exit(110);
    }
    // SAFETY: a fixed diagnostic continuation, not a DSO constructor. The
    // installed policy permits this retained parent-bound stream only.
    if unsafe { libc::write(3, b"I".as_ptr().cast(), 1) } != 1 {
        exit(120);
    }
    if mode >= 10 {
        // Only fixture transport controls use this continuation. The native
        // policy is already installed; no loader/Ready or broker is activated.
        drop(installed.listener);
        // SAFETY: the one-shot bootstrap transfer descriptor has its existing
        // separately admitted close role. Protected FD3 remains untouched.
        unsafe { libc::close(128) };
        control::child(&mut installed.restrictions, mode, b)
    }
    send_listener(installed.listener.as_raw_fd(), mode == 3);
    drop(installed);
    // SAFETY: the two specifically permitted bootstrap descriptors close once;
    // bank issuance excludes them forever. Future FD allocation is kernel-denied.
    unsafe {
        libc::close(128);
    }
    if control::byte(b) != b'L' {
        exit(111);
    }
    let path = if mode == 1 { c"/proc/self/fd/1" } else { c"/trust-cap/libfixture.so" };
    let mut result = [0u8; 8];
    for at in [0, 4] {
        // SAFETY: the NUL-terminated fixture literal is only a virtual alias;
        // the kernel blocks this open for the immutable capability service.
        let fd = unsafe {
            libc::syscall(
                libc::SYS_openat,
                libc::AT_FDCWD,
                path.as_ptr(),
                libc::O_RDONLY | libc::O_CLOEXEC,
                0u32,
            )
        };
        if fd != 33 + (at / 4) as i64 {
            exit(112);
        }
        // SAFETY: one bounded initialized destination; these bank FDs are RO.
        if unsafe { libc::read(fd as i32, result[at..].as_mut_ptr().cast(), 4) } != 4 {
            exit(113);
        }
    }
    // SAFETY: the parent-bound channel receives eight diagnostic bytes only.
    if unsafe { libc::write(3, result.as_ptr().cast(), result.len()) } != 8 {
        exit(114);
    }
    exit(0)
}
extern "C" fn interrupted(_: i32) {
    // SAFETY: the signal handler writes one constant byte to the retained
    // parent-bound channel only; write is async-signal-safe and policy-admitted.
    unsafe {
        libc::write(3, b"S".as_ptr().cast(), 1);
    }
}
fn send_listener(fd: i32, duplicate: bool) {
    #[repr(C)]
    struct Space {
        words: [usize; 8],
    }
    let mut control = Space { words: [0; 8] };
    let mut iov = libc::iovec { iov_base: b"LISTENv1".as_ptr() as *mut _, iov_len: 8 };
    // SAFETY: msghdr is a zero-initializable C plain-data structure.
    let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
    msg.msg_iov = &mut iov;
    msg.msg_iovlen = 1;
    msg.msg_control = control.words.as_mut_ptr().cast();
    // SAFETY: aligned fixed control storage fits a single FD; initialized CMSG
    // lengths and payload point only within it. Only the one-shot H permits it.
    unsafe {
        let size = if duplicate { 8 } else { 4 };
        msg.msg_controllen = libc::CMSG_SPACE(size).try_into().unwrap_or_else(|_| exit(115));
        let c = libc::CMSG_FIRSTHDR(&msg);
        (*c).cmsg_level = libc::SOL_SOCKET;
        (*c).cmsg_type = libc::SCM_RIGHTS;
        (*c).cmsg_len = libc::CMSG_LEN(size).try_into().unwrap_or_else(|_| exit(115));
        (libc::CMSG_DATA(c) as *mut i32).write_unaligned(fd);
        if duplicate {
            (libc::CMSG_DATA(c) as *mut i32).add(1).write_unaligned(fd);
        }
        if libc::sendmsg(128, &msg, libc::MSG_NOSIGNAL) != 8 {
            libc::_exit(115);
        }
    }
}
fn exit(code: i32) -> ! {
    // SAFETY: diagnostics terminate without running forbidden FD destructors.
    unsafe { libc::_exit(code) }
}
#[test]
fn real_kernel_immutable_service_retains_mm_and_independent_offsets() {
    let b = budget();
    let c = closure(b.clone());
    let expected = c.binding().artifact;
    let (mut f, _dir) = start(0, b.clone());
    handoff(&mut f, &b);
    let listener = bootstrap::receive(&f.bootstrap, f.child.pid as u32, &b).unwrap();
    assert!(File::open(format!("/proc/{}/mem", f.child.pid)).is_err());
    let mut service = Service::adopt(listener, f.memory, f.child.pid as u32, c).unwrap();
    f.control.write_all(b"L").unwrap();
    let mut identity = None;
    for at in 0..2 {
        wait(service.listener_fd(), &b);
        let issued = service.ready_once().unwrap();
        assert_eq!((issued.object, issued.target), (0, 33 + at));
        assert_eq!(issued.sha256, expected);
        assert_eq!(issued.size, 8192);
        if let Some(original) = identity {
            assert_eq!(issued.file, original);
        } else {
            identity = Some(issued.file);
        }
    }
    let mut bytes = [0; 8];
    f.control.read_exact(&mut bytes).unwrap();
    assert_eq!(&bytes, b"\x7fELF\x7fELF");
    let end = Instant::now() + Duration::from_secs(1);
    while !f.child.exited().unwrap() {
        assert!(Instant::now() < end);
        std::thread::sleep(Duration::from_millis(1));
    }
    let status = f.child.stop_and_reap().unwrap();
    assert_eq!(libc::WEXITSTATUS(status), 0);
    drop(service);
    drop(f.control);
    drop(f.bootstrap);
    b.check().unwrap();
}

#[test]
fn real_native_entry_refuses_before_continuation_and_cannot_retry() {
    for mode in [5, 7, 8, 9] {
        let b = budget();
        let (mut f, _dir) = start(mode, b);
        let mut marker = [0u8; 1];
        f.control.read_exact(&mut marker).unwrap();
        assert_eq!(&marker, b"R");
        let status = f.child.stop_and_reap().unwrap();
        // stop_and_reap may win the race with the child's immediate _exit.
        assert!(libc::WIFEXITED(status) || libc::WTERMSIG(status) == libc::SIGKILL);
        if libc::WIFEXITED(status) {
            assert_eq!(libc::WEXITSTATUS(status), 117);
        }
        let mut next = [0u8; 1];
        assert_eq!(
            f.control.read(&mut next).unwrap(),
            0,
            "no installed/entry marker followed refusal"
        );
    }
}

#[test]
fn real_native_entry_closes_ambient_predicted_listener_slot() {
    let b = budget();
    let (mut f, _dir) = start(6, b.clone());
    handoff(&mut f, &b);
    let listener = bootstrap::receive(&f.bootstrap, f.child.pid as u32, &b).unwrap();
    let mut service =
        Service::adopt(listener, f.memory, f.child.pid as u32, closure(b.clone())).unwrap();
    f.control.write_all(b"L").unwrap();
    for _ in 0..2 {
        wait(service.listener_fd(), &b);
        service.ready_once().unwrap();
    }
    let mut bytes = [0; 8];
    f.control.read_exact(&mut bytes).unwrap();
    assert_eq!(&bytes, b"\x7fELF\x7fELF");
    f.child.stop_and_reap().unwrap();
}
#[test]
fn real_unknown_procfd_request_refuses_and_reaps() {
    let b = budget();
    let c = closure(b.clone());
    let (mut f, _dir) = start(1, b.clone());
    handoff(&mut f, &b);
    let listener = bootstrap::receive(&f.bootstrap, f.child.pid as u32, &b).unwrap();
    let mut service = Service::adopt(listener, f.memory, f.child.pid as u32, c).unwrap();
    f.control.write_all(b"L").unwrap();
    wait(service.listener_fd(), &b);
    assert!(service.ready_once().is_err());
    assert!(b.check().is_err());
    assert_eq!(libc::WTERMSIG(f.child.stop_and_reap().unwrap()), libc::SIGKILL);
}

#[test]
fn real_terminal_owner_or_target_cannot_resume_service() {
    for cancel in [false, true] {
        let b = budget();
        let c = closure(b.clone());
        let (mut f, _dir) = start(0, b.clone());
        handoff(&mut f, &b);
        let listener = bootstrap::receive(&f.bootstrap, f.child.pid as u32, &b).unwrap();
        let mut service = Service::adopt(listener, f.memory, f.child.pid as u32, c).unwrap();
        f.control.write_all(b"L").unwrap();
        wait(service.listener_fd(), &b);
        if cancel {
            b.cancel();
        } else {
            f.child.stop_and_reap().unwrap();
        }
        assert!(service.ready_once().is_err());
        assert!(b.check().is_err());
        if !f.child.reaped {
            f.child.stop_and_reap().unwrap();
        }
    }
}

#[test]
fn real_handoff_requires_exact_owner_and_one_descriptor() {
    for mode in [0, 3] {
        let b = budget();
        let (mut f, _dir) = start(mode, b.clone());
        handoff(&mut f, &b);
        let task = f.child.pid as u32 + u32::from(mode == 0);
        assert!(bootstrap::receive(&f.bootstrap, task, &b).is_err());
        assert!(b.check().is_err());
        f.child.stop_and_reap().unwrap();
    }
}

#[test]
fn real_readiness_then_target_exit_or_nonfatal_signal_refuses() {
    for mode in [0, 4] {
        let b = budget();
        let c = closure(b.clone());
        let (mut f, _dir) = start(mode, b.clone());
        handoff(&mut f, &b);
        let listener = bootstrap::receive(&f.bootstrap, f.child.pid as u32, &b).unwrap();
        let mut service = Service::adopt(listener, f.memory, f.child.pid as u32, c).unwrap();
        f.control.write_all(b"L").unwrap();
        wait(service.listener_fd(), &b);
        assert!(
            service
                .ready_once_after_poll(|| {
                    if mode == 0 {
                        f.child.stop_and_reap().unwrap();
                    } else {
                        // SAFETY: this is the still-owned unreaped direct child; the
                        // fixed nonfatal handler acknowledges actual signal delivery.
                        assert_eq!(unsafe { libc::kill(f.child.pid, libc::SIGUSR1) }, 0);
                        let mut seen = [0u8; 1];
                        f.control.read_exact(&mut seen).unwrap();
                        assert_eq!(&seen, b"S");
                    }
                })
                .is_err()
        );
        assert!(b.check().is_err());
        assert!(service.ready_once().is_err());
        if !f.child.reaped {
            f.child.stop_and_reap().unwrap();
        }
    }
}
