//! Actual native seccomp/Landlock controls, without a DSO or Ready producer.
//! The existing owned fork fixture supplies B3's FD roles and empty environment.
//! Its post-fork mm is a diagnostic, not qualification of a production native
//! executable/runtime closure or the separate exact native Client ABI bridge.
use std::io::{Read, Write};
use std::net::Shutdown;
use std::time::{Duration, Instant};

use trust_process_isolation::{Binding, Budget, Envelope, Handle, HandleKind, Message, Transport};

use super::{Fixture, exit, start};

fn budget() -> Budget {
    let base = super::budget();
    let mut limits = base.limits();
    limits.frame_bytes = 65536;
    Budget::new(limits, base.deadline()).unwrap()
}

fn begin() -> Envelope {
    let binding = Binding {
        version: 1,
        invocation: 1,
        compiler: [1; 32],
        worker: [2; 32],
        artifact: [3; 32],
        metadata: [4; 32],
        unit: [5; 32],
        input_closure: [6; 32],
        host_abi: [7; 32],
    };
    let stream = Handle { invocation: 1, slot: 0, generation: 1, kind: HandleKind::Stream };
    let span = Handle { invocation: 1, slot: 1, generation: 1, kind: HandleKind::Span };
    Envelope {
        binding,
        message: Message::Begin {
            declaration: 0,
            kind: 0,
            inputs: vec![stream],
            globals: [span; 3],
        },
    }
}
pub(super) fn byte(b: &Budget) -> u8 {
    let mut byte = 0;
    loop {
        if b.check().is_err() {
            exit(121)
        }
        // SAFETY: initialized one-byte writable storage and authenticated FD3.
        let n = unsafe { libc::read(3, (&mut byte as *mut u8).cast(), 1) };
        if n == 1 {
            return byte;
        }
        if n >= 0 || std::io::Error::last_os_error().raw_os_error() != Some(libc::EAGAIN) {
            exit(121)
        }
        let timeout = libc::timespec { tv_sec: 0, tv_nsec: 1_000_000 };
        let mut p = libc::pollfd { fd: 3, events: libc::POLLIN, revents: 0 };
        // SAFETY: initialized single poll record and finite initialized timeout.
        unsafe { libc::ppoll(&mut p, 1, &timeout, std::ptr::null()) };
    }
}
pub(super) fn child(installed: &mut crate::Installed, mode: u8, b: &Budget) -> ! {
    let mut control = installed.control().unwrap_or_else(|_| exit(122));
    let received = control.receive(b);
    if mode == 18 || mode == 19 {
        if received.is_ok() || b.check().is_ok() || control.receive(b).is_ok() {
            exit(123)
        }
        refused();
    }
    let frame = received.unwrap_or_else(|_| exit(122));
    let before = b.usage().unwrap_or_else(|_| exit(122)).wire_bytes;
    let request = trust_process_isolation::decode(&frame, b).unwrap_or_else(|_| exit(122));
    if request != begin()
        || b.usage().unwrap_or_else(|_| exit(122)).wire_bytes != before + frame.len() as u64
    {
        exit(122)
    }
    let finish = Envelope { binding: request.binding, message: Message::Finish { output: None } };
    let frame = trust_process_isolation::encode(&finish, b).unwrap_or_else(|_| exit(122));
    if mode == 10 {
        control.send(&frame, b).unwrap_or_else(|_| exit(122));
        control.close();
        drop(control);
        // SAFETY: only admitted observations of the retained protected slot.
        if unsafe { libc::fcntl(3, libc::F_GETFD) } < 0
            || unsafe { libc::fcntl(3, libc::F_GETFL) } & libc::O_NONBLOCK == 0
            || b.check().is_err()
        {
            exit(123)
        }
        exit(0)
    }
    if mode == 12 {
        // Drop is logical and the latch lives in Installed, not this borrow.
        drop(control);
        if installed.control().is_ok() || b.check().is_ok() {
            exit(123)
        }
        refused();
    }
    let error = match mode {
        11 => {
            let other = Budget::new(b.limits(), b.deadline()).unwrap_or_else(|_| exit(123));
            let error = control.send(&frame, &other).unwrap_err();
            if other.check().is_err() {
                exit(123)
            }
            error
        }
        13 => {
            b.cancel();
            control.receive(b).unwrap_err()
        }
        14 => control.receive(b).unwrap_err(),
        15 | 16 => control.send(&frame, b).unwrap_err(),
        17 => {
            let large = Envelope {
                binding: finish.binding,
                message: Message::Failure { reason: "x".repeat(60_000) },
            };
            let large = trust_process_isolation::encode(&large, b).unwrap_or_else(|_| exit(123));
            control.send(&large, b).unwrap_err()
        }
        _ => exit(123),
    };
    if b.check().is_ok() || control.send(&frame, b) != Err(error) {
        exit(123)
    }
    if mode == 16 || mode == 17 {
        // Broken peer / full send buffer cannot carry a refusal diagnostic.
        // SAFETY: verify retained FD3 survived logical refusal, then terminate.
        if unsafe { libc::fcntl(3, libc::F_GETFD) } < 0 {
            exit(123)
        }
        exit(76)
    }
    refused()
}
fn refused() -> ! {
    // SAFETY: the fixed diagnostic uses the still-retained parent-bound slot;
    // the parent is reading in these modes and kernel exit supplies final EOF.
    if unsafe { libc::fcntl(3, libc::F_GETFD) } < 0
        || unsafe { libc::write(3, b"R".as_ptr().cast(), 1) } != 1
    {
        exit(123)
    }
    exit(76)
}
fn installed(f: &mut Fixture) {
    let mut marker = [0];
    f.control.read_exact(&mut marker).unwrap();
    assert_eq!(&marker, b"I", "no transport before actual native filter installation");
}
fn status(f: &mut Fixture, b: &Budget) -> i32 {
    while !f.child.exited().unwrap() {
        b.check().unwrap();
        std::thread::sleep(Duration::from_millis(1));
    }
    let status = f.child.stop_and_reap().unwrap();
    let mut unused = 0;
    // SAFETY: only this fixture's owned, already-reaped positive PID is queried.
    assert_eq!(unsafe { libc::waitpid(f.child.pid, &mut unused, libc::WNOHANG) }, -1);
    assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::ECHILD));
    status
}
#[test]
fn native_filter_retained_control_finish_eof_successful_reaped_exit() {
    let b = budget();
    let (mut f, _dir) = start(10, b.clone());
    installed(&mut f);
    let frame = trust_process_isolation::encode(&begin(), &b).unwrap();
    // Force a partial prefix and a readiness wait under the installed policy.
    f.control.write_all(&frame[..1]).unwrap();
    std::thread::sleep(Duration::from_millis(20));
    f.control.write_all(&frame[1..]).unwrap();
    let mut prefix = [0; 4];
    f.control.read_exact(&mut prefix).unwrap();
    let len = trust_process_isolation::frame_payload_length(prefix, &b).unwrap();
    let mut result = vec![0; len + 4];
    result[..4].copy_from_slice(&prefix);
    f.control.read_exact(&mut result[4..]).unwrap();
    assert_eq!(
        trust_process_isolation::decode(&result, &b).unwrap(),
        Envelope { binding: begin().binding, message: Message::Finish { output: None } }
    );
    assert_eq!(f.control.read(&mut [0]).unwrap(), 0, "Finish requires actual EOF");
    let status = status(&mut f, &b);
    assert!(libc::WIFEXITED(status));
    assert_eq!(libc::WEXITSTATUS(status), 0);
    b.check().unwrap();
}
#[test]
fn native_filter_owner_drop_cancellation_and_bad_frames_stay_terminal() {
    for mode in [11, 12, 13, 18, 19] {
        let b = budget();
        let (mut f, _dir) = start(mode, b.clone());
        installed(&mut f);
        let mut frame = trust_process_isolation::encode(&begin(), &b).unwrap();
        if mode == 18 {
            frame = (b.limits().frame_bytes + 1).to_le_bytes().to_vec();
        }
        if mode == 19 {
            frame.truncate(7);
        }
        f.control.write_all(&frame).unwrap();
        if mode == 19 {
            f.control.shutdown(Shutdown::Write).unwrap();
        }
        let mut marker = [0];
        f.control.read_exact(&mut marker).unwrap();
        assert_eq!(&marker, b"R", "mode {mode} must refuse before Finish");
        assert_eq!(f.control.read(&mut marker).unwrap(), 0);
        let status = status(&mut f, &b);
        assert!(libc::WIFEXITED(status));
        assert_eq!(libc::WEXITSTATUS(status), 76);
    }
}
#[test]
fn native_filter_sigpipe_default_is_terminal_and_ignored_is_sticky() {
    for mode in [15, 16] {
        let b = budget();
        let (mut f, _dir) = start(mode, b.clone());
        installed(&mut f);
        // Shut the parent's receiving half before supplying Begin: the child
        // must attempt write only after it has consumed this complete request.
        f.control.shutdown(Shutdown::Read).unwrap();
        f.control.write_all(&trust_process_isolation::encode(&begin(), &b).unwrap()).unwrap();
        let status = status(&mut f, &b);
        if mode == 15 {
            assert!(libc::WIFSIGNALED(status));
            assert_eq!(libc::WTERMSIG(status), libc::SIGPIPE);
        } else {
            assert!(libc::WIFEXITED(status));
            assert_eq!(libc::WEXITSTATUS(status), 76);
        }
    }
}
#[test]
fn native_filter_read_and_backpressured_write_use_original_deadline() {
    for mode in [14, 17] {
        let owner = budget();
        let b = Budget::new(owner.limits(), Instant::now() + Duration::from_secs(4)).unwrap();
        let (mut f, _dir) = start(mode, b.clone());
        installed(&mut f);
        f.control.write_all(&trust_process_isolation::encode(&begin(), &b).unwrap()).unwrap();
        // Keep parent endpoint alive but do not read until child deadline.
        let status = status(&mut f, &owner);
        assert!(b.check().is_err(), "child must reach original absolute deadline");
        assert!(libc::WIFEXITED(status));
        assert_eq!(libc::WEXITSTATUS(status), 76);
        let mut bytes = Vec::new();
        f.control.read_to_end(&mut bytes).unwrap();
        if mode == 14 {
            assert_eq!(bytes, b"R");
        } else {
            assert!(!bytes.is_empty() && bytes.len() < 60_000, "partial nonblocking send");
        }
    }
}
