#![crate_type = "lib"]
use std::os::fd::{AsRawFd, FromRawFd, IntoRawFd, OwnedFd, RawFd};
use std::os::unix::process::CommandExt;
use std::process::{Command, Stdio};

#[derive(Clone, Copy)]
pub struct Strip {
    bound: RawFd,
}

// 1. std::process::Command, plain spawn (the bug-class site: inherits every non-CLOEXEC fd)
pub fn c1_plain_spawn() -> std::io::Result<u32> {
    let child = Command::new("/bin/true").spawn()?;
    Ok(child.id())
}
// 2. Command builder methods by &mut
pub fn c2_builder(cmd: &mut Command) {
    cmd.arg("-c").stdin(Stdio::null());
}
// 3. pre_exec with a by-move FnMut closure capturing a Copy value, looping over an fd range
pub fn c3_pre_exec(cmd: &mut Command, strip: Strip) {
    unsafe {
        cmd.pre_exec(move || {
            for fd in 3..strip.bound {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            Ok(())
        });
    }
}
// 4. pre_exec whose closure body is a straight-line call (no loop)
pub fn c4_pre_exec_call(cmd: &mut Command, fd: RawFd) {
    unsafe {
        cmd.pre_exec(move || {
            libc::close(fd);
            Ok(())
        });
    }
}
// 5. OwnedFd / AsRawFd / FromRawFd / IntoRawFd
pub fn c5_as_raw(fd: &OwnedFd) -> RawFd {
    fd.as_raw_fd()
}
pub fn c6_from_raw(raw: RawFd) -> OwnedFd {
    unsafe { OwnedFd::from_raw_fd(raw) }
}
pub fn c7_into_raw(fd: OwnedFd) -> RawFd {
    fd.into_raw_fd()
}
pub fn c8_drop_owned(fd: OwnedFd) {
    drop(fd)
}
// 6. a fd-range loop over libc (cross-crate) fcntl, as a statement and with a counter
pub fn c9_range_loop(lo: RawFd, hi: RawFd) {
    for fd in lo..hi {
        unsafe {
            libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
        }
    }
}
pub fn c10_range_loop_count(lo: RawFd, hi: RawFd) -> i32 {
    let mut n = 0;
    for fd in lo..hi {
        if unsafe { libc::fcntl(fd, libc::F_GETFD) } >= 0 {
            n += 1;
        }
    }
    n
}
pub fn c11_while_loop(lo: RawFd, hi: RawFd) {
    let mut fd = lo;
    while fd < hi {
        unsafe {
            libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
        }
        fd += 1;
    }
}
// 7. flock on an owned fd (ownerlock shape)
pub fn c12_flock(fd: &OwnedFd) -> bool {
    unsafe { libc::flock(fd.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) == 0 }
}
// 8. fork/exec straight line (pty shape), with the child strip
pub fn c13_fork(strip: Strip, path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < strip.bound {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}
// 9. out-param through &mut local (waitpid)
pub fn c14_waitpid(pid: i32) -> i32 {
    let mut st = 0;
    unsafe { libc::waitpid(pid, &mut st, 0) };
    st
}
// 10. pipe into [i32; 2]
pub fn c15_pipe() -> (i32, i32) {
    let mut p = [0i32; 2];
    unsafe { libc::pipe(p.as_mut_ptr()) };
    (p[0], p[1])
}
