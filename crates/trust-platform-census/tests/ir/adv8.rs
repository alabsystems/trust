#![crate_type = "lib"]
use std::os::fd::FromRawFd;
// Control for C-2: an std OwnedFd dropped implicitly in the child.
pub fn adv_owned_implicit(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        {
            let _t = unsafe { std::os::fd::OwnedFd::from_raw_fd(libc::dup(1)) };
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}
