#![crate_type = "lib"]
// E1: the child creates a kqueue; if that fails (ENOMEM/ENFILE are real
// outcomes) it execs WITHOUT the strip: every inherited foreign fd leaks.
pub fn adv_errpath_kqueue(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let kq = unsafe { libc::kqueue() };
        if kq == -1 {
            unsafe {
                libc::execv(path, argv);
                libc::_exit(127)
            }
        }
        let mut fd = 3;
        while fd < i32::MAX {
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

// E2: the same with socket(AF_UNIX, SOCK_STREAM, 0) (ENOBUFS/ENFILE/EACCES).
pub fn adv_errpath_socket(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let s = unsafe { libc::socket(1, 1, 0) };
        if s == -1 {
            unsafe {
                libc::execv(path, argv);
                libc::_exit(127)
            }
        }
        let mut fd = 3;
        while fd < i32::MAX {
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
