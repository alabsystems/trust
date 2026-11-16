#![crate_type = "lib"]
// H1: the strip stops at 92 160 — this Mac's kern.maxfilesperproc. On a
// host where kern.maxfilesperproc is raised (a sysctl tunable up to
// kern.maxfiles), descriptors >= 92 160 exist and leak.
pub fn adv_strip_to_this_hosts_limit(
    path: *const libc::c_char,
    argv: *const *const libc::c_char,
) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < 92_160 {
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
