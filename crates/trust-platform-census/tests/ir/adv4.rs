#![crate_type = "lib"]
// B1: a descriptor loop the ForRange recognizer does not summarize (step 2),
// bounded at 20 000: the forked child's run-to-exec macro step executes
// every iteration, outside the state budget.
pub fn adv_step2_bounded(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < 20_000 {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 2;
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}
