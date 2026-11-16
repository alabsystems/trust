#![crate_type = "lib"]
// An upstream (non-std) crate that forks and execs without stripping.
pub fn spawn_leaky(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        unsafe {
            libc::dup(1);
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}
