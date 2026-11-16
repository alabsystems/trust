//! The VARIADIC `fcntl` declared in a LOCAL `extern "C"` block, with the values of `libc`'s
//! Darwin constants (`F_GETFD` = 1, `F_SETFD` = 2, `FD_CLOEXEC` = 1).
#![crate_name = "va"]

unsafe extern "C" {
    fn fcntl(fd: i32, cmd: i32, ...) -> i32;
}

pub fn f1_setfd_cloexec(fd: i32) -> i32 {
    unsafe { fcntl(fd, 2, 1) }
}

pub fn f1_getfd(fd: i32) -> i32 {
    unsafe { fcntl(fd, 1) }
}
