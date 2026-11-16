//! TEETH, built with the DEFAULT backend only. A `(...)` declaration with zero fixed parameters,
//! called as written. This is the placement `CallVariadic { fixed_args: 0 }` would give the
//! producer's `fcntl` declaration: on aarch64-apple-darwin every argument goes on the stack, and
//! `fcntl` reads `fd` and `cmd` from `w0`/`w1`, which hold whatever the caller left there.
#![crate_name = "va"]

unsafe extern "C" {
    fn fcntl(...) -> i32;
}

pub fn f1_setfd_cloexec(fd: i32) -> i32 {
    unsafe { fcntl(fd, 2i32, 1i32) }
}

pub fn f1_getfd(fd: i32) -> i32 {
    unsafe { fcntl(fd, 1i32) }
}
