#![crate_type = "lib"]
// T1: an i32 cell read back as u32 through a pointer cast. -1 as u32 is
// 4294967295 > 100: the child execs WITHOUT the strip (every foreign fd
// leaks). The census keeps the i32 value -1 for the u32 load.
pub fn adv_reinterpret_guard(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut code: i32 = -1;
        let wide = unsafe { *(&mut code as *mut i32 as *mut u32) };
        if wide > 100 {
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

// T2: the same through a #[repr(C)] union.
#[repr(C)]
pub union Word {
    i: i32,
    u: u32,
}
pub fn adv_union_guard(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let w = Word { i: -1 };
        let wide = unsafe { w.u };
        if wide > 100 {
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

// T3: transmute.
pub fn adv_transmute_guard(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let wide: u32 = unsafe { std::mem::transmute::<i32, u32>(-1) };
        if wide > 100 {
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
