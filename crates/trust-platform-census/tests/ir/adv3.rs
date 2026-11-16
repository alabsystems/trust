#![crate_type = "lib"]
// Adversarial census inputs, round 3.

// A4: a capturing closure handed to core's Iterator::for_each (the one
// closure-as-value shape the producer splices today) dups stdout in the
// child AFTER the full strip.
pub fn adv_for_each_dup(
    srcs: &[i32],
    path: *const libc::c_char,
    argv: *const *const libc::c_char,
) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        let k = 0;
        srcs.iter().for_each(move |x| unsafe {
            libc::dup(*x + k);
        });
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// F2: an upstream crate's spawner (no strip): no site in this crate.
pub fn adv_upstream_spawn(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    upstream_spawn::spawn_leaky(path, argv)
}

// L1: strip that skips descriptor 7 (must be refuted: a foreign fd at 7 leaks).
pub fn adv_strip_skip7(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            if fd != 7 {
                unsafe {
                    libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
                }
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

// L2: strip with `<=` and a bound of i32::MAX - 1 (complete: must not be refuted).
pub fn adv_strip_le(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd <= i32::MAX - 1 {
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

// L3: strip that closes instead of marking, then dup2s stdout onto 3 (a lane
// by placement: must not be refuted).
pub fn adv_close_then_place(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::close(fd);
            }
            fd += 1;
        }
        unsafe {
            libc::dup2(1, 3);
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// L4: strip whose step is 2 (only odd numbers marked: must be refuted).
pub fn adv_strip_step2(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX - 1 {
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

// L5: the strip stops early when fcntl fails with EBADF... on the FIRST
// closed slot (a classic bug: stops at the first hole): must be refuted.
pub fn adv_strip_until_hole(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } == -1 {
                break;
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

// X1: the child execs only if a parent-side value is 0; else exits. The
// strip happens only on the other arm (a pid-dependent shape).
pub fn adv_exec_without_strip_if_nonzero(
    path: *const libc::c_char,
    argv: *const *const libc::c_char,
) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        if pid == 0 {
            unsafe {
                libc::execv(path, argv);
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
