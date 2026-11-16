#![crate_type = "lib"]
// Adversarial census inputs (review of census/c0 cec67a957f). Every root
// forks; the child strips EVERY descriptor >= 3 (the census_shapes
// `spawn_full_inline` strip, verbatim), then does one more thing, then execs.
// The "one more thing" is where the leak hides.

// A: a capturing closure passed to a core combinator dups stdout in the
// child AFTER the strip (the dup is not close-on-exec): a real leak.
pub fn adv_closure_core(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        let src = 1;
        let _ = Some(()).map(|_| unsafe { libc::dup(src) });
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// B: the same leak through a local fn item passed by value.
fn dup_one(fd: i32) -> i32 {
    unsafe { libc::dup(fd) }
}
pub fn adv_fnitem_core(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        let _ = Some(1).map(dup_one);
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// C: census_shapes' erased `for` (S1), one call deeper: the `for` body calls
// a local helper instead of libc directly.
fn leak_one() {
    unsafe {
        libc::dup(1);
    }
}
fn dup_via_helper_for(n: i32) {
    for _ in 0..n {
        leak_one();
    }
}
pub fn adv_erased_helper(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        dup_via_helper_for(1);
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// D: a guard whose Drop clears FD_CLOEXEC on descriptor 5 (implicit drop).
pub struct Inherit {
    fd: i32,
}
impl Drop for Inherit {
    fn drop(&mut self) {
        unsafe {
            libc::fcntl(self.fd, libc::F_SETFD, 0);
        }
    }
}
pub fn adv_drop_guard(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
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
            let _g = Inherit { fd: 5 };
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// E: the process re-execs itself holding a non-close-on-exec dup of stdout.
pub fn adv_reexec(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    unsafe {
        libc::dup(1);
        libc::execv(path, argv)
    }
}

// F: the child clears FD_CLOEXEC on descriptor 5 through a local helper
// that the strip loop calls only for fd == 5 (control: must be refuted).
pub fn adv_unstrip_direct(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        unsafe {
            libc::fcntl(5, libc::F_SETFD, 0);
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// G: unsigned strip bound (u32::MAX) and an `as i32` descriptor.
pub fn adv_u32_strip(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd: u32 = 3;
        while fd < u32::MAX {
            unsafe {
                libc::fcntl(fd as i32, libc::F_SETFD, libc::FD_CLOEXEC);
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

// H: std::thread::spawn on the path (STD-THREAD-SPAWN is now a model row).
pub fn adv_thread(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let x = 7;
    let _h = std::thread::spawn(move || x + 1);
    let pid = unsafe { libc::fork() };
    if pid == 0 {
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
