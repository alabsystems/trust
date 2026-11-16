#![crate_type = "lib"]
// Adversarial census inputs, round 2. Every root forks; the child strips
// EVERY descriptor >= 3 (census_shapes' strip, verbatim), does one more
// thing, then execs.

// D2: a guard whose Drop dups stdout (not close-on-exec): implicit drop.
pub struct DupOnDrop {
    src: i32,
}
impl Drop for DupOnDrop {
    fn drop(&mut self) {
        unsafe {
            libc::dup(self.src);
        }
    }
}
pub fn adv_drop_dup(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
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
            let _g = DupOnDrop { src: 1 };
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// D3: the same guard, dropped EXPLICITLY with std::mem::drop.
pub fn adv_drop_dup_explicit(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
            }
            fd += 1;
        }
        let g = DupOnDrop { src: 1 };
        drop(g);
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// D4 (correct code): a user descriptor owner whose Drop closes. The child
// dups stdout into it and drops it before exec: NO leak.
pub struct Fd(i32);
impl Drop for Fd {
    fn drop(&mut self) {
        unsafe {
            libc::close(self.0);
        }
    }
}
pub fn adv_owner_closed(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
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
            let _t = Fd(unsafe { libc::dup(1) });
        }
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// C2 (correct code): the strip is a `for` that calls a local helper; the
// child is fully stripped: NO leak.
fn mark(fd: i32) {
    unsafe {
        libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
    }
}
fn strip_for(bound: i32) {
    for fd in 3..bound {
        mark(fd);
    }
}
pub fn adv_strip_via_for(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        strip_for(i32::MAX);
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// C3 (correct code): same, the `for` ignores its index and closes a fixed
// descriptor (the leak-free twin of census_shapes' erased `for`).
fn close_dup_for(n: i32) {
    for _ in 0..n {
        unsafe {
            libc::close(3);
        }
    }
}
pub fn adv_close_via_for(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
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
            libc::dup2(1, 3);
        }
        close_dup_for(1);
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// U2: the child CLEARS FD_CLOEXEC on every descriptor >= 3 (an un-strip),
// then execs: every inherited foreign descriptor leaks.
pub fn adv_unstrip_all(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    let pid = unsafe { libc::fork() };
    if pid == 0 {
        let mut fd = 3;
        while fd < i32::MAX {
            unsafe {
                libc::fcntl(fd, libc::F_SETFD, 0);
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

// A2: a MOVE closure passed to a core combinator dups stdout after the strip.
pub fn adv_move_closure(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
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
        let _ = Some(()).map(move |_| unsafe { libc::dup(src) });
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// A3: a local generic helper that calls its closure argument.
fn apply<F: FnOnce() -> i32>(f: F) -> i32 {
    f()
}
pub fn adv_generic_closure(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
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
        apply(move || unsafe { libc::dup(src) });
        unsafe {
            libc::execv(path, argv);
            libc::_exit(127)
        }
    }
    pid
}

// S1: fork through a match on the pid.
pub fn adv_match_pid(path: *const libc::c_char, argv: *const *const libc::c_char) -> i32 {
    match unsafe { libc::fork() } {
        0 => {
            let mut fd = 3;
            while fd < i32::MAX {
                unsafe {
                    libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
                }
                fd += 1;
            }
            unsafe {
                libc::dup(1);
            }
            unsafe {
                libc::execv(path, argv);
                libc::_exit(127)
            }
        }
        pid => pid,
    }
}
