//! THE PTY SHELL SPAWN — `aterm_pty::spawn_shell_with_pid_cell_px`
//! (`crates/aterm-pty/src/unix.rs`), the child that is EVERY user shell:
//! the NEW body on aterm `fix/fd-inherit-ceiling` (ef421cedb) and the OLD one
//! on its base, aterm `origin/main` ad35a5d85, which carried its own copy of
//! the 65 536-capped strip.
//!
//! The PTY child must fork — the session sandbox's `setrlimit` and
//! `login_tty`'s `TIOCSCTTY` are not `posix_spawn` file actions — so it
//! strips. The two bodies differ ONLY in the strip's bound and where it is
//! read; everything else below is shared, and lines below 1446 of unix.rs
//! are identical in both commits.
//!
//! OLD, ad35a5d85 unix.rs:1461-1472 (read at :1772, in the parent):
//!
//! ```text
//! fn inherited_fd_ceiling() -> libc::c_int {
//!     const CAP: libc::rlim_t = 1 << 16;
//!     let mut limit = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
//!     let read = unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut limit) } == 0;
//!     let soft = if read { limit.rlim_cur.min(CAP) } else { CAP };
//!     libc::c_int::try_from(soft).unwrap_or(libc::c_int::MAX)
//! }
//! ...                                         // child, (3b), :1977-1983
//!     let mut fd = libc::STDERR_FILENO + 1;
//!     while fd < fd_ceiling {
//!         libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC);
//!         fd += 1;
//!     }
//! ```
//!
//! NEW, ef421cedb unix.rs:1750 and :1963 (and aterm-uds spawnfd.rs:842-931):
//!
//! ```text
//! let inherit_strip = aterm_uds::spawnfd::InheritStrip::prepare();   // parent
//! ...
//! inherit_strip.apply();                                              // child, (3b)
//!
//! pub fn prepare() -> Self { Self { bound: descriptor_bound() } }
//! pub fn apply(self) {
//!     for fd in 3..self.bound { unsafe { fcntl(fd, F_SETFD, FD_CLOEXEC); } }
//! }
//! pub fn descriptor_bound() -> RawFd {      // the Darwin arm
//!     sysctlbyname("kern.maxfilesperproc", ..)   // 92 160 here; else 1 << 20
//! }
//! ```
//!
//! The rest, the same in both (new line numbers; ad35a5d85's are 22 higher
//! from the status channel on):
//!
//! ```text
//! let (status_rd, status_wr, _status_carrier) = open_exec_status_channel()?;   // :1745
//! let (master, slave) = match open_pty_pair_cloexec(termp.as_ref(), Some(&ws)) {
//!     Ok(pair) => pair,
//!     Err(err) => { libc::close(status_rd); libc::close(status_wr); return Err(err); }
//! };                                                                            // :1774
//! let pid = unsafe { libc::fork() };                                            // :1790
//! if pid == 0 {
//!     libc::close(status_rd);                                                   // (0)  :1810
//!     if libc::login_tty(slave) == -1 {                                         // (0a) :1849
//!         libc::dup2(slave, 0); libc::dup2(slave, 1); libc::dup2(slave, 2);
//!         if slave > 2 { libc::close(slave); }
//!     }
//!     /* sigaction(1..32, SIG_DFL); sigprocmask(SIG_SETMASK, empty) */          // (0b)
//!     if limits.apply(sandbox_cap).is_err() {                                   // (1)  :1895
//!         libc::write(status_wr, &b'S', 1); libc::_exit(126);
//!     }
//!     if let Some(dir) = &chdir_c { libc::chdir(dir.as_ptr()); }                // (2)
//!     if master > 2 { libc::close(master); }                                    // (3)  :1933
//!     /* (3b) the strip */
//!     libc::execve(exec_target.as_ptr(), argv.as_ptr(), envp.as_ptr());        // (4)  :1973
//!     libc::write(status_wr, &b'E', 1); libc::_exit(127);
//! }
//! libc::close(slave);                                                           // :1992
//! libc::close(status_wr);                                                       // :2017
//! ```
//!
//! `login_tty(fd)` is, per aterm's disassembly of libsystem_c (unix.rs
//! :1812-1820): `setsid()`; `ioctl(fd, TIOCSCTTY, NULL)` (-1 on failure);
//! `dup2(fd, 0..=2)`; `close(fd)` when fd > 2. Its failure is the
//! `TIOCSCTTY`, before any `dup2`, and aterm's fallback then makes the same
//! three `dup2`s and the same close — so both arms are one descriptor
//! sequence, encoded once; `setsid` and `TIOCSCTTY` (no descriptor effect,
//! not in the model) are disclosed, not encoded.

use trust_platform::{Call, Errno, Oracle, darwin};

use super::{
    ABOVE_OLD_CAP, ATERM_BASE, ATERM_FIX, Fixture, WindowRace, add_racer, add_window_racer, fcntl,
    fix_env, loc, window_env,
};
use crate::env::EnvSpec;
use crate::program::{
    Bind, BodyId, CmpOp, Cond, Expr, FdInherit, Lane, Mutation, Operand, ProgramBuilder, VarId,
};

const PATH: &str = "crates/aterm-pty/src/unix.rs";
const UDS: &str = "crates/aterm-uds/src/spawnfd.rs";

/// Which body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Version {
    /// ad35a5d85: `inherited_fd_ceiling()` in the parent, capped at 65 536.
    Main,
    /// ef421cedb: `InheritStrip::prepare()` — `kern.maxfilesperproc`.
    Fix,
}

/// The session's resource sandbox (`aterm_sandbox::Limits`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sandbox {
    /// `Limits::inherit()` (the daily-driver User/Master modes): every limit
    /// `None`, so `apply` makes no `setrlimit` at all.
    Inherit,
    /// `Limits::shell_default()` on macOS (Safety/Containment): only
    /// `open_files: Some(8192)` — `getrlimit(NOFILE)` then
    /// `setrlimit(NOFILE, min(8192, hard), hard)` IN THE CHILD, BEFORE the
    /// strip (aterm-sandbox unix.rs:17-33, 63-86). `address_space` is `None`
    /// on macOS, CPU and file size `None`.
    ShellDefault,
}

/// The line numbers of one version's `spawn_shell_with_pid_cell_px`.
struct Lines {
    commit: &'static str,
    status: u32,
    strip_read: u32,
    pair: u32,
    fork: u32,
    close_status_rd: u32,
    login_tty: u32,
    sig: u32,
    limits: u32,
    close_master: u32,
    strip: u32,
    execve: u32,
    close_slave: u32,
    close_status_wr: u32,
}

const FIX: Lines = Lines {
    commit: ATERM_FIX,
    status: 1745,
    strip_read: 1750,
    pair: 1774,
    fork: 1790,
    close_status_rd: 1810,
    login_tty: 1849,
    sig: 1879,
    limits: 1895,
    close_master: 1933,
    strip: 1963,
    execve: 1973,
    close_slave: 1992,
    close_status_wr: 2017,
};

const MAIN: Lines = Lines {
    commit: ATERM_BASE,
    status: 1769,
    strip_read: 1772,
    pair: 1796,
    fork: 1812,
    close_status_rd: 1832,
    login_tty: 1871,
    sig: 1901,
    limits: 1917,
    close_master: 1955,
    strip: 1978,
    execve: 1993,
    close_slave: 2012,
    close_status_wr: 2037,
};

/// The variables of one spawn.
struct Vars {
    status_rd: VarId,
    status_wr: VarId,
    ok: VarId,
    got: VarId,
    master: VarId,
    slave: VarId,
    cloexec_fd: VarId,
    cloexec_ok: VarId,
    strip_hi: VarId,
    strip_fd: VarId,
    pid: VarId,
    rc: VarId,
    rl_soft: VarId,
}

/// `open_exec_status_channel()` on macOS (unix.rs:1134-1225), its fifo
/// carrier `open_exec_status_fifo()` (:1032-1117) inline. Leaves the ends in
/// `status_rd`/`status_wr`; returns 0, or -1 for its `Err`.
fn status_channel(p: &mut ProgramBuilder, v: &Vars) -> BodyId {
    let c = ATERM_FIX; // lines < 1446: identical in both commits
    let l = |line: &str| loc(c, PATH, line);
    let (rd, wr, ok, got) = (v.status_rd, v.status_wr, v.ok, v.got);
    let fifo = "$TMPDIR/aterm-xstatus-<pid>-<seq>-<random> (mkfifo'd at :1044)";
    let fifo_note = "a FIFO this spawn mkfifo'd (mode 0600, in a 0700 per-user directory) and \
                     unlinks once both ends are open: it is not a fresh vnode, but neither open \
                     blocks (the read end is O_NONBLOCK and opened first; the write end opens \
                     with that reader present), so its descriptor-table effect is the open \
                     clause's: a fresh description at the lowest free number, FD_CLOEXEC from \
                     O_CLOEXEC. The FIFO's data and EOF (the exec-status protocol) are not \
                     modeled and fd-inherit reads neither; both ends naming ONE object is lost \
                     (two descriptions here)";
    p.body("open_exec_status_channel", Vec::new(), |b| {
        b.assign(&l("1162"), ok, Expr::Use(Operand::Lit(0)));
        // open_exec_status_fifo: (1) mkfifo, (2) chmod — disclosed.
        // (3) READ END
        b.open_assuming(
            &l("1062-1066"),
            fifo,
            Call::Open {
                flags: darwin::O_RDONLY
                    | darwin::O_NONBLOCK
                    | darwin::O_CLOEXEC
                    | darwin::O_NOFOLLOW,
            },
            Bind::ret(rd),
            "status_fifo_rd",
            vec![Oracle::Nominal, Oracle::Fail(Errno::ENOENT)],
            fifo_note,
        );
        // if rd < 0 { unlink; return Err } — into the fallback below.
        b.when(&l("1068"), Cond::ne(Operand::Var(rd), Operand::Lit(-1)), |t| {
            // (4) WRITE END
            t.open_assuming(
                &l("1079-1083"),
                fifo,
                Call::Open { flags: darwin::O_WRONLY | darwin::O_CLOEXEC | darwin::O_NOFOLLOW },
                Bind::ret(wr),
                "status_fifo_wr",
                vec![Oracle::Nominal],
                fifo_note,
            );
            t.if_(
                &l("1085"),
                Cond::eq(Operand::Var(wr), Operand::Lit(-1)),
                |e| {
                    e.event(
                        &l("1090"),
                        "close",
                        Call::Close { fd: Operand::Var(rd) },
                        Bind::none(),
                    );
                },
                |o| {
                    // (5) unlink — disclosed.
                    // :1103 `!fifo_ends_are_one_private_object(rd, wr)` (fstat x2,
                    // disclosed: true for the fifo just made) `|| !fd_is_cloexec(rd)
                    // || !fd_is_cloexec(wr)` — F_GETFD each, short-circuit.
                    o.event(
                        &l("816"),
                        "fcntl",
                        fcntl(Operand::Var(rd), darwin::F_GETFD, 0),
                        Bind::ret(got),
                    );
                    o.when(&l("817"), Cond::eq(Operand::Var(got), Operand::Lit(1)), |t2| {
                        t2.event(
                            &l("816"),
                            "fcntl",
                            fcntl(Operand::Var(wr), darwin::F_GETFD, 0),
                            Bind::ret(got),
                        );
                        t2.when(&l("817"), Cond::eq(Operand::Var(got), Operand::Lit(1)), |t3| {
                            t3.assign(&l("1114"), ok, Expr::Use(Operand::Lit(1)));
                        });
                    });
                    o.when(&l("1103"), Cond::eq(Operand::Var(ok), Operand::Lit(0)), |e| {
                        e.event(
                            &l("1107"),
                            "close",
                            Call::Close { fd: Operand::Var(rd) },
                            Bind::none(),
                        );
                        e.event(
                            &l("1108"),
                            "close",
                            Call::Close { fd: Operand::Var(wr) },
                            Bind::none(),
                        );
                    });
                },
            );
        });
        // THE RACY FALLBACK (:1175-1209): pipe(2), then F_SETFD on both.
        b.when(&l("1175"), Cond::eq(Operand::Var(ok), Operand::Lit(0)), |f| {
            f.event_full(
                &l("1183"),
                "pipe",
                Call::Pipe,
                Bind::pair(rd, wr),
                vec![Oracle::Nominal],
                None,
                vec!["status_pipe_rd", "status_pipe_wr"],
            );
            f.when(&l("1183"), Cond::eq(Operand::Var(rd), Operand::Lit(-1)), |e| {
                e.ret(&l("1184"), Some(Operand::Lit(-1)));
            });
            f.event(
                &l("1192"),
                "fcntl",
                fcntl(Operand::Var(rd), darwin::F_SETFD, darwin::FD_CLOEXEC),
                Bind::ret(got),
            );
            f.when(&l("1193"), Cond::ne(Operand::Var(got), Operand::Lit(-1)), |t| {
                t.event(
                    &l("1193"),
                    "fcntl",
                    fcntl(Operand::Var(wr), darwin::F_SETFD, darwin::FD_CLOEXEC),
                    Bind::ret(got),
                );
            });
            f.when(&l("1195"), Cond::eq(Operand::Var(got), Operand::Lit(-1)), |e| {
                e.event(&l("1199"), "close", Call::Close { fd: Operand::Var(rd) }, Bind::none());
                e.event(&l("1200"), "close", Call::Close { fd: Operand::Var(wr) }, Bind::none());
                e.ret(&l("1202"), Some(Operand::Lit(-1)));
            });
            // note_racy_exec_status_carrier: a stderr line — disclosed.
        });
        // :1216 fd_set_nonblocking(rd): F_GETFL, then F_SETFL(flags | O_NONBLOCK).
        b.event(&l("833"), "fcntl", fcntl(Operand::Var(rd), darwin::F_GETFL, 0), Bind::ret(got));
        b.when(&l("834"), Cond::ne(Operand::Var(got), Operand::Lit(-1)), |t| {
            t.event(
                &l("834"),
                "fcntl",
                fcntl(Operand::Var(rd), darwin::F_SETFL, i64::from(darwin::O_NONBLOCK)),
                Bind::ret(got),
            );
        });
        b.when(&l("1216"), Cond::eq(Operand::Var(got), Operand::Lit(-1)), |e| {
            e.event(&l("1220"), "close", Call::Close { fd: Operand::Var(rd) }, Bind::none());
            e.event(&l("1221"), "close", Call::Close { fd: Operand::Var(wr) }, Bind::none());
            e.ret(&l("1223"), Some(Operand::Lit(-1)));
        });
        b.ret(&l("1225"), Some(Operand::Lit(0)));
    })
}

/// `fd_is_cloexec_or_make_it(fd)` (unix.rs:330-342): returns 1 (true) or 0.
fn cloexec_or_make_it(p: &mut ProgramBuilder, v: &Vars) -> BodyId {
    let l = |line: &str| loc(ATERM_FIX, PATH, line);
    let (fd, got) = (v.cloexec_fd, v.got);
    p.body("fd_is_cloexec_or_make_it", vec![fd], |b| {
        b.event(&l("334"), "fcntl", fcntl(Operand::Var(fd), darwin::F_GETFD, 0), Bind::ret(got));
        b.when(&l("335"), Cond::eq(Operand::Var(got), Operand::Lit(-1)), |e| {
            e.ret(&l("336"), Some(Operand::Lit(0)));
        });
        // flags & FD_CLOEXEC != 0: FD_CLOEXEC is Darwin's only descriptor flag.
        b.when(&l("338"), Cond::eq(Operand::Var(got), Operand::Lit(1)), |t| {
            t.ret(&l("339"), Some(Operand::Lit(1)));
        });
        // flags | FD_CLOEXEC, with flags == 0 here.
        b.event(
            &l("341"),
            "fcntl",
            fcntl(Operand::Var(fd), darwin::F_SETFD, darwin::FD_CLOEXEC),
            Bind::ret(got),
        );
        b.when(&l("341"), Cond::eq(Operand::Var(got), Operand::Lit(-1)), |e| {
            e.ret(&l("341"), Some(Operand::Lit(0)));
        });
        b.ret(&l("341"), Some(Operand::Lit(1)));
    })
}

/// `open_pty_pair_cloexec(termp, winp)` (unix.rs:408-493): leaves the ends in
/// `master`/`slave`; returns 0, or -1 for its `Err` (which closes what it
/// opened).
fn pty_pair(p: &mut ProgramBuilder, v: &Vars, cloexec: BodyId) -> BodyId {
    let l = |line: &str| loc(ATERM_FIX, PATH, line);
    let (master, slave, ok) = (v.master, v.slave, v.cloexec_ok);
    let fd = v.cloexec_fd;
    p.body("open_pty_pair_cloexec", Vec::new(), |b| {
        // (1) MASTER: posix_openpt(O_RDWR | O_NOCTTY | O_CLOEXEC)
        b.open_assuming(
            &l("414"),
            "/dev/ptmx",
            Call::Open { flags: darwin::O_RDWR | darwin::O_NOCTTY | darwin::O_CLOEXEC },
            Bind::ret(master),
            "pty_master",
            vec![Oracle::Nominal],
            "posix_openpt(flags), which the symbol table names a gap (\"pty masters are not \
             modeled\"), is encoded as the open clause of a fresh description: MEASURED \
             2026-09-30 on this Mac, posix_openpt(O_RDWR|O_NOCTTY|O_CLOEXEC) returns the lowest \
             free number with FD_CLOEXEC set; the master's pty semantics are not modeled",
        );
        // `opened < 0` with EINVAL retries without O_CLOEXEC (:416-431): the
        // open takes the nominal oracle only, so neither arm is explored.
        b.when(&l("415"), Cond::eq(Operand::Var(master), Operand::Lit(-1)), |e| {
            e.ret(&l("424"), Some(Operand::Lit(-1)));
        });
        // :433 if !fd_is_cloexec_or_make_it(master) { close(master); return Err }
        b.call(&l("433"), cloexec, vec![(fd, Operand::Var(master))], Some(ok));
        b.when(&l("433"), Cond::eq(Operand::Var(ok), Operand::Lit(0)), |e| {
            e.event(&l("437"), "close", Call::Close { fd: Operand::Var(master) }, Bind::none());
            e.ret(&l("439"), Some(Operand::Lit(-1)));
        });
        // (2) :445 grantpt + unlockpt — ioctls on the master, disclosed.
        // (3) SLAVE: open_pts_slave(master) — pts_name (TIOCPTYGNAME,
        //     disclosed), then open(name, O_RDWR | O_NOCTTY | O_CLOEXEC) :302-307.
        b.open(
            &l("302-307"),
            "/dev/ttys<N> (TIOCPTYGNAME's answer)",
            Call::Open { flags: darwin::O_RDWR | darwin::O_NOCTTY | darwin::O_CLOEXEC },
            Bind::ret(slave),
            "pty_slave",
        );
        b.when(&l("456"), Cond::eq(Operand::Var(slave), Operand::Lit(-1)), |e| {
            e.event(&l("461"), "close", Call::Close { fd: Operand::Var(master) }, Bind::none());
            e.ret(&l("463"), Some(Operand::Lit(-1)));
        });
        // :466 if !fd_is_cloexec_or_make_it(slave) { close both; return Err }
        b.call(&l("466"), cloexec, vec![(fd, Operand::Var(slave))], Some(ok));
        b.when(&l("466"), Cond::eq(Operand::Var(ok), Operand::Lit(0)), |e| {
            e.event(&l("470"), "close", Call::Close { fd: Operand::Var(slave) }, Bind::none());
            e.event(&l("471"), "close", Call::Close { fd: Operand::Var(master) }, Bind::none());
            e.ret(&l("473"), Some(Operand::Lit(-1)));
        });
        // (4) tcsetattr + TIOCSWINSZ on the slave (:483, :490) — disclosed.
        b.ret(&l("492"), Some(Operand::Lit(0)));
    })
}

/// The old `inherited_fd_ceiling()` (ad35a5d85 unix.rs:1461-1472).
fn inherited_fd_ceiling(p: &mut ProgramBuilder, v: &Vars) -> BodyId {
    let l = |line: &str| loc(ATERM_BASE, PATH, line);
    let (rc, soft, out) = (v.rc, v.rl_soft, v.strip_hi);
    p.body("inherited_fd_ceiling (ad35a5d85, aterm-pty)", Vec::new(), |b| {
        b.event(
            &l("1468"),
            "getrlimit",
            Call::Getrlimit { resource: darwin::RLIMIT_NOFILE },
            Bind { ret: Some(rc), rlim_soft: Some(soft), ..Bind::default() },
        );
        b.if_(
            &l("1469"),
            Cond::eq(Operand::Var(rc), Operand::Lit(0)),
            |t| t.assign(&l("1469"), out, Expr::Min(Operand::Var(soft), Operand::Lit(1 << 16))),
            |e| e.assign(&l("1469"), out, Expr::Use(Operand::Lit(1 << 16))),
        );
        b.ret(&l("1470"), Some(Operand::Var(out)));
    })
}

/// The other thread of the fixture.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Racer {
    /// No other thread.
    None,
    /// The e17e2d6d5 pair racer ([`add_racer`]).
    Pair,
    /// The window racer ([`add_window_racer`]).
    Window(WindowRace),
}

fn build(
    name: &'static str,
    version: Version,
    sandbox: Sandbox,
    racer: Racer,
    env: EnvSpec,
) -> Fixture {
    let ln = match version {
        Version::Main => &MAIN,
        Version::Fix => &FIX,
    };
    let c = ln.commit;
    let l = |line: u32| loc(c, PATH, &line.to_string());
    let mut p = ProgramBuilder::new(name);
    p.provenance("aterm", c, PATH, "spawn_shell_with_pid_cell_px: the PTY shell's fork and child");
    if version == Version::Fix {
        p.provenance("aterm", c, UDS, "InheritStrip::prepare/apply, descriptor_bound (Darwin)");
    }
    let v = Vars {
        status_rd: p.var("status_rd", -1),
        status_wr: p.var("status_wr", -1),
        ok: p.var("fifo_ok", -1),
        got: p.var("got", -1),
        master: p.var("master", -1),
        slave: p.var("slave", -1),
        cloexec_fd: p.var("cloexec_fd", -1),
        cloexec_ok: p.var("cloexec_ok", -1),
        strip_hi: p.var("strip_bound", -1),
        strip_fd: p.var("strip_fd", -1),
        pid: p.var("pid", -1),
        rc: p.var("rc", -1),
        rl_soft: p.var("rl_soft", -1),
    };
    let channel = status_channel(&mut p, &v);
    let cloexec = cloexec_or_make_it(&mut p, &v);
    let pair = pty_pair(&mut p, &v, cloexec);
    let ceiling = (version == Version::Main).then(|| inherited_fd_ceiling(&mut p, &v));
    let site = p.site(
        "pty_shell",
        &l(ln.fork),
        Some(FdInherit {
            lanes: (0..3).map(|fd| Lane { fd, ofd_class: "pty_slave".to_string() }).collect(),
        }),
    );
    let strip_one = {
        let fd = v.strip_fd;
        let line = match version {
            Version::Main => loc(c, PATH, "1980"),
            Version::Fix => loc(c, UDS, "876"),
        };
        p.body("strip one fd", Vec::new(), move |b| {
            b.event(
                &line,
                "fcntl",
                fcntl(Operand::Var(fd), darwin::F_SETFD, darwin::FD_CLOEXEC),
                Bind::none(),
            );
        })
    };
    let (status_rd, status_wr, master, slave, rc) =
        (v.status_rd, v.status_wr, v.master, v.slave, v.rc);
    let (strip_hi, strip_fd) = (v.strip_hi, v.strip_fd);
    let child = p.body("the PTY child (fork to execve)", Vec::new(), |b| {
        // (0) close the status read end.
        b.event(
            &l(ln.close_status_rd),
            "close",
            Call::Close { fd: Operand::Var(status_rd) },
            Bind::none(),
        );
        // (0a) login_tty(slave): setsid + TIOCSCTTY disclosed; then (or, on its
        //      failure, aterm's fallback) dup2 x3 and close(slave) if > 2.
        for target in 0..3 {
            b.event(
                &l(ln.login_tty + 1 + target),
                "dup2",
                Call::Dup2 { from: Operand::Var(slave), to: Operand::Lit(i64::from(target)) },
                Bind::none(),
            );
        }
        b.when(
            &l(ln.login_tty + 4),
            Cond::Cmp(CmpOp::Gt, Operand::Var(slave), Operand::Lit(2)),
            |t| {
                t.event(
                    &l(ln.login_tty + 5),
                    "close",
                    Call::Close { fd: Operand::Var(slave) },
                    Bind::none(),
                );
            },
        );
        // (0b) signals: no descriptor effect.
        b.neutral(&l(ln.sig), "sigaction");
        b.neutral(&l(ln.sig + 4), "sigemptyset");
        b.neutral(&l(ln.sig + 6), "sigprocmask");
        // (1) limits.apply(sandbox_cap)
        if sandbox == Sandbox::ShellDefault {
            let sl = |line: &str| loc(c, "crates/aterm-sandbox/src/unix.rs", line);
            // set_limit(RLIMIT_NOFILE, Some(8192)): getrlimit for the hard
            // ceiling, then setrlimit(min(8192, hard), hard).
            b.event(
                &sl("70"),
                "getrlimit",
                Call::Getrlimit { resource: darwin::RLIMIT_NOFILE },
                Bind::ret(rc),
            );
            b.event(
                &sl("81"),
                "setrlimit",
                Call::Setrlimit {
                    resource: darwin::RLIMIT_NOFILE,
                    soft: 8192,
                    hard: darwin::RLIM_INFINITY,
                },
                Bind::ret(rc),
            );
            b.when(&l(ln.limits), Cond::eq(Operand::Var(rc), Operand::Lit(-1)), |e| {
                // write(status_wr, 'S') — disclosed; then _exit(126).
                e.event(&l(ln.limits + 7), "_exit", Call::Exit { status: 126 }, Bind::none());
            });
        }
        // (2) chdir — disclosed.
        // (3) close(master) when master > 2.
        b.when(
            &l(ln.close_master - 1),
            Cond::Cmp(CmpOp::Gt, Operand::Var(master), Operand::Lit(2)),
            |t| {
                t.event(
                    &l(ln.close_master),
                    "close",
                    Call::Close { fd: Operand::Var(master) },
                    Bind::none(),
                );
            },
        );
        // (3b) THE STRIP: every number from 3 up to the bound read in the parent.
        b.tag("strip").for_range(
            &l(ln.strip),
            strip_fd,
            Operand::Lit(3),
            Operand::Var(strip_hi),
            strip_one,
        );
        // (4) execve; on failure write(status_wr, 'E') — disclosed — and _exit(127).
        b.event_full(
            &l(ln.execve),
            "execve",
            Call::Exec,
            Bind::ret(rc),
            vec![Oracle::Nominal, Oracle::Fail(Errno::ENOENT)],
            None,
            Vec::new(),
        );
        b.event(&l(ln.execve + 3), "_exit", Call::Exit { status: 127 }, Bind::none());
    });
    let (pid, ok) = (v.pid, v.ok);
    let main = p.body("spawn_shell_with_pid_cell_px", Vec::new(), |b| {
        // let (status_rd, status_wr, _) = open_exec_status_channel()?;
        b.call(&l(ln.status), channel, Vec::new(), Some(ok));
        b.when(&l(ln.status), Cond::eq(Operand::Var(ok), Operand::Lit(-1)), |e| {
            e.ret(&l(ln.status), None);
        });
        match version {
            // let inherit_strip = InheritStrip::prepare();  — descriptor_bound():
            // sysctlbyname("kern.maxfilesperproc") = 92 160 (disclosed).
            Version::Fix => {
                b.assign(&loc(c, UDS, "898-913"), strip_hi, Expr::Use(Operand::Lit(92_160)));
            }
            // let fd_ceiling = inherited_fd_ceiling();
            Version::Main => {
                if let Some(cb) = ceiling {
                    b.call(&l(ln.strip_read), cb, Vec::new(), Some(strip_hi));
                }
            }
        }
        // let (master, slave) = match open_pty_pair_cloexec(..) { Err => close both; return }
        b.call(&l(ln.pair), pair, Vec::new(), Some(ok));
        b.when(&l(ln.pair), Cond::eq(Operand::Var(ok), Operand::Lit(-1)), |e| {
            e.event(
                &l(ln.pair + 6),
                "close",
                Call::Close { fd: Operand::Var(status_rd) },
                Bind::none(),
            );
            e.event(
                &l(ln.pair + 7),
                "close",
                Call::Close { fd: Operand::Var(status_wr) },
                Bind::none(),
            );
            e.ret(&l(ln.pair + 9), None);
        });
        // let pid = unsafe { libc::fork() };
        b.fork(&l(ln.fork), child, site, Some(pid));
        // PARENT: close(slave); close(status_wr); then the status wait (read /
        // poll: past the fd-inherit horizon, not modeled).
        b.event(&l(ln.close_slave), "close", Call::Close { fd: Operand::Var(slave) }, Bind::none());
        b.event(
            &l(ln.close_status_wr),
            "close",
            Call::Close { fd: Operand::Var(status_wr) },
            Bind::none(),
        );
    });
    p.root("main", main);
    match racer {
        Racer::None => {}
        Racer::Pair => {
            add_racer(&mut p);
        }
        Racer::Window(race) => {
            add_window_racer(&mut p, race);
        }
    }
    p.disclose(
        "PTY spawn, parent: the argv/envp/exec-target build and spawn_termios are data only; \
         spawn_termios's FIRST call per process opens and closes a throwaway pty pair (both \
         ends close-on-exec from birth, closed before this spawn's pair) — the fixture is a \
         spawn after the first; mkfifo, chmod and unlink of the status FIFO, fstat (the \
         fifo_ends_are_one_private_object check, true for the fifo just made), grantpt/unlockpt \
         and TIOCPTYGNAME on the master, and tcsetattr/TIOCSWINSZ on the slave have no \
         descriptor-table effect and are not encoded; note_racy_exec_status_carrier writes one \
         stderr line; the parent's status wait after the fork (read/poll) is past the horizon",
    );
    p.disclose(
        "PTY spawn, child: login_tty's setsid and ioctl(TIOCSCTTY), chdir, and the one-byte \
         write(status_wr) before each _exit have no descriptor-table effect and are not \
         encoded; login_tty's failure (TIOCSCTTY, before any dup2) and aterm's fallback make \
         the same dup2 x3 + close as its success, so the two arms are one encoded sequence; \
         fork takes the nominal oracle only",
    );
    p.disclose(
        "PTY spawn, F_SETFL's argument in fd_set_nonblocking is evaluated by hand: the read \
         end's F_GETFL is O_RDONLY (|O_NONBLOCK for the fifo), so flags | O_NONBLOCK is \
         O_NONBLOCK",
    );
    match version {
        Version::Fix => p.disclose(
            "InheritStrip::prepare (ef421cedb) reads descriptor_bound() = \
             sysctlbyname(\"kern.maxfilesperproc\"), a read-only sysctl the symbol table does \
             not model: encoded as the environment's measured value 92160 (its failure arm, \
             1 << 20, only strips further); the Linux arms (close_range, /proc/self/fd) are not \
             Darwin and not encoded",
        ),
        Version::Main => {}
    }
    if sandbox == Sandbox::ShellDefault {
        p.disclose(
            "Limits::shell_default on macOS installs only RLIMIT_NOFILE: set_limit's setrlimit \
             operands are evaluated by hand with the environment's hard limit RLIM_INFINITY: \
             setrlimit(NOFILE, min(8192, hard), hard)",
        );
    }
    let hygiene = match version {
        Version::Fix => vec![Mutation::DeleteStmt("strip".to_string())],
        Version::Main => Vec::new(),
    };
    Fixture {
        name,
        program: p.build(),
        env,
        premises: Vec::new(),
        expect_refuted: version == Version::Main,
        hygiene,
    }
}

/// NEW BODY N4: the PTY shell spawn of ef421cedb with the daily-driver
/// sandbox (`Limits::inherit()`), under the e17e2d6d5 pair racer, with one
/// unflagged foreign descriptor at every partition position and at 70 000.
/// No premise. Must NOT be refuted; deleting the strip must flip it.
#[must_use]
pub fn fix_shell() -> Fixture {
    build("pty_fix_shell", Version::Fix, Sandbox::Inherit, Racer::Pair, fix_env(Vec::new()))
}

/// NEW BODY N4 under the WINDOW racer (it toggles the soft limit to 1024 and
/// back to 70 064, then takes 2000 and 70 000 — around the bound's read in
/// the parent), with the foreign descriptor at 70 000. No premise. Must NOT
/// be refuted; deleting the strip must flip it.
#[must_use]
pub fn fix_shell_window() -> Fixture {
    build(
        "pty_fix_shell_window",
        Version::Fix,
        Sandbox::Inherit,
        Racer::Window(WindowRace::High),
        window_env(Vec::new(), vec![ABOVE_OLD_CAP]),
    )
}

/// NEW BODY N5: N4 with the hardened sandbox (`Limits::shell_default()`):
/// the child LOWERS its soft limit to 8192 before the strip, so the strip
/// marks descriptors far above the child's own limit — which `F_SETFD` does
/// (MEASURED 2026-09-30 on this Mac: in a child that lowered its soft limit
/// to 8192, `fcntl(70000, F_SETFD, FD_CLOEXEC)` returned 0 and the
/// descriptor did not survive `execve`; without the call it did). A foreign
/// descriptor at every partition position (8191..8193 among them) and at
/// 70 000; no other thread. Must NOT be refuted; deleting the strip must
/// flip it.
#[must_use]
pub fn fix_shell_hardened() -> Fixture {
    build(
        "pty_fix_shell_hardened",
        Version::Fix,
        Sandbox::ShellDefault,
        Racer::None,
        fix_env(Vec::new()),
    )
}

/// OLD-MAIN, the PTY copy (ad35a5d85): the same spawn with
/// `inherited_fd_ceiling()` — min(soft, 65 536), read in the parent — in
/// N4's environment (the pair racer, a foreign descriptor at every partition
/// position and at 70 000). Must be REFUTED: every user shell inherited what
/// sat at 65 536..92 159 (the fix's PTY test fails on main).
#[must_use]
pub fn main_fd_70000() -> Fixture {
    build("pty_main_fd_70000", Version::Main, Sandbox::Inherit, Racer::Pair, fix_env(Vec::new()))
}

/// OLD-MAIN, the PTY copy, the WINDOW alone: the window racer takes only
/// 2000 (`race-low`) and there is no foreign descriptor, so the only
/// refutation is the ceiling read before the fork seeing the toggled-down
/// 1024. Must be REFUTED, by the racer's descriptor at 2000.
#[must_use]
pub fn main_ceiling_window() -> Fixture {
    build(
        "pty_main_ceiling_window",
        Version::Main,
        Sandbox::Inherit,
        Racer::Window(WindowRace::Low),
        window_env(Vec::new(), Vec::new()),
    )
}
