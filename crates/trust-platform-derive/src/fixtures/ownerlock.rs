//! Bug 1: aterm `crates/aterm-uds/src/ownerlock.rs`, the owner-lock probe and
//! its tests (plan §3 M2, P-LOCK-RELEASE).
//!
//! `flock` binds to the open file DESCRIPTION. A lock released by `close`
//! alone ends only when the description's LAST reference goes, and a child
//! forked in the meantime holds one until it execs; `LOCK_UN` releases it for
//! every holder (all MEASURED by `trust-platform`'s conformance run).
//!
//! * [`bare_close`] — aterm a6362ba55 (= ba30edc71^): the test's holder lets
//!   go with `drop(file)`. A sibling test's `pre_exec` spawn (RL-HARNESS: the
//!   `aterm-uds` lib tests run concurrently, and `spawnfd`'s tests fork)
//!   forked while the lock was held keeps it past that drop. MUST be refuted.
//! * [`unlock_then_close`] — aterm ba30edc71: `release(file)` takes
//!   `LOCK_UN`, then closes; the test parks a child between fork and exec
//!   across the release. Must NOT be refuted.
//! * [`probe_shipped`] — aterm main 79e636cdb (ownerlock.rs unchanged since
//!   6df3a3c78): `a_child_forked_mid_probe_does_not_keep_the_probes_lock`,
//!   which forks the parked child INSIDE the probe, between its `flock` and
//!   its `LOCK_UN`. Must NOT be refuted.
//! * [`probe_no_unlock`] — the same with the probe's `LOCK_UN` deleted: the
//!   parked-child forcing case (16cdc4ba0: "With `LOCK_UN` removed that probe
//!   reads LIVE"). MUST be refuted.
//!
//! The owner's release points (`StmtKind::Release`) are where the code says
//! it has let go: the probe's return after its `close` (P-LOCK-RELEASE: "at a
//! function's return, every OFD the call created and no longer references
//! has `lock = none`") and the test's `drop(file)` / `release(file)` (the
//! very next assertion expects the lock free).
//!
//! Hand census (printed into every model's notes): the `CString::new` NUL
//! check, `last_os_error` and the `Owner` mapping have no platform effect;
//! assertions are not encoded (a failed one ends the test, removing later
//! events only); `temp_dir`/`remove_dir_all`/`create_dir_all` are not encoded
//! (the namespace is flat: `ownerlock/m.log` is one name); the parked child's
//! socket read timeout (10 s, `SO_RCVTIMEO`) is not modeled — its read waits
//! for the parent's byte; `Command::status` is `spawn` then `wait`
//! (`waitpid`); the exec'd `/bin/sh -c 'exit 0'` / `/usr/bin/true` image is not
//! modeled (RL-IMAGE-EXIT: it exits whenever it likes).

use trust_platform::std_summaries::{CommandShape, CommandStd, StdioPlan};
use trust_platform::{Call, SocketOp, darwin};

use super::{M2Fixture, Property, loc, m2_env};
use crate::program::{
    Bind, BodyBuilder, BodyId, CmpOp, Cond, Mutation, Operand, ProgramBuilder, VarId,
};

const PATH: &str = "crates/aterm-uds/src/ownerlock.rs";

/// aterm ba30edc71^ (the pre-fix test).
pub const PRE: &str = "a6362ba55";
/// aterm ba30edc71 (the holder takes `LOCK_UN`, then closes).
pub const FIX: &str = "ba30edc71";
/// aterm origin/main when these fixtures were written (ownerlock.rs is
/// 6df3a3c78's).
pub const MAIN: &str = "79e636cdb";

// `std::env::temp_dir().join(format!("ownerlock-{}", std::process::id()))`:
// temp_dir() is $TMPDIR, /var/folders/<..>/T — canonically
// /private/var/folders/<..>/T (the model's namespace takes one spelling).
const M_LOG: &str = "/private/var/folders/T/ownerlock-PID/m.log";
const ABSENT: &str = "/private/var/folders/T/ownerlock-PID/absent.log";
const LINK: &str = "/private/var/folders/T/ownerlock-PID/link.log";
const MID_LOG: &str = "/private/var/folders/T/ownerlock-mid-PID/m.log";

/// `probe`'s open flags (ownerlock.rs: `O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC`).
const PROBE_FLAGS: i32 = darwin::O_NOFOLLOW | darwin::O_NONBLOCK | darwin::O_CLOEXEC;

/// `std::fs::File::create`'s flags (std adds `O_CLOEXEC`).
const CREATE: i32 = darwin::O_WRONLY | darwin::O_CREAT | darwin::O_TRUNC;

/// The probe's variables (shared by its inlined calls: they run in turn).
struct ProbeVars {
    fd: VarId,
    rc: VarId,
}

/// The lines of `probe` / `probe_while_locked` at one commit.
struct ProbeLines {
    commit: &'static str,
    open: &'static str,
    flock: &'static str,
    while_locked: &'static str,
    unlock: &'static str,
    close: &'static str,
    ret: &'static str,
}

/// `probe` at a6362ba55 (identical, line for line, at ba30edc71: that commit
/// changed only the tests).
const PROBE_PRE: ProbeLines = ProbeLines {
    commit: PRE,
    open: "65",
    flock: "70",
    while_locked: "72",
    unlock: "74",
    close: "77",
    ret: "78",
};

/// `probe_while_locked` at main.
const PROBE_MAIN: ProbeLines = ProbeLines {
    commit: MAIN,
    open: "78",
    flock: "83",
    while_locked: "86",
    unlock: "88",
    close: "91",
    ret: "92",
};

/// The probe of `path`, inlined at each call:
///
/// ```text
/// let fd = unsafe { open(c_path.as_ptr(), FLAGS) };
/// if fd < 0 { return Owner::Unknown; }
/// let locked = unsafe { flock(fd, LOCK_EX | LOCK_NB) } == 0;
/// if locked {
///     while_locked();                       // main only; `|| {}` when shipped
///     unsafe { flock(fd, LOCK_UN) };
/// }
/// unsafe { close(fd) };
/// ```
///
/// Its return is the owner's release point for the `probe` class.
fn probe_body(
    p: &mut ProgramBuilder,
    v: &ProbeVars,
    lines: &ProbeLines,
    path: &str,
    while_locked: impl FnOnce(&mut BodyBuilder),
) -> BodyId {
    let l = |line: &str| loc(lines.commit, PATH, line);
    let (fd, rc) = (v.fd, v.rc);
    p.body(&format!("probe({path})"), Vec::new(), |b| {
        b.event_full(
            &l(lines.open),
            "open",
            Call::OpenPath { at: None, path: path.to_string(), flags: PROBE_FLAGS },
            Bind::ret(fd),
            vec![trust_platform::Oracle::Nominal],
            None,
            vec!["probe"],
        );
        b.when(&l(lines.open), Cond::Cmp(CmpOp::Lt, Operand::Var(fd), Operand::Lit(0)), |b| {
            b.ret(&l(lines.open), None);
        });
        b.event(
            &l(lines.flock),
            "flock",
            Call::Flock { fd: Operand::Var(fd), op: darwin::LOCK_EX | darwin::LOCK_NB },
            Bind::ret(rc),
        );
        b.when(&l(lines.while_locked), Cond::eq(Operand::Var(rc), Operand::Lit(0)), |b| {
            while_locked(b);
            b.tag("probe_unlock").event(
                &l(lines.unlock),
                "flock",
                Call::Flock { fd: Operand::Var(fd), op: darwin::LOCK_UN },
                Bind::none(),
            );
        });
        b.event(&l(lines.close), "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
        b.release(&l(lines.ret), &["probe"]);
    })
}

/// RL-HARNESS: a sibling `#[test]` of the `aterm-uds` lib tests that forks a
/// child which execs — `spawnfd`'s tests do, through `Command::spawn` with a
/// `pre_exec` strip (ba30edc71's message: "skipping `spawnfd` alone dropped
/// it to 3/100"). Encoded as its essence, a `fork` and the child's `execve`:
/// the child holds a copy of every descriptor the process has open from its
/// fork to its exec, which is the window that decides whether a lock
/// outlives its owner. (std's status pipe and the strip act on the sibling's
/// own descriptors and the child's own table.)
fn add_sibling(p: &mut ProgramBuilder) -> usize {
    let at =
        |what: &str| format!("aterm-uds lib tests (RL-HARNESS): a sibling spawnfd test: {what}");
    let site = p.site("sibling_spawn", &at("fork"), None);
    let pid = p.var("sibling.pid", -1);
    let child = p.body("sibling child", Vec::new(), |b| {
        b.event_full(
            &at("execvp(\"/bin/sh\")"),
            "execvp",
            Call::Exec,
            Bind::none(),
            vec![trust_platform::Oracle::Nominal],
            None,
            Vec::new(),
        );
    });
    let body = p.body("sibling test", Vec::new(), |b| {
        b.fork(&at("Command::spawn: fork"), child, site, Some(pid));
    });
    p.root("sibling test (RL-HARNESS)", body)
}

/// The parked child's variables.
struct Park {
    ours: VarId,
    theirs: VarId,
    spawner: usize,
}

/// The lines of the parked child at one commit.
struct ParkLines {
    commit: &'static str,
    pair: &'static str,
    timeout: &'static str,
    thread: &'static str,
    command: &'static str,
    write: &'static str,
    read: &'static str,
    ok: &'static str,
    status: &'static str,
    drop_theirs: &'static str,
}

/// The spawner thread of the parked child:
///
/// ```text
/// let spawner = std::thread::spawn(move || {
///     let mut cmd = std::process::Command::new(SHELL);   // /usr/bin/true at ba30edc71
///     cmd.stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null());
///     unsafe {
///         cmd.pre_exec(move || {
///             let mut byte = 0u8;
///             write(theirs_fd, (&raw const byte).cast(), 1);
///             read(theirs_fd, (&raw mut byte).cast(), 1);
///             Ok(())
///         });
///     }
///     let status = cmd.status();
///     drop(theirs);
///     status
/// });
/// ```
fn add_parked(p: &mut ProgramBuilder, lines: &ParkLines) -> Park {
    let l = |line: &str| loc(lines.commit, PATH, line);
    let ours = p.var("park.ours", -1);
    let theirs = p.var("park.theirs", -1);
    let pid = p.var("park.pid", -1);
    let site = p.site("parked_spawn", &l(lines.status), None);
    let hook = p.body("parked pre_exec", Vec::new(), |b| {
        b.io(
            &l(lines.write),
            Call::WriteSome { fd: Operand::Var(theirs) },
            Bind::none(),
            "write(theirs_fd, &byte, 1): one byte to a socketpair end the parent keeps open",
        );
        b.io(
            &l(lines.read),
            Call::ReadSome { fd: Operand::Var(theirs) },
            Bind::none(),
            "read(theirs_fd, &mut byte, 1): one byte from that end (the 10 s SO_RCVTIMEO is \
             not modeled: the read waits for the parent's byte or end of file)",
        );
        b.ret(&l(lines.ok), Some(Operand::Lit(0)));
    });
    let body = p.body("spawner thread", Vec::new(), |b| {
        b.neutral(&l(lines.command), "std::os::unix::process::CommandExt::pre_exec");
        b.spawn(
            &l(lines.status),
            [StdioPlan::Null; 3],
            CommandShape::with_pre_exec().under(CommandStd::Upstream),
            vec![hook],
            site,
            Some(pid),
        );
        b.when(&l(lines.status), Cond::ne(Operand::Var(pid), Operand::Lit(-1)), |b| {
            b.event(
                &l(lines.status),
                "waitpid",
                Call::Waitpid { pid: Operand::Var(pid), options: 0 },
                Bind::none(),
            );
        });
        b.event(
            &l(lines.drop_theirs),
            "close",
            Call::Close { fd: Operand::Var(theirs) },
            Bind::none(),
        );
    });
    let spawner = p.thread("spawner", body);
    let _ = (lines.pair, lines.timeout, lines.thread);
    Park { ours, theirs, spawner }
}

/// Park the child (the main thread's half): the socketpair, the read timeout
/// on the child's end, the spawner thread, and the wait for the child's byte.
fn park_here(b: &mut BodyBuilder, park: &Park, lines: &ParkLines) {
    let l = |line: &str| loc(lines.commit, PATH, line);
    b.std_row(
        &l(lines.pair),
        "std::os::unix::net::UnixStream::pair",
        Vec::new(),
        vec![park.ours, park.theirs],
        vec!["park_ours", "park_theirs"],
    );
    b.event(
        &l(lines.timeout),
        "setsockopt",
        Call::SocketOp { fd: Operand::Var(park.theirs), op: SocketOp::Setsockopt },
        Bind::none(),
    );
    b.spawn_thread(&l(lines.thread), park.spawner);
}

fn program(name: &str) -> ProgramBuilder {
    let mut p = ProgramBuilder::new(name);
    p.lock_release_policy();
    p.disclose(
        "ownerlock: CString::new's NUL check, last_os_error and the Owner mapping have no \
         platform effect; assertions are not encoded (a failed one ends the test, removing later \
         events only); temp_dir/remove_dir_all/create_dir_all are not encoded (the namespace is \
         flat; temp_dir() is spelled canonically, /private/var/folders/T, and the pid PID); \
         Command::status is spawn then wait (waitpid); the exec'd image is not modeled",
    );
    p
}

/// The test of a6362ba55 / ba30edc71, both versions:
///
/// ```text
/// let file = std::fs::File::create(&path).expect("create");
/// assert_eq!(unsafe { flock(file.as_raw_fd(), 2 | 4) }, 0);
/// assert_eq!(probe(&path), Owner::Live, "held through another open");
/// // a6362ba55:   drop(file);
/// // ba30edc71:   park a child; release(file) = flock(LOCK_UN), drop(file);
/// assert_eq!(probe(&path), Owner::Dead, "the holder closed it" / "released it");
/// // ba30edc71:   ours.write_all(b"g"); spawner.join();
/// assert_eq!(probe(&path), Owner::Dead, "the probe released its own lock");
/// assert_eq!(probe(&dir.join("absent.log")), Owner::Unknown);
/// std::os::unix::fs::symlink(&path, &link).expect("symlink");
/// assert_eq!(probe(&link), Owner::Unknown, "a symlink is never followed");
/// ```
fn reads_the_owner_lock(fixed: bool) -> crate::program::EventProgram {
    let commit = if fixed { FIX } else { PRE };
    let name = if fixed { "ownerlock_unlock_then_close" } else { "ownerlock_bare_close" };
    let mut p = program(name);
    p.provenance("aterm", commit, PATH, "tests::the_probe_reads_the_owner_lock, and probe");
    let l = |line: &str| loc(commit, PATH, line);
    let pv = ProbeVars { fd: p.var("probe.fd", -1), rc: p.var("probe.rc", -1) };
    let file = p.var("file", -1);
    let rc = p.var("rc", -1);
    let probe_m = probe_body(&mut p, &pv, &PROBE_PRE, M_LOG, |_| {});
    let probe_absent = probe_body(&mut p, &pv, &PROBE_PRE, ABSENT, |_| {});
    let probe_link = probe_body(&mut p, &pv, &PROBE_PRE, LINK, |_| {});
    let lines = ParkLines {
        commit: FIX,
        pair: "145",
        timeout: "146",
        thread: "150",
        command: "151",
        write: "161",
        read: "162",
        ok: "163",
        status: "166",
        drop_theirs: "167",
    };
    let park = fixed.then(|| add_parked(&mut p, &lines));
    let ln = |pre: &'static str, fix: &'static str| if fixed { fix } else { pre };
    let main = p.body("the_probe_reads_the_owner_lock", Vec::new(), |b| {
        b.std_open(&l(ln("111", "137")), "std::fs::File::create", M_LOG, CREATE, file, "holder");
        b.event(
            &l(ln("113", "139")),
            "flock",
            Call::Flock { fd: Operand::Var(file), op: darwin::LOCK_EX | darwin::LOCK_NB },
            Bind::ret(rc),
        );
        b.call(&l(ln("114", "140")), probe_m, Vec::new(), None);
        if let Some(park) = &park {
            park_here(b, park, &lines);
            b.io(
                &l("171"),
                Call::ReadSome { fd: Operand::Var(park.ours) },
                Bind::none(),
                "ours.read_exact(&mut parked): the child's one byte",
            );
            // release(file), ownerlock.rs:112-117.
            b.tag("release_unlock").event(
                &l("115"),
                "flock",
                Call::Flock { fd: Operand::Var(file), op: darwin::LOCK_UN },
                Bind::none(),
            );
            b.event(&l("116"), "close", Call::Close { fd: Operand::Var(file) }, Bind::none());
            b.release(&l("172"), &["holder"]);
        } else {
            b.event(&l("115"), "close", Call::Close { fd: Operand::Var(file) }, Bind::none());
            b.release(&l("115"), &["holder"]);
        }
        b.call(&l(ln("116", "175")), probe_m, Vec::new(), None);
        if let Some(park) = &park {
            b.io(
                &l("176"),
                Call::WriteSome { fd: Operand::Var(park.ours) },
                Bind::none(),
                "ours.write_all(b\"g\"): one byte that lets the child exec",
            );
            b.join(&l("177"), park.spawner);
        }
        b.call(&l(ln("117", "181")), probe_m, Vec::new(), None);
        b.call(&l(ln("118", "182")), probe_absent, Vec::new(), None);
        b.event(
            &l(ln("120", "184")),
            "symlink",
            Call::Symlink { target: M_LOG.to_string(), path: LINK.to_string() },
            Bind::none(),
        );
        b.call(&l(ln("121", "185")), probe_link, Vec::new(), None);
    });
    p.root("main", main);
    add_sibling(&mut p);
    p.build()
}

/// Bug 1 as shipped in the test before ba30edc71: MUST be refuted.
#[must_use]
pub fn bare_close() -> M2Fixture {
    M2Fixture {
        name: "ownerlock_bare_close",
        program: reads_the_owner_lock(false),
        env: m2_env(&[]),
        property: Property::LockRelease,
        expect_refuted: true,
        current_main: false,
        hygiene: Vec::new(),
    }
}

/// ba30edc71: must NOT be refuted; deleting either `LOCK_UN` refutes it.
#[must_use]
pub fn unlock_then_close() -> M2Fixture {
    M2Fixture {
        name: "ownerlock_unlock_then_close",
        program: reads_the_owner_lock(true),
        env: m2_env(&[]),
        property: Property::LockRelease,
        expect_refuted: false,
        current_main: false,
        hygiene: vec![
            Mutation::DeleteStmt("release_unlock".to_string()),
            Mutation::DeleteStmt("probe_unlock".to_string()),
        ],
    }
}

/// Main's `a_child_forked_mid_probe_does_not_keep_the_probes_lock`:
///
/// ```text
/// drop(std::fs::File::create(&path).expect("create"));
/// let mut parked = None;
/// let first = probe_while_locked(&path, || parked = Some(Parked::park()));
/// assert_eq!(first, Owner::Dead, "nobody holds it");
/// let parked = parked.expect("the probe took the free lock and forked holding it");
/// assert_eq!(probe(&path), Owner::Dead, "the child forked mid-probe kept the probe's lock: …");
/// let status = parked.release();      // let_go: write_all(b"g"), shutdown(Write); join
/// ```
fn mid_probe() -> crate::program::EventProgram {
    let mut p = program("ownerlock_mid_probe");
    p.provenance(
        "aterm",
        MAIN,
        PATH,
        "probe_while_locked, Parked, tests::a_child_forked_mid_probe_does_not_keep_the_probes_lock",
    );
    let l = |line: &str| loc(MAIN, PATH, line);
    let pv = ProbeVars { fd: p.var("probe.fd", -1), rc: p.var("probe.rc", -1) };
    let created = p.var("created", -1);
    let parked = p.var("parked", 0);
    let lines = ParkLines {
        commit: MAIN,
        pair: "172",
        timeout: "173",
        thread: "177",
        command: "178",
        write: "190",
        read: "191",
        ok: "192",
        status: "195",
        drop_theirs: "196",
    };
    let park = add_parked(&mut p, &lines);
    let (ours, spawner) = (park.ours, park.spawner);
    let probe_park = probe_body(&mut p, &pv, &PROBE_MAIN, MID_LOG, |b| {
        // while_locked = || parked = Some(Parked::park())   (tests, 292)
        park_here(b, &park, &lines);
        b.io(
            &l("206"),
            Call::ReadSome { fd: Operand::Var(ours) },
            Bind::none(),
            "parked.ours.read_exact(&mut byte): the child's one byte",
        );
        b.assign(&l("292"), parked, crate::program::Expr::Use(Operand::Lit(1)));
    });
    let probe_plain = probe_body(&mut p, &pv, &PROBE_MAIN, MID_LOG, |_| {});
    let main = p.body("a_child_forked_mid_probe_does_not_keep_the_probes_lock", Vec::new(), |b| {
        b.std_open(&l("289"), "std::fs::File::create", MID_LOG, CREATE, created, "created");
        b.event(&l("289"), "close", Call::Close { fd: Operand::Var(created) }, Bind::none());
        b.call(&l("292"), probe_park, Vec::new(), None);
        b.call(&l("296"), probe_plain, Vec::new(), None);
        // parked.release(): let_go (229-232), then the join (217).
        b.when(&l("294"), Cond::eq(Operand::Var(parked), Operand::Lit(1)), |b| {
            b.io(
                &l("230"),
                Call::WriteSome { fd: Operand::Var(ours) },
                Bind::none(),
                "self.ours.write_all(b\"g\"): one byte that lets the child exec",
            );
            b.event(
                &l("231"),
                "shutdown",
                Call::SocketOp { fd: Operand::Var(ours), op: SocketOp::Shutdown },
                Bind::none(),
            );
            b.join(&l("217"), spawner);
        });
    });
    p.root("main", main);
    add_sibling(&mut p);
    p.build()
}

/// Main as shipped: must NOT be refuted; deleting the probe's `LOCK_UN`
/// refutes it ([`probe_no_unlock`]).
#[must_use]
pub fn probe_shipped() -> M2Fixture {
    M2Fixture {
        name: "probe_shipped",
        program: mid_probe(),
        env: m2_env(&[]),
        property: Property::LockRelease,
        expect_refuted: false,
        current_main: true,
        hygiene: vec![Mutation::DeleteStmt("probe_unlock".to_string())],
    }
}

/// The parked-child forcing case: main's test with the probe's `LOCK_UN`
/// deleted. MUST be refuted.
#[must_use]
pub fn probe_no_unlock() -> M2Fixture {
    let mut program = mid_probe()
        .mutate(&Mutation::DeleteStmt("probe_unlock".to_string()))
        .unwrap_or_else(|e| panic!("{e:?}"));
    program.name = "probe_no_unlock".to_string();
    M2Fixture {
        name: "probe_no_unlock",
        program,
        env: m2_env(&[]),
        property: Property::LockRelease,
        expect_refuted: true,
        current_main: false,
        hygiene: Vec::new(),
    }
}
