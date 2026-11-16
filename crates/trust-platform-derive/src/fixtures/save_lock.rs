//! A bug-1 variant in CURRENT aterm main's tests (79e636cdb):
//! `crates/aterm-gui/src/native_document_host.rs`,
//! `a_lock_held_for_one_stalled_device_barrier_is_waited_out_not_reported_busy`
//! (lines 2864-2903; native_document_host.rs is 389de9dbe's at main).
//!
//! ```text
//! let holder = open_write_lock(&lock_path).unwrap();
//! acquire_write_lock(&holder).unwrap();
//! let started = std::time::Instant::now();
//! let released = std::thread::spawn(move || {
//!     std::thread::sleep(HELD);              // 100 ms
//!     drop(holder);                          // <- close alone, no LOCK_UN
//! });
//! let verdict = commit_atomic_bytes(&contents.baseline, b"after");
//! let waited = started.elapsed();
//! released.join().unwrap();
//! assert!(matches!(verdict, AtomicCommitResult::Committed(_)),
//!         "a {HELD:?} lock holder must be waited out, not reported busy: {verdict:?}");
//! ```
//!
//! The holder lets go by `drop` — `close` alone. The aterm-gui test binary
//! runs PTY tests concurrently, and a PTY session is a raw `fork`
//! (`aterm-pty/src/unix.rs:1812` at 79e636cdb) whose child holds a copy of every
//! descriptor until it `execve`s. A fork landing while the holder's lock is
//! held keeps that lock past the `drop`, and the commit's preflight (a 500 ms
//! budget, `PREFLIGHT_RETRY_BUDGET`, :1673) waits out the child's exec on top
//! of the 100 ms hold — the sibling test 40 lines below says a fork's copy
//! outlives a close "measured up to 523 ms here" against exactly that budget,
//! and released ITS holder with `unlock()` before `drop` for that reason
//! (the fd-copy sweep of 2026-09-27). This one was missed: a flake, the same
//! class as bug 1's ba30edc71.
//!
//! * [`bare_drop`] — the shipped test: refuted.
//! * [`unlock_then_drop`] — the repair (`holder.unlock()` before the drop, as
//!   `held_save_lock_returns_busy_and_retry_commits` does): not refuted;
//!   deleting the `LOCK_UN` refutes it.
//!
//! Hand census (printed into the models' notes): `unique_file` /
//! `read_atomic_file` / the commit's file writes are not encoded (no lock);
//! `open_write_lock`'s `fstat` is-a-file check holds and its `fchmod` has no
//! descriptor effect; `acquire_write_lock` takes the free lock at its first
//! try; the commit's preflight is encoded as its first try of the lock (its
//! bounded retries are not: the property is about the holder's release, not
//! the waiter); the 100 ms sleep has no platform event; the PTY child's
//! `login_tty` and strip act on its own table.

use trust_platform::{Call, Oracle, darwin};

use super::{M2Fixture, Property, loc, m2_env};
use crate::program::{Bind, Cond, EventProgram, Mutation, Operand, ProgramBuilder};

const PATH: &str = "crates/aterm-gui/src/native_document_host.rs";
const PTY: &str = "crates/aterm-pty/src/unix.rs";

/// aterm origin/main.
pub const MAIN: &str = "79e636cdb";

/// `unique_file("waited-save-lock", ..)`'s write lock, beside the document in
/// a temp_dir() directory (spelled canonically).
const LOCK: &str = "/private/var/folders/T/aterm-doc-PID/.waited-save-lock.aterm-write.lock";

/// `open_write_lock`'s flags (std adds `O_CLOEXEC`; the custom flags add
/// `O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK`).
const WRITE_LOCK_FLAGS: i32 =
    darwin::O_RDWR | darwin::O_CREAT | darwin::O_CLOEXEC | darwin::O_NOFOLLOW | darwin::O_NONBLOCK;

fn test(unlock_first: bool) -> EventProgram {
    let name = if unlock_first { "save_lock_unlock_then_drop" } else { "save_lock_bare_drop" };
    let mut p = ProgramBuilder::new(name);
    p.lock_release_policy();
    p.provenance(
        "aterm",
        MAIN,
        PATH,
        "tests::a_lock_held_for_one_stalled_device_barrier_is_waited_out_not_reported_busy",
    );
    p.provenance("aterm", MAIN, PTY, "spawn: fork, execve (a concurrent PTY test)");
    p.disclose(
        "save lock: unique_file/read_atomic_file/the commit's writes are not encoded; \
         open_write_lock's is-a-file check holds and its fchmod has no descriptor effect; \
         acquire_write_lock takes the free lock at its first try; the commit's preflight is its \
         first try of the lock (the bounded retries are not encoded); the sleep has no event; \
         the PTY child's login_tty and strip act on its own table; the lock's temp_dir() \
         directory is spelled canonically, /private/var/folders/T",
    );
    if unlock_first {
        p.disclose("PROPOSED FIX (not in aterm): holder.unlock() before drop(holder)");
    }
    let l = |line: &str| loc(MAIN, PATH, line);
    let holder = p.var("holder", -1);
    let rc = p.var("rc", -1);
    let probe = p.var("commit.lock", -1);
    let prc = p.var("commit.rc", -1);
    let release = p.body("released thread", Vec::new(), |b| {
        if unlock_first {
            b.tag("holder_unlock").event(
                &l("2886"),
                "flock",
                Call::Flock { fd: Operand::Var(holder), op: darwin::LOCK_UN },
                Bind::none(),
            );
        }
        b.event(&l("2886"), "close", Call::Close { fd: Operand::Var(holder) }, Bind::none());
        b.release(&l("2886"), &["save_lock_holder"]);
    });
    let released = p.thread("released", release);
    let main = p.body(
        "a_lock_held_for_one_stalled_device_barrier_is_waited_out_not_reported_busy",
        Vec::new(),
        |b| {
            b.event_full(
                &l("2879"),
                "open",
                Call::OpenPath { at: None, path: LOCK.to_string(), flags: WRITE_LOCK_FLAGS },
                Bind::ret(holder),
                vec![Oracle::Nominal],
                None,
                vec!["save_lock_holder"],
            );
            b.event(
                &l("2880"),
                "flock",
                Call::Flock { fd: Operand::Var(holder), op: darwin::LOCK_EX | darwin::LOCK_NB },
                Bind::ret(rc),
            );
            b.spawn_thread(&l("2884"), released);
            // commit_atomic_bytes (2889) -> lock_and_verify_target (1710-1716):
            // the save lock's own open, then its first try (1578).
            b.event_full(
                &l("1710"),
                "open",
                Call::OpenPath { at: None, path: LOCK.to_string(), flags: WRITE_LOCK_FLAGS },
                Bind::ret(probe),
                vec![Oracle::Nominal],
                None,
                vec!["commit_lock"],
            );
            b.event(
                &l("1712"),
                "flock",
                Call::Flock { fd: Operand::Var(probe), op: darwin::LOCK_EX | darwin::LOCK_NB },
                Bind::ret(prc),
            );
            b.when(&l("1716"), Cond::eq(Operand::Var(prc), Operand::Lit(0)), |b| {
                // HeldAdvisoryLock's drop: LOCK_UN, then the close.
                b.event(
                    &l("1619"),
                    "flock",
                    Call::Flock { fd: Operand::Var(probe), op: darwin::LOCK_UN },
                    Bind::none(),
                );
            });
            b.event(&l("1619"), "close", Call::Close { fd: Operand::Var(probe) }, Bind::none());
            b.join(&l("2891"), released);
        },
    );
    p.root("main", main);
    // A concurrent PTY test's session spawn (aterm-pty unix.rs:1812, :1993 at
    // 79e636cdb).
    let site = p.site("pty_session", &loc(MAIN, PTY, "1812"), None);
    let pid = p.var("pty.pid", -1);
    let child = p.body("pty child", Vec::new(), |b| {
        b.event_full(
            &loc(MAIN, PTY, "1993"),
            "execve",
            Call::Exec,
            Bind::none(),
            vec![Oracle::Nominal],
            None,
            Vec::new(),
        );
    });
    let spawner = p.body("a PTY test (RL-HARNESS)", Vec::new(), |b| {
        b.fork(&loc(MAIN, PTY, "1812"), child, site, Some(pid));
    });
    p.root("PTY test (RL-HARNESS)", spawner);
    p.build()
}

/// The shipped test: refuted — a real flake on current main.
#[must_use]
pub fn bare_drop() -> M2Fixture {
    M2Fixture {
        name: "save_lock_bare_drop",
        program: test(false),
        env: m2_env(&[]),
        property: Property::LockRelease,
        expect_refuted: true,
        current_main: true,
        hygiene: Vec::new(),
    }
}

/// The repair (not in aterm): not refuted; deleting the `LOCK_UN` refutes it.
#[must_use]
pub fn unlock_then_drop() -> M2Fixture {
    M2Fixture {
        name: "save_lock_unlock_then_drop",
        program: test(true),
        env: m2_env(&[]),
        property: Property::LockRelease,
        expect_refuted: false,
        current_main: false,
        hygiene: vec![Mutation::DeleteStmt("holder_unlock".to_string())],
    }
}
