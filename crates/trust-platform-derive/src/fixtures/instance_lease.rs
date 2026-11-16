//! A bug-1 variant on CURRENT aterm main (79e636cdb): the dead-instance sweep
//! of `crates/aterm-gui/src/control_auth.rs` probes a dead instance's lease
//! with `try_lock` (`flock(LOCK_EX|LOCK_NB)`) and lets go of the lock it took
//! by DROPPING the `File` — `close` alone, no `LOCK_UN`.
//!
//! `DeadNamespaceSweep::run_batch_with_hook` (control_auth.rs:2105-2156):
//!
//! ```text
//! before_lease_probe();
//! let (lease_state, acquired_lease) = match namespace
//!     .open_existing_namespace_lock_at_retained(OsStr::new(INSTANCE_LEASE_FILE))
//! {
//!     Ok(lease) => match lease.try_lock() {
//!         Ok(()) => (InstanceLeaseState::Acquirable, Some(lease)),
//!         Err(TryLockError::WouldBlock) => (InstanceLeaseState::Held, None),
//!         Err(TryLockError::Error(_)) => (InstanceLeaseState::Invalid, None),
//!     },
//!     ..
//! };
//! ..
//! if decide_instance_namespace_sweep(lease_state, legacy_pid_alive) == Remove {
//!     let _acquired_lease = acquired_lease;
//!     if namespace.validate_path_identity().is_err() {
//!         continue;                                   // <- the lease drops: close, no LOCK_UN
//!     }
//!     let tombstone = fresh_instance_tombstone_name();
//!     if self.root.rename_child_exact(&entry_name, &namespace, &tombstone).is_err() {
//!         continue;                                   // <- the same
//!     }
//!     ..
//!     mutated |= cleanup_instance_tombstone(..);      // the lease file is removed
//! }                                                   // <- the lease drops
//! ```
//!
//! The sweep runs on aterm-gui's cleanup worker; another thread spawns PTY
//! sessions with a raw `fork` (`aterm-pty/src/unix.rs:1812` at 79e636cdb,
//! `:1791` on origin/main b4aa8577e), whose child holds a copy of every
//! descriptor the process has open until it `execve`s (`:1993`; `:1977`). A fork landing between the sweep's `try_lock` and its drop
//! keeps the dead instance's lease LOCKED after the sweep let go of it — on
//! the two `continue` paths with the lease file still in place, so every
//! probe of it (this process's next sweep, another aterm's) reads the dead
//! instance as LIVE until that child execs. It is exactly the probe defect
//! `ownerlock.rs` fixed with `LOCK_UN` before `close` (16cdc4ba0, ba30edc71;
//! the 2026-09-27 fd-hygiene sweep elsewhere), missed here.
//!
//! * [`sweep_main`] — the shipped code: refuted (a real bug).
//! * [`sweep_unlock_first`] — the repair (`LOCK_UN` before each drop of an
//!   acquired lease, as `ownerlock::probe` does): not refuted; deleting either
//!   `LOCK_UN` refutes it.
//!
//! Hand census (printed into the models' notes):
//! `open_existing_namespace_lock_at_retained` is `openat(leaf, name, O_RDWR |
//! O_NOFOLLOW | O_NONBLOCK | O_CLOEXEC)` through the retained directory
//! descriptor (pinned_dir.rs:598-618) — encoded as `open` of the lease's path
//! (the model's namespace is flat; the directory descriptor pins the same
//! directory); its `st_nlink == 1` check is assumed to hold (link counts are
//! not modeled); `validate_path_identity` (pinned_dir.rs:620-633) is encoded
//! as the open of the namespace directory it makes, whose failure (the
//! oracle's `EACCES`) is its `Err` — the identity comparison it adds is not
//! modeled; `rename_child_exact` is not modeled (its `Err` takes the same
//! `continue`); `cleanup_instance_tombstone` is encoded as the removal of the
//! lease file; the PTY child's `login_tty` and descriptor strip act on its own
//! table and are not encoded.

use trust_platform::{Call, Errno, NodeKind, Oracle, darwin};

use super::{M2Fixture, Property, loc, m2_env};
use crate::program::{Bind, Cond, EventProgram, Mutation, Operand, ProgramBuilder};

const PATH: &str = "crates/aterm-gui/src/control_auth.rs";
const PINNED: &str = "crates/aterm-gui/src/pinned_dir.rs";
const PTY: &str = "crates/aterm-pty/src/unix.rs";
const OBSERVER: &str = "crates/aterm-gui/src/consent_observer.rs";
const SPAWNFD: &str = "crates/aterm-uds/src/spawnfd.rs";

/// aterm origin/main when these fixtures were written.
pub const MAIN: &str = "79e636cdb";

/// aterm origin/main at the M2 review (2026-10-01): `control_auth.rs`,
/// `pinned_dir.rs` unchanged since [`MAIN`]; the consent observer spawns its
/// `log` tool through `spawnfd::spawn` (99eee8aa1).
pub const MAIN_NOW: &str = "b4aa8577e";

/// What spawns beside the sweep.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Racer {
    /// A PTY session: a raw `fork`, then `execve` (aterm-pty).
    PtyFork,
    /// The consent observer's `/usr/bin/log stream`: `spawnfd::spawn`, a
    /// `posix_spawn` with `POSIX_SPAWN_CLOEXEC_DEFAULT` — whose child holds a
    /// copy of the WHOLE table, close-on-exec entries included, until its image
    /// starts (the M2 model review's F1, MEASURED).
    LaneSpawn,
}

/// A dead instance's namespace directory under the sweep's root (the control
/// socket directory, spelled canonically ROOT) and its lease
/// (`INSTANCE_LEASE_FILE`, control_auth.rs:1805).
const NS_DIR: &str = "/private/var/folders/T/aterm-ROOT/dead-instance";
const LEASE: &str = "/private/var/folders/T/aterm-ROOT/dead-instance/.instance.lease";

fn sweep(unlock_first: bool, racer: Racer) -> EventProgram {
    let name = match (unlock_first, racer) {
        (true, _) => "instance_sweep_unlock_first",
        (false, Racer::PtyFork) => "instance_sweep_main",
        (false, Racer::LaneSpawn) => "instance_sweep_main_lane_spawn",
    };
    let mut p = ProgramBuilder::new(name);
    p.lock_release_policy();
    p.provenance(
        "aterm",
        MAIN,
        PATH,
        "DeadNamespaceSweep::run_batch_with_hook, one dead namespace",
    );
    p.provenance("aterm", MAIN, PINNED, "open_existing_namespace_lock_at_retained");
    match racer {
        Racer::PtyFork => p.provenance("aterm", MAIN, PTY, "spawn: fork, execve"),
        Racer::LaneSpawn => {
            p.provenance("aterm", MAIN_NOW, OBSERVER, "run_log_tool: spawnfd::spawn(log stream)");
            p.provenance(
                "aterm",
                MAIN_NOW,
                SPAWNFD,
                "platform::spawn: posix_spawn, CLOEXEC_DEFAULT",
            );
            p.disclose(
                "lane spawn: spawnfd::spawn's file actions (stdin /dev/null, stdout the pipe, \
                 stderr /dev/null) and its SETSIGDEF/SETSIGMASK attributes are left out: they act \
                 on the child's own table after its copy, and the copy is what holds the lease",
            );
        }
    }
    p.disclose(
        "instance sweep: the retained-directory openat is encoded as open of the lease's path \
         (flat namespace); st_nlink == 1 is assumed; validate_path_identity is the open of the \
         namespace directory it makes (its failure is the oracle's EACCES; the identity \
         comparison is not modeled); rename_child_exact is not modeled (its Err takes the same \
         continue); cleanup_instance_tombstone is the lease file's removal; the PTY child's \
         login_tty and strip are not encoded; the sweep's root (the control socket directory) \
         is spelled canonically, /private/var/folders/T/aterm-ROOT",
    );
    if unlock_first {
        p.disclose("PROPOSED FIX (not in aterm): LOCK_UN before each drop of an acquired lease");
    }
    let l = |line: &str| loc(MAIN, PATH, line);
    let lp = |line: &str| loc(MAIN, PINNED, line);
    let lease = p.var("lease", -1);
    let node = p.var("lease.node", -1);
    let ftype = p.var("lease.ftype", -1);
    let rc = p.var("try_lock", -1);
    let dir = p.var("validate", -1);
    let unlock = |b: &mut crate::program::BodyBuilder, tag: &str, line: &str| {
        if unlock_first {
            b.tag(tag).event(
                &l(line),
                "flock",
                Call::Flock { fd: Operand::Var(lease), op: darwin::LOCK_UN },
                Bind::none(),
            );
        }
    };
    let body = p.body("run_batch_with_hook (one dead namespace)", Vec::new(), |b| {
        b.event_full(
            &lp("603"),
            "open",
            Call::OpenPath {
                at: None,
                path: LEASE.to_string(),
                flags: darwin::O_RDWR | darwin::O_NOFOLLOW | darwin::O_NONBLOCK | darwin::O_CLOEXEC,
            },
            Bind::ret(lease),
            vec![Oracle::Nominal],
            None,
            vec!["lease"],
        );
        b.when(&l("2123"), Cond::eq(Operand::Var(lease), Operand::Lit(-1)), |b| {
            b.ret(&l("2126"), None);
        });
        b.event(
            &lp("610"),
            "fstat",
            Call::Fstat { fd: Operand::Var(lease) },
            Bind { ret: Some(node), ret2: Some(ftype), rlim_soft: None },
        );
        b.when(
            &lp("611"),
            Cond::ne(Operand::Var(ftype), Operand::Lit(i64::from(darwin::S_IFREG))),
            |b| {
                b.event(&lp("612"), "close", Call::Close { fd: Operand::Var(lease) }, Bind::none());
                b.ret(&l("2126"), None);
            },
        );
        b.event(
            &l("2118"),
            "flock",
            Call::Flock { fd: Operand::Var(lease), op: darwin::LOCK_EX | darwin::LOCK_NB },
            Bind::ret(rc),
        );
        b.when(&l("2120"), Cond::ne(Operand::Var(rc), Operand::Lit(0)), |b| {
            // Held / Invalid: the lease drops holding no lock of ours.
            b.event(&l("2120"), "close", Call::Close { fd: Operand::Var(lease) }, Bind::none());
            b.ret(&l("2121"), None);
        });
        // Acquirable -> Remove (control_auth.rs:1842).
        b.event_full(
            &lp("621"),
            "open",
            Call::OpenPath {
                at: None,
                path: NS_DIR.to_string(),
                flags: darwin::O_RDONLY | darwin::O_DIRECTORY | darwin::O_CLOEXEC,
            },
            Bind::ret(dir),
            vec![Oracle::Nominal, Oracle::Fail(Errno::EACCES)],
            None,
            vec!["validate_dir"],
        );
        b.when(&l("2137"), Cond::eq(Operand::Var(dir), Operand::Lit(-1)), |b| {
            unlock(b, "unlock_on_continue", "2138");
            b.event(&l("2138"), "close", Call::Close { fd: Operand::Var(lease) }, Bind::none());
            b.release(&l("2138"), &["lease"]);
            b.ret(&l("2138"), None);
        });
        b.event(&lp("632"), "close", Call::Close { fd: Operand::Var(dir) }, Bind::none());
        b.event(&l("2150"), "unlink", Call::Unlink { path: LEASE.to_string() }, Bind::none());
        unlock(b, "unlock_on_done", "2156");
        b.event(&l("2156"), "close", Call::Close { fd: Operand::Var(lease) }, Bind::none());
        b.release(&l("2156"), &["lease"]);
    });
    p.root("cleanup worker", body);
    if racer == Racer::LaneSpawn {
        // The consent observer's thread starts `/usr/bin/log stream`
        // (consent_observer.rs:1087 -> spawnfd.rs:709).
        let site = p.site("log_tool", &loc(MAIN_NOW, SPAWNFD, "709"), None);
        let pid = p.var("log.pid", -1);
        let observer = p.body("consent observer", Vec::new(), |b| {
            b.event_full(
                &loc(MAIN_NOW, SPAWNFD, "709"),
                "posix_spawn",
                Call::Spawn { actions: Vec::new(), flags: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT },
                Bind::ret(pid),
                vec![Oracle::Nominal],
                Some(site),
                Vec::new(),
            );
        });
        p.root("consent observer", observer);
        return p.build();
    }
    // Another aterm-gui thread spawns a PTY session (aterm-pty unix.rs:1812,
    // :1993 at 79e636cdb): fork, then (login_tty, the strip) execve.
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
    let spawner = p.body("session spawn", Vec::new(), |b| {
        b.fork(&loc(MAIN, PTY, "1812"), child, site, Some(pid));
    });
    p.root("session spawner", spawner);
    p.build()
}

fn env() -> crate::env::EnvSpec {
    m2_env(&[(NS_DIR, NodeKind::Directory), (LEASE, NodeKind::Regular)])
}

/// The shipped sweep: refuted — a real bug on current main.
#[must_use]
pub fn sweep_main() -> M2Fixture {
    M2Fixture {
        name: "instance_sweep_main",
        program: sweep(false, Racer::PtyFork),
        env: env(),
        property: Property::LockRelease,
        expect_refuted: true,
        current_main: true,
        hygiene: Vec::new(),
    }
}

/// The repair (not in aterm): not refuted; deleting the `LOCK_UN` of the
/// `continue` path refutes it. The `LOCK_UN` of the done path (2156) is NOT
/// load-bearing: the lease file was unlinked at 2150, so no name reaches the
/// node a leaked lock would stay on, and no probe can contend for it (the M2
/// checker review's L8) — it stays in the repair as hygiene, not in the sweep.
#[must_use]
pub fn sweep_unlock_first() -> M2Fixture {
    M2Fixture {
        name: "instance_sweep_unlock_first",
        program: sweep(true, Racer::PtyFork),
        env: env(),
        property: Property::LockRelease,
        expect_refuted: false,
        current_main: false,
        hygiene: vec![Mutation::DeleteStmt("unlock_on_continue".to_string())],
    }
}

/// The shipped sweep beside a `posix_spawn` with `POSIX_SPAWN_CLOEXEC_DEFAULT`
/// (current main b4aa8577e: the consent observer's log tool through
/// `spawnfd::spawn`): refuted — the spawn's child holds the close-on-exec lease
/// copy between its halves, so the inheritance fix 99eee8aa1 (spawns that hand
/// the child nothing) does not close bug 1's window. The repair is the same
/// `LOCK_UN`.
#[must_use]
pub fn sweep_main_lane_spawn() -> M2Fixture {
    M2Fixture {
        name: "instance_sweep_main_lane_spawn",
        program: sweep(false, Racer::LaneSpawn),
        env: env(),
        property: Property::LockRelease,
        expect_refuted: true,
        current_main: true,
        hygiene: Vec::new(),
    }
}
