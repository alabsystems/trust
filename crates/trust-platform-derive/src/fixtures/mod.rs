//! The M1 acceptance fixtures: aterm code transcribed BY HAND into event
//! programs (plan §3 M1, bug 3), until the THIR -> trust-ir producer lowers
//! the aterm-uds bodies itself (P1-P3).
//!
//! Each fixture names the aterm commit and file it was read from and quotes
//! the code it encodes next to the statements that encode it; every
//! statement's [`crate::program::Loc`] is `aterm@<commit>:<path>:<line>`.
//!
//! What is hand-encoded, and so trusted rather than derived:
//! * the event programs themselves (the census's job);
//! * the caller context (`fabric_launch.rs`'s `Stdio::null()` stdin and the
//!   `UnixStream::pair()` far ends passed in);
//! * the racing thread (the e17e2d6d5 probe's `UnixStream::pair()` racer,
//!   which also spawns a child);
//! * the spawn-builder state of `pspawn.rs` and of the new `spawnfd.rs` (the
//!   file actions and flags are written on the `posix_spawn` event; the
//!   builder calls are census rows);
//! * the `fd-inherit` policy lanes and the `fd-bound` premise's cap;
//! * for the fix-branch fixtures ([`lane`], [`pty`]) and the old-main bug
//!   fixtures added with them: the window racer ([`add_window_racer`], the
//!   fix branch's measurement harness), and every call the hand census leaves
//!   out or evaluates by hand, listed in the program's
//!   [`crate::program::EventProgram::disclosures`] and printed into every
//!   derived model's notes.

pub mod instance_lease;
pub mod lane;
pub mod lifeline;
pub mod ownerlock;
pub mod pspawn;
pub mod pty;
pub mod save_lock;
pub mod spawnfd;

use trust_platform::std_summaries::{CommandShape, CommandStd, StdioPlan};
use trust_platform::{Call, NodeKind, darwin};

use crate::env::{EnvSpec, Limits, Slot};
use crate::program::{Bind, BodyId, EventProgram, Mutation, Operand, ProgramBuilder};
use crate::property::Premise;

/// aterm `main` when these fixtures were written.
pub const ATERM_MAIN: &str = "93b6d38f3";

/// aterm `origin/main` when the fix branch was cut (its base): the OLD bodies
/// the old-main bug fixtures and [`pty::main_fd_70000`] encode.
pub const ATERM_BASE: &str = "ad35a5d85";

/// aterm `fix/fd-inherit-ceiling` (worktree `aterm-wt/fd-leak-fix`, not yet
/// pushed): the NEW bodies [`lane`] and [`pty`] encode.
pub const ATERM_FIX: &str = "ef421cedb";

/// The descriptor number the fix's reproduction parked an unflagged
/// descriptor at: above the old 65 536 cap, below `kern.maxfilesperproc`.
pub const ABOVE_OLD_CAP: i64 = 70_000;

/// `aterm@<commit>:<path>:<line>`.
#[must_use]
pub fn loc(commit: &str, path: &str, line: &str) -> String {
    format!("aterm@{commit}:{path}:{line}")
}

/// One acceptance fixture.
#[derive(Clone, Debug)]
pub struct Fixture {
    pub name: &'static str,
    pub program: EventProgram,
    pub env: EnvSpec,
    pub premises: Vec<Premise>,
    /// The verdict the plan requires.
    pub expect_refuted: bool,
    /// Its fd-hygiene steps: deleting any one must flip a fixed fixture to
    /// refuted (the mutant sweep).
    pub hygiene: Vec<Mutation>,
}

/// The environment of the spawnfd fixtures: the descriptor arguments on 3,
/// 4 or below the ceiling; one unflagged foreign descriptor at every
/// position of the partition (below the strip's start, inside it, at its
/// cap 65536 and above — only possible with a soft limit above 65536, and
/// this machine's is 1048576); the fd-bound premise's cap, 65536.
#[must_use]
pub fn spawnfd_env() -> EnvSpec {
    EnvSpec {
        limits: Limits::measured_darwin(),
        param_slots: vec![Slot::Exact(3), Slot::Exact(4), Slot::Mid],
        foreign: true,
        foreign_at: Vec::new(),
        fd_bound_cap: Some(65_536),
        names: Vec::new(),
    }
}

/// The environment of the `posix_spawn` fixture: no descriptor arguments.
#[must_use]
pub fn pspawn_env() -> EnvSpec {
    EnvSpec { param_slots: Vec::new(), ..spawnfd_env() }
}

/// The environment of the fix-branch fixtures: this machine's limits, the
/// descriptor arguments on `param_slots`, one unflagged foreign descriptor
/// at every partition position AND at [`ABOVE_OLD_CAP`], and NO premise —
/// the new bodies claim no fd-bound.
#[must_use]
pub fn fix_env(param_slots: Vec<Slot>) -> EnvSpec {
    EnvSpec {
        limits: Limits::measured_darwin(),
        param_slots,
        foreign: true,
        foreign_at: vec![ABOVE_OLD_CAP],
        fd_bound_cap: None,
        names: Vec::new(),
    }
}

/// The racing thread root: the e17e2d6d5 probe's racer (a thread looping
/// `UnixStream::pair()`, here once), which also starts another child with a
/// plain `Command::spawn()` (std's posix_spawn path, inherited stdio), then
/// drops the pair. Its spawn site is NOT under the policy: it is another
/// component's child, an event source for the root under test.
///
/// Source: aterm e17e2d6d5 commit message, "a scratch probe forking /bin/sh
/// beside four threads looping UnixStream::pair() found a stray descriptor in
/// the child in 708 of 2000 spawns". The probe was not committed; this body is
/// that description, plus the spawn the M1 task asks the racer to make.
pub fn add_racer(p: &mut ProgramBuilder) -> BodyId {
    let at = |what: &str| format!("aterm@e17e2d6d5:<probe racer thread, commit message>:{what}");
    let x = p.var("race_x", -1);
    let y = p.var("race_y", -1);
    let site = p.site("racer_spawn", &at("Command::new(\"/bin/sh\").spawn()"), None);
    let body = p.body("racer thread", Vec::new(), |b| {
        // let (x, y) = UnixStream::pair()?;
        b.std_row(
            &at("UnixStream::pair()"),
            "std::os::unix::net::UnixStream::pair",
            Vec::new(),
            vec![x, y],
            vec!["race_pair_a", "race_pair_b"],
        );
        // let _ = Command::new("/bin/sh").spawn();
        b.spawn(
            &at("Command::new(\"/bin/sh\").spawn()"),
            [StdioPlan::Inherit; 3],
            CommandShape::default().under(CommandStd::Upstream),
            Vec::new(),
            site,
            None,
        );
        // drop((x, y));
        b.event(&at("drop(x)"), "close", Call::Close { fd: Operand::Var(x) }, Bind::none());
        b.event(&at("drop(y)"), "close", Call::Close { fd: Operand::Var(y) }, Bind::none());
    });
    p.root("racer", body);
    body
}

/// The environment of a window-racer fixture: this machine's limits, the
/// descriptor arguments on `param_slots`, the foreign descriptor only at the
/// measured `foreign_at` positions (none, or [`ABOVE_OLD_CAP`]) — the racer
/// is the interleaving under test, and the product of every partition
/// position with its interleavings is what [`fix_env`]'s fixtures (with the
/// pair racer) cover — and no premise.
#[must_use]
pub fn window_env(param_slots: Vec<Slot>, foreign_at: Vec<i64>) -> EnvSpec {
    EnvSpec { foreign: false, foreign_at, ..fix_env(param_slots) }
}

/// What the window racer takes once it has raised the limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WindowRace {
    /// `race(.., high = false)` (the harness's `race-low` stage): one
    /// unflagged descriptor at or above 2000.
    Low,
    /// `race(.., high = true)` (stage `race`): also one at or above
    /// [`ABOVE_OLD_CAP`].
    High,
}

/// The WINDOW RACER: a thread that toggles the soft `RLIMIT_NOFILE` down and
/// back up and then takes an unflagged descriptor above the old ceiling — the
/// race of the ceiling read before the fork (old-main bug 2). Transcribed
/// from the fix branch's measurement harness, one iteration of its loop:
///
/// ```text
/// fn set_soft_limit(soft: u64) -> u64 {
///     let mut l = Rl { cur: 0, max: 0 };
///     unsafe { getrlimit(NOFILE, &mut l) };
///     l.cur = soft.min(l.max);
///     assert_eq!(unsafe { setrlimit(NOFILE, &l) }, 0);
///     l.cur
/// }
/// fn unflagged_at_or_above(floor: RawFd) -> OwnedFd {
///     let file = std::fs::File::open("/dev/null").unwrap();
///     let fd = unsafe { fcntl(file.as_raw_fd(), F_DUPFD, floor) };
///     assert!(fd >= floor);
///     unsafe { OwnedFd::from_raw_fd(fd) }
/// }                                         // `file` drops: close
/// fn race(stop: &AtomicBool, high_soft: u64, high: bool) {
///     while !stop.load(Ordering::Relaxed) {
///         set_soft_limit(1024);
///         set_soft_limit(high_soft);        // 70_064 (staged_race)
///         let low = unflagged_at_or_above(RACE_LOW);          // 2000
///         let above = high.then(|| unflagged_at_or_above(ABOVE_OLD_CAP));
///         /* spin 200 us */
///         drop(low);
///         drop(above);
///     }
/// }
/// ```
///
/// Source: `measure_main.rs`, the scratch harness of the fix branch (not
/// committed; quoted by ef421cedb's message: "5/2000 spawns from the window
/// alone; 1617/2000 with the >65536 stand-in, under a racing thread"). The
/// `getrlimit` of `set_soft_limit` (read for `l.max` only) is not an
/// interleaving point here, and the `setrlimit` operands are evaluated by
/// hand from the environment's hard limit (`RLIM_INFINITY`): `soft.min(l.max)`
/// is `soft`.
pub fn add_window_racer(p: &mut ProgramBuilder, race: WindowRace) -> BodyId {
    let at = |what: &str| format!("aterm@{ATERM_FIX}:<harness measure_main.rs, race()>:{what}");
    let rc = p.var("race_rl_rc", -1);
    let file_lo = p.var("race_file_lo", -1);
    let low = p.var("race_low", -1);
    let file_hi = p.var("race_file_hi", -1);
    let above = p.var("race_above", -1);
    p.disclose(
        "window racer (measure_main.rs race(), one iteration): set_soft_limit(s) is getrlimit \
         then setrlimit(min(s, hard), hard); the getrlimit, a read whose value the racer uses \
         only for l.max, is not encoded as an interleaving point, and min(s, hard) is evaluated \
         by hand with the environment's hard limit RLIM_INFINITY; std::fs::File::open(\"/dev/null\") \
         is STD-OPEN's one step, open(O_RDONLY|O_CLOEXEC); the 200 us spin has no platform event",
    );
    let body = p.body("window racer thread", Vec::new(), |b| {
        for soft in [1024u64, 70_064] {
            // getrlimit(NOFILE, &mut l): read for l.max only — not encoded.
            b.event(
                &at(&format!("set_soft_limit({soft}): setrlimit(NOFILE, &l)")),
                "setrlimit",
                Call::Setrlimit {
                    resource: darwin::RLIMIT_NOFILE,
                    soft,
                    hard: darwin::RLIM_INFINITY,
                },
                Bind::ret(rc),
            );
        }
        let take = |b: &mut crate::program::BodyBuilder,
                    file: crate::program::VarId,
                    out: crate::program::VarId,
                    floor: i64,
                    ofd: &str| {
            b.open(
                &at(&format!("unflagged_at_or_above({floor}): File::open(\"/dev/null\")")),
                "/dev/null",
                Call::Open { flags: darwin::O_RDONLY | darwin::O_CLOEXEC },
                Bind::ret(file),
                ofd,
            );
            b.event(
                &at(&format!("unflagged_at_or_above({floor}): fcntl(file, F_DUPFD, {floor})")),
                "fcntl",
                fcntl(Operand::Var(file), F_DUPFD, floor),
                Bind::ret(out),
            );
            b.event(
                &at(&format!("unflagged_at_or_above({floor}): drop(file)")),
                "close",
                Call::Close { fd: Operand::Var(file) },
                Bind::none(),
            );
        };
        take(b, file_lo, low, 2000, "race_devnull_low");
        if race == WindowRace::High {
            take(b, file_hi, above, ABOVE_OLD_CAP, "race_devnull_high");
        }
        b.event(&at("drop(low)"), "close", Call::Close { fd: Operand::Var(low) }, Bind::none());
        if race == WindowRace::High {
            b.event(
                &at("drop(above)"),
                "close",
                Call::Close { fd: Operand::Var(above) },
                Bind::none(),
            );
        }
    });
    p.root("window racer", body);
    body
}

/// The property an M2 fixture is checked under.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Property {
    /// P-LOCK-RELEASE (`AG !lock_leak`; non-vacuity `released_shared`).
    LockRelease,
    /// fd-identity (`AG !fd_identity_violation`; non-vacuity `number_reused`).
    FdIdentity,
}

/// One M2 acceptance fixture (plan §3 M2: bugs 1 and 2), or a current-main
/// finding.
#[derive(Clone, Debug)]
pub struct M2Fixture {
    pub name: &'static str,
    pub program: EventProgram,
    pub env: EnvSpec,
    pub property: Property,
    /// The verdict the plan requires (or, for a finding, what was found).
    pub expect_refuted: bool,
    /// This encodes CURRENT aterm main (a real bug when refuted).
    pub current_main: bool,
    /// Its hygiene steps: deleting any one must flip a fixed fixture to
    /// refuted (the mutant sweep).
    pub hygiene: Vec<Mutation>,
}

/// The environment of the M2 fixtures: this machine's limits, no descriptor
/// arguments, no foreign descriptor (the concurrency under test is the
/// program's and RL-HARNESS's threads), no premise, and the namespace
/// `names` before the program runs.
#[must_use]
pub fn m2_env(names: &[(&str, NodeKind)]) -> EnvSpec {
    EnvSpec {
        limits: Limits::measured_darwin(),
        param_slots: Vec::new(),
        foreign: false,
        foreign_at: Vec::new(),
        fd_bound_cap: None,
        names: names.iter().map(|(p, k)| ((*p).to_string(), *k)).collect(),
    }
}

/// The M2 fixtures: bug 1 (ownerlock), bug 2 (lifeline), and the
/// current-main findings.
#[must_use]
pub fn m2() -> Vec<M2Fixture> {
    vec![
        ownerlock::bare_close(),
        ownerlock::unlock_then_close(),
        ownerlock::probe_no_unlock(),
        ownerlock::probe_shipped(),
        lifeline::retired_number(),
        lifeline::identity(),
        instance_lease::sweep_main(),
        instance_lease::sweep_main_lane_spawn(),
        instance_lease::sweep_unlock_first(),
        save_lock::bare_drop(),
        save_lock::unlock_then_drop(),
    ]
}

/// Every acceptance fixture, in the plan's order, plus the original
/// 2c016005d body; then the old-main bug fixtures and the fix branch's new
/// bodies (ef421cedb).
#[must_use]
pub fn all() -> Vec<Fixture> {
    vec![
        spawnfd::no_strip(),
        spawnfd::strip_first_premise(),
        spawnfd::strip_first_no_premise(),
        spawnfd::strip_after_placing(),
        spawnfd::no_dupfd_move(),
        pspawn::cloexec_default(),
        spawnfd::original_dup_only(),
        // Old main (ad35a5d85 = be339c9b2's body): must be REFUTED.
        spawnfd::strip_first_fd_70000(),
        spawnfd::strip_first_fd_70000_kernel_bound(),
        spawnfd::strip_first_ceiling_window(),
        pty::main_fd_70000(),
        pty::main_ceiling_window(),
        // The fix branch (ef421cedb): must NOT be refuted.
        lane::launch(),
        lane::launch_window(),
        lane::sources_on_the_targets(),
        lane::sources_at_open_max(),
        pty::fix_shell(),
        pty::fix_shell_window(),
        pty::fix_shell_hardened(),
    ]
}

pub(crate) fn fcntl(fd: Operand, cmd: i32, arg: i64) -> Call<Operand> {
    Call::Fcntl { fd, cmd, arg }
}

pub(crate) const F_DUPFD: i32 = darwin::F_DUPFD;
