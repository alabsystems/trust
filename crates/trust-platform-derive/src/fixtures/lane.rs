//! THE NEW BRIDGE LAUNCH on aterm `fix/fd-inherit-ceiling` (ef421cedb):
//! `aterm_uds::spawnfd::spawn_with_two_fds` (`crates/aterm-uds/src/spawnfd.rs`)
//! is now a `posix_spawn` with `POSIX_SPAWN_CLOEXEC_DEFAULT` — no strip, no
//! ceiling, no `pre_exec` — and its caller is `aterm-gui`'s
//! `fabric_launch::launch_once` (`crates/aterm-gui/src/fabric_launch.rs`).
//!
//! ef421cedb, spawnfd.rs:333-351 and 373-390:
//!
//! ```text
//! pub fn spawn_with_two_fds(cmd: LaneCommand, first: OwnedFd, second: OwnedFd)
//!     -> io::Result<LaneChild> {
//!     let LaneCommand { program, args, env, stdin, stdout, stderr } = cmd;
//!     let image = Image::build(&program, &args, env)?;
//!     let stdio = [stage(stdin)?, stage(stdout)?, stage(stderr)?];
//!     let lanes = [off_the_targets(first)?, off_the_targets(second)?];
//!     let pid = platform::spawn(&image, &stdio, &lanes)?;
//!     Ok(LaneChild { pid, status: None })
//! }                                   // `lanes` drops: both closed here
//!
//! fn off_the_targets(fd: OwnedFd) -> io::Result<OwnedFd> {
//!     let raw = fd.as_raw_fd();
//!     if placeable(raw) { return Ok(fd); }      // FIRST_FREE (5) ..= 10 239
//!     let copy = unsafe { fcntl(raw, F_DUPFD_CLOEXEC, FIRST_FREE) };
//!     if copy < 0 { return Err(io::Error::last_os_error()); }
//!     let copy = unsafe { OwnedFd::from_raw_fd(copy) };
//!     if !placeable(copy.as_raw_fd()) { return Err(io::Error::from_raw_os_error(EMFILE)); }
//!     Ok(copy)
//! }                                   // `fd` drops: the original is closed
//! ```
//!
//! The Darwin `platform::spawn` (spawnfd.rs:569-633):
//!
//! ```text
//! let mut objects = Objects::new()?;            // attr_init, file_actions_init
//! let flags = POSIX_SPAWN_CLOEXEC_DEFAULT | POSIX_SPAWN_SETSIGDEF | POSIX_SPAWN_SETSIGMASK;
//! check(posix_spawnattr_setflags(&mut objects.attr, flags))?;
//! check(posix_spawnattr_setsigmask(&mut objects.attr, &empty))?;
//! check(posix_spawnattr_setsigdefault(&mut objects.attr, &pipe_only))?;
//! for (target, slot) in (0..).zip(stdio) {
//!     check(match slot {
//!         ChildStdio::Null => open_null(..),                    // addopen /dev/null
//!         ChildStdio::Inherit if fcntl(target, F_GETFD) >= 0 =>
//!             posix_spawn_file_actions_addinherit_np(&mut objects.actions, target),
//!         ChildStdio::Inherit => open_null(..),
//!         ChildStdio::Fd(fd) => posix_spawn_file_actions_adddup2(.., fd.as_raw_fd(), target),
//!     })?;
//! }
//! for (target, lane) in [BRIDGE_VERB_FD, BRIDGE_PUSH_FD].into_iter().zip(lanes) {
//!     check(posix_spawn_file_actions_adddup2(&mut objects.actions, lane.as_raw_fd(), target))?;
//! }
//! check(posix_spawn(&mut pid, image.path.as_ptr(), &objects.actions, &objects.attr,
//!                   argv.as_ptr(), envp.as_ptr()))?;
//! Ok(pid)                                       // `objects` drops: both destroyed
//! ```
//!
//! The builder calls touch no host state; their effect — the file actions
//! and flags — is written on the `posix_spawn` event, one event per
//! combination of the two `F_GETFD` answers (the action list is data the
//! code builds; an event's list is fixed).

use trust_platform::call::FileAction;
use trust_platform::{Call, Errno, Oracle, darwin};

use super::{
    ABOVE_OLD_CAP, ATERM_FIX, Fixture, WindowRace, add_racer, add_window_racer, fcntl, fix_env,
    loc, window_env,
};
use crate::env::Slot;
use crate::program::{
    Bind, BodyBuilder, BodyId, CmpOp, Cond, Expr, FdInherit, Lane, Mutation, Operand,
    ProgramBuilder, SiteId, VarId,
};

const PATH: &str = "crates/aterm-uds/src/spawnfd.rs";
const LAUNCH: &str = "crates/aterm-gui/src/fabric_launch.rs";

fn l(line: &str) -> String {
    loc(ATERM_FIX, PATH, line)
}

/// `placeable(fd)` (spawnfd.rs:116-125, the Darwin arm):
/// `(FIRST_FREE..ACTION_FD_LIMIT).contains(&fd)`, `FIRST_FREE = 5`,
/// `ACTION_FD_LIMIT = 10_240`.
fn placeable(fd: VarId) -> Cond {
    Cond::And(
        Box::new(Cond::Cmp(CmpOp::Ge, Operand::Var(fd), Operand::Lit(5))),
        Box::new(Cond::Cmp(CmpOp::Lt, Operand::Var(fd), Operand::Lit(10_240))),
    )
}

/// The descriptor-holding variables of one launch.
struct LaneVars {
    first: VarId,
    second: VarId,
    lane0: VarId,
    lane1: VarId,
    copy: VarId,
    getfd1: VarId,
    getfd2: VarId,
    pid: VarId,
}

/// `off_the_targets(fd)` for the lane in `lane`, inline (its `?` returns
/// from `spawn_with_two_fds`, dropping `others`, the descriptors the caller
/// still owns). `tag` names the then-arm of `!placeable(raw)` for the mutant
/// sweep.
fn off_the_targets(b: &mut BodyBuilder, v: &LaneVars, lane: VarId, others: &[VarId], tag: &str) {
    let copy = v.copy;
    let others = others.to_vec();
    b.neutral(&l("374"), "std::os::fd::AsRawFd::as_raw_fd");
    // if placeable(raw) { return Ok(fd); }  — the move is the else-arm.
    b.tag(tag).when(&l("375"), Cond::Not(Box::new(placeable(lane))), |t| {
        // let copy = unsafe { fcntl(raw, F_DUPFD_CLOEXEC, FIRST_FREE) };
        t.event(
            &l("380"),
            "fcntl",
            fcntl(Operand::Var(lane), darwin::F_DUPFD_CLOEXEC, 5),
            Bind::ret(copy),
        );
        // if copy < 0 { return Err(..) }  — `fd` and the caller's others drop.
        t.when(&l("381"), Cond::eq(Operand::Var(copy), Operand::Lit(-1)), |e| {
            e.event(&l("390"), "close", Call::Close { fd: Operand::Var(lane) }, Bind::none());
            for o in &others {
                e.event(&l("348"), "close", Call::Close { fd: Operand::Var(*o) }, Bind::none());
            }
            e.ret(&l("382"), Some(Operand::Lit(-1)));
        });
        t.neutral(&l("385"), "std::os::fd::FromRawFd::from_raw_fd");
        // if !placeable(copy) { return Err(EMFILE) }  — `copy` and `fd` drop.
        t.when(&l("386"), Cond::Not(Box::new(placeable(copy))), |e| {
            e.event(&l("387"), "close", Call::Close { fd: Operand::Var(copy) }, Bind::none());
            e.event(&l("390"), "close", Call::Close { fd: Operand::Var(lane) }, Bind::none());
            for o in &others {
                e.event(&l("348"), "close", Call::Close { fd: Operand::Var(*o) }, Bind::none());
            }
            e.ret(&l("387"), Some(Operand::Lit(-1)));
        });
        // Ok(copy) — and `fd`, the original, drops at the closing brace.
        t.event(&l("390"), "close", Call::Close { fd: Operand::Var(lane) }, Bind::none());
        t.assign(&l("389"), lane, Expr::Use(Operand::Var(copy)));
    });
}

/// The `posix_spawn` of `platform::spawn` for one pair of `F_GETFD`
/// answers: stdin `/dev/null` (`addopen(0, O_RDONLY)`), stdout and stderr
/// `addinherit_np` when open, else `addopen(/dev/null, O_WRONLY)`, the two
/// lanes `adddup2`ed onto 3 and 4.
fn spawn_event(b: &mut BodyBuilder, v: &LaneVars, site: SiteId, out_open: bool, err_open: bool) {
    let mut actions = vec![FileAction::Open { fd: Operand::Lit(0), flags: darwin::O_RDONLY }];
    let mut names = vec!["devnull_stdin"];
    for (target, open, name) in [(1, out_open, "devnull_stdout"), (2, err_open, "devnull_stderr")] {
        if open {
            actions.push(FileAction::Inherit { fd: Operand::Lit(target) });
        } else {
            actions.push(FileAction::Open { fd: Operand::Lit(target), flags: darwin::O_WRONLY });
            names.push(name);
        }
    }
    actions.push(FileAction::Dup2 { from: Operand::Var(v.lane0), to: Operand::Lit(3) });
    actions.push(FileAction::Dup2 { from: Operand::Var(v.lane1), to: Operand::Lit(4) });
    b.tag("posix_spawn").event_full(
        &l("623-630"),
        "posix_spawn",
        Call::Spawn {
            actions,
            flags: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT
                | darwin::POSIX_SPAWN_SETSIGDEF
                | darwin::POSIX_SPAWN_SETSIGMASK,
        },
        Bind::ret(v.pid),
        vec![Oracle::Nominal, Oracle::Fail(Errno::ENOENT)],
        Some(site),
        names,
    );
}

/// `spawn_with_two_fds(cmd, first, second)` on Darwin, with launch_once's
/// stdio (`Null`, `Inherit`, `Inherit`); returns the pid or -1.
fn spawn_with_two_fds(p: &mut ProgramBuilder, v: &LaneVars, site: SiteId) -> BodyId {
    p.body("spawn_with_two_fds (ef421cedb)", Vec::new(), |b| {
        // let image = Image::build(&program, &args, env)?;  — CStrings and a
        // PATH search by `metadata` (stat): no descriptor (disclosed).
        // let stdio = [stage(stdin)?, stage(stdout)?, stage(stderr)?];  —
        // Null / Inherit / Inherit: no `Fd` slot, so no event.
        // let lanes = [off_the_targets(first)?, off_the_targets(second)?];
        b.assign(&l("348"), v.lane0, Expr::Use(Operand::Var(v.first)));
        off_the_targets(b, v, v.lane0, &[v.second], "move_first");
        b.assign(&l("348"), v.lane1, Expr::Use(Operand::Var(v.second)));
        off_the_targets(b, v, v.lane1, &[v.lane0], "move_second");
        // let pid = platform::spawn(&image, &stdio, &lanes)?;
        b.neutral(&l("533"), "posix_spawnattr_init");
        b.neutral(&l("536"), "posix_spawn_file_actions_init");
        b.neutral(&l("583"), "posix_spawnattr_setflags");
        b.neutral(&l("584"), "posix_spawnattr_setsigmask");
        b.neutral(&l("585"), "posix_spawnattr_setsigdefault");
        // target 0, ChildStdio::Null: open_null
        b.neutral(&l("589-595"), "posix_spawn_file_actions_addopen");
        // targets 1 and 2, ChildStdio::Inherit: `fcntl(target, F_GETFD) >= 0`
        for (target, got) in [(1, v.getfd1), (2, v.getfd2)] {
            b.event(
                &l("601"),
                "fcntl",
                fcntl(Operand::Lit(target), darwin::F_GETFD, 0),
                Bind::ret(got),
            );
            b.if_(
                &l("601"),
                Cond::Cmp(CmpOp::Ge, Operand::Var(got), Operand::Lit(0)),
                |t| t.neutral(&l("602"), "posix_spawn_file_actions_addinherit_np"),
                |e| e.neutral(&l("604"), "posix_spawn_file_actions_addopen"),
            );
        }
        b.neutral(&l("616"), "posix_spawn_file_actions_adddup2");
        b.neutral(&l("616"), "posix_spawn_file_actions_adddup2");
        let open = |g: VarId| Cond::Cmp(CmpOp::Ge, Operand::Var(g), Operand::Lit(0));
        b.if_(
            &l("601"),
            open(v.getfd1),
            |t| {
                t.if_(
                    &l("601"),
                    open(v.getfd2),
                    |tt| spawn_event(tt, v, site, true, true),
                    |te| spawn_event(te, v, site, true, false),
                );
            },
            |e| {
                e.if_(
                    &l("601"),
                    open(v.getfd2),
                    |et| spawn_event(et, v, site, false, true),
                    |ee| spawn_event(ee, v, site, false, false),
                );
            },
        );
        // `objects` drops on both paths.
        b.neutral(&l("549"), "posix_spawn_file_actions_destroy");
        b.neutral(&l("550"), "posix_spawnattr_destroy");
        // `lanes` drops at the end of `spawn_with_two_fds`, on the `?` path
        // and the `Ok` path alike.
        b.event(&l("351"), "close", Call::Close { fd: Operand::Var(v.lane0) }, Bind::none());
        b.event(&l("351"), "close", Call::Close { fd: Operand::Var(v.lane1) }, Bind::none());
        b.ret(&l("349-350"), Some(Operand::Var(v.pid)));
    })
}

fn lane_vars(p: &mut ProgramBuilder, first: VarId, second: VarId) -> LaneVars {
    LaneVars {
        first,
        second,
        lane0: p.var("lane0", -1),
        lane1: p.var("lane1", -1),
        copy: p.var("copy", -1),
        getfd1: p.var("getfd_stdout", -1),
        getfd2: p.var("getfd_stderr", -1),
        pid: p.var("pid", -1),
    }
}

fn bridge_site(p: &mut ProgramBuilder, first_class: &str, second_class: &str) -> SiteId {
    p.site(
        "bridge",
        &l("623-630"),
        Some(FdInherit {
            lanes: vec![
                Lane { fd: 3, ofd_class: first_class.to_string() },
                Lane { fd: 4, ofd_class: second_class.to_string() },
            ],
        }),
    )
}

fn disclose_common(p: &mut ProgramBuilder) {
    p.disclose(
        "spawn_with_two_fds (ef421cedb): Image::build (CStrings; resolve() stats PATH entries \
         with std::fs::metadata) and stage(Null|Inherit) have no descriptor effect and are not \
         encoded; their errors return before any descriptor is touched but the lanes' drops",
    );
    p.disclose(
        "spawn_with_two_fds (ef421cedb): the posix_spawn_file_actions_*/posix_spawnattr_* calls \
         are census rows whose effect is written on the posix_spawn event; their own `check(..)?` \
         failures (EINVAL/ENOMEM, and EBADF for a number >= OPEN_MAX that off_the_targets \
         excludes) are not explored; the spawn itself explores ENOENT",
    );
}

/// NEW BODY N1: the whole bridge launch — `launch_once` (fabric_launch.rs
/// 474-503) calling `spawn_with_two_fds`:
///
/// ```text
/// let (near_verb, far_verb) = UnixStream::pair()?;
/// let (near_push, far_push) = UnixStream::pair()?;
/// let mut cmd = LaneCommand::new(&argv[0]);
/// cmd.args(&argv[1..])
///     .env_exactly(filter_child_env(std::env::vars_os()))
///     .stdin(ChildStdio::Null)
///     .stdout(ChildStdio::Inherit)
///     .stderr(ChildStdio::Inherit);
/// let child = aterm_uds::spawnfd::spawn_with_two_fds(
///     cmd, OwnedFd::from(far_verb), OwnedFd::from(far_push))?;
/// ```
///
/// with the far ends wherever allocation puts them, the e17e2d6d5 pair
/// racer (which also spawns), and one unflagged foreign descriptor at every
/// partition position and at 70 000. No premise. Must NOT be refuted.
#[must_use]
pub fn launch() -> Fixture {
    launch_with("lane_launch", None)
}

/// NEW BODY N1, under the WINDOW racer instead (it toggles the soft limit
/// to 1024 and back to 70 064, then takes 2000 and 70 000), with the
/// foreign descriptor at 70 000. No premise. Must NOT be refuted.
#[must_use]
pub fn launch_window() -> Fixture {
    launch_with("lane_launch_window", Some(WindowRace::High))
}

fn launch_with(name: &'static str, window: Option<WindowRace>) -> Fixture {
    let mut p = ProgramBuilder::new(name);
    p.provenance("aterm", ATERM_FIX, PATH, "spawn_with_two_fds: posix_spawn, CLOEXEC_DEFAULT");
    p.provenance("aterm", ATERM_FIX, LAUNCH, "launch_once: two UnixStream::pair(), the far ends");
    let near_verb = p.var("near_verb", -1);
    let far_verb = p.var("far_verb", -1);
    let near_push = p.var("near_push", -1);
    let far_push = p.var("far_push", -1);
    let first = p.var("first", -1);
    let second = p.var("second", -1);
    let child = p.var("child", -1);
    let v = lane_vars(&mut p, first, second);
    let site = bridge_site(&mut p, "far_verb", "far_push");
    let body = spawn_with_two_fds(&mut p, &v, site);
    let ll = |line: &str| loc(ATERM_FIX, LAUNCH, line);
    let main = p.body("launch_once (ef421cedb)", Vec::new(), |b| {
        b.std_row(
            &ll("478"),
            "std::os::unix::net::UnixStream::pair",
            Vec::new(),
            vec![near_verb, far_verb],
            vec!["near_verb", "far_verb"],
        );
        b.std_row(
            &ll("479"),
            "std::os::unix::net::UnixStream::pair",
            Vec::new(),
            vec![near_push, far_push],
            vec!["near_push", "far_push"],
        );
        // LaneCommand::new(..).args(..).env_exactly(..).stdin(..)..: data only.
        // OwnedFd::from(far_verb), OwnedFd::from(far_push): moves.
        b.assign(&ll("501"), first, Expr::Use(Operand::Var(far_verb)));
        b.assign(&ll("502"), second, Expr::Use(Operand::Var(far_push)));
        b.call(&ll("499-503"), body, Vec::new(), Some(child));
        // `?`: on Err the near ends drop; on Ok they are attached to the
        // server (crate::control::attach_fabric_bridge) — after the spawn.
        b.when(&ll("503"), Cond::eq(Operand::Var(child), Operand::Lit(-1)), |e| {
            e.event(&ll("503"), "close", Call::Close { fd: Operand::Var(near_verb) }, Bind::none());
            e.event(&ll("503"), "close", Call::Close { fd: Operand::Var(near_push) }, Bind::none());
        });
    });
    p.root("main", main);
    match window {
        Some(race) => {
            add_window_racer(&mut p, race);
        }
        None => {
            add_racer(&mut p);
        }
    }
    disclose_common(&mut p);
    p.disclose(
        "launch_once (ef421cedb): the LaneCommand builder and filter_child_env are data only; \
         after the spawn the near ends move into the control server \
         (attach_fabric_bridge), past the fd-inherit horizon, and are not encoded",
    );
    let clear = Mutation::ClearSpawnFlag {
        tag: "posix_spawn".to_string(),
        flag: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT,
    };
    let (env, hygiene) = match window {
        None => (
            fix_env(Vec::new()),
            vec![
                clear,
                // launch_once's far_push lands on 4 when the pair racer held 3
                // and 4 across the first pair() and closed them before the
                // second; far_verb can never be 3 (a pair's far end is above
                // its near end) and on 4 it is read before 4 is replaced, so
                // the move of `first` is not load-bearing in THIS caller — the
                // API fixture [`sources_on_the_targets`] sweeps it.
                Mutation::DeleteThen("move_second".to_string()),
            ],
        ),
        // The window racer holds one small descriptor at a time, so the far
        // ends never sit on 3 and 4 together: only CLOEXEC_DEFAULT is swept.
        Some(_) => (window_env(Vec::new(), vec![ABOVE_OLD_CAP]), vec![clear]),
    };
    Fixture { name, program: p.build(), env, premises: Vec::new(), expect_refuted: false, hygiene }
}

/// `spawn_with_two_fds` called with lanes RL-INIT places (the API, not one
/// caller's allocation), with launch_once's stdio.
fn api(name: &'static str, slots: Vec<Slot>, racer: bool, hygiene: Vec<Mutation>) -> Fixture {
    let mut p = ProgramBuilder::new(name);
    p.provenance("aterm", ATERM_FIX, PATH, "spawn_with_two_fds: posix_spawn, CLOEXEC_DEFAULT");
    p.provenance(
        "aterm",
        ATERM_FIX,
        LAUNCH,
        "launch_once's stdio (Null, Inherit, Inherit); the lanes are placed by RL-INIT",
    );
    let first = p.fd_param("first", "first", Some("first_peer"));
    let second = p.fd_param("second", "second", Some("second_peer"));
    let child = p.var("child", -1);
    let v = lane_vars(&mut p, first, second);
    let site = bridge_site(&mut p, "first", "second");
    let body = spawn_with_two_fds(&mut p, &v, site);
    let main = p.body("caller", Vec::new(), |b| {
        b.call(&l("333-351"), body, Vec::new(), Some(child));
    });
    p.root("main", main);
    if racer {
        add_racer(&mut p);
    }
    disclose_common(&mut p);
    Fixture {
        name,
        program: p.build(),
        env: fix_env(slots),
        premises: Vec::new(),
        expect_refuted: false,
        hygiene,
    }
}

/// NEW BODY N2: the API with a lane ON a target — `first`/`second` on 3, on
/// 4, swapped, or above them — under the e17e2d6d5 racer, a foreign
/// descriptor at every partition position and at 70 000. No premise. Must
/// NOT be refuted. Deleting either move (`dup2(3, 3)` keeps `FD_CLOEXEC`;
/// a source on the other target is clobbered first) or `CLOEXEC_DEFAULT`
/// must flip it.
#[must_use]
pub fn sources_on_the_targets() -> Fixture {
    api(
        "lane_sources_on_the_targets",
        vec![Slot::Exact(3), Slot::Exact(4), Slot::Mid],
        true,
        vec![
            Mutation::ClearSpawnFlag {
                tag: "posix_spawn".to_string(),
                flag: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT,
            },
            Mutation::DeleteThen("move_first".to_string()),
            Mutation::DeleteThen("move_second".to_string()),
        ],
    )
}

/// NEW BODY N3: the API with a lane at or above `OPEN_MAX` (10 240), which
/// libc refuses in a file action — at 10 239 (placeable as it is), 10 240
/// and 20 000 (moved first) — and a foreign descriptor at every partition
/// position and at 70 000. No racer, no premise. Must NOT be refuted. (A
/// deleted move here is no fd-inherit refutation: the `adddup2` fails
/// `EBADF` at add time and the launch returns `Err` — the model refuses such
/// an action list by name — so only `CLOEXEC_DEFAULT` is swept.)
#[must_use]
pub fn sources_at_open_max() -> Fixture {
    api(
        "lane_sources_at_open_max",
        vec![Slot::Exact(10_239), Slot::Exact(10_240), Slot::Exact(20_000)],
        false,
        vec![Mutation::ClearSpawnFlag {
            tag: "posix_spawn".to_string(),
            flag: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT,
        }],
    )
}
