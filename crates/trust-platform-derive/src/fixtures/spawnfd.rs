//! `aterm_uds::spawnfd::spawn_with_two_fds` and its variants
//! (`crates/aterm-uds/src/spawnfd.rs`).
//!
//! The caller is `aterm-gui`'s `fabric_launch::launch_once`
//! (`crates/aterm-gui/src/fabric_launch.rs:473-501` on aterm main):
//!
//! ```text
//! let (near_verb, far_verb) = UnixStream::pair()?;
//! let (near_push, far_push) = UnixStream::pair()?;
//! let mut cmd = Command::new(&argv[0]);
//! cmd.args(&argv[1..]).env_clear().envs(..)
//!     .stdin(Stdio::null()).stdout(Stdio::inherit()).stderr(Stdio::inherit());
//! let child = aterm_uds::spawnfd::spawn_with_two_fds(
//!     cmd, OwnedFd::from(far_verb), OwnedFd::from(far_push))?;
//! ```
//!
//! so `first`/`second` are close-on-exec socketpair ends whose near ends the
//! root also holds (close-on-exec), and the child's stdin is `/dev/null`.
//!
//! The historical refutations select `CommandStd::Upstream` and retain the
//! explicit `inherit_all_fds` premise. That bit alone does not select upstream's
//! placement and relocation contract. Trust Command lowering remains a named
//! refusal; direct platform controls check its SP1 behavior separately.

use trust_platform::std_summaries::{CommandShape, CommandStd, StdioPlan};
use trust_platform::{Call, darwin};

use super::{
    ABOVE_OLD_CAP, ATERM_BASE, F_DUPFD, Fixture, WindowRace, add_racer, add_window_racer, fcntl,
    loc, spawnfd_env,
};
use crate::env::EnvSpec;
use crate::program::{
    Bind, BodyId, Cond, Expr, FdInherit, Lane, Mutation, Operand, ProgramBuilder, VarId,
};
use crate::property::Premise;

const PATH: &str = "crates/aterm-uds/src/spawnfd.rs";

#[derive(Clone, Copy, PartialEq, Eq)]
enum Variant {
    /// 5ff0c8733: no strip at all.
    NoStrip,
    /// be339c9b2 (= aterm main's body): strip first, then place.
    StripFirst,
    /// The plan's mutant of be339c9b2: the strip after the placement.
    StripAfterPlacing,
    /// The plan's mutant of be339c9b2: no `F_DUPFD` move off the targets.
    NoDupfdMove,
}

struct Vars {
    first: VarId,
    second: VarId,
    a: VarId,
    b: VarId,
    moved_a: VarId,
    moved_b: VarId,
    r: VarId,
    ceiling: VarId,
}

fn vars(p: &mut ProgramBuilder) -> Vars {
    Vars {
        // fabric_launch's far_verb / far_push, moved into the closure.
        first: p.fd_param("first", "first", Some("first_peer")),
        second: p.fd_param("second", "second", Some("second_peer")),
        a: p.var("a", -1),
        b: p.var("b", -1),
        moved_a: p.var("moved_a", -1),
        moved_b: p.var("moved_b", -1),
        r: p.var("dup2_ret", -1),
        ceiling: p.var("ceiling", -1),
    }
}

/// `inherited_fd_ceiling` (be339c9b2, spawnfd.rs:217-245; the 64-bit Apple
/// arm):
///
/// ```text
/// const CAP: u64 = 1 << 16;
/// let mut limit = Rlimit { cur: 0, max: 0 };
/// let soft = if unsafe { getrlimit(RLIMIT_NOFILE, &mut limit) } == 0 {
///     limit.cur.min(CAP)
/// } else {
///     CAP
/// };
/// RawFd::try_from(soft).unwrap_or(RawFd::MAX)
/// ```
fn inherited_fd_ceiling(p: &mut ProgramBuilder, commit: &str) -> BodyId {
    let rc = p.var("getrlimit_rc", -1);
    let soft = p.var("limit_cur", -1);
    let out = p.var("ceiling_soft", -1);
    p.body("inherited_fd_ceiling", Vec::new(), |b| {
        b.event(
            &loc(commit, PATH, "228"),
            "getrlimit",
            Call::Getrlimit { resource: darwin::RLIMIT_NOFILE },
            Bind { ret: Some(rc), rlim_soft: Some(soft), ..Bind::default() },
        );
        b.if_(
            &loc(commit, PATH, "228"),
            Cond::eq(Operand::Var(rc), Operand::Lit(0)),
            |t| {
                t.assign(
                    &loc(commit, PATH, "229"),
                    out,
                    Expr::Min(Operand::Var(soft), Operand::Lit(1 << 16)),
                );
            },
            |e| e.assign(&loc(commit, PATH, "231"), out, Expr::Use(Operand::Lit(1 << 16))),
        );
        b.ret(&loc(commit, PATH, "233"), Some(Operand::Var(out)));
    })
}

/// `mark_inherited_close_on_exec` (be339c9b2, spawnfd.rs:264-274):
///
/// ```text
/// pub fn mark_inherited_close_on_exec(ceiling: RawFd) {
///     let mut fd: RawFd = 3;
///     while fd < ceiling {
///         unsafe { fcntl(fd, F_SETFD, FD_CLOEXEC); }
///         fd += 1;
///     }
/// }
/// ```
fn mark_inherited_close_on_exec(p: &mut ProgramBuilder, commit: &str) -> (BodyId, VarId) {
    let ceiling = p.var("mark_ceiling", -1);
    let fd = p.var("strip_fd", -1);
    let one = p.body("strip one fd", Vec::new(), |b| {
        b.event(
            &loc(commit, PATH, "270"),
            "fcntl",
            fcntl(Operand::Var(fd), darwin::F_SETFD, darwin::FD_CLOEXEC),
            Bind::none(),
        );
    });
    let body = p.body("mark_inherited_close_on_exec", vec![ceiling], |b| {
        b.for_range(&loc(commit, PATH, "265-273"), fd, Operand::Lit(3), Operand::Var(ceiling), one);
    });
    (body, ceiling)
}

/// The `pre_exec` closure of `spawn_with_two_fds`. Line numbers are
/// be339c9b2's (5ff0c8733's are 24 lower: it has no ceiling read and no
/// strip). be339c9b2, spawnfd.rs:131-199:
///
/// ```text
/// pre_exec(&mut cmd, move || {
///     mark_inherited_close_on_exec(ceiling);                 // be339c9b2 only
///     let mut a = first.as_raw_fd();
///     let mut b = second.as_raw_fd();
///     let mut moved_a: RawFd = -1;
///     let mut moved_b: RawFd = -1;
///     if a == BRIDGE_VERB_FD || a == BRIDGE_PUSH_FD {
///         a = fcntl(a, F_DUPFD, BRIDGE_PUSH_FD + 1);
///         if a == -1 { return Err(io::Error::last_os_error()); }
///         moved_a = a;
///     }
///     if b == BRIDGE_VERB_FD || b == BRIDGE_PUSH_FD {
///         b = fcntl(b, F_DUPFD, BRIDGE_PUSH_FD + 1);
///         if b == -1 { return Err(io::Error::last_os_error()); }
///         moved_b = b;
///     }
///     if dup2(a, BRIDGE_VERB_FD) == -1 { return Err(io::Error::last_os_error()); }
///     if dup2(b, BRIDGE_PUSH_FD) == -1 { return Err(io::Error::last_os_error()); }
///     if moved_a != -1 { close(moved_a); }
///     if moved_b != -1 { close(moved_b); }
///     Ok(())
/// });
/// ```
fn closure(
    p: &mut ProgramBuilder,
    v: &Vars,
    variant: Variant,
    commit: &str,
    mark: Option<(BodyId, VarId)>,
) -> BodyId {
    let off = if variant == Variant::NoStrip { 24 } else { 0 };
    let l = |line: u32| loc(commit, PATH, &(line - off).to_string());
    let strip = |b: &mut crate::program::BodyBuilder, line: &str| {
        if let Some((mark, mark_ceiling)) = mark {
            b.tag("strip").call(
                &loc(commit, PATH, line),
                mark,
                vec![(mark_ceiling, Operand::Var(v.ceiling))],
                None,
            );
        }
    };
    let (a, bv, moved_a, moved_b, r) = (v.a, v.b, v.moved_a, v.moved_b, v.r);
    let (first, second) = (v.first, v.second);
    p.body("spawn_with_two_fds pre_exec closure", Vec::new(), |b| {
        if variant == Variant::StripFirst || variant == Variant::NoDupfdMove {
            strip(b, "137");
        }
        b.neutral(&l(138), "std::os::fd::AsRawFd::as_raw_fd");
        b.assign(&l(138), a, Expr::Use(Operand::Var(first)));
        b.neutral(&l(139), "std::os::fd::AsRawFd::as_raw_fd");
        b.assign(&l(139), bv, Expr::Use(Operand::Var(second)));
        b.assign(&l(163), moved_a, Expr::Use(Operand::Lit(-1)));
        b.assign(&l(164), moved_b, Expr::Use(Operand::Lit(-1)));
        if variant != Variant::NoDupfdMove {
            for (src, moved, line) in [(a, moved_a, 165u32), (bv, moved_b, 172u32)] {
                let tag = if src == a { "move_a" } else { "move_b" };
                b.tag(tag).when(
                    &l(line),
                    Cond::or(
                        Cond::eq(Operand::Var(src), Operand::Lit(3)),
                        Cond::eq(Operand::Var(src), Operand::Lit(4)),
                    ),
                    |t| {
                        t.event(
                            &l(line + 1),
                            "fcntl",
                            fcntl(Operand::Var(src), F_DUPFD, 5),
                            Bind::ret(src),
                        );
                        t.when(&l(line + 2), Cond::eq(Operand::Var(src), Operand::Lit(-1)), |e| {
                            e.ret(&l(line + 3), Some(Operand::Lit(-1)));
                        });
                        t.assign(&l(line + 5), moved, Expr::Use(Operand::Var(src)));
                    },
                );
            }
        }
        for (src, target, line) in [(a, 3, 179u32), (bv, 4, 182u32)] {
            let tag = if target == 3 { "place_a" } else { "place_b" };
            b.tag(tag).event(
                &l(line),
                "dup2",
                Call::Dup2 { from: Operand::Var(src), to: Operand::Lit(target) },
                Bind::ret(r),
            );
            b.when(&l(line), Cond::eq(Operand::Var(r), Operand::Lit(-1)), |e| {
                e.ret(&l(line + 1), Some(Operand::Lit(-1)));
            });
        }
        for (moved, line, tag) in
            [(moved_a, 192u32, "close_tmp_a"), (moved_b, 195u32, "close_tmp_b")]
        {
            b.when(&l(line), Cond::ne(Operand::Var(moved), Operand::Lit(-1)), |t| {
                t.tag(tag).event(
                    &l(line + 1),
                    "close",
                    Call::Close { fd: Operand::Var(moved) },
                    Bind::none(),
                );
            });
        }
        if variant == Variant::StripAfterPlacing {
            strip(b, "197 (moved: the plan's strip-after-placing variant)");
        }
        b.ret(&l(198), Some(Operand::Lit(0)));
    })
}

/// The function body: `spawn_with_two_fds(cmd, first, second)` with
/// fabric_launch's stdio, followed by the drop of `cmd` (which closes the
/// closure's `first`/`second` in the parent).
fn build(name: &str, commit: &str, variant: Variant) -> crate::program::EventProgram {
    build_with(name, commit, variant, None)
}

/// [`build`] with the window racer INSTEAD of the e17e2d6d5 pair racer when
/// `window` names one (the two racers' product is too large to explore;
/// each is checked on its own).
fn build_with(
    name: &str,
    commit: &str,
    variant: Variant,
    window: Option<WindowRace>,
) -> crate::program::EventProgram {
    let mut p = ProgramBuilder::new(name);
    p.disclose("Historical upstream-inheritance fixture: the Command selects CommandStd::Upstream and retains explicit inherit_all_fds; direct platform controls check Trust SP1 separately.");
    p.provenance("aterm", commit, PATH, "spawn_with_two_fds and its pre_exec closure");
    p.provenance(
        "aterm",
        super::ATERM_MAIN,
        "crates/aterm-gui/src/fabric_launch.rs",
        "launch_once: UnixStream::pair() far ends, Stdio::null() stdin",
    );
    let v = vars(&mut p);
    let strip = variant != Variant::NoStrip;
    let off = if strip { 0 } else { 24 };
    let l = |line: u32| loc(commit, PATH, &(line - off).to_string());
    let ceiling_body = strip.then(|| inherited_fd_ceiling(&mut p, commit));
    let mark = strip.then(|| mark_inherited_close_on_exec(&mut p, commit));
    let pre_exec = closure(&mut p, &v, variant, commit, mark);
    let site = p.site(
        "bridge",
        &l(201),
        Some(FdInherit {
            lanes: vec![
                Lane { fd: 3, ofd_class: "first".to_string() },
                Lane { fd: 4, ofd_class: "second".to_string() },
            ],
        }),
    );
    let child = p.var("child", -1);
    let (first, second, ceiling) = (v.first, v.second, v.ceiling);
    let main = p.body("spawn_with_two_fds", Vec::new(), |b| {
        if let Some(cb) = ceiling_body {
            // let ceiling = inherited_fd_ceiling();
            b.call(&l(120), cb, Vec::new(), Some(ceiling));
        }
        b.neutral(&l(131), "std::os::unix::process::CommandExt::pre_exec");
        // cmd.spawn()
        // These historical fixtures test the caller's strip against the
        // upstream inheritance premise. Select the historical upstream std
        // explicitly; the direct model's SP1 behavior has separate controls.
        b.spawn(
            &l(201),
            [StdioPlan::Null, StdioPlan::Inherit, StdioPlan::Inherit],
            CommandShape {
                inherit_all_fds: true,
                ..CommandShape::with_pre_exec().under(CommandStd::Upstream)
            },
            vec![pre_exec],
            site,
            Some(child),
        );
        // `cmd` drops at the end of the function: the closure's OwnedFds close.
        b.event(&l(202), "close", Call::Close { fd: Operand::Var(first) }, Bind::none());
        b.event(&l(202), "close", Call::Close { fd: Operand::Var(second) }, Bind::none());
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
    p.build()
}

fn hygiene() -> Vec<Mutation> {
    vec![
        Mutation::DeleteStmt("strip".to_string()),
        Mutation::DeleteThen("move_a".to_string()),
        Mutation::DeleteThen("move_b".to_string()),
        Mutation::DeleteStmt("close_tmp_a".to_string()),
        Mutation::DeleteStmt("close_tmp_b".to_string()),
    ]
}

/// Fixture 1: aterm 5ff0c8733 `spawn_with_two_fds` (spawnfd.rs:100-178): no strip.
/// Must be REFUTED for fd-inherit (the racer's half-flagged pair, or any
/// unflagged foreign descriptor, survives the child's exec).
#[must_use]
pub fn no_strip() -> Fixture {
    Fixture {
        name: "no_strip",
        program: build("no_strip", "5ff0c8733", Variant::NoStrip),
        env: spawnfd_env(),
        premises: Vec::new(),
        expect_refuted: true,
        hygiene: Vec::new(),
    }
}

/// Fixture 2: aterm be339c9b2 (= aterm main's body, unchanged but for a comment):
/// strip first, then place; under the fd-bound premise. Must NOT be refuted.
#[must_use]
pub fn strip_first_premise() -> Fixture {
    Fixture {
        name: "strip_first_premise",
        program: build("strip_first", "be339c9b2", Variant::StripFirst),
        env: spawnfd_env(),
        premises: vec![Premise::FdBound],
        expect_refuted: false,
        hygiene: hygiene(),
    }
}

/// Fixture 3: The same body without the premise: REFUTED by the descriptor at or
/// above the ceiling the strip never reaches.
#[must_use]
pub fn strip_first_no_premise() -> Fixture {
    Fixture {
        name: "strip_first_no_premise",
        program: build("strip_first", "be339c9b2", Variant::StripFirst),
        env: spawnfd_env(),
        premises: Vec::new(),
        expect_refuted: true,
        hygiene: Vec::new(),
    }
}

/// Fixture 4: be339c9b2 with the strip moved after the placement (the order its
/// commit message rules out: "a strip run after the placement would re-mark
/// 3 and 4 and exec the bridge with both closed"). REFUTED: a lane is closed
/// at exec.
#[must_use]
pub fn strip_after_placing() -> Fixture {
    Fixture {
        name: "strip_after_placing",
        program: build("strip_after_placing", "be339c9b2", Variant::StripAfterPlacing),
        env: spawnfd_env(),
        premises: vec![Premise::FdBound],
        expect_refuted: true,
        hygiene: Vec::new(),
    }
}

/// Fixture 5: be339c9b2 without the `F_DUPFD` moves off the targets: `dup2(3, 3)` is a
/// no-op that keeps `FD_CLOEXEC` (the strip set it; `UnixStream::pair()` did
/// too). REFUTED: a lane is closed at exec. (2c016005d, the original body,
/// had only a `dup` for `b == 3`; see [`original_dup_only`].)
#[must_use]
pub fn no_dupfd_move() -> Fixture {
    Fixture {
        name: "no_dupfd_move",
        program: build("no_dupfd_move", "be339c9b2", Variant::NoDupfdMove),
        env: spawnfd_env(),
        premises: vec![Premise::FdBound],
        expect_refuted: true,
        hygiene: Vec::new(),
    }
}

/// Extra: the ORIGINAL body, aterm 2c016005d spawnfd.rs:67-104:
///
/// ```text
/// pre_exec(&mut cmd, move || {
///     let a = first.as_raw_fd();
///     let mut b = second.as_raw_fd();
///     if b == BRIDGE_VERB_FD {
///         b = dup(b);
///         if b == -1 { return Err(io::Error::last_os_error()); }
///     }
///     if dup2(a, BRIDGE_VERB_FD) == -1 { return Err(..); }
///     if dup2(b, BRIDGE_PUSH_FD) == -1 { return Err(..); }
///     Ok(())
/// });
/// cmd.spawn()
/// ```
#[must_use]
pub fn original_dup_only() -> Fixture {
    const C: &str = "2c016005d";
    let l = |line: u32| loc(C, PATH, &line.to_string());
    let mut p = ProgramBuilder::new("original_dup_only");
    p.disclose("Historical upstream-inheritance fixture: the Command selects CommandStd::Upstream and retains explicit inherit_all_fds; direct platform controls check Trust SP1 separately.");
    p.provenance("aterm", C, PATH, "the original spawn_with_two_fds");
    let v = vars(&mut p);
    let (a, bv, r, first, second) = (v.a, v.b, v.r, v.first, v.second);
    let pre_exec = p.body("spawn_with_two_fds pre_exec closure (2c016005d)", Vec::new(), |b| {
        b.neutral(&l(80), "std::os::fd::AsRawFd::as_raw_fd");
        b.assign(&l(80), a, Expr::Use(Operand::Var(first)));
        b.neutral(&l(81), "std::os::fd::AsRawFd::as_raw_fd");
        b.assign(&l(81), bv, Expr::Use(Operand::Var(second)));
        b.when(&l(88), Cond::eq(Operand::Var(bv), Operand::Lit(3)), |t| {
            t.event(&l(89), "dup", Call::Dup { fd: Operand::Var(bv) }, Bind::ret(bv));
            t.when(&l(90), Cond::eq(Operand::Var(bv), Operand::Lit(-1)), |e| {
                e.ret(&l(91), Some(Operand::Lit(-1)));
            });
        });
        for (src, target, line) in [(a, 3, 94u32), (bv, 4, 97u32)] {
            b.event(
                &l(line),
                "dup2",
                Call::Dup2 { from: Operand::Var(src), to: Operand::Lit(target) },
                Bind::ret(r),
            );
            b.when(&l(line), Cond::eq(Operand::Var(r), Operand::Lit(-1)), |e| {
                e.ret(&l(line + 1), Some(Operand::Lit(-1)));
            });
        }
        b.ret(&l(100), Some(Operand::Lit(0)));
    });
    let site = p.site(
        "bridge",
        &l(103),
        Some(FdInherit {
            lanes: vec![
                Lane { fd: 3, ofd_class: "first".to_string() },
                Lane { fd: 4, ofd_class: "second".to_string() },
            ],
        }),
    );
    let child = p.var("child", -1);
    let main = p.body("spawn_with_two_fds (2c016005d)", Vec::new(), |b| {
        b.neutral(&l(79), "std::os::unix::process::CommandExt::pre_exec");
        b.spawn(
            &l(103),
            [StdioPlan::Null, StdioPlan::Inherit, StdioPlan::Inherit],
            CommandShape {
                inherit_all_fds: true,
                ..CommandShape::with_pre_exec().under(CommandStd::Upstream)
            },
            vec![pre_exec],
            site,
            Some(child),
        );
        b.event(&l(104), "close", Call::Close { fd: Operand::Var(first) }, Bind::none());
        b.event(&l(104), "close", Call::Close { fd: Operand::Var(second) }, Bind::none());
    });
    p.root("main", main);
    add_racer(&mut p);
    Fixture {
        name: "original_dup_only",
        program: p.build(),
        env: spawnfd_env(),
        premises: vec![Premise::FdBound],
        expect_refuted: true,
        hygiene: Vec::new(),
    }
}

// ---------------------------------------------------------------------------
// OLD MAIN's bugs, each a fixture that must be REFUTED. aterm `origin/main`
// at the fix branch's base (ad35a5d85) carries be339c9b2's
// `spawn_with_two_fds` unchanged but for doc comments (`git diff be339c9b2
// ad35a5d85 -- crates/aterm-uds/src/spawnfd.rs`: one comment paragraph), so
// the statements and their line numbers are be339c9b2's, as above.
// ---------------------------------------------------------------------------

/// The environment of old-main bug 1: the foreign descriptor ONLY at
/// [`ABOVE_OLD_CAP`] — no partition positions — so a refutation can only be
/// that descriptor.
fn fd_70000_env(fd_bound_cap: Option<i64>) -> EnvSpec {
    EnvSpec { foreign: false, foreign_at: vec![ABOVE_OLD_CAP], fd_bound_cap, ..spawnfd_env() }
}

/// OLD-MAIN BUG 1: `inherited_fd_ceiling` caps the strip at 65 536
/// (`limit.cur.min(CAP)`, `CAP = 1 << 16`), but Darwin allocates up to
/// `kern.maxfilesperproc` (92 160) whenever the soft limit is higher — this
/// shell's is 1 048 576. An unflagged descriptor at 70 000 (the fix's
/// reproduction: 20/20 bridge launches inherited it) is never marked. No
/// premise. Must be REFUTED, by the descriptor at 70 000.
#[must_use]
pub fn strip_first_fd_70000() -> Fixture {
    let mut program = build("strip_first_fd_70000", "be339c9b2", Variant::StripFirst);
    program.add_provenance(
        "aterm",
        ATERM_BASE,
        PATH,
        "unchanged since be339c9b2 (doc comments only)",
    );
    Fixture {
        name: "strip_first_fd_70000",
        program,
        env: fd_70000_env(None),
        premises: Vec::new(),
        expect_refuted: true,
        hygiene: Vec::new(),
    }
}

/// OLD-MAIN BUG 1 under the fd-bound premise at the REAL kernel bound: "every
/// open fd < min(soft RLIMIT_NOFILE, 92 160)" holds for 70 000, so a premise
/// that states what the kernel guarantees does not excuse the 65 536 cap.
/// Must be REFUTED under the premise.
#[must_use]
pub fn strip_first_fd_70000_kernel_bound() -> Fixture {
    let mut program = build("strip_first_fd_70000", "be339c9b2", Variant::StripFirst);
    program.add_provenance(
        "aterm",
        ATERM_BASE,
        PATH,
        "unchanged since be339c9b2 (doc comments only)",
    );
    Fixture {
        name: "strip_first_fd_70000_kernel_bound",
        program,
        env: fd_70000_env(Some(92_160)),
        premises: vec![Premise::FdBound],
        expect_refuted: true,
        hygiene: Vec::new(),
    }
}

/// OLD-MAIN BUG 2: the ceiling is read in the PARENT (spawnfd.rs:120,
/// `let ceiling = inherited_fd_ceiling();`) before the fork. The window
/// racer lowers the soft limit to 1024, the read sees 1024, the racer raises
/// it to 70 064 and takes an unflagged descriptor at 2000, the fork copies
/// it, and the strip stops at 1024. No foreign descriptor (the refutation is
/// the window's alone), and the premise is aterm's OWN, cap 65 536: at the
/// fork every descriptor is below min(70 064, 65 536), so the premise the
/// old code was written under does not excuse it either. The window racer
/// replaces the e17e2d6d5 pair racer here. Must be REFUTED, by the racer's
/// descriptor at 2000.
#[must_use]
pub fn strip_first_ceiling_window() -> Fixture {
    let mut program = build_with(
        "strip_first_ceiling_window",
        "be339c9b2",
        Variant::StripFirst,
        Some(WindowRace::Low),
    );
    program.add_provenance(
        "aterm",
        ATERM_BASE,
        PATH,
        "unchanged since be339c9b2 (doc comments only)",
    );
    Fixture {
        name: "strip_first_ceiling_window",
        program,
        env: EnvSpec { foreign: false, ..spawnfd_env() },
        premises: vec![Premise::FdBound],
        expect_refuted: true,
        hygiene: Vec::new(),
    }
}
