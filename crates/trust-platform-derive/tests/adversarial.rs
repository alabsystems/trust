//! Regression tests for the two adversarial reviews of M1 (2026-09-30).
//!
//! Every program here was a WRONG verdict of the checker at 614f050986:
//! A1-A7 and D1 leaked a descriptor into a policy child yet came back from
//! NativeTyEngine `Proved {ExplicitStateModel, Sound}`; B1-B3 were refuted
//! although correct; C2/C3 checked formulas the model cannot answer. Each is
//! checked through the same NativeTyEngine path as the acceptance fixtures
//! (refutation-only payload), and every refutation is explained and
//! re-executed. The model-review findings that reach the derivation (F3 torn
//! table copies, F6 DR-1, F7 std's path choice, F11 std's spawn error path)
//! are pinned at the end.
//!
//! The historical leak controls explicitly select `CommandStd::Upstream` and
//! retain their `inherit_all_fds` premise. Trust's different placement and
//! relocation are not selected by that bit. Current Trust neighbors are checked
//! separately; historical fixture populations keep their explicit std choice.

use trust_platform::call::FileAction;
use trust_platform::std_summaries::{CommandShape, CommandStd, StdioPlan};
use trust_platform::{Call, Errno, Oracle, darwin};
use trust_platform_derive::derive::{DeriveOptions, Derived};
use trust_platform_derive::env::{EnvSpec, Limits, Slot};
use trust_platform_derive::fixtures::{self, add_racer, spawnfd_env};
use trust_platform_derive::lower::LowerError;
use trust_platform_derive::program::{
    Bind, BodyBuilder, BodyId, CmpOp, Cond, EventProgram, Expr, FdInherit, Lane, Operand,
    ProgramBuilder, VarId,
};
use trust_platform_derive::property::{self, FormulaError, Premise, Violation, premised};
use trust_platform_derive::{DeriveError, derive, fd_inherit_formula, non_vacuity_formula};
use trust_router::full_verification::NativeTyEngine;
use trust_types::TY_TEMPORAL_MODEL_METADATA_KEY;
use trust_verifier_api::{
    BundleSubject, EvidenceStatus, MetadataEntry, ObligationKind, SourceLocation,
    TrustContractBundle, TrustObligation, VerificationEngine,
};

#[path = "adversarial/current_command.rs"]
mod current_command;

const L: &str = "adv:review";

fn ty(d: &Derived, formula: &str) -> (EvidenceStatus, Option<Vec<usize>>, Vec<String>) {
    let payload = d.payload(formula).unwrap_or_else(|e| panic!("`{formula}`: {e}"));
    let obligation = TrustObligation {
        obligation_id: format!("vc:adv::{}:temporal_safety:{}", d.name(), formula.len()),
        kind: ObligationKind::TemporalSafety,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: format!("adv `{formula}`"),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_metadata_value().expect("serializes"),
        }],
    };
    let mut bundle = TrustContractBundle::empty(
        format!("bundle-{}", d.name()),
        BundleSubject::Function {
            crate_name: "adv".to_string(),
            path: format!("adv::{}", d.name()),
        },
    );
    bundle.obligations.push(obligation.clone());
    let ev = NativeTyEngine::new().verify(&bundle, &[obligation]).remove(0);
    assert!(ev.proof_strength.is_none(), "a derived model never proves: {ev:?}");
    let trace = ev.counterexample.as_ref().and_then(|ce| {
        ce.data["trace"].as_array().map(|steps| {
            steps
                .iter()
                .map(|s| s["value"].as_str().and_then(|v| v.parse::<usize>().ok()).unwrap())
                .collect()
        })
    });
    (ev.status, trace, ev.diagnostics)
}

fn derive_ok(prog: &EventProgram, env: &EnvSpec) -> Derived {
    derive(prog, env, &DeriveOptions::default())
        .unwrap_or_else(|e| panic!("{}: derivation failed: {e}", prog.name))
}

/// `formula` is refuted by ty and the trace re-executes to a state carrying
/// `want`; returns the violations and the replay's event lines.
fn refuted(d: &Derived, formula: &str, want: &str) -> (Vec<Violation>, Vec<String>) {
    let (status, trace, diags) = ty(d, formula);
    assert_eq!(
        status,
        EvidenceStatus::Failed,
        "{}: `{formula}` must be refuted: {diags:?}",
        d.name()
    );
    let trace = trace.expect("a refutation carries a trace");
    let replay = d
        .replay(&trace, &[want])
        .unwrap_or_else(|e| panic!("{}: the trace must re-execute: {e}", d.name()));
    let lines = replay.steps.iter().flat_map(|s| s.events.clone()).collect();
    (replay.violations, lines)
}

/// The fd-inherit formula under `premises` is refuted (with a replayed
/// trace); returns the violations.
fn leaks(d: &Derived, premises: &[Premise]) -> Vec<Violation> {
    let want = premised(property::VIOLATION, premises);
    refuted(d, &fd_inherit_formula(premises), &want).0
}

/// Not refuted (Unknown: refutation-only) and not vacuous.
fn clean(d: &Derived, premises: &[Premise]) {
    let (status, _, diags) = ty(d, &fd_inherit_formula(premises));
    assert_eq!(status, EvidenceStatus::Unknown, "{}: must not be refuted: {diags:?}", d.name());
    let exec = premised(property::POLICY_EXEC, premises);
    refuted(d, &non_vacuity_formula(premises), &exec);
}

fn fcntl(fd: Operand, cmd: i32, arg: i64) -> Call<Operand> {
    Call::Fcntl { fd, cmd, arg }
}

/// `inherited_fd_ceiling` exactly as be339c9b2 (min(soft, 1<<16)).
fn ceiling_body(p: &mut ProgramBuilder) -> BodyId {
    let rc = p.var("getrlimit_rc", -1);
    let soft = p.var("limit_cur", -1);
    let out = p.var("ceiling_soft", -1);
    p.body("inherited_fd_ceiling", Vec::new(), |b| {
        b.event(
            L,
            "getrlimit",
            Call::Getrlimit { resource: darwin::RLIMIT_NOFILE },
            Bind { ret: Some(rc), rlim_soft: Some(soft), ..Bind::default() },
        );
        b.if_(
            L,
            Cond::eq(Operand::Var(rc), Operand::Lit(0)),
            |t| t.assign(L, out, Expr::Min(Operand::Var(soft), Operand::Lit(1 << 16))),
            |e| e.assign(L, out, Expr::Use(Operand::Lit(1 << 16))),
        );
        b.ret(L, Some(Operand::Var(out)));
    })
}

#[derive(Clone, Copy)]
enum Strip {
    FromTo { lo: i64 },
    CeilingPlus(i64),
    Literal(i64),
    LitSum(i64, i64),
}

/// be339c9b2's `spawn_with_two_fds` with the strip replaced by `strip`, an
/// optional racer, and an optional foreign thread that may raise the soft
/// limit and then takes an unflagged descriptor at `floor`.
fn two_fd(
    name: &str,
    strip: Strip,
    racer: bool,
    foreign: Option<(Option<u64>, i64)>,
) -> EventProgram {
    let mut p = ProgramBuilder::new(name);
    p.disclose("Historical adversarial inheritance fixture: the Command explicitly selects CommandStd::Upstream and retains inherit_all_fds; current Trust neighbors are separate controls.");
    let first = p.fd_param("first", "first", Some("first_peer"));
    let second = p.fd_param("second", "second", Some("second_peer"));
    let a = p.var("a", -1);
    let bv = p.var("b", -1);
    let moved_a = p.var("moved_a", -1);
    let moved_b = p.var("moved_b", -1);
    let r = p.var("r", -1);
    let ceiling = p.var("ceiling", -1);
    let hi = p.var("strip_hi", -1);
    let fd = p.var("strip_fd", -1);
    let cb = ceiling_body(&mut p);
    let one = p.body("strip one", Vec::new(), |b| {
        b.event(
            L,
            "fcntl",
            fcntl(Operand::Var(fd), darwin::F_SETFD, darwin::FD_CLOEXEC),
            Bind::none(),
        );
    });
    let closure = p.body("pre_exec", Vec::new(), |b| {
        match strip {
            Strip::FromTo { lo } => {
                b.for_range(L, fd, Operand::Lit(lo), Operand::Var(ceiling), one)
            }
            Strip::CeilingPlus(k) => {
                b.assign(L, hi, Expr::Add(Operand::Var(ceiling), Operand::Lit(k)));
                b.for_range(L, fd, Operand::Lit(3), Operand::Var(hi), one);
            }
            Strip::Literal(n) => b.for_range(L, fd, Operand::Lit(3), Operand::Lit(n), one),
            Strip::LitSum(x, y) => {
                b.assign(L, hi, Expr::Add(Operand::Lit(x), Operand::Lit(y)));
                b.for_range(L, fd, Operand::Lit(3), Operand::Var(hi), one);
            }
        }
        b.assign(L, a, Expr::Use(Operand::Var(first)));
        b.assign(L, bv, Expr::Use(Operand::Var(second)));
        b.assign(L, moved_a, Expr::Use(Operand::Lit(-1)));
        b.assign(L, moved_b, Expr::Use(Operand::Lit(-1)));
        for (src, moved) in [(a, moved_a), (bv, moved_b)] {
            b.when(
                L,
                Cond::or(
                    Cond::eq(Operand::Var(src), Operand::Lit(3)),
                    Cond::eq(Operand::Var(src), Operand::Lit(4)),
                ),
                |t| {
                    t.event(
                        L,
                        "fcntl",
                        fcntl(Operand::Var(src), darwin::F_DUPFD, 5),
                        Bind::ret(src),
                    );
                    t.when(L, Cond::eq(Operand::Var(src), Operand::Lit(-1)), |e| {
                        e.ret(L, Some(Operand::Lit(-1)));
                    });
                    t.assign(L, moved, Expr::Use(Operand::Var(src)));
                },
            );
        }
        for (src, target) in [(a, 3), (bv, 4)] {
            b.event(
                L,
                "dup2",
                Call::Dup2 { from: Operand::Var(src), to: Operand::Lit(target) },
                Bind::ret(r),
            );
            b.when(L, Cond::eq(Operand::Var(r), Operand::Lit(-1)), |e| {
                e.ret(L, Some(Operand::Lit(-1)))
            });
        }
        for moved in [moved_a, moved_b] {
            b.when(L, Cond::ne(Operand::Var(moved), Operand::Lit(-1)), |t| {
                t.event(L, "close", Call::Close { fd: Operand::Var(moved) }, Bind::none());
            });
        }
        b.ret(L, Some(Operand::Lit(0)));
    });
    let site = p.site(
        "bridge",
        L,
        Some(FdInherit {
            lanes: vec![
                Lane { fd: 3, ofd_class: "first".to_string() },
                Lane { fd: 4, ofd_class: "second".to_string() },
            ],
        }),
    );
    let child = p.var("child", -1);
    let main = p.body("spawn_with_two_fds", Vec::new(), |b| {
        b.call(L, cb, Vec::new(), Some(ceiling));
        b.neutral(L, "std::os::unix::process::CommandExt::pre_exec");
        b.spawn(
            L,
            [StdioPlan::Null, StdioPlan::Inherit, StdioPlan::Inherit],
            CommandShape {
                inherit_all_fds: true,
                ..CommandShape::with_pre_exec().under(CommandStd::Upstream)
            },
            vec![closure],
            site,
            Some(child),
        );
        b.event(L, "close", Call::Close { fd: Operand::Var(first) }, Bind::none());
        b.event(L, "close", Call::Close { fd: Operand::Var(second) }, Bind::none());
    });
    p.root("main", main);
    if racer {
        add_racer(&mut p);
    }
    if let Some((raise, floor)) = foreign {
        let y = p.var("foreign_fd", -1);
        let body = p.body("foreign thread", Vec::new(), |b| {
            if let Some(soft) = raise {
                b.event(
                    L,
                    "setrlimit",
                    Call::Setrlimit {
                        resource: darwin::RLIMIT_NOFILE,
                        soft,
                        hard: darwin::RLIM_INFINITY,
                    },
                    Bind::none(),
                );
            }
            b.event(L, "fcntl", fcntl(Operand::Lit(0), darwin::F_DUPFD, floor), Bind::ret(y));
        });
        p.root("foreign", body);
    }
    p.build()
}

fn plain_env() -> EnvSpec {
    EnvSpec {
        limits: Limits::measured_darwin(),
        param_slots: Vec::new(),
        foreign: true,
        foreign_at: Vec::new(),
        fd_bound_cap: None,
        names: Vec::new(),
    }
}

fn cloexec_default_spawn(b: &mut BodyBuilder, site: usize, pid: VarId) {
    let actions =
        (0..3).map(|fd| FileAction::Open { fd: Operand::Lit(fd), flags: darwin::O_RDWR }).collect();
    b.event_full(
        L,
        "posix_spawn",
        Call::Spawn {
            actions,
            flags: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT | darwin::POSIX_SPAWN_SETSIGDEF,
        },
        Bind::ret(pid),
        vec![Oracle::Nominal, Oracle::Fail(Errno::ENOENT)],
        Some(site),
        vec!["devnull0", "devnull1", "devnull2"],
    );
}

fn extra_at(v: &[Violation], pred: impl Fn(i32) -> bool) -> bool {
    v.iter().any(|x| matches!(x, Violation::Extra { fd, .. } if pred(*fd)))
}

// ---- (a) false passes ---------------------------------------------------------

/// A1: a literal strip `3..256` misses an unflagged descriptor at 256 or
/// above; RL-INIT now places one on each side of 256.
#[test]
fn a1_literal_strip_end_is_refuted() {
    let d = derive_ok(&two_fd("a1", Strip::Literal(256), true, None), &spawnfd_env());
    let v = leaks(&d, &[Premise::FdBound]);
    assert!(extra_at(&v, |fd| (256..65_536).contains(&fd)), "{v:?}");
}

/// A2: `3..ceiling-1` misses fd 65535, which fd-bound allows.
#[test]
fn a2_strip_one_short_is_refuted() {
    let d = derive_ok(&two_fd("a2", Strip::CeilingPlus(-1), true, None), &spawnfd_env());
    let v = leaks(&d, &[Premise::FdBound]);
    assert!(extra_at(&v, |fd| fd == 65_535), "{v:?}");
}

/// A3: four `F_DUPFD(0, 65536)`s land on 65536..65539 (the old scaled
/// instance spilled them into the next interval); the guard `x4 < 70000` holds, so
/// the leaky plain spawn runs.
#[test]
fn a3_allocation_past_a_high_constant_is_real() {
    let mut p = ProgramBuilder::new("a3_spill");
    p.disclose("Historical adversarial inheritance fixture: leaky_plain_spawn selects CommandStd::Upstream and retains explicit inherit_all_fds.");
    let xs: Vec<VarId> = (1..=4).map(|i| p.var(&format!("x{i}"), -1)).collect();
    let pid = p.var("pid", -1);
    let site_a = p.site("leaky_plain_spawn", L, Some(FdInherit { lanes: Vec::new() }));
    let site_b = p.site("cloexec_default", L, Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        for x in &xs {
            b.event(L, "fcntl", fcntl(Operand::Lit(0), darwin::F_DUPFD, 65_536), Bind::ret(*x));
        }
        for x in &xs {
            b.event(L, "close", Call::Close { fd: Operand::Var(*x) }, Bind::none());
        }
        b.if_(
            L,
            Cond::Cmp(CmpOp::Lt, Operand::Var(xs[3]), Operand::Lit(70_000)),
            |t| {
                t.spawn(
                    L,
                    [StdioPlan::Inherit; 3],
                    CommandShape {
                        inherit_all_fds: true,
                        ..CommandShape::default().under(CommandStd::Upstream)
                    },
                    Vec::new(),
                    site_a,
                    None,
                );
            },
            |e| cloexec_default_spawn(e, site_b, pid),
        );
    });
    p.root("main", main);
    let d = derive_ok(&p.build(), &plain_env());
    let (v, lines) = refuted(&d, &fd_inherit_formula(&[]), property::VIOLATION);
    assert!(
        v.iter().any(|x| matches!(x, Violation::Extra { site, .. } if site == "leaky_plain_spawn"))
    );
    assert!(lines.iter().any(|l| l.contains("F_DUPFD, 65536) = 65539")), "{lines:#?}");
}

/// A4: a strip from 6 misses a foreign descriptor at 5.
#[test]
fn a4_strip_from_six_is_refuted_without_a_racer() {
    let d = derive_ok(&two_fd("a4", Strip::FromTo { lo: 6 }, false, None), &spawnfd_env());
    let v = leaks(&d, &[Premise::FdBound]);
    assert!(extra_at(&v, |fd| fd == 5), "{v:?}");
}

/// A5: `setrlimit(NOFILE, 1000, INF)` succeeds at the real constants (the
/// old scaled instance returned EPERM), so the ceiling is 1000 and fd 2000 leaks.
#[test]
fn a5_setrlimit_operands_are_real() {
    let mut p = ProgramBuilder::new("a5_lowered_limit");
    p.disclose("Historical adversarial inheritance fixture: the Command selects CommandStd::Upstream and retains explicit inherit_all_fds so the caller's lowered-limit strip is measured.");
    let x = p.var("x", -1);
    let ceiling = p.var("ceiling", -1);
    let fd = p.var("strip_fd", -1);
    let cb = ceiling_body(&mut p);
    let one = p.body("strip one", Vec::new(), |b| {
        b.event(
            L,
            "fcntl",
            fcntl(Operand::Var(fd), darwin::F_SETFD, darwin::FD_CLOEXEC),
            Bind::none(),
        );
    });
    let closure = p.body("pre_exec", Vec::new(), |b| {
        b.for_range(L, fd, Operand::Lit(3), Operand::Var(ceiling), one);
        b.ret(L, Some(Operand::Lit(0)));
    });
    let site = p.site("child", L, Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        b.event(L, "fcntl", fcntl(Operand::Lit(0), darwin::F_DUPFD, 2000), Bind::ret(x));
        b.event(
            L,
            "setrlimit",
            Call::Setrlimit {
                resource: darwin::RLIMIT_NOFILE,
                soft: 1000,
                hard: darwin::RLIM_INFINITY,
            },
            Bind::none(),
        );
        b.call(L, cb, Vec::new(), Some(ceiling));
        b.spawn(
            L,
            [StdioPlan::Inherit; 3],
            CommandShape {
                inherit_all_fds: true,
                ..CommandShape::with_pre_exec().under(CommandStd::Upstream)
            },
            vec![closure],
            site,
            None,
        );
    });
    p.root("main", main);
    let d = derive_ok(&p.build(), &plain_env());
    let v = leaks(&d, &[]);
    assert!(extra_at(&v, |fd| fd == 2000), "{v:?}");
}

/// D1: aterm's park raise. Launched from the Dock (soft 256), a thread
/// raises the limit to 4096 and takes fd 300 after the spawn read the
/// ceiling (256): the strip misses 300, which fd-bound allows (300 < 4096).
/// RL-INIT also places a foreign descriptor above the soft limit (a number
/// inherited from a higher-limit parent survives exec): once the raise makes
/// fd-bound admit it, the strip to the stale ceiling misses that one too, so
/// ty's counterexample may be either leak in the raised window; the thread's
/// fd-300 leak is checked on the explored states.
#[test]
fn d1_park_raise_races_the_ceiling_read() {
    let env = EnvSpec {
        limits: Limits { soft: 256, hard: darwin::RLIM_INFINITY, max_files_per_proc: 92_160 },
        param_slots: vec![Slot::Exact(3), Slot::Exact(4), Slot::Mid],
        foreign: true,
        foreign_at: Vec::new(),
        fd_bound_cap: Some(65_536),
        names: Vec::new(),
    };
    let d = derive_ok(&two_fd("d1", Strip::FromTo { lo: 3 }, true, Some((Some(4096), 300))), &env);
    let v = leaks(&d, &[Premise::FdBound]);
    assert!(extra_at(&v, |fd| (256..4096).contains(&fd)), "{v:?}");
    let thread_leak = d.graph().configs.iter().any(|c| {
        property::violations_premised(d.core(), c)
            .iter()
            .any(|(x, under)| *under && matches!(x, Violation::Extra { fd: 300, .. }))
    });
    assert!(thread_leak, "the strip misses the thread's fd 300 on some explored path");
}

/// A7: the strip `3..(10 + 1000)` is arithmetic on real numbers now: a
/// descriptor at or above 1010 (the thread's 1012, or a foreign one at the
/// strip's end) survives.
#[test]
fn a7_arithmetic_on_constants_is_real() {
    let d = derive_ok(
        &two_fd("a7", Strip::LitSum(10, 1000), false, Some((None, 1012))),
        &spawnfd_env(),
    );
    let v = leaks(&d, &[Premise::FdBound]);
    assert!(extra_at(&v, |fd| (1010..65_536).contains(&fd)), "{v:?}");
}

/// A6: the premise is evaluated per child at its snapshot: a transient fd
/// above the cap, closed before the leaky spawn, does not excuse it.
#[test]
fn a6_an_earlier_premise_failure_excuses_nothing_later() {
    let mut p = ProgramBuilder::new("a6_transient_high");
    p.disclose("Historical adversarial inheritance fixture: the leaky Command selects CommandStd::Upstream and retains explicit inherit_all_fds.");
    let pid = p.var("pid", -1);
    let x = p.var("x", -1);
    let site_a = p.site("clean", L, Some(FdInherit { lanes: Vec::new() }));
    let site_b = p.site("leaky", L, Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        cloexec_default_spawn(b, site_a, pid);
        b.event(L, "fcntl", fcntl(Operand::Lit(0), darwin::F_DUPFD, 65_536), Bind::ret(x));
        b.event(L, "close", Call::Close { fd: Operand::Var(x) }, Bind::none());
        b.spawn(
            L,
            [StdioPlan::Inherit; 3],
            CommandShape {
                inherit_all_fds: true,
                ..CommandShape::default().under(CommandStd::Upstream)
            },
            Vec::new(),
            site_b,
            None,
        );
    });
    p.root("main", main);
    let env = EnvSpec { fd_bound_cap: Some(65_536), ..plain_env() };
    let d = derive_ok(&p.build(), &env);
    let v = leaks(&d, &[Premise::FdBound]);
    assert!(
        v.iter().any(|x| matches!(x, Violation::Extra { site, .. } if site == "leaky")),
        "{v:?}"
    );
}

/// The historical upstream controls really leak on both spawn paths. Their
/// Trust neighbors strip before the hooks; their explicit inheritance opt-out
/// is a one-bit leak mutant. Preserve both historical upstream leak populations.
#[test]
fn default_sp1_neighbors_and_their_opt_out_mutants_replay() {
    let fork = two_fd("default_sp1_fork", Strip::Literal(256), false, None);
    let mut p = ProgramBuilder::new("default_sp1_posix");
    let site = p.site("child", L, Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        b.spawn(
            L,
            [StdioPlan::Inherit; 3],
            CommandShape {
                inherit_all_fds: true,
                ..CommandShape::default().under(CommandStd::Upstream)
            },
            Vec::new(),
            site,
            None,
        );
    });
    p.root("main", main);
    for (program, env, premises) in
        [(fork, spawnfd_env(), vec![Premise::FdBound]), (p.build(), plain_env(), Vec::new())]
    {
        // Preserve the replayed positive leak under its historical premises.
        leaks(&derive_ok(&program, &env), &premises);
        for inherit_all_fds in [false, true] {
            let mut neighbor = program.clone();
            for note in &mut neighbor.disclosures {
                if note.starts_with("Historical adversarial inheritance fixture:") {
                    *note = format!(
                        "Current Trust neighbor: retain Trust placement and relocation; inherit_all_fds={inherit_all_fds}. The historical upstream population is checked separately."
                    );
                }
            }
            let mut changed = 0;
            for body in &mut neighbor.bodies {
                for block in &mut body.blocks {
                    for stmt in &mut block.stmts {
                        if let trust_platform_derive::program::StmtKind::Std(
                            trust_platform_derive::program::StdCall::CommandSpawn { shape, .. },
                        ) = &mut stmt.kind
                        {
                            assert_eq!(shape.std, CommandStd::Upstream);
                            assert!(shape.inherit_all_fds);
                            shape.std = CommandStd::Trust;
                            shape.inherit_all_fds = inherit_all_fds;
                            changed += 1;
                        }
                    }
                }
            }
            assert_eq!(changed, 1);
            let d = derive_ok(&neighbor, &env);
            if inherit_all_fds {
                leaks(&d, &premises);
            } else {
                clean(&d, &premises);
            }
        }
    }
}

// ---- (b) false refutations ------------------------------------------------------

/// B1: the jobserver pattern clears FD_CLOEXEC on a descriptor held in a
/// variable: declared, by number, as the child runs.
#[test]
fn b1_jobserver_by_variable_is_declared() {
    let mut p = ProgramBuilder::new("b1_jobserver");
    let js = p.fd_param("jobserver", "jobserver", None);
    let closure = p.body("pre_exec", Vec::new(), |b| {
        b.event(L, "fcntl", fcntl(Operand::Var(js), darwin::F_SETFD, 0), Bind::none());
        b.ret(L, Some(Operand::Lit(0)));
    });
    let site = p.site("make", L, Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        b.spawn(
            L,
            [StdioPlan::Inherit; 3],
            CommandShape::with_pre_exec().under(CommandStd::Upstream),
            vec![closure],
            site,
            None,
        );
    });
    p.root("main", main);
    let env =
        EnvSpec { param_slots: vec![Slot::Exact(3), Slot::Mid], foreign: false, ..plain_env() };
    clean(&derive_ok(&p.build(), &env), &[]);
}

/// B2: a lane at fd 100 is compared at its real number.
#[test]
fn b2_lane_above_the_small_points() {
    let mut p = ProgramBuilder::new("b2_high_lane");
    let first = p.fd_param("first", "first", None);
    let r = p.var("r", -1);
    let closure = p.body("pre_exec", Vec::new(), |b| {
        b.event(
            L,
            "dup2",
            Call::Dup2 { from: Operand::Var(first), to: Operand::Lit(100) },
            Bind::ret(r),
        );
        b.ret(L, Some(Operand::Lit(0)));
    });
    let site = p.site(
        "child",
        L,
        Some(FdInherit { lanes: vec![Lane { fd: 100, ofd_class: "first".to_string() }] }),
    );
    let main = p.body("main", Vec::new(), |b| {
        b.spawn(
            L,
            [StdioPlan::Inherit; 3],
            CommandShape::with_pre_exec().under(CommandStd::Upstream),
            vec![closure],
            site,
            None,
        );
        b.event(L, "close", Call::Close { fd: Operand::Var(first) }, Bind::none());
    });
    p.root("main", main);
    let env = EnvSpec { param_slots: vec![Slot::Mid], foreign: false, ..plain_env() };
    clean(&derive_ok(&p.build(), &env), &[]);
}

/// B3: scratch `dup2` targets later closed are allowed, not required. (The
/// arguments sit on 3 and 4, the review's layout: with arguments elsewhere
/// std's status pipe lands on 3/4 and the closure's own `dup2`s clobber its
/// write end — a real hazard on std's exec-error path, which the model
/// refuses by name because the clobbering description's kind is unknown.)
#[test]
fn b3_scratch_dup2_targets_are_not_lanes() {
    let mut p = ProgramBuilder::new("b3_scratch_targets");
    let first = p.fd_param("first", "first", None);
    let second = p.fd_param("second", "second", None);
    let r = p.var("r", -1);
    let closure = p.body("pre_exec", Vec::new(), |b| {
        for (from, to) in [
            (Operand::Var(first), 10),
            (Operand::Var(second), 11),
            (Operand::Lit(10), 3),
            (Operand::Lit(11), 4),
        ] {
            b.event(L, "dup2", Call::Dup2 { from, to: Operand::Lit(to) }, Bind::ret(r));
        }
        b.event(L, "close", Call::Close { fd: Operand::Lit(10) }, Bind::none());
        b.event(L, "close", Call::Close { fd: Operand::Lit(11) }, Bind::none());
        b.ret(L, Some(Operand::Lit(0)));
    });
    let site = p.site(
        "bridge",
        L,
        Some(FdInherit {
            lanes: vec![
                Lane { fd: 3, ofd_class: "first".to_string() },
                Lane { fd: 4, ofd_class: "second".to_string() },
            ],
        }),
    );
    let main = p.body("main", Vec::new(), |b| {
        b.spawn(
            L,
            [StdioPlan::Inherit; 3],
            CommandShape::with_pre_exec().under(CommandStd::Upstream),
            vec![closure],
            site,
            None,
        );
    });
    p.root("main", main);
    let env = EnvSpec {
        param_slots: vec![Slot::Exact(3), Slot::Exact(4)],
        foreign: false,
        ..plain_env()
    };
    clean(&derive_ok(&p.build(), &env), &[]);
}

// ---- (c) what ty is asked ---------------------------------------------------------

/// C2/C3: a misspelt atom, or one the horizon cut changes (`fd_bound` "now"),
/// is refused before ty sees it: an unknown atom is false everywhere, so it
/// would check vacuously.
#[test]
fn c_formulas_outside_the_vocabulary_are_refused() {
    let f = fixtures::spawnfd::no_strip();
    let d = derive_ok(&f.program, &f.env);
    for bad in [
        "AG !fd_inherit_violaton",
        "AG !(fd_inherit_violation && fd_bnd)",
        "AX AG fd_bound",
        "AG !(fd_inherit_violation && fd_bound)",
    ] {
        match d.payload(bad) {
            Err(FormulaError::UnknownAtom(_)) => {}
            other => panic!("`{bad}` must be refused: {other:?}"),
        }
    }
    assert!(matches!(d.payload("AG !!!"), Err(FormulaError::Parse(_))));
    // The payload a derived model emits is refutation-only.
    assert!(d.payload(&fd_inherit_formula(&[])).expect("vetted").is_refutation_only());
}

// ---- model findings, at the derivation ------------------------------------------

/// F3: a lane inherited by number while another thread re-points it with
/// `dup2`: the torn table copy misses it (measured), so the lane can be
/// missing at exec. An atomic-copy model never finds this.
#[test]
fn f3_torn_copy_loses_an_inherited_lane() {
    let mut p = ProgramBuilder::new("f3_torn_lane");
    let first = p.fd_param("first", "first", None);
    let lane = p.var("lane", -1);
    let other = p.var("other", -1);
    let pid = p.var("pid", -1);
    let site = p.site(
        "child",
        L,
        Some(FdInherit { lanes: vec![Lane { fd: 50, ofd_class: "first".to_string() }] }),
    );
    let main = p.body("main", Vec::new(), |b| {
        b.event(L, "fcntl", fcntl(Operand::Var(first), darwin::F_DUPFD, 50), Bind::ret(lane));
        b.event(
            L,
            "fcntl",
            fcntl(Operand::Var(first), darwin::F_DUPFD_CLOEXEC, 60),
            Bind::ret(other),
        );
        b.event_full(
            L,
            "posix_spawn",
            Call::Spawn { actions: Vec::new(), flags: 0 },
            Bind::ret(pid),
            vec![Oracle::Nominal],
            Some(site),
            Vec::new(),
        );
    });
    p.root("main", main);
    let racer = p.body("re-pointing thread", Vec::new(), |b| {
        b.event(
            L,
            "dup2",
            Call::Dup2 { from: Operand::Lit(60), to: Operand::Lit(50) },
            Bind::none(),
        );
    });
    p.root("racer", racer);
    let env = EnvSpec { param_slots: vec![Slot::Mid], foreign: false, ..plain_env() };
    let d = derive_ok(&p.build(), &env);
    let (v, lines) =
        refuted(&d, &format!("AG !{}", property::LANE_MISSING), property::LANE_MISSING);
    assert!(v.iter().any(|x| matches!(x, Violation::Missing { fd: 50, .. })), "{v:?}");
    assert!(lines.iter().any(|l| l.contains("torn table copy")), "{lines:#?}");
}

/// F6/DR-1: a `pre_exec` closure that calls a function that is not
/// async-signal-safe, in a multithreaded parent, is a named error; the same
/// closure in a single-threaded parent is fine.
#[test]
fn f6_dr1_not_async_signal_safe_in_a_multithreaded_fork_child() {
    let build = |threads: bool| {
        let mut p = ProgramBuilder::new("f6_dr1");
        let kq = p.var("kq", -1);
        let closure = p.body("pre_exec", Vec::new(), |b| {
            b.event(L, "kqueue", Call::Kqueue, Bind::ret(kq));
            b.ret(L, Some(Operand::Lit(0)));
        });
        let site = p.site("child", L, Some(FdInherit { lanes: Vec::new() }));
        let main = p.body("main", Vec::new(), |b| {
            b.spawn(
                L,
                [StdioPlan::Inherit; 3],
                CommandShape::with_pre_exec().under(CommandStd::Upstream),
                vec![closure],
                site,
                None,
            );
        });
        p.root("main", main);
        if threads {
            let idle = p.body("idle thread", Vec::new(), |b| {
                b.event(
                    L,
                    "getrlimit",
                    Call::Getrlimit { resource: darwin::RLIMIT_NOFILE },
                    Bind::none(),
                );
            });
            p.root("idle", idle);
        }
        p.build()
    };
    let env = EnvSpec { foreign: false, ..plain_env() };
    match derive(&build(true), &env, &DeriveOptions::default()) {
        Err(DeriveError::Explore(e)) => {
            assert!(e.to_string().contains("DR-1") && e.to_string().contains("kqueue"), "{e}")
        }
        other => panic!("expected a DR-1 error, got {:?}", other.map(|d| d.stats())),
    }
    derive_ok(&build(false), &env);
}

/// F7: std takes the FORK path for `setsid(true)` on Darwin; its child steps
/// (setsid) are not modeled, so the spawn is refused by name instead of
/// being summarized as `posix_spawnp`.
#[test]
fn f7_setsid_takes_std_fork_path() {
    let mut p = ProgramBuilder::new("f7_setsid");
    let site = p.site("child", L, Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        b.spawn(
            L,
            [StdioPlan::Inherit; 3],
            CommandShape { setsid: true, ..CommandShape::default() },
            Vec::new(),
            site,
            None,
        );
    });
    p.root("main", main);
    match derive(&p.build(), &plain_env(), &DeriveOptions::default()) {
        Err(DeriveError::Lower(e)) => assert!(e.to_string().contains("setsid"), "{e}"),
        other => panic!("expected a named refusal, got {:?}", other.map(|d| d.stats())),
    }
}

/// Both current Trust builder paths lower their own rows, retain std origins,
/// and reach a policy exec without leaking an inherited foreign descriptor.
#[test]
fn current_trust_builder_rows_are_supported_without_proof_authority() {
    for shape in [CommandShape::default(), CommandShape::with_pre_exec()] {
        assert_eq!(shape.std, CommandStd::Trust);
        let mut p = ProgramBuilder::new("trust_std_spawn");
        let site = p.site("child", L, Some(FdInherit { lanes: Vec::new() }));
        let hook = p.body("hook", Vec::new(), |b| b.ret(L, Some(Operand::Lit(0))));
        let hooks = if shape.pre_exec { vec![hook] } else { Vec::new() };
        let main = p.body("main", Vec::new(), |b| {
            if shape.pre_exec {
                b.spawn_fork(L, [StdioPlan::Inherit; 3], hooks, site, None);
            } else {
                b.spawn_posix(L, [StdioPlan::Inherit; 3], site, None);
            }
        });
        p.root("main", main);
        let program = p.build();
        let d = derive_ok(&program, &plain_env());
        clean(&d, &[]);
        let mut mutant = program.clone();
        for body in &mut mutant.bodies {
            for block in &mut body.blocks {
                for stmt in &mut block.stmts {
                    if let trust_platform_derive::program::StmtKind::Std(
                        trust_platform_derive::program::StdCall::CommandSpawn { shape, .. },
                    ) = &mut stmt.kind
                    {
                        assert_eq!(shape.std, CommandStd::Trust);
                        shape.inherit_all_fds = true;
                    }
                }
            }
        }
        leaks(&derive_ok(&mutant, &plain_env()), &[]);
    }
}

/// F11: an exec failure on std's fork path reaches the caller's `Err` branch:
/// the child reports on the status pipe and exits, the parent reaps it and
/// `spawn()` returns `Err`. Here only that branch makes a (leaky) policy
/// spawn, so the refutation's trace must pass through std's error path.
#[test]
fn f11_spawn_error_path_is_reachable() {
    let mut p = ProgramBuilder::new("f11_err");
    let child = p.var("child", -1);
    let closure = p.body("pre_exec", Vec::new(), |b| b.ret(L, Some(Operand::Lit(0))));
    let first = p.site("first_try", L, None);
    let fallback = p.site("fallback", L, Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        b.spawn(
            L,
            [StdioPlan::Inherit; 3],
            CommandShape::with_pre_exec().under(CommandStd::Upstream),
            vec![closure],
            first,
            Some(child),
        );
        b.when(L, Cond::eq(Operand::Var(child), Operand::Lit(-1)), |t| {
            // The fallback must actually leak for this error-path test.
            // Explicitly select the historical upstream contract as well as
            // its inheritance premise. This is a historical error-path control.
            t.spawn(
                L,
                [StdioPlan::Inherit; 3],
                CommandShape {
                    inherit_all_fds: true,
                    ..CommandShape::default().under(CommandStd::Upstream)
                },
                Vec::new(),
                fallback,
                None,
            );
        });
    });
    p.root("main", main);
    let d = derive_ok(&p.build(), &plain_env());
    let (v, lines) = refuted(&d, &fd_inherit_formula(&[]), property::VIOLATION);
    assert!(v.iter().any(|x| matches!(x, Violation::Extra { site, .. } if site == "fallback")));
    for want in ["execvp() = -1 ENOENT", "write(", "_exit(1)", "read(", "waitpid("] {
        assert!(lines.iter().any(|l| l.contains(want)), "`{want}` missing from {lines:#?}");
    }
}
