//! X1 end to end (design 2026-10-01 §2.6, PR 6): what the census emits for
//! values and guards it could not track, through NativeTyEngine and the
//! replay — the path the host will take (refutation-only payload).
//!
//! * An undecided guard (`Cond::Nondet`) is explored both ways. A refutation
//!   through one is found, replays, and the replay lists the choice it took
//!   (`Replay::overapprox`): Critique C-9's record, from which the host
//!   reports `PC-OVERAPPROX` instead of an error. A refutation that takes no
//!   choice lists none.
//! * A choice inside a forked child's `pre_exec` code splits the child's
//!   macro step; the trace still replays.
//! * An untracked value (`Expr::Opaque`) that reaches nothing the model
//!   executes changes nothing; one that reaches a descriptor operand is the
//!   named refusal `LowerError::Untracked`, with the place it came from.
//!   The shape is `spawnfd::platform::check` as the THIR -> trust-ir producer
//!   emits it for aterm-uds (the dump quoted at the test).
//! * The census review's F4 lane rule (placing a FOREIGN description declares
//!   no lane) holds on M2's split `posix_spawn` too (`land/m2-census`): there
//!   the child's declared set is computed at the first half.

use trust_platform::call::FileAction;
use trust_platform::std_summaries::{CommandShape, CommandStd, StdioPlan};
use trust_platform::{Call, Oracle, darwin};
use trust_platform_derive::derive::{DeriveOptions, Derived};
use trust_platform_derive::env::{EnvSpec, Limits};
use trust_platform_derive::lower::LowerError;
use trust_platform_derive::program::{
    Bind, BodyBuilder, Cond, EventProgram, Expr, FdInherit, Operand, ProgramBuilder, VarId,
};
use trust_platform_derive::trace::Replay;
use trust_platform_derive::track::OPAQUE_VALUE;
use trust_platform_derive::{DeriveError, derive, fd_inherit_formula, non_vacuity_formula};
use trust_router::full_verification::NativeTyEngine;
use trust_types::TY_TEMPORAL_MODEL_METADATA_KEY;
use trust_verifier_api::{
    BundleSubject, EvidenceStatus, MetadataEntry, ObligationKind, SourceLocation,
    TrustContractBundle, TrustObligation, VerificationEngine,
};

fn ty(d: &Derived, formula: &str) -> (EvidenceStatus, Option<Vec<usize>>, Vec<String>) {
    let payload = d.payload(formula).unwrap_or_else(|e| panic!("`{formula}`: {e}"));
    let obligation = TrustObligation {
        obligation_id: format!("vc:x1::{}:temporal_safety:{}", d.name(), formula.len()),
        kind: ObligationKind::TemporalSafety,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: format!("x1 `{formula}`"),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_metadata_value().expect("serializes"),
        }],
    };
    let mut bundle = TrustContractBundle::empty(
        format!("bundle-{}", d.name()),
        BundleSubject::Function { crate_name: "x1".to_string(), path: format!("x1::{}", d.name()) },
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

/// `formula` is refuted, and its trace re-executes to a state carrying
/// `want`.
fn refuted(d: &Derived, formula: &str, want: &str) -> Replay {
    let (status, trace, diags) = ty(d, formula);
    assert_eq!(
        status,
        EvidenceStatus::Failed,
        "{}: `{formula}` must be refuted: {diags:?}",
        d.name()
    );
    let trace = trace.expect("a refutation carries a trace");
    let r = d
        .replay(&trace, &[want])
        .unwrap_or_else(|e| panic!("{}: the trace must re-execute: {e}", d.name()));
    println!("{} `{formula}` ({:?}): refuted, replayed:", d.name(), d.stats());
    for l in lines(&r) {
        println!("    {l}");
    }
    for c in &r.overapprox {
        println!("  over-approximating: {c}");
    }
    r
}

fn not_refuted(d: &Derived) {
    let (status, _, diags) = ty(d, &fd_inherit_formula(&[]));
    assert_eq!(status, EvidenceStatus::Unknown, "{}: must not be refuted: {diags:?}", d.name());
    // Not vacuous: a policy child does exec.
    refuted(d, &non_vacuity_formula(&[]), "policy_exec");
}

fn derive_ok(p: &EventProgram) -> Derived {
    derive(p, &env(), &DeriveOptions::default())
        .unwrap_or_else(|e| panic!("{}: derivation failed: {e}", p.name))
}

/// stdio only: no foreign descriptor, so a leak is the program's own.
fn env() -> EnvSpec {
    EnvSpec {
        limits: Limits::measured_darwin(),
        param_slots: Vec::new(),
        foreign: false,
        foreign_at: Vec::new(),
        fd_bound_cap: None,
        names: Vec::new(),
    }
}

fn open_devnull(b: &mut BodyBuilder, loc: &str, fd: VarId) {
    b.open(loc, "/dev/null", Call::Open { flags: darwin::O_RDONLY }, Bind::ret(fd), "devnull");
}

fn close(b: &mut BodyBuilder, loc: &str, fd: VarId) {
    b.event(loc, "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
}

fn lines(r: &Replay) -> Vec<String> {
    r.steps.iter().flat_map(|s| s.events.clone()).collect()
}

/// `open` without `O_CLOEXEC`; `if <undecided> { close }`; a plain std
/// spawn with explicit upstream inheritance (no CLOEXEC_DEFAULT): the
/// else-arm leaks. Default Trust SP1 strips independently of this guard.
fn guarded_close(then_closes: bool, els_closes: bool) -> EventProgram {
    let mut p = ProgramBuilder::new(&format!("guarded_close_{then_closes}_{els_closes}"));
    p.disclose("Historical guard/replay fixture: the Command selects CommandStd::Upstream and retains explicit inherit_all_fds so the caller's close determines whether it leaks.");
    let fd = p.var("fd", -1);
    let site = p.site("child", "x1.rs:9", Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        open_devnull(b, "x1.rs:1", fd);
        b.if_(
            "x1.rs:2 if untracked()",
            Cond::Nondet,
            |b| {
                if then_closes {
                    close(b, "x1.rs:3", fd);
                }
            },
            |b| {
                if els_closes {
                    close(b, "x1.rs:5", fd);
                }
            },
        );
        b.spawn(
            "x1.rs:9",
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
    p.build()
}

#[test]
fn a_refutation_through_an_undecided_guard_replays_and_lists_the_choice() {
    let d = derive_ok(&guarded_close(true, false));
    assert!(
        d.notes().iter().any(|n| n.contains("over-approximation") && n.contains("x1.rs:2")),
        "the model's notes disclose the guard: {:?}",
        d.notes()
    );
    // Every choice step has an event-map entry at the branch.
    let nondet: Vec<_> = d.event_map().values().filter(|i| i.text.contains('?')).collect();
    assert_eq!(nondet.len(), 2, "one action per arm: {:?}", d.event_map().keys());
    assert!(nondet.iter().all(|i| i.events[0].loc == "x1.rs:2 if untracked()"));

    let r = refuted(&d, &fd_inherit_formula(&[]), "fd_inherit_violation");
    assert_eq!(r.overapprox.len(), 1, "{:?}", r.overapprox);
    let choice = &r.overapprox[0];
    assert!(!choice.then, "the leak is on the else-arm: {choice}");
    assert_eq!(choice.loc, "x1.rs:2 if untracked()");
    assert!(lines(&r).iter().any(|l| l.contains("else-arm")), "{:#?}", lines(&r));
    assert!(
        r.violations.iter().any(|v| format!("{v:?}").contains("devnull")),
        "{:?}",
        r.violations
    );
}

#[test]
fn an_undecided_guard_with_both_arms_safe_is_not_refuted() {
    not_refuted(&derive_ok(&guarded_close(true, true)));
}

/// The same leak with no guard at all: the refutation takes no choice, so
/// it is an error candidate (C-9 admits it).
#[test]
fn a_refutation_that_takes_no_choice_lists_none() {
    let mut p = ProgramBuilder::new("plain_leak");
    p.disclose("Historical guard/replay fixture: the Command selects CommandStd::Upstream and retains explicit inherit_all_fds and leaks without making a guard choice.");
    let fd = p.var("fd", -1);
    let site = p.site("child", "x1.rs:9", Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        open_devnull(b, "x1.rs:1", fd);
        b.spawn(
            "x1.rs:9",
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
    let r = refuted(&derive_ok(&p.build()), &fd_inherit_formula(&[]), "fd_inherit_violation");
    assert!(r.overapprox.is_empty(), "{:?}", r.overapprox);
}

/// An undecided guard in `pre_exec` code: the forked child stops at it
/// (ending its macro step), takes the choice as a step of its own before
/// anyone else moves, and resumes. The leak (the else-arm skips the
/// `FD_CLOEXEC`) is refuted, replayed, and the child's choice listed.
#[test]
fn a_choice_inside_a_forked_child_splits_its_macro_step_and_replays() {
    let mut p = ProgramBuilder::new("pre_exec_choice");
    p.disclose("Historical guard/replay fixture: the Command selects CommandStd::Upstream and retains explicit inherit_all_fds so the hook's choice determines whether it leaks.");
    let fd = p.var("fd", -1);
    let site = p.site("child", "x1.rs:9", Some(FdInherit { lanes: Vec::new() }));
    let hook = p.body("pre_exec", Vec::new(), |b| {
        b.when("x1.rs:20 if untracked()", Cond::Nondet, |b| {
            b.event(
                "x1.rs:21",
                "fcntl",
                Call::Fcntl { fd: Operand::Var(fd), cmd: darwin::F_SETFD, arg: darwin::FD_CLOEXEC },
                Bind::none(),
            );
        });
        b.ret("x1.rs:22", Some(Operand::Lit(0)));
    });
    let main = p.body("main", Vec::new(), |b| {
        open_devnull(b, "x1.rs:1", fd);
        b.spawn(
            "x1.rs:9",
            [StdioPlan::Inherit; 3],
            CommandShape {
                inherit_all_fds: true,
                ..CommandShape::with_pre_exec().under(CommandStd::Upstream)
            },
            vec![hook],
            site,
            None,
        );
    });
    p.root("main", main);
    let d = derive_ok(&p.build());
    let r = refuted(&d, &fd_inherit_formula(&[]), "fd_inherit_violation");
    assert_eq!(r.overapprox.len(), 1, "{:?}", r.overapprox);
    assert!(r.overapprox[0].actor.starts_with("child["), "{}", r.overapprox[0]);
    assert!(!r.overapprox[0].then);

    // With the then-arm only (the program always marks it), nothing leaks.
    let mut q = ProgramBuilder::new("pre_exec_always");
    q.disclose("Historical guard/replay safe twin: the Command selects CommandStd::Upstream and retains explicit inherit_all_fds; every hook arm must prevent its own leak.");
    let fd = q.var("fd", -1);
    let site = q.site("child", "x1.rs:9", Some(FdInherit { lanes: Vec::new() }));
    let hook = q.body("pre_exec", Vec::new(), |b| {
        b.if_(
            "x1.rs:20 if untracked()",
            Cond::Nondet,
            |b| {
                b.event(
                    "x1.rs:21",
                    "fcntl",
                    Call::Fcntl {
                        fd: Operand::Var(fd),
                        cmd: darwin::F_SETFD,
                        arg: darwin::FD_CLOEXEC,
                    },
                    Bind::none(),
                );
            },
            |b| close(b, "x1.rs:23", fd),
        );
        b.ret("x1.rs:22", Some(Operand::Lit(0)));
    });
    let main = q.body("main", Vec::new(), |b| {
        open_devnull(b, "x1.rs:1", fd);
        b.spawn(
            "x1.rs:9",
            [StdioPlan::Inherit; 3],
            CommandShape {
                inherit_all_fds: true,
                ..CommandShape::with_pre_exec().under(CommandStd::Upstream)
            },
            vec![hook],
            site,
            None,
        );
    });
    q.root("main", main);
    not_refuted(&derive_ok(&q.build()));
}

/// `spawnfd::platform::check` as the producer lowers it for aterm-uds
/// (`scratchpad/trustc-platform/out/uds-dump/ir/aterm_uds.trust-ir.txt`,
/// lines 2231-2249, aterm `4ba80b2b6`):
///
/// ```text
/// rustcc fn @"spawnfd::platform::check"(functy.51) {
/// bb0(%0: i32):
///     %2 = const i32 0  ; #loc: 11 641 17
///     %3 = icmp eq i32 %0, %2  ; #loc: 11 641 11
///     condbr %3, bb1, bb2  ; #loc: 11 641 8
/// bb1:
///     %4 = const enum.17 { 0, phantomdata }  ; #loc: 11 642 12
///     br bb3(%4)  ; #loc: 11 641 8
/// bb2:
///     %5 = call @func.290(%0)  ; #loc: 11 644 16
///     %6 = const enum.17 { 1, { { { 0 }, {  } } } }  ; #loc: 11 644 12
///     %7 = insertfield enum.17 %6, 1, %5  ; #loc: 11 644 12
///     br bb3(%7)  ; #loc: 11 641 8
/// bb3(%1: enum.17):
///     ret %1  ; #loc: 11 646 5
/// }
/// ```
///
/// `func.290` is `std::io::Error::from_raw_os_error`: an untracked value.
/// `io::Result<()>` is flattened to its tag and its `Err` payload, and the
/// block parameter `%1` gets a parallel copy on each incoming edge (design
/// §2.3). Written here as the census will write it. The call sites are
/// synthetic: `check(fcntl(99, F_GETFD))` takes the `Err` arm at run time
/// (fd 99 is closed), `check(fcntl(0, F_GETFD))` the `Ok` arm, which guards
/// a spawn.
fn check_program(close_the_error: bool) -> EventProgram {
    let mut p = ProgramBuilder::new("platform_check");
    let rc = p.var("check:%0", -1);
    let tag = p.var("check:%1.tag", -1);
    let payload = p.var("check:%1.err", -1);
    let err = p.var("check:%5", -1);
    let bad_flags = p.var("caller:bad_rc", -1);
    let bad = p.var("caller:bad", -1);
    let flags = p.var("caller:rc", -1);
    let ok = p.var("caller:ok", -1);
    let at = |line: u32, col: u32| {
        format!("aterm@4ba80b2b6:crates/aterm-uds/src/spawnfd.rs:{line}:{col}")
    };
    let check = p.body("spawnfd::platform::check", vec![rc], |b| {
        b.if_(
            &at(641, 8),
            Cond::eq(Operand::Var(rc), Operand::Lit(0)),
            |b| b.assign(&at(642, 12), tag, Expr::Use(Operand::Lit(0))),
            |b| {
                b.assign(&at(644, 16), err, Expr::Opaque);
                b.assign(&at(644, 12), tag, Expr::Use(Operand::Lit(1)));
                b.assign(&at(644, 12), payload, Expr::Use(Operand::Var(err)));
            },
        );
        b.ret(&at(646, 5), Some(Operand::Var(tag)));
    });
    let site = p.site("child", "caller:3", Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("caller", Vec::new(), |b| {
        b.event(
            "caller:0",
            "fcntl",
            Call::Fcntl { fd: Operand::Lit(99), cmd: darwin::F_GETFD, arg: 0 },
            Bind::ret(bad_flags),
        );
        b.call("caller:0b", check, vec![(rc, Operand::Var(bad_flags))], Some(bad));
        if close_the_error {
            close(b, "caller:0c", payload);
        }
        b.event(
            "caller:1",
            "fcntl",
            Call::Fcntl { fd: Operand::Lit(0), cmd: darwin::F_GETFD, arg: 0 },
            Bind::ret(flags),
        );
        b.call("caller:2", check, vec![(rc, Operand::Var(flags))], Some(ok));
        b.when("caller:3", Cond::eq(Operand::Var(ok), Operand::Lit(0)), |b| {
            b.spawn(
                "caller:3",
                [StdioPlan::Inherit; 3],
                CommandShape::default().under(CommandStd::Upstream),
                Vec::new(),
                site,
                None,
            );
        });
    });
    p.root("caller", main);
    p.build()
}

#[test]
fn an_untracked_error_payload_that_reaches_nothing_changes_nothing() {
    let d = derive_ok(&check_program(false));
    assert!(d.notes().iter().any(|n| n.contains("untracked values")), "{:?}", d.notes());
    // The Err arm ran: some explored state holds the untracked payload.
    let payload = d.core().prog.var_id("check:%1.err").expect("var");
    assert!(
        d.graph().configs.iter().any(|c| c.actors.iter().any(|a| a.vars[payload] == OPAQUE_VALUE)),
        "the Err arm never ran"
    );
    not_refuted(&d);
}

#[test]
fn an_untracked_value_used_as_a_descriptor_is_the_named_refusal() {
    match derive(&check_program(true), &env(), &DeriveOptions::default()) {
        Err(DeriveError::Lower(LowerError::Untracked { var, used_as, loc, origin })) => {
            assert_eq!(var, "check:%1.err");
            assert!(used_as.contains("operand 0 of `close`"), "{used_as}");
            assert_eq!(loc.0, "caller:0c");
            assert!(origin.0.ends_with("spawnfd.rs:644:16"), "{origin}");
        }
        Err(e) => panic!("expected LowerError::Untracked, got {e}"),
        Ok(_) => panic!("an untracked descriptor operand was admitted"),
    }
}

/// An untracked value read by a guard that was NOT written `Nondet` is
/// refused as well (the census must say the guard is undecided).
#[test]
fn an_untracked_guard_must_be_nondet() {
    let mut p = ProgramBuilder::new("untracked_guard");
    let x = p.var("x", 0);
    let site = p.site("child", "x1.rs:9", Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        b.assign("x1.rs:1", x, Expr::Opaque);
        b.when("x1.rs:2", Cond::eq(Operand::Var(x), Operand::Lit(0)), |b| {
            b.spawn(
                "x1.rs:9",
                [StdioPlan::Inherit; 3],
                CommandShape::default().under(CommandStd::Upstream),
                Vec::new(),
                site,
                None,
            );
        });
    });
    p.root("main", main);
    assert!(matches!(
        derive(&p.build(), &env(), &DeriveOptions::default()),
        Err(DeriveError::Lower(LowerError::Untracked { .. }))
    ));
}

/// The census review's F4 on M2's split `posix_spawn` (the merge of
/// `census/c0` onto M2). A program under an M2 policy spawns in two halves
/// (`SpawnBegin`, then the file actions at `SpawnEnd`), and the child's
/// declared lanes are computed at the first half. `adddup2(src, 3)` with
/// `POSIX_SPAWN_CLOEXEC_DEFAULT` leaves the child exactly fd 3: when `src` is
/// the RL-INIT foreign descriptor the program never created, that is a leak
/// (refuted, replayed); when it is the program's own description, it is a
/// declared lane (not refuted, not vacuous).
#[test]
fn f4_a_foreign_description_placed_by_a_split_posix_spawn_declares_no_lane() {
    let build = |own: bool| {
        let mut p =
            ProgramBuilder::new(if own { "split_spawn_own" } else { "split_spawn_foreign" });
        let fd = p.var("fd", -1);
        let pid = p.var("pid", -1);
        let site = p.site("child", "f4.rs:9", Some(FdInherit { lanes: Vec::new() }));
        let main = p.body("main", Vec::new(), |b| {
            let src = if own {
                open_devnull(b, "f4.rs:1", fd);
                Operand::Var(fd)
            } else {
                Operand::Lit(5)
            };
            b.event_full(
                "f4.rs:9 posix_spawn(adddup2(src, 3), CLOEXEC_DEFAULT)",
                "posix_spawn",
                Call::Spawn {
                    actions: vec![FileAction::Dup2 { from: src, to: Operand::Lit(3) }],
                    flags: darwin::POSIX_SPAWN_CLOEXEC_DEFAULT,
                },
                Bind::ret(pid),
                vec![Oracle::Nominal],
                Some(site),
                Vec::new(),
            );
        });
        p.root("main", main);
        // Any M2 policy makes the program M2-shaped: the spawn is split.
        p.lock_release_policy();
        p.build()
    };
    let env = EnvSpec { foreign: true, ..env() };
    let derive_env = |p: &EventProgram| {
        derive(p, &env, &DeriveOptions::default())
            .unwrap_or_else(|e| panic!("{}: derivation failed: {e}", p.name))
    };
    for own in [false, true] {
        let d = derive_env(&build(own));
        assert!(
            d.event_map().values().any(|i| i.text.contains("~resume")),
            "{}: the spawn must be split (SpawnBegin, then SpawnEnd): {:?}",
            d.name(),
            d.event_map().keys()
        );
        if own {
            not_refuted(&d);
        } else {
            let r = refuted(&d, &fd_inherit_formula(&[]), "fd_inherit_violation");
            assert!(
                r.violations.iter().any(|v| format!("{v:?}").contains("foreign")),
                "the foreign description leaks at 3: {:?}",
                r.violations
            );
        }
    }
}
