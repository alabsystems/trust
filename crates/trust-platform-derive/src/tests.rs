//! Unit tests of the derivation pieces (the ty-checked acceptance is
//! `tests/acceptance.rs`).

use std::collections::{BTreeSet, VecDeque};

use trust_platform::{Call, Oracle, darwin};

use crate::derive::{DeriveOptions, Derived, HALT, derive};
use crate::env::{EnvSpec, Limits};
use crate::lower::{LowerError, lower};
use crate::partition::Partition;
use crate::program::{Bind, FdInherit, Operand, ProgramBuilder, StmtKind};
use crate::{fixtures, property};

/// States of the machine reachable from `rl_init` carrying `atom`.
fn reachable_with(d: &Derived, atom: &str) -> usize {
    let n = d.machine.states.len();
    let mut succ = vec![Vec::new(); n];
    for (f, _, t) in &d.machine.transitions {
        succ[*f].push(*t);
    }
    let mut seen = vec![false; n];
    let mut q = VecDeque::from([0usize]);
    seen[0] = true;
    let mut hits = 0;
    while let Some(s) = q.pop_front() {
        if d.machine.labels.get(&s).is_some_and(|l| l.iter().any(|x| x == atom)) {
            hits += 1;
        }
        for t in &succ[s] {
            if !seen[*t] {
                seen[*t] = true;
                q.push_back(*t);
            }
        }
    }
    hits
}

#[test]
fn every_fixture_derives_and_the_verdict_atoms_are_where_the_plan_says() {
    for f in fixtures::all() {
        let d = derive(&f.program, &f.env, &DeriveOptions::default())
            .unwrap_or_else(|e| panic!("{}: {e}", f.name));
        let bad = reachable_with(&d, &property::premised(property::VIOLATION, &f.premises));
        assert_eq!(bad > 0, f.expect_refuted, "{}: {} bad states; {:?}", f.name, bad, d.stats);
        let exec = property::premised(property::POLICY_EXEC, &f.premises);
        assert!(reachable_with(&d, &exec) > 0, "{}: no policy exec", f.name);
        assert!(d.stats.encoding_exact, "{}: scalar encoding not injective", f.name);
        println!("{}: {:?}", f.name, d.stats);
    }
}

#[test]
fn every_machine_action_is_in_the_event_map() {
    let f = fixtures::spawnfd::strip_first_premise();
    let d = derive(&f.program, &f.env, &DeriveOptions::default()).expect("derives");
    let labels: BTreeSet<&str> = d.machine.transitions.iter().map(|(_, l, _)| l.as_str()).collect();
    for l in labels {
        let info = d.event_map.get(l).unwrap_or_else(|| panic!("{l} has no event-map entry"));
        assert!(!info.events.is_empty());
        for e in &info.events {
            assert!(!e.loc.is_empty(), "{l}: an event without a location");
        }
    }
}

#[test]
fn an_unmodeled_symbol_is_a_named_refusal() {
    // `flock` is modeled since M2; `kevent` is still a named gap.
    let mut p = ProgramBuilder::new("kevent_user");
    let fd = p.var("fd", 3);
    let body = p.body("main", Vec::new(), |b| {
        b.event("x.rs:1", "kevent", Call::Close { fd: Operand::Var(fd) }, Bind::none());
    });
    p.root("main", body);
    match lower(&p.build()) {
        Err(LowerError::Unmodeled { effect, .. }) => assert_eq!(effect.symbol, "kevent"),
        other => panic!("expected an UnmodeledPlatformEffect, got {other:?}"),
    }
}

#[test]
fn a_symbol_naming_another_clause_is_refused() {
    let mut p = ProgramBuilder::new("mismatch");
    let fd = p.var("fd", 3);
    let body = p.body("main", Vec::new(), |b| {
        b.event("x.rs:1", "dup2", Call::Close { fd: Operand::Var(fd) }, Bind::none());
    });
    p.root("main", body);
    assert!(matches!(lower(&p.build()), Err(LowerError::SymbolMismatch { .. })));
}

/// RL-INIT places a foreign descriptor at every point of the partition and
/// on both sides of it, and at every additive shift (the classes a program
/// can tell apart: below the strip's start, inside it, at its end).
#[test]
fn the_partition_offers_every_class_edge() {
    let p = Partition::new([3, 4, 5, 256, 65_536, 92_160], [-1]);
    assert_eq!(p.mid_lo(), 6);
    let pos = p.positions(3, 92_160, &[9]);
    for want in [3, 4, 5, 6, 9, 255, 256, 257, 65_535, 65_536, 65_537, 92_159] {
        assert!(pos.contains(&want), "{want} missing from {pos:?}");
    }
    assert!(!pos.contains(&92_160), "at the allocation limit");
    assert!(!pos.contains(&2), "below 3");
}

/// The strip loop (one SD-3 step) does exactly what its 65 533 `fcntl`
/// calls do one by one on the platform model, at the real constants.
#[test]
fn the_strip_step_equals_the_unrolled_loop_on_the_platform_model() {
    use trust_platform::{Access, Host, OfdKind, Rlimit};
    let mut h = Host::new(92_160);
    let root = h.add_root(Rlimit { soft: 1_048_576, hard: darwin::RLIM_INFINITY });
    for fd in [0, 1, 2, 5, 9, 70, 65_535, 65_536] {
        h.install_fresh(root, fd, OfdKind::Opaque, Access::ReadWrite, 0, false).expect("install");
    }
    let fork = trust_platform::step(&h, root, &Call::Fork, Oracle::Nominal).expect("fork");
    let child = match fork.result {
        Ok(trust_platform::Ret::Int(n)) => trust_platform::Pid(u32::try_from(n).unwrap_or(0)),
        other => panic!("{other:?}"),
    };
    let mut unrolled = fork.host.clone();
    for fd in 3..65_536 {
        let call = Call::Fcntl { fd, cmd: darwin::F_SETFD, arg: darwin::FD_CLOEXEC };
        unrolled =
            trust_platform::step(&unrolled, child, &call, Oracle::Nominal).expect("fcntl").host;
    }
    let flags: Vec<(i32, bool)> =
        unrolled.proc(child).expect("child").table.iter().map(|(fd, e)| (*fd, e.cloexec)).collect();
    assert_eq!(
        flags,
        vec![
            (0, false),
            (1, false),
            (2, false),
            (5, true),
            (9, true),
            (70, true),
            (65_535, true),
            (65_536, false)
        ]
    );
}

/// Verdicts must be deterministic (D-15(D5)): deriving twice gives the
/// same transported bytes.
#[test]
fn the_derivation_is_deterministic() {
    let f = fixtures::spawnfd::no_strip();
    let once = |_: ()| {
        derive(&f.program, &f.env, &DeriveOptions::default())
            .expect("derives")
            .payload(&property::fd_inherit_formula(&[]))
            .expect("a vetted formula")
            .to_metadata_value()
            .expect("serializes")
    };
    assert_eq!(once(()), once(()));
}

/// The strip loop's fast path (one execution per gap of closed slots) gives
/// exactly the table the full 65 533-iteration loop gives, on tables with
/// descriptors at the gap edges, and a loop body that is not uniform runs
/// every iteration.
#[test]
fn the_strip_fast_path_equals_every_iteration() {
    use trust_platform::std_summaries::StdioPlan;
    use trust_platform::{Call, darwin};
    for strip_hi in [65_536i64, 300, 7] {
        let mut p = ProgramBuilder::new("strip");
        let fd = p.var("fd", -1);
        let x = p.var("x", -1);
        let one = p.body("one", Vec::new(), |b| {
            b.event(
                "s.rs:1",
                "fcntl",
                Call::Fcntl { fd: Operand::Var(fd), cmd: darwin::F_SETFD, arg: darwin::FD_CLOEXEC },
                Bind::none(),
            );
        });
        let closure = p.body("pre_exec", Vec::new(), |b| {
            b.for_range("s.rs:2", fd, Operand::Lit(3), Operand::Lit(strip_hi), one);
            b.ret("s.rs:3", Some(Operand::Lit(0)));
        });
        let site = p.site("child", "s.rs:4", Some(FdInherit { lanes: Vec::new() }));
        let main = p.body("main", Vec::new(), |b| {
            for floor in [5i64, 299, 300, 65_535, 65_536, 70_000] {
                b.event(
                    "s.rs:5",
                    "fcntl",
                    Call::Fcntl { fd: Operand::Lit(0), cmd: darwin::F_DUPFD, arg: floor },
                    Bind::ret(x),
                );
            }
            // Isolate this loop under the historical upstream std contract;
            // retain its opt-out premise and exact unrolled-loop table oracle.
            b.spawn(
                "s.rs:6",
                [StdioPlan::Inherit; 3],
                trust_platform::std_summaries::CommandShape {
                    inherit_all_fds: true,
                    ..trust_platform::std_summaries::CommandShape::with_pre_exec()
                        .under(trust_platform::std_summaries::CommandStd::Upstream)
                },
                vec![closure],
                site,
                None,
            );
        });
        p.root("main", main);
        let env = EnvSpec {
            limits: Limits::measured_darwin(),
            param_slots: Vec::new(),
            foreign: false,
            foreign_at: Vec::new(),
            fd_bound_cap: None,
            names: Vec::new(),
        };
        let d = derive(&p.build(), &env, &DeriveOptions::default()).expect("derives");
        // The child's table at exec, from the explored model ...
        let exec = d
            .graph
            .configs
            .iter()
            .find_map(|c| {
                c.spawns.iter().find(|r| r.execd).and_then(|r| c.host.proc(r.pid)).cloned()
            })
            .expect("the child execs");
        // ... against the unrolled loop on the platform model.
        let held: Vec<i32> = exec.table.keys().copied().collect();
        let want: Vec<i32> = [0, 1, 2, 5, 299, 300, 65_535, 65_536, 70_000]
            .into_iter()
            .filter(|fd| *fd < 3 || i64::from(*fd) >= strip_hi)
            .collect();
        assert_eq!(held, want, "strip 3..{strip_hi}");
    }
}

// ---- M2: P-LOCK-RELEASE, fd-identity, threads --------------------------------------

fn m2_env() -> EnvSpec {
    fixtures::m2_env(&[("/dev/null", trust_platform::NodeKind::CharDevice)])
}

/// A named open of `path` in a canonical test directory (the namespace takes
/// one absolute spelling per file).
fn open_named(path: &str, flags: i32) -> Call<Operand> {
    let path = if path.starts_with('/') {
        path.to_string()
    } else {
        format!("/private/tmp/derive-unit/{path}")
    };
    Call::OpenPath { at: None, path, flags }
}

#[test]
fn m2_atoms_exist_only_under_their_policy() {
    // An M1 program's vocabulary has no M2 atom, so a misspelt policy is a
    // refused formula, never a vacuous pass.
    let f = fixtures::spawnfd::no_strip();
    let d = derive(&f.program, &f.env, &DeriveOptions::default()).expect("derives");
    assert!(d.payload(&property::lock_release_formula()).is_err());
    assert!(d.payload(&property::fd_identity_formula()).is_err());
    let o = fixtures::ownerlock::bare_close();
    let d = derive(&o.program, &o.env, &DeriveOptions::default()).expect("derives");
    assert!(d.payload(&property::lock_release_formula()).is_ok());
    assert!(d.payload(&property::fd_identity_formula()).is_err());
}

#[test]
fn an_unflagged_locked_descriptor_lives_on_in_the_exec_d_image() {
    // P-LOCK-RELEASE across exec: the child's copy survives an exec without
    // O_CLOEXEC, so the exec'd image holds the lock after the owner's close.
    let build = |cloexec: bool| {
        let mut p = ProgramBuilder::new("exec_keeps_lock");
        p.lock_release_policy();
        let fd = p.var("fd", -1);
        let pid = p.var("pid", -1);
        let site = p.site("child", "x.rs:3", None);
        let child = p.body("child", Vec::new(), |b| {
            b.event("x.rs:4", "execve", Call::Exec, Bind::none());
        });
        let flags =
            darwin::O_RDONLY | darwin::O_CREAT | if cloexec { darwin::O_CLOEXEC } else { 0 };
        let main = p.body("main", Vec::new(), |b| {
            b.event_full(
                "x.rs:1",
                "open",
                open_named("f", flags),
                Bind::ret(fd),
                vec![Oracle::Nominal],
                None,
                vec!["f"],
            );
            b.event(
                "x.rs:2",
                "flock",
                Call::Flock { fd: Operand::Var(fd), op: darwin::LOCK_EX },
                Bind::none(),
            );
            b.fork("x.rs:3", child, site, Some(pid));
            b.event("x.rs:5", "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
            b.release("x.rs:5", &["f"]);
        });
        p.root("main", main);
        p.build()
    };
    for (cloexec, leaks) in [(false, true), (true, true)] {
        // Even close-on-exec leaks: the child may still be between its fork
        // and its exec when the owner closes (the split point at exec).
        let d = derive(&build(cloexec), &m2_env(), &DeriveOptions::default()).expect("derives");
        assert_eq!(reachable_with(&d, property::LOCK_LEAK) > 0, leaks, "cloexec {cloexec}");
    }
    // With LOCK_UN before the close, neither leaks.
    let mut prog = build(false);
    let fd = prog.var_id("fd").expect("fd");
    let at = prog
        .stmts()
        .find(|(_, s)| matches!(s.kind, crate::program::StmtKind::Event(ref e) if matches!(e.call, Call::Close { .. })))
        .map(|(at, _)| at)
        .expect("the close");
    prog.bodies[at.body].blocks[at.block].stmts.insert(
        at.idx,
        crate::program::Stmt {
            kind: crate::program::StmtKind::Event(crate::program::Event {
                symbol: "flock".into(),
                call: Call::Flock { fd: Operand::Var(fd), op: darwin::LOCK_UN },
                bind: Bind::none(),
                oracles: vec![Oracle::Nominal],
                site: None,
                ofd_names: Vec::new(),
                std_origin: None,
                path: None,
                assumption: None,
            }),
            loc: crate::program::Loc::new("x.rs:5"),
            tag: None,
        },
    );
    let d = derive(&prog, &m2_env(), &DeriveOptions::default()).expect("derives");
    assert_eq!(reachable_with(&d, property::LOCK_LEAK), 0);
    assert!(reachable_with(&d, property::RELEASED_SHARED) > 0, "non-vacuous");
}

#[test]
fn fd_identity_binds_closes_and_exempts_fstat() {
    // main: open a file (fd 3), close it, then act on 3. A second thread
    // opens /dev/null. Acting with F_GETFD after the reuse is a violation;
    // asking fstat is not; acting on a number main never bound observes it.
    let build = |probe: Call<Operand>| {
        let mut p = ProgramBuilder::new("identity");
        let fd = p.var("fd", -1);
        let sq = p.var("sq", -1);
        let main = p.body("main", Vec::new(), |b| {
            b.event_full(
                "x.rs:1",
                "open",
                open_named("f", darwin::O_RDONLY | darwin::O_CREAT),
                Bind::ret(fd),
                vec![Oracle::Nominal],
                None,
                vec!["f"],
            );
            b.event("x.rs:2", "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
            b.event("x.rs:3", probe.symbol(), probe.clone(), Bind::none());
        });
        let other = p.body("other", Vec::new(), |b| {
            b.event_full(
                "y.rs:1",
                "open",
                open_named("/dev/null", darwin::O_RDONLY),
                Bind::ret(sq),
                vec![Oracle::Nominal],
                None,
                vec!["squatter"],
            );
        });
        let r = p.root("main", main);
        p.root("other", other);
        p.fd_identity_policy(&[r]);
        p.build()
    };
    let getfd = Call::Fcntl { fd: Operand::Var(0), cmd: darwin::F_GETFD, arg: 0 };
    let d = derive(&build(getfd), &m2_env(), &DeriveOptions::default()).expect("derives");
    assert!(reachable_with(&d, property::FD_IDENTITY_VIOLATION) > 0);
    assert!(reachable_with(&d, property::NUMBER_REUSED) > 0);
    let d =
        derive(&build(Call::Fstat { fd: Operand::Var(0) }), &m2_env(), &DeriveOptions::default())
            .expect("derives");
    assert_eq!(reachable_with(&d, property::FD_IDENTITY_VIOLATION), 0);
    assert!(reachable_with(&d, property::NUMBER_REUSED) > 0, "non-vacuous");
    // A number main never bound (7): its first observation binds it.
    let d = derive(
        &build(Call::Fcntl { fd: Operand::Lit(7), cmd: darwin::F_GETFD, arg: 0 }),
        &m2_env(),
        &DeriveOptions::default(),
    )
    .expect("derives");
    assert_eq!(reachable_with(&d, property::FD_IDENTITY_VIOLATION), 0);
}

#[test]
fn a_dormant_thread_starts_at_its_spawn_with_the_spawners_variables_and_join_waits() {
    let mut p = ProgramBuilder::new("threads");
    p.lock_release_policy();
    let fd = p.var("fd", -1);
    let done = p.var("done", 0);
    let t = p.body("t", Vec::new(), |b| {
        // Uses the spawner's `fd` value: a copy of its variables.
        b.event("t.rs:1", "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
    });
    let tid = p.thread("t", t);
    let main = p.body("main", Vec::new(), |b| {
        b.event_full(
            "m.rs:1",
            "open",
            open_named("f", darwin::O_RDONLY | darwin::O_CREAT),
            Bind::ret(fd),
            vec![Oracle::Nominal],
            None,
            vec!["f"],
        );
        b.spawn_thread("m.rs:2", tid);
        b.join("m.rs:3", tid);
        b.assign("m.rs:4", done, crate::program::Expr::Use(Operand::Lit(1)));
    });
    p.root("main", main);
    let prog = p.build();
    let d = derive(&prog, &m2_env(), &DeriveOptions::default()).expect("derives");
    // Every finished state: main joined after t closed fd 3 (it is gone).
    let ends: Vec<_> = d
        .graph
        .configs
        .iter()
        .filter(|c| c.actors.iter().all(crate::interp::Actor::done))
        .collect();
    assert!(!ends.is_empty());
    for c in ends {
        assert!(c.host.proc(trust_platform::Pid(1)).is_some_and(|p| !p.table.contains_key(&3)));
        assert_eq!(c.host.proc(trust_platform::Pid(1)).map(|p| p.threads), Some(2));
    }
    // Before the spawn, t does not exist.
    let init = &d.graph.configs[d.graph.inits[0].1];
    assert_eq!(init.actors.len(), 1);
}

#[test]
fn m2_census_refuses_what_it_cannot_name() {
    // A release of a class nothing allocates is a typo, not a vacuous pass.
    let mut p = ProgramBuilder::new("typo");
    let main = p.body("main", Vec::new(), |b| b.release("x.rs:1", &["nothing"]));
    p.root("main", main);
    assert!(matches!(lower(&p.build()), Err(LowerError::Malformed(_))));
    // A raw read without the census's statement of its effect is refused.
    let mut p = ProgramBuilder::new("raw_read");
    let main = p.body("main", Vec::new(), |b| {
        b.event("x.rs:1", "read", Call::ReadSome { fd: Operand::Lit(0) }, Bind::none());
    });
    p.root("main", main);
    assert!(matches!(lower(&p.build()), Err(LowerError::Unmodeled { .. })));
}

/// False-pass guards for the M2 properties.
#[test]
fn m2_adversarial_guards() {
    // (1) A release mark placed BEFORE the bare close still catches the leak:
    // released classes are sticky, the leak appears once the owner's last
    // reference goes. (2) A lock taken by O_EXLOCK leaks the same way.
    for (mark_first, exlock) in [(true, false), (false, true)] {
        let mut p = ProgramBuilder::new("guard");
        p.lock_release_policy();
        let fd = p.var("fd", -1);
        let pid = p.var("pid", -1);
        let site = p.site("child", "x.rs:3", None);
        let child = p.body("child", Vec::new(), |b| {
            b.event("x.rs:4", "execve", Call::Exec, Bind::none());
        });
        let flags = darwin::O_RDONLY
            | darwin::O_CREAT
            | darwin::O_CLOEXEC
            | if exlock { darwin::O_EXLOCK } else { 0 };
        let main = p.body("main", Vec::new(), |b| {
            b.event_full(
                "x.rs:1",
                "open",
                open_named("f", flags),
                Bind::ret(fd),
                vec![Oracle::Nominal],
                None,
                vec!["f"],
            );
            if !exlock {
                b.event(
                    "x.rs:2",
                    "flock",
                    Call::Flock { fd: Operand::Var(fd), op: darwin::LOCK_EX },
                    Bind::none(),
                );
            }
            if mark_first {
                b.release("x.rs:5", &["f"]);
            }
            b.event("x.rs:5", "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
            if !mark_first {
                b.release("x.rs:5", &["f"]);
            }
        });
        let sib = p.body("sibling", Vec::new(), |b| b.fork("x.rs:3", child, site, Some(pid)));
        p.root("main", main);
        p.root("sibling", sib);
        let d = derive(&p.build(), &m2_env(), &DeriveOptions::default()).expect("derives");
        assert!(
            reachable_with(&d, property::LOCK_LEAK) > 0,
            "mark_first {mark_first} exlock {exlock}: the leak must be reachable"
        );
    }
    // (3) fd-identity through dup2: main closes its number, a stranger takes
    // it, main dup2s onto it believing it closed — closing the stranger's.
    let mut p = ProgramBuilder::new("dup2_onto_stranger");
    let fd = p.var("fd", -1);
    let keep = p.var("keep", -1);
    let sq = p.var("sq", -1);
    let main = p.body("main", Vec::new(), |b| {
        b.event_full(
            "m.rs:1",
            "open",
            open_named("a", darwin::O_RDONLY | darwin::O_CREAT),
            Bind::ret(keep),
            vec![Oracle::Nominal],
            None,
            vec!["a"],
        );
        b.event_full(
            "m.rs:2",
            "open",
            open_named("b", darwin::O_RDONLY | darwin::O_CREAT),
            Bind::ret(fd),
            vec![Oracle::Nominal],
            None,
            vec!["b"],
        );
        b.event("m.rs:3", "close", Call::Close { fd: Operand::Var(fd) }, Bind::none());
        b.event(
            "m.rs:4",
            "dup2",
            Call::Dup2 { from: Operand::Var(keep), to: Operand::Var(fd) },
            Bind::none(),
        );
    });
    let other = p.body("other", Vec::new(), |b| {
        b.event_full(
            "o.rs:1",
            "open",
            open_named("/dev/null", darwin::O_RDONLY),
            Bind::ret(sq),
            vec![Oracle::Nominal],
            None,
            vec!["squatter"],
        );
    });
    let r = p.root("main", main);
    p.root("other", other);
    p.fd_identity_policy(&[r]);
    let d = derive(&p.build(), &m2_env(), &DeriveOptions::default()).expect("derives");
    assert!(reachable_with(&d, property::FD_IDENTITY_VIOLATION) > 0);
}

// ---- L1c (X2): typed trace sites and the replay token ---------------------------

/// ty's counterexample to `formula` on `d` (the in-process `ty` primary,
/// through the typed refutation-only API the host reads).
fn ty_trace(d: &Derived, formula: &str) -> Vec<usize> {
    use trust_router::full_verification::{NativeTyEngine, RefutationOnlyVerdict};
    use trust_verifier_api::{MetadataEntry, ObligationKind, SourceLocation, TrustObligation};
    let payload = d.payload(formula).unwrap_or_else(|e| panic!("`{formula}`: {e}"));
    let obligation = TrustObligation {
        obligation_id: format!("vc:derive_unit::{}:temporal_safety:0", d.name),
        kind: ObligationKind::TemporalSafety,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: format!("unit `{formula}`"),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![MetadataEntry {
            key: trust_types::TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_metadata_value().expect("serializes"),
        }],
    };
    match NativeTyEngine::new().check_refutation_only(&obligation) {
        RefutationOnlyVerdict::Counterexample { trace } => trace,
        v => panic!("{}: `{formula}` must be refuted: {v:?}", d.name),
    }
}

/// The spawnfd fixture's refutation (`no_strip`) and its token.
fn spawnfd_refutation() -> (crate::fixtures::Fixture, Derived, Vec<usize>) {
    let f = fixtures::spawnfd::no_strip();
    assert!(f.expect_refuted);
    let d = derive(&f.program, &f.env, &DeriveOptions::default()).expect("derives");
    let trace = ty_trace(&d, &property::fd_inherit_formula(&f.premises));
    (f, d, trace)
}

/// Every Loc a statement of `p` carries, and every Loc a block terminator
/// carries.
fn program_locs(
    p: &crate::program::EventProgram,
) -> (BTreeSet<crate::program::Loc>, BTreeSet<crate::program::Loc>) {
    let blocks = || p.bodies.iter().flat_map(|b| &b.blocks);
    (
        blocks().flat_map(|k| k.stmts.iter().map(|s| s.loc.clone())).collect(),
        blocks().map(|k| k.term_loc.clone()).collect(),
    )
}

/// L1c: in the spawnfd fixture's refutation, every step's fired events are
/// typed sites parallel to its event lines; every non-environment site is a
/// position of the program whose Loc is a statement Loc of the fixture as
/// written; every environment step cites its RL clause; every std-origin
/// step cites its row.
#[test]
fn spawnfd_refutation_sites_are_program_locs_or_cited_environment_steps() {
    use crate::trace::{RL_CLAUSES, RL_INIT};
    let (f, d, trace) = spawnfd_refutation();
    let want = property::premised(property::VIOLATION, &f.premises);
    let token = d.replay_token(&trace, &[want.as_str()]).expect("the refutation mints a token");
    let r = token.replay();
    let (statements, terminators) = program_locs(&f.program);
    let (mut program, mut environment, mut std_rows) = (0, 0, 0);
    for (j, s) in r.steps.iter().enumerate() {
        assert_eq!(s.sites.len(), s.events.len(), "step {j}: sites are parallel to events");
        for site in &s.sites {
            if site.environment {
                environment += 1;
                assert!(site.at.is_none(), "step {j}: {site:?}");
                let clause = site.rl_clause.expect("an environment step cites its RL clause");
                assert!(RL_CLAUSES.contains(&clause), "{clause}");
                continue;
            }
            program += 1;
            let at = site.at.expect("a program step names its position");
            assert_eq!(d.core.prog.loc_at(at), Some(&site.loc), "step {j}: {at}");
            // A statement position carries a statement Loc of the fixture as
            // written; a terminator position (a guard's choice) a
            // terminator Loc.
            let terminator = d.core.prog.stmt(at).is_none();
            let written = if terminator { &terminators } else { &statements };
            assert!(
                written.contains(&site.loc),
                "step {j}: `{}` is no {} Loc of {}",
                site.loc,
                if terminator { "terminator" } else { "statement" },
                f.name
            );
            assert!(site.rl_clause.is_none(), "{site:?}");
            if site.std_row.is_some() {
                std_rows += 1;
            }
        }
    }
    // Not vacuous: the trace starts in RL-INIT, runs program code, and
    // reaches std's spawn rows.
    assert_eq!(r.steps[0].sites[0].rl_clause, Some(RL_INIT));
    assert!(environment > 0 && program > 0 && std_rows > 0, "{program} {environment} {std_rows}");
    assert_eq!(token.blocks(), trace.as_slice());
    assert_eq!(token.steps().len(), r.steps.len());
}

/// X2's three conditions are each load-bearing: a replay that breaks one
/// mints no token.
#[test]
fn a_replay_that_breaks_an_x2_condition_mints_no_token() {
    use crate::trace::TokenError;
    let (f, d, trace) = spawnfd_refutation();
    let want = property::premised(property::VIOLATION, &f.premises);
    let steps = d.explain(&trace).expect("explains");
    let replay = d.replay(&trace, &[want.as_str()]).expect("replays");
    d.check_x2(&steps, &replay).expect("the untouched replay holds X2");

    // (a) a step dropped, or a step whose events were not re-executed.
    let mut short = replay.clone();
    short.steps.pop();
    assert!(matches!(d.check_x2(&steps, &short), Err(TokenError::NotReexecuted { .. })));
    let mut hollow = replay.clone();
    let k = hollow.steps.iter().position(|s| !s.sites.is_empty()).expect("a step fires");
    hollow.steps[k].sites.clear();
    assert!(matches!(d.check_x2(&steps, &hollow), Err(TokenError::NotReexecuted { .. })));

    // (b) an environment step without its clause, or with one the
    // derivation does not implement.
    for clause in [None, Some("RL-MADE-UP")] {
        let mut uncited = replay.clone();
        let site = uncited
            .steps
            .iter_mut()
            .flat_map(|s| s.sites.iter_mut())
            .find(|s| s.environment)
            .expect("an environment step");
        site.rl_clause = clause;
        assert!(
            matches!(d.check_x2(&steps, &uncited), Err(TokenError::UncitedEnvironment { .. })),
            "{clause:?}"
        );
    }

    // (c) a std-origin step without its row.
    let mut rowless = replay.clone();
    let site = rowless
        .steps
        .iter_mut()
        .flat_map(|s| s.sites.iter_mut())
        .find(|s| s.std_row.is_some())
        .expect("a std-origin step");
    site.std_row = None;
    assert!(matches!(d.check_x2(&steps, &rowless), Err(TokenError::UncitedStdRow { .. })));

    // And a trace that does not reproduce the property mints nothing: a
    // name no state carries is no violation proposition (H3), and a real one
    // the final state lacks does not replay.
    assert!(matches!(
        d.replay_token(&trace, &["policy_exec_never_named"]),
        Err(TokenError::NotARefutation { .. })
    ));
    assert!(matches!(
        d.replay_token(&trace, &[property::LANE_CROSSED]),
        Err(TokenError::Replay(_))
    ));
}

// ---- Red-team holes H3 and H4 (L1c) --------------------------------------------

/// H3: a token witnesses a REFUTATION. Before the fix `replay_token` minted
/// one for every prefix of the refutation with nothing wanted, and for a
/// non-vacuity witness of the FIXED twin (`strip_first_premise`, NOT
/// refuted) wanting nothing or `policy_exec`.
#[test]
fn a_token_is_minted_only_for_a_refutation() {
    use crate::trace::TokenError;
    let (f, d, trace) = spawnfd_refutation();
    let want = property::premised(property::VIOLATION, &f.premises);
    for k in 1..=trace.len() {
        assert!(
            matches!(d.replay_token(&trace[..k], &[]), Err(TokenError::NotARefutation { .. })),
            "prefix {k}/{} with nothing wanted",
            trace.len()
        );
    }
    for k in 0..trace.len() {
        assert!(d.replay_token(&trace[..k], &[want.as_str()]).is_err(), "prefix {k}");
    }
    let token = d.replay_token(&trace, &[want.as_str()]).expect("the refutation mints");
    assert!(!token.replay().violations.is_empty());
    assert_eq!(token.want(), std::slice::from_ref(&want));

    let fixed = fixtures::spawnfd::strip_first_premise();
    assert!(!fixed.expect_refuted);
    let df = derive(&fixed.program, &fixed.env, &DeriveOptions::default()).expect("derives");
    let witness = ty_trace(&df, &property::non_vacuity_formula(&fixed.premises));
    let exec = property::premised(property::POLICY_EXEC, &fixed.premises);
    df.replay(&witness, &[exec.as_str()]).expect("the non-vacuity witness replays");
    for wanted in [&[][..], &[exec.as_str()][..], &[property::POLICY_EXEC][..]] {
        assert!(
            matches!(df.replay_token(&witness, wanted), Err(TokenError::NotARefutation { .. })),
            "the fixed twin's witness, wanting {wanted:?}"
        );
    }
    // Every violation atom is a refutation; every non-vacuity atom is not.
    for a in property::vocabulary(&d.core) {
        let violation = property::violation_atoms(&d.core).contains(&a);
        let non_vacuity = a.starts_with(property::POLICY_EXEC)
            || a == property::RELEASED_SHARED
            || a == property::NUMBER_REUSED;
        assert_eq!(violation, !non_vacuity, "{a}");
    }
}

/// H4 (C7d): a step relabelled as the horizon stutter re-executed nothing,
/// and the replay skipped it. `Derived`'s fields are read-only outside the
/// crate; inside it, a "stutter" that moves the machine is refused.
#[test]
fn a_relabelled_step_is_never_skipped() {
    use crate::trace::TokenError;
    let (f, d, trace) = spawnfd_refutation();
    let steps = d.explain(&trace).expect("explains");
    let last = steps.last().expect("a step").clone();
    assert_ne!(last.info.label, HALT);
    assert_ne!(last.from, last.to, "the last step is a real transition");
    let mut t = d.clone();
    t.event_map.get_mut(&last.info.label).expect("label").label = HALT.to_string();
    let tampered = t.explain(&trace).expect("explains");
    assert_eq!(tampered.last().map(|s| s.info.label.as_str()), Some(HALT));
    let replay = t.replay(&trace, &[]).expect("the edited replay skips the step");
    match t.check_x2(&tampered, &replay) {
        Err(TokenError::NotReexecuted { detail, .. }) => {
            assert!(detail.contains("stutter moves"), "{detail}");
        }
        other => panic!("a relabelled step passed X2 (a): {other:?}"),
    }
    let want = property::premised(property::VIOLATION, &f.premises);
    for wanted in [&[][..], &[want.as_str()][..]] {
        assert!(t.replay_token(&trace, wanted).is_err(), "{wanted:?}");
    }
}

/// H4 (C7a, C7b): a token records the program and environment it replayed
/// on, so one minted from an edited derivation (std rows erased, Locs
/// rewritten — edits only this crate can make) is never the original's.
#[test]
fn a_token_of_an_edited_derivation_is_not_the_original_s() {
    let (f, d, trace) = spawnfd_refutation();
    let want = property::premised(property::VIOLATION, &f.premises);
    let genuine = d.replay_token(&trace, &[want.as_str()]).expect("the refutation mints");
    assert!(genuine.is_of(&d));
    let rows = |t: &crate::trace::ReplayToken| {
        t.replay().steps.iter().flat_map(|s| &s.sites).filter(|s| s.std_row.is_some()).count()
    };
    assert!(rows(&genuine) > 0, "the refutation runs through std rows");
    let mut rowless = d.clone();
    let mut moved = d.clone();
    for (t, erase) in [(&mut rowless, true), (&mut moved, false)] {
        for body in &mut t.core.prog.bodies {
            for block in &mut body.blocks {
                for stmt in &mut block.stmts {
                    if erase {
                        match &mut stmt.kind {
                            StmtKind::Event(ev) => ev.std_origin = None,
                            StmtKind::Fork { std_origin, .. } => *std_origin = None,
                            _ => {}
                        }
                    } else {
                        stmt.loc.0 = "attacker.rs:1:1".to_string();
                    }
                }
                if !erase {
                    block.term_loc.0 = "attacker.rs:2:1".to_string();
                }
            }
        }
    }
    for (what, t) in [("std rows erased", &rowless), ("Locs rewritten", &moved)] {
        if let Ok(tok) = t.replay_token(&trace, &[want.as_str()]) {
            assert!(tok.is_of(t), "{what}");
            assert!(
                !tok.is_of(&d),
                "{what}: the edited derivation's token passes as the original's"
            );
        }
    }
}
