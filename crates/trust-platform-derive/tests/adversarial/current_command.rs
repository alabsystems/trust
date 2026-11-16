//! Current Trust rows through lowering, exploration, ty and authenticated replay.

use trust_platform::Ret;
use trust_platform_derive::program::{StdCall, StmtKind};
use trust_platform_derive::trace::{Replay, ReplayToken, TokenError};
use trust_router::full_verification::{RefutationCompleteness, RefutationOnlyVerdict};

use super::*;

fn checked_trace(d: &Derived, atom: &str, reachable: bool) -> Option<Vec<usize>> {
    // C-1: compare ty with the actual explored configurations, not just the
    // encoding's labels. Unknown wire evidence alone is not completeness.
    let explored = d
        .graph()
        .configs
        .iter()
        .any(|c| property::labels(d.core(), c).iter().any(|label| label == atom));
    assert_eq!(explored, reachable, "{}: {atom}", d.name());
    let formula = format!("AG !{atom}");
    let payload = d.payload(&formula).unwrap();
    let obligation = TrustObligation {
        obligation_id: format!("vc:current_command::test:temporal_safety:{atom}"),
        kind: ObligationKind::TemporalSafety,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: "current Trust Command control; refutation-only".into(),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.into(),
            value: payload.to_metadata_value().unwrap(),
        }],
    };
    let typed = NativeTyEngine::new().check_refutation_only(&obligation);
    // The existing wire helper also checks that proof_strength is absent.
    let (wire, _, _) = ty(d, &formula);
    assert_eq!(wire, if reachable { EvidenceStatus::Failed } else { EvidenceStatus::Unknown });
    match (reachable, typed) {
        (
            false,
            RefutationOnlyVerdict::NoCounterexample {
                completeness: RefutationCompleteness::Exhaustive,
            },
        ) => None,
        (true, RefutationOnlyVerdict::Counterexample { trace }) => Some(trace),
        other => panic!("{}: exploration and typed ty disagree: {other:?}", d.name()),
    }
}

fn check(d: &Derived, atom: &str, reachable: bool) -> Option<ReplayToken> {
    checked_trace(d, atom, reachable).map(|trace| {
        let token = d.replay_token(&trace, &[atom]).unwrap();
        assert!(token.is_of(d));
        assert!(token.replay().overapprox.is_empty());
        token
    })
}

fn safe(d: &Derived) -> Replay {
    assert!(check(d, property::VIOLATION, false).is_none());
    let trace = checked_trace(d, property::POLICY_EXEC, true).unwrap();
    let want = [property::POLICY_EXEC];
    // A positive execution witness grants no violation-token authority.
    assert!(matches!(d.replay_token(&trace, &want), Err(TokenError::NotARefutation { .. })));
    let replay = d.replay(&trace, &want).unwrap();
    assert!(replay.overapprox.is_empty());
    replay
}

fn small_env(soft: u64) -> EnvSpec {
    EnvSpec {
        limits: Limits { soft, hard: darwin::RLIM_INFINITY, max_files_per_proc: 256 },
        foreign: false,
        foreign_at: vec![70],
        ..plain_env()
    }
}

fn fork_with_hook(request: u64) -> EventProgram {
    let mut p = ProgramBuilder::new("current_trust_hook");
    let hook = p.body("hook", Vec::new(), |b| {
        b.event(L, "ioctl", Call::Ioctl { fd: Operand::Lit(70), request, arg: 0 }, Bind::none());
        b.ret(L, Some(Operand::Lit(0)));
    });
    let site = p.site("child", L, Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        b.spawn_fork(L, [StdioPlan::Inherit; 3], vec![hook], site, None);
    });
    p.root("main", main);
    p.build()
}

#[test]
fn status_relocation_and_allocation_fallback_keep_the_strip_and_hook_order() {
    for (soft, writer) in [(8, 4), (256, 10)] {
        let env = small_env(soft);
        let d = derive_ok(&fork_with_hook(darwin::FIOCLEX), &env);
        let replay = safe(&d);
        assert!(d.partition().constants().contains(&3));
        assert!(d.partition().constants().contains(&10));
        let calls: Vec<_> = d.graph().action_logs.iter().flatten().collect();
        assert!(
            calls.iter().any(|f| {
                f.call == Some(Call::StdStatusFd { fd: 4 })
                    && f.result == Some(Ok(Ret::Int(writer)))
            }),
            "the actual row must relocate or retain its writer at soft={soft}"
        );
        assert!(calls.iter().any(|f| {
            f.call
                == Some(Call::StdCloseMovedStatus { old: 4, new: i32::try_from(writer).unwrap() })
        }));
        assert!(
            replay.steps.iter().flat_map(|s| &s.sites).any(|s| s.std_row == Some("STD-SPAWN-FORK"))
        );
        for (_, stmt) in d.core().prog.stmts() {
            if let StmtKind::Event(ev) = &stmt.kind
                && matches!(
                    ev.call,
                    Call::StdStatusFd { .. }
                        | Call::StdCloseMovedStatus { .. }
                        | Call::StdMarkCloexec
                )
            {
                assert_eq!(ev.std_origin.as_ref().unwrap().row, "STD-SPAWN-FORK");
            }
        }
        // One request changes after the SAME Trust strip. A foreign fd is
        // never declared merely because a hook unflags it. fd70 is above the
        // soft limit in the fallback control and must still be stripped.
        let mutant = derive_ok(&fork_with_hook(darwin::FIONCLEX), &env);
        let replay = check(&mutant, property::VIOLATION, true).unwrap();
        assert!(
            replay
                .replay()
                .violations
                .iter()
                .any(|v| { matches!(v, Violation::Extra { fd: 70, .. }) })
        );
    }
}

fn same_number_stdio(fork: bool, stdio: StdioPlan) -> EventProgram {
    let mut p = ProgramBuilder::new("current_trust_stdio");
    let hook = p.body("hook", Vec::new(), |b| b.ret(L, Some(Operand::Lit(0))));
    let site = p.site(
        "child",
        L,
        Some(FdInherit {
            lanes: vec![Lane {
                fd: 0,
                ofd_class: if fork { "STD-SPAWN-FORK_0_0" } else { "STD-SPAWN-POSIX_0_0" }.into(),
            }],
        }),
    );
    let main = p.body("main", Vec::new(), |b| {
        // Null's O_CLOEXEC open now lands on its own stdio target, fd0.
        // Both Trust paths must clear that flag rather than use dup2(0, 0).
        b.event(L, "close", Call::Close { fd: Operand::Lit(0) }, Bind::none());
        b.spawn(
            L,
            [stdio, StdioPlan::Inherit, StdioPlan::Inherit],
            if fork { CommandShape::with_pre_exec() } else { CommandShape::default() },
            if fork { vec![hook] } else { Vec::new() },
            site,
            None,
        );
    });
    p.root("main", main);
    p.build()
}

#[test]
fn same_number_stdio_clears_cloexec_but_a_closed_inherited_slot_stays_closed() {
    let env = EnvSpec { foreign: false, ..plain_env() };
    for fork in [false, true] {
        safe(&derive_ok(&same_number_stdio(fork, StdioPlan::Null), &env));
        let mutant = derive_ok(&same_number_stdio(fork, StdioPlan::Inherit), &env);
        let replay = check(&mutant, property::VIOLATION, true).unwrap();
        assert!(
            replay
                .replay()
                .violations
                .iter()
                .any(|v| matches!(v, Violation::Missing { fd: 0, .. }))
        );
    }
}

#[test]
fn current_fork_error_channel_reaches_the_callers_err_branch() {
    let mut p = ProgramBuilder::new("current_trust_error");
    let pid = p.var("pid", -1);
    let hook = p.body("hook", Vec::new(), |b| b.ret(L, Some(Operand::Lit(-1))));
    let first = p.site("attempt", L, None);
    let fallback = p.site("fallback", L, Some(FdInherit { lanes: Vec::new() }));
    let main = p.body("main", Vec::new(), |b| {
        b.spawn_fork(L, [StdioPlan::Inherit; 3], vec![hook], first, Some(pid));
        b.when(L, Cond::eq(Operand::Var(pid), Operand::Lit(-1)), |b| {
            b.spawn_posix(L, [StdioPlan::Inherit; 3], fallback, None);
        });
    });
    p.root("main", main);
    let program = p.build();
    let d = derive_ok(&program, &small_env(256));
    let replay = safe(&d);
    let lines: Vec<_> = replay.steps.iter().flat_map(|s| &s.events).collect();
    for want in ["StdStatusFd", "write(", "_exit(1)", "read(", "waitpid("] {
        assert!(lines.iter().any(|line| line.contains(want)), "{want}: {lines:#?}");
    }
    let mut mutant = program;
    let mut changed = 0;
    for body in &mut mutant.bodies {
        for block in &mut body.blocks {
            for stmt in &mut block.stmts {
                if let StmtKind::Std(StdCall::CommandSpawn { shape, site, .. }) = &mut stmt.kind
                    && *site == fallback
                {
                    shape.inherit_all_fds = true;
                    changed += 1;
                }
            }
        }
    }
    assert_eq!(changed, 1);
    check(&derive_ok(&mutant, &small_env(256)), property::VIOLATION, true).unwrap();
}

#[test]
fn current_compositions_do_not_exempt_arbitrary_hooks_from_dr1() {
    let build = |unsafe_hook| {
        let mut p = ProgramBuilder::new("current_trust_dr1");
        let hook = p.body("hook", Vec::new(), |b| {
            if unsafe_hook {
                b.event(L, "kqueue", Call::Kqueue, Bind::none());
            }
            b.ret(L, Some(Operand::Lit(0)));
        });
        let site = p.site("child", L, Some(FdInherit { lanes: Vec::new() }));
        let main = p.body("main", Vec::new(), |b| {
            b.spawn_fork(L, [StdioPlan::Inherit; 3], vec![hook], site, None)
        });
        p.root("main", main);
        let idle = p.body("idle", Vec::new(), |b| {
            b.event(
                L,
                "getrlimit",
                Call::Getrlimit { resource: darwin::RLIMIT_NOFILE },
                Bind::none(),
            )
        });
        p.root("idle", idle);
        p.build()
    };
    let env = EnvSpec { foreign: false, ..plain_env() };
    safe(&derive_ok(&build(false), &env));
    match derive(&build(true), &env, &DeriveOptions::default()) {
        Err(DeriveError::Explore(e)) => {
            assert!(e.to_string().contains("DR-1") && e.to_string().contains("kqueue"), "{e}")
        }
        other => {
            panic!("expected the current hook's DR-1 refusal, got {:?}", other.map(|d| d.stats()))
        }
    }
}
