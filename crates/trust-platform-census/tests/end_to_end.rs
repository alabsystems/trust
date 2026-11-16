//! The census end to end (design 2026-10-01 §2.7, PR 7): REAL trust-ir —
//! stage1 trustc dumps in `tests/ir/`, each naming its trustc in its
//! `; trustc` header (`tests/dump_provenance.rs`) —
//! translated, derived, checked by NativeTyEngine, refutations replayed,
//! and site verdicts joined (C-1, C-4, C-9).
//!
//! `census_shapes.trust_ir` is the dump of `census_shapes.rs`: the
//! measurement's aterm shapes (`repro/constructs.rs` `c13_fork` — raw fork,
//! `while` strip, `execv` — and `c3_pre_exec`'s strip closure, both
//! verbatim) with callers that fix the strip bound, plus the refusal
//! shapes. `constructs.trust_ir` is the dump of `constructs.rs`, the
//! measurement's `repro/constructs.rs`.

mod common;

use common::*;
use trust_platform::std_summaries::CommandStd;
use trust_platform_census::verdict::{NonVacuity, Outcome, SiteVerdict, site_verdict};
use trust_platform_census::{CensusOptions, SiteGate, SiteKind};
use trust_platform_derive::program::{StmtKind, Term};

fn has_stmt(rp: &trust_platform_census::RootProgram, f: impl Fn(&StmtKind) -> bool) -> bool {
    rp.program.bodies.iter().any(|b| b.blocks.iter().any(|k| k.stmts.iter().any(|s| f(&s.kind))))
}

/// Preserve the pre-SP1 census population explicitly. This is a test-only
/// historical harness, never the production census's current Trust selector.
fn historical_upstream_harnesses(
    mut out: trust_platform_census::CensusOutput,
) -> trust_platform_census::CensusOutput {
    for rp in &mut out.roots {
        for body in &mut rp.program.bodies {
            for block in &mut body.blocks {
                for stmt in &mut block.stmts {
                    if let StmtKind::Std(trust_platform_derive::program::StdCall::CommandSpawn {
                        shape,
                        ..
                    }) = &mut stmt.kind
                    {
                        assert_eq!(shape.std, CommandStd::Trust);
                        assert!(!shape.inherit_all_fds);
                        shape.std = CommandStd::Upstream;
                        shape.inherit_all_fds = true;
                    }
                }
            }
        }
        for premise in &mut rp.premises {
            if premise.code == "P-HOOK-HARNESS" {
                premise.text = "historical Upstream synthetic pre_exec harness with explicit inherit_all_fds; not a current Trust Command witness".into();
                rp.program.disclosures.push(premise.text.clone());
            }
        }
    }
    out
}

/// The site of `kind` in `body`.
fn site(out: &trust_platform_census::CensusOutput, body: &str, kind: SiteKind) -> usize {
    out.sites
        .iter()
        .find(|s| s.body == body && s.kind == kind)
        .unwrap_or_else(|| panic!("no {kind:?} site in `{body}`"))
        .id
}

/// The raw fork + `while` strip + `execv` body of aterm's PTY child
/// (c13_fork, verbatim), reached from a caller that caps the strip at
/// 65 536 — ad35a5d85's `inherited_fd_ceiling` CAP. RL-INIT places an
/// unflagged foreign descriptor at the partition point 65 536, below the
/// allocation limit (92 160 here): the strip misses it, the child execs
/// holding it. REFUTED, and the trace replays with no over-approximating
/// choice.
#[test]
fn raw_fork_strip_that_misses_a_range_is_refuted_with_a_replayed_trace() {
    let m = module("census_shapes");
    let out = census(&m, "census_shapes");
    let (i, rp) = root(&out, &m, "spawn_capped");
    // The translation: a raw fork whose child runs the strip as ONE
    // ForRange step, then execv.
    assert!(has_stmt(rp, |k| matches!(k, StmtKind::Fork { .. })), "no Fork");
    assert!(
        has_stmt(
            rp,
            |k| matches!(k, StmtKind::ForRange { lo: _, hi, .. } if *hi != trust_platform_derive::program::Operand::Lit(0))
        ),
        "the strip is not a ForRange: {:#?}",
        rp.program.bodies
    );
    assert!(
        rp.notes.iter().any(|n| n.contains("ForRange") && n.contains("block-parameter")),
        "{:?}",
        rp.notes
    );
    let ps = rp.policy_sites[0];
    assert_eq!(out.sites[ps.site].kind, SiteKind::Fork);
    let (e, replay) = evidence(&out, i, ps.program_site);
    let Outcome::Refuted { trace, overapprox } = &e.outcome else {
        panic!("spawn_capped must be refuted: {e:?}")
    };
    assert!(overapprox.is_empty(), "no over-approximation on this path: {overapprox:?}");
    assert!(e.derive_violation, "the derivation's exploration agrees");
    let r = replay.expect("replayed");
    assert!(
        r.violations.iter().any(|v| v.to_string().contains("foreign")),
        "the leak is the foreign descriptor: {:?}",
        r.violations
    );
    assert!(
        trace.iter().any(|l| l.contains("for fd in 3..65536")),
        "the strip stops at the cap: {trace:#?}"
    );
    println!("spawn_capped refuted; replay:");
    for l in trace {
        println!("    {l}");
    }
    for v in &r.violations {
        println!("  violation: {v}");
    }
    // Every Loc in the trace maps back to trust-ir (L1c): each fired event of
    // the replay is a program position whose Loc is in the root's `locs`, or
    // an environment step that cites its RL clause.
    let (mut program, mut environment) = (0, 0);
    for s in &r.steps {
        assert_eq!(s.sites.len(), s.events.len(), "sites are parallel to events: {s:?}");
        for site in &s.sites {
            if site.environment {
                environment += 1;
                assert!(site.rl_clause.is_some(), "an uncited environment step: {site:?}");
            } else {
                program += 1;
                assert!(
                    rp.locs.contains_key(&site.loc),
                    "`{}` is not a trust-ir position of {}",
                    site.loc,
                    rp.name
                );
            }
        }
    }
    assert!(program > 0 && environment > 0, "{program} program, {environment} environment steps");
    assert!(rp.locs.keys().any(|l| l.0.contains("census_shapes.rs:14:23")));
}

/// The same fork + strip with its own site, stripping to i32::MAX: NOT
/// refuted, and the per-site non-vacuity check is witnessed (a child of
/// THIS site execs, with no over-approximating choice).
#[test]
fn raw_fork_full_strip_is_not_refuted() {
    let m = module("census_shapes");
    let out = census(&m, "census_shapes");
    let s = site(&out, "spawn_full_inline", SiteKind::Fork);
    let ev = evidence_for_site(&out, s);
    assert_eq!(ev.len(), envs().len(), "one derivation per library environment");
    for e in &ev {
        assert!(matches!(e.outcome, Outcome::NoCounterexample { .. }), "{e:?}");
        assert_eq!(e.non_vacuity, NonVacuity::Witnessed);
    }
    // Evidence from one environment only is not enough.
    assert!(matches!(site_verdict(&out, s, &ev[..1]), SiteVerdict::Unanalysed(_)));
    match site_verdict(&out, s, &ev) {
        SiteVerdict::NotRefuted { premises, roots } => {
            assert_eq!(roots.len(), 1);
            let codes: Vec<_> = premises.iter().map(|p| p.code).collect();
            println!("spawn_full_inline: not refuted under {codes:?}");
            assert!(codes.contains(&"P-NO-LANES"), "{codes:?}");
            assert!(codes.contains(&"P-RLIMIT-SOFT") && codes.contains(&"P-FORK-SUCCEEDS"));
            // The overflow check of `fd += 1` was discharged by the guard:
            // no panic premise is left.
            assert!(!codes.contains(&"P-PANIC-ENDS-PATH"), "{codes:?}");
        }
        v => panic!("spawn_full_inline must not be refuted: {v:?}"),
    }
}

/// `fork_strip_exec`'s fork site is reached by every `spawn_*` caller. Its
/// verdict is the join over them (C-4): the full strip's root alone reads
/// "no counterexample", the 65 536 cap's root refutes it, the refused
/// roots are unanalysed — and the join is REFUTED.
#[test]
fn a_site_verdict_is_the_join_over_its_roots() {
    let m = module("census_shapes");
    let out = census(&m, "census_shapes");
    let s = site(&out, "fork_strip_exec", SiteKind::Fork);
    let reaching: Vec<String> =
        out.roots_reaching(s).iter().map(|r| trust_platform_census::fn_path(&m, *r)).collect();
    for want in
        ["spawn_capped", "spawn_full", "spawn_ceiling", "spawn_sysconf", "spawn_pid_dependent"]
    {
        assert!(reaching.iter().any(|r| r == want), "{want} reaches it: {reaching:?}");
    }
    assert!(matches!(out.gate(s), SiteGate::Unanalysed(_)), "refused roots reach it");
    let ev = evidence_for_site(&out, s);
    let by = |name: &str| {
        let (i, _) = root(&out, &m, name);
        ev.iter().find(|e| e.root == i).unwrap_or_else(|| panic!("{name}"))
    };
    assert!(matches!(by("spawn_full").outcome, Outcome::NoCounterexample { .. }));
    assert_eq!(by("spawn_full").non_vacuity, NonVacuity::Witnessed);
    // The bound from an inlined local helper (`ceiling()` = 1 << 16).
    assert!(
        matches!(&by("spawn_ceiling").outcome, Outcome::Refuted { overapprox, .. } if overapprox.is_empty())
    );
    match site_verdict(&out, s, &ev) {
        SiteVerdict::Refuted { root, .. } => {
            println!("fork_strip_exec's site: refuted through {}", out.roots[root].name);
        }
        v => panic!("the join must be refuted: {v:?}"),
    }
}

/// aterm's `pre_exec` strip (c3_pre_exec's closure, verbatim: a `for`
/// over `3..bound` through an alloca cell) runs in the child of a harness
/// spawn explicitly selecting historical upstream std (P-HOOK-HARNESS).
/// Capped at 65 536: refuted; to i32::MAX: not refuted, with a capped mutant.
#[test]
fn historical_upstream_pre_exec_is_refuted_when_capped_and_not_when_full() {
    let m = module("census_shapes");
    let out = historical_upstream_harnesses(census(&m, "census_shapes"));
    let (i, rp) = root(&out, &m, "hook_capped");
    assert!(
        rp.notes.iter().any(|n| n.contains("ForRange") && n.contains("cell form")),
        "{:?}",
        rp.notes
    );
    assert!(has_stmt(rp, |k| matches!(k, StmtKind::Std(_))), "the harness spawn");
    assert!(
        has_stmt(rp, |k| matches!(k,
        StmtKind::Std(trust_platform_derive::program::StdCall::CommandSpawn { shape, .. })
            if shape.inherit_all_fds && shape.std == CommandStd::Upstream)),
        "the isolated hook names its upstream std and inheritance opt-out"
    );
    assert!(
        rp.premises
            .iter()
            .any(|p| p.code == "P-HOOK-HARNESS" && p.text.contains("explicit inherit_all_fds")),
        "{:?}",
        rp.premises
    );
    let (e, _) = evidence(&out, i, rp.policy_sites[0].program_site);
    assert!(
        matches!(&e.outcome, Outcome::Refuted { overapprox, .. } if overapprox.is_empty()),
        "{e:?}"
    );

    let ps = rp.policy_sites[0];
    let SiteVerdict::Refuted { premises, .. } =
        site_verdict(&out, ps.site, std::slice::from_ref(&e))
    else {
        panic!("the conditional refutation keeps its premises")
    };
    assert!(
        premises
            .iter()
            .any(|p| p.code == "P-HOOK-HARNESS" && p.text.contains("explicit inherit_all_fds"))
    );
    let s = site(&out, "hook_full_inline", SiteKind::PreExecHook);
    let ev = evidence_for_site(&out, s);
    match site_verdict(&out, s, &ev) {
        SiteVerdict::NotRefuted { premises, .. } => {
            let codes: Vec<_> = premises.iter().map(|p| p.code).collect();
            assert!(codes.contains(&"P-HOOK-HARNESS"), "{codes:?}");
        }
        v => panic!("hook_full_inline must not be refuted: {v:?}"),
    }
    let (full, _) = root(&out, &m, "hook_full_inline");
    let mut mutant = out.clone();
    let mut changed = 0;
    for body in &mut mutant.roots[full].program.bodies {
        for block in &mut body.blocks {
            for stmt in &mut block.stmts {
                if let StmtKind::ForRange { hi, .. } = &mut stmt.kind {
                    *hi = trust_platform_derive::program::Operand::Lit(65_536);
                    changed += 1;
                }
            }
        }
    }
    assert_eq!(changed, 1);
    let ev = evidence_for_site(&mutant, s);
    assert!(matches!(site_verdict(&mutant, s, &ev), SiteVerdict::Refuted { .. }));
}

/// The production census's synthetic harness uses current Trust's strip and
/// relocation. It still does not recover the caller's real Command object.
#[test]
fn current_trust_harness_keeps_the_strip_and_a_post_strip_foreign_leak_mutant() {
    let m = module("census_shapes");
    let out = census(&m, "census_shapes");
    let (i, rp) = root(&out, &m, "hook_capped");
    assert!(has_stmt(rp, |k| matches!(k,
        StmtKind::Std(trust_platform_derive::program::StdCall::CommandSpawn { shape, .. })
        if shape.std == CommandStd::Trust && !shape.inherit_all_fds)));
    assert!(rp.premises.iter().any(|p| p.code == "P-HOOK-HARNESS"
        && p.text.contains("current Trust SP1")
        && p.text.contains("not recovered")));
    let (e, _) = evidence(&out, i, rp.policy_sites[0].program_site);
    assert!(matches!(e.outcome, Outcome::NoCounterexample { .. }), "{e:?}");
    assert_eq!(e.non_vacuity, NonVacuity::Witnessed);
    assert!(!e.derive_violation);

    // This registration has its own complete root, so all FC-4 conditions
    // can be checked over every library environment by the ordinary verdict.
    let s = site(&out, "hook_full_inline", SiteKind::PreExecHook);
    let ev = evidence_for_site(&out, s);
    assert!(matches!(site_verdict(&out, s, &ev), SiteVerdict::NotRefuted { .. }));
    let (full, _) = root(&out, &m, "hook_full_inline");
    let mut mutant = out.clone();
    let mut changed = 0;
    for body in &mut mutant.roots[full].program.bodies {
        for block in &mut body.blocks {
            for stmt in &mut block.stmts {
                if let StmtKind::Event(ev) = &mut stmt.kind
                    && let trust_platform::Call::Fcntl { cmd, arg, .. } = &mut ev.call
                    && *cmd == trust_platform::darwin::F_SETFD
                    && *arg == trust_platform::darwin::FD_CLOEXEC
                {
                    // One constant: clear rather than set CLOEXEC AFTER the
                    // unchanged Trust strip. Foreign descriptors are not lanes.
                    *arg = 0;
                    changed += 1;
                }
            }
        }
    }
    assert_eq!(changed, 1);
    let ev = evidence_for_site(&mutant, s);
    assert!(ev.iter().any(|e| matches!(&e.outcome,
        Outcome::Refuted { overapprox, .. } if overapprox.is_empty())
        && e.derive_violation));
    assert!(matches!(site_verdict(&mutant, s, &ev), SiteVerdict::Refuted { .. }));
}

/// The measurement's aterm shapes (`constructs.rs`): `c13_fork` and
/// `c3_pre_exec` as LIBRARY roots take the strip bound from their caller,
/// so the bound is untracked and the root is the named refusal
/// `PC-UNTRACKED-FD` — never a pass.
#[test]
fn the_real_constructs_bodies_as_library_roots_are_named_refusals() {
    let m = module("constructs");
    let out = census(&m, "constructs");
    for name in ["c13_fork", "c3_pre_exec"] {
        let codes = root_codes(&out, &m, name);
        assert!(codes.contains(&"PC-UNTRACKED-FD"), "{name}: {codes:?}");
        println!("{name}: {codes:?}");
    }
    // c4's closure closes the captured `fd`, a caller's value.
    assert!(root_codes(&out, &m, "c4_pre_exec_call").contains(&"PC-UNTRACKED-FD"));
    // Every policy site of the module is unanalysed.
    for s in out.sites.iter().filter(|s| s.policy) {
        assert!(matches!(out.gate(s.id), SiteGate::Unanalysed(_)), "{s:?}");
    }
}

/// An unknown call on a root's path is a named refusal, and a site with a
/// refusal can never read "not refuted" — whatever evidence is offered.
#[test]
fn an_unknown_call_is_a_named_refusal_and_its_site_is_never_not_refuted() {
    let m = module("census_shapes");
    let out = census(&m, "census_shapes");
    // `setsid` in the forked child: a named gap of the platform model.
    assert!(root_codes(&out, &m, "spawn_setsid").contains(&"PC-UNMODELED"));
    // `std::process::id`: not in the std table.
    assert!(root_codes(&out, &m, "spawn_after_id").contains(&"PC-UNKNOWN-STD"));
    // `sysconf` (not in the symbol table) and its truncating cast.
    let c = root_codes(&out, &m, "spawn_sysconf");
    assert!(c.contains(&"PC-UNMODELED") && c.contains(&"PC-FD-TRUNC"), "{c:?}");
    let s = site(&out, "spawn_setsid", SiteKind::Fork);
    let forged = vec![trust_platform_census::verdict::SiteEvidence {
        root: 0,
        program_site: 0,
        env: 0,
        outcome: Outcome::NoCounterexample {
            completeness: trust_platform_census::verdict::Completeness::Exhaustive,
        },
        non_vacuity: NonVacuity::Witnessed,
        derive_violation: false,
    }];
    match site_verdict(&out, s, &forged) {
        SiteVerdict::Unanalysed(rs) => {
            assert!(rs.iter().any(|r| r.code() == "PC-UNMODELED"), "{rs:?}");
        }
        v => panic!("a refused site read {v:?}"),
    }
}

/// I-EFFECTS-COVERED (Critique C-16). The child duplicates stdout (no
/// FD_CLOEXEC) inside a `for` that the 771983b92 producer's wave-ER summary
/// ERASED (`dup_stdout_for` lowered to a bare `ret`; held in
/// `tests/ir/771983b92/`): with the HIR's effect list the root is
/// `PC-PRODUCER-ERASED`. Its faithful `while` twin is refuted. Without the
/// check — a host whose HIR list agreed with the erased IR — the same leak
/// would read "not refuted": the false pass the gate stops.
///
/// Today's producer lowers the `for` (S1), so on today's dump the same root
/// translates and its leak is refuted like its `while` twin's: the gate's
/// refusal was the producer's erasure, never a verdict.
#[test]
fn an_erased_effect_is_producer_erased_not_a_pass() {
    let held = "771983b92/census_shapes";
    let m = module(held);
    let out = census(&m, held);
    let rs = out.root_refusals(func(&m, "spawn_erased_leak"));
    assert!(
        rs.iter().any(|r| r.code() == "PC-PRODUCER-ERASED" && r.to_string().contains("dup")),
        "{rs:?}"
    );
    let (i, rp) = root(&out, &m, "spawn_dup_leak");
    let (e, _) = evidence(&out, i, rp.policy_sites[0].program_site);
    assert!(
        matches!(&e.outcome, Outcome::Refuted { overapprox, .. } if overapprox.is_empty()),
        "{e:?}"
    );

    // The counterfactual: drop the erased call from the HIR list.
    let lying =
        sidecar(held).replace("effects dup_stdout_for 187:53=dup", "effects dup_stdout_for");
    assert_ne!(lying, sidecar(held));
    let out2 = census_with(&m, &lying, &CensusOptions::default());
    let (j, rp2) = root(&out2, &m, "spawn_erased_leak");
    let (e2, _) = evidence(&out2, j, rp2.policy_sites[0].program_site);
    assert!(
        matches!(e2.outcome, Outcome::NoCounterexample { .. }),
        "without I-EFFECTS-COVERED the erased leak reads not refuted: {e2:?}"
    );

    // Today's dump: the loop is lowered, the root translates, the leak is
    // refuted with the loop's `dup` in the replayed trace.
    let m = module("census_shapes");
    let out = census(&m, "census_shapes");
    assert_eq!(root_codes(&out, &m, "spawn_erased_leak"), Vec::<&str>::new());
    let (k, rp3) = root(&out, &m, "spawn_erased_leak");
    let (e3, _) = evidence(&out, k, rp3.policy_sites[0].program_site);
    match &e3.outcome {
        Outcome::Refuted { trace, overapprox } => {
            assert!(overapprox.is_empty(), "{e3:?}");
            assert!(trace.iter().any(|l| l.contains("dup(1)")), "{trace:#?}");
        }
        other => panic!("today's lowered `for` leak must be refuted: {other:?}"),
    }
}

/// Per-site non-vacuity (Critique C-1): a child that `_exit`s before any
/// exec gives "no counterexample", but no witness that the site's child
/// execs — PC-INCOMPLETE, not "not refuted".
#[test]
fn a_site_whose_child_never_execs_is_incomplete() {
    let m = module("census_shapes");
    let out = census(&m, "census_shapes");
    let s = site(&out, "spawn_never_execs", SiteKind::Fork);
    let ev = evidence_for_site(&out, s);
    assert!(matches!(ev[0].outcome, Outcome::NoCounterexample { .. }));
    assert_eq!(ev[0].non_vacuity, NonVacuity::Missing);
    match site_verdict(&out, s, &ev) {
        SiteVerdict::Unanalysed(rs) => {
            assert!(rs.iter().any(|r| r.code() == "PC-INCOMPLETE"), "{rs:?}")
        }
        v => panic!("{v:?}"),
    }
}

/// Critique C-9: the strip's bound depends on `getpid()`, which the census
/// does not track; the guard is `Cond::Nondet`, the leak is found through
/// its else-arm, and the replay lists that choice — PC-OVERAPPROX, not an
/// error.
#[test]
fn a_refutation_through_an_untracked_guard_is_overapprox() {
    let m = module("census_shapes");
    let out = census(&m, "census_shapes");
    let (i, rp) = root(&out, &m, "spawn_pid_dependent");
    assert!(rp.notes.iter().any(|n| n.contains("Cond::Nondet")), "{:?}", rp.notes);
    let (e, _) = evidence(&out, i, rp.policy_sites[0].program_site);
    let Outcome::Refuted { overapprox, .. } = &e.outcome else { panic!("{e:?}") };
    assert!(!overapprox.is_empty());
    let s = rp.policy_sites[0].site;
    match site_verdict(&out, s, std::slice::from_ref(&e)) {
        SiteVerdict::Unanalysed(rs) => assert!(rs.iter().any(|r| r.code() == "PC-OVERAPPROX")),
        SiteVerdict::Refuted { .. } => {
            // Another root (the 65 536 cap) refutes the shared site cleanly.
        }
        v => panic!("{v:?}"),
    }
}

/// The census over the REAL aterm-uds dump (aterm 4ba80b2b6): the producer
/// spliced none of its spawn bodies, so there is no analysable spawn root,
/// and the host's HIR sites (read from aterm's source at that commit) are
/// all `PC-BODY-NOT-LOWERED`; the Linux arm's fork, which only the product
/// configuration of another target compiles, is `PC-CFG-SKEW`.
#[test]
fn the_real_aterm_uds_dump_has_no_unnamed_gap() {
    let m = module("aterm_uds");
    let out = census(&m, "aterm_uds");
    println!("aterm-uds: {:?}", out.stats);
    assert!(out.roots.is_empty(), "no spliced aterm-uds body spawns");
    let hir = |body: &str, line, col, callee: &str| trust_platform_census::HirSite {
        body: body.into(),
        line,
        col,
        callee: callee.into(),
    };
    let darwin = vec![
        hir("spawnfd::platform::spawn", 709, 25, "posix_spawn"),
        hir("spawnfd::platform::spawn", 718, 21, "posix_spawn"),
        hir("pspawn::spawn_cloexec_default", 118, 12, "posix_spawn"),
        hir("spawnfd::darwin_strip::mark_listed", 1101, 20, "fcntl"),
    ];
    let rs = trust_platform_census::coverage::sites_covered(&m, &out, &darwin);
    assert_eq!(rs.len(), darwin.len(), "{rs:?}");
    assert!(rs.iter().all(|r| r.refusal.code() == "PC-BODY-NOT-LOWERED"), "{rs:?}");
    let mut linux = darwin.clone();
    linux.push(hir("spawnfd::platform::spawn", 820, 27, "fork"));
    let skew = trust_platform_census::coverage::cfg_skew(&darwin, &linux);
    assert_eq!(skew.len(), 1);
    assert_eq!(skew[0].refusal.code(), "PC-CFG-SKEW");
    assert_eq!(skew[0].hir.as_ref().map(|h| h.line), Some(820), "the shipped site, by identity");
}

/// Every Loc of a root's program — each statement's and each block
/// terminator's (an undecided guard's choice step fires at a terminator) —
/// maps to a trust-ir position unless it is one of the census's synthetic
/// `<…>` Locs, and every branch the census emits terminates its block (a
/// sanity check of the CFG the derivation consumes).
#[test]
fn locs_map_back_to_trust_ir() {
    let m = module("census_shapes");
    let out = census(&m, "census_shapes");
    let mut terminators = 0;
    for rp in &out.roots {
        for b in &rp.program.bodies {
            for blk in &b.blocks {
                for s in &blk.stmts {
                    if s.loc.0.starts_with('<') {
                        continue;
                    }
                    assert!(rp.locs.contains_key(&s.loc), "{}: {}", rp.name, s.loc);
                }
                if !blk.term_loc.0.starts_with('<') {
                    terminators += 1;
                    assert!(
                        rp.locs.contains_key(&blk.term_loc),
                        "{}: terminator {}",
                        rp.name,
                        blk.term_loc
                    );
                }
                if let Term::Branch { then, els, .. } = blk.term {
                    assert!(then < b.blocks.len() && els < b.blocks.len());
                }
            }
        }
    }
    assert!(terminators > 0, "no terminator Loc was checked");
}
