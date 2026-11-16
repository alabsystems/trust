//! M1 acceptance (plan §3 M1, bug 3): every fixture's derived model is
//! checked by trust-router's `NativeTyEngine` — the in-process `ty` primary —
//! through exactly the path a compiler obligation takes: a `TrustObligation`
//! whose metadata carries the (refutation-only) `TyTemporalModelPayload`
//! under `TY_TEMPORAL_MODEL_METADATA_KEY`. A `Failed` verdict's state trace is
//! mapped back to source events and re-executed. A fixture the plan requires
//! NOT to be refuted comes back `Unknown` — a derived model never proves
//! (SD-8) — and its non-vacuity is itself a replayed refutation (a policy
//! child does exec).
//!
//! Run with `--nocapture` to see the per-fixture report.

use trust_platform_derive::derive::{DeriveOptions, Derived, Stats};
use trust_platform_derive::fixtures::{self, Fixture};
use trust_platform_derive::program::Mutation;
use trust_platform_derive::property::{self, Premise, Violation, premised};
use trust_platform_derive::{derive, fd_inherit_formula, non_vacuity_formula};
use trust_router::full_verification::NativeTyEngine;
use trust_types::TY_TEMPORAL_MODEL_METADATA_KEY;
use trust_verifier_api::{
    BundleSubject, EvidenceStatus, MetadataEntry, ObligationKind, SourceLocation,
    TrustContractBundle, TrustObligation, VerificationEngine,
};

/// What ty said about one property of one derived model.
struct TyVerdict {
    status: EvidenceStatus,
    /// Machine state ids of the counterexample (Failed only).
    trace: Option<Vec<usize>>,
    diagnostics: Vec<String>,
    strength: Option<String>,
}

fn check_with_ty(d: &Derived, property: &str) -> TyVerdict {
    let payload = d.payload(property).unwrap_or_else(|e| panic!("`{property}`: {e}"));
    let obligation = TrustObligation {
        obligation_id: format!("vc:aterm_uds::{}:temporal_safety:{}", d.name(), property.len()),
        kind: ObligationKind::TemporalSafety,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: format!("platform protocol `{property}` ({})", trust_platform::PLATFORM_SPEC),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_metadata_value().expect("the payload serializes"),
        }],
    };
    let mut bundle = TrustContractBundle::empty(
        format!("bundle-{}", d.name()),
        BundleSubject::Function {
            crate_name: "aterm_uds".to_string(),
            path: format!("aterm_uds::spawnfd::{}", d.name()),
        },
    );
    bundle.obligations.push(obligation.clone());
    let mut evidence = NativeTyEngine::new().verify(&bundle, &[obligation]);
    assert_eq!(evidence.len(), 1, "one obligation, one evidence");
    let ev = evidence.remove(0);
    let trace = ev.counterexample.as_ref().and_then(|ce| {
        ce.data["trace"].as_array().map(|steps| {
            steps
                .iter()
                .map(|s| {
                    s["value"]
                        .as_str()
                        .and_then(|v| v.parse::<usize>().ok())
                        .expect("ty trace steps carry machine state ids")
                })
                .collect()
        })
    });
    TyVerdict {
        status: ev.status,
        trace,
        diagnostics: ev.diagnostics.clone(),
        strength: ev.proof_strength.as_ref().map(|s| format!("{s:?}")),
    }
}

fn stats_line(s: &Stats) -> String {
    format!(
        "{} RL-INIT tables, {} explored states, {} machine states ({} encoded + rl_init), {} \
         transitions, {} actions, {} horizon states, encoding exact: {}, payload {} bytes",
        s.init_tables,
        s.concrete_states,
        s.machine_states,
        s.abstract_states,
        s.machine_transitions,
        s.actions,
        s.horizon_states,
        s.encoding_exact,
        s.payload_bytes
    )
}

fn derive_fixture(f: &Fixture) -> Derived {
    derive(&f.program, &f.env, &DeriveOptions::default())
        .unwrap_or_else(|e| panic!("{}: derivation failed: {e}", f.name))
}

fn want_atoms(premises: &[Premise]) -> Vec<String> {
    vec![premised(property::VIOLATION, premises)]
}

/// A derived model's "no counterexample": Unknown, saying it is not a proof.
fn assert_not_refuted(d: &Derived, formula: &str) -> TyVerdict {
    let v = check_with_ty(d, formula);
    assert_eq!(
        v.status,
        EvidenceStatus::Unknown,
        "{}: `{formula}` must be neither refuted nor proved: {:?}",
        d.name(),
        v.diagnostics
    );
    assert!(v.strength.is_none());
    assert!(v.diagnostics.iter().any(|d| d.contains("refutation-only")), "{:?}", v.diagnostics);
    v
}

/// Check, explain and replay one refutation; returns the replayed
/// violations.
fn refutation(d: &Derived, formula: &str, want: &[String], report: bool) -> Vec<Violation> {
    let want: Vec<&str> = want.iter().map(String::as_str).collect();
    let want = want.as_slice();
    let v = check_with_ty(d, formula);
    assert_eq!(
        v.status,
        EvidenceStatus::Failed,
        "{}: `{formula}` must be refuted: {:?}",
        d.name(),
        v.diagnostics
    );
    let trace = v.trace.expect("a Failed verdict carries a state trace");
    assert_eq!(trace.first(), Some(&0), "the trace starts at rl_init");
    let steps = d.explain(&trace).expect("every trace step maps to an action");
    let replay = d.replay(&trace, want).unwrap_or_else(|e| {
        panic!("{}: the ty trace must replay at the real constants: {e}", d.name())
    });
    if report {
        println!("  ty: Failed `{formula}`; trace of {} machine states:", trace.len());
        for (s, r) in steps.iter().zip(&replay.steps) {
            println!("    [{}] {} ({})", r.actor, s.info.label, s.info.text);
            for e in &r.events {
                println!("        {e}");
            }
        }
        for viol in &replay.violations {
            println!("    => {viol}");
        }
    }
    replay.violations
}

#[test]
fn acceptance_fixtures_through_native_ty() {
    let mut summary = Vec::new();
    for f in fixtures::all() {
        let d = derive_fixture(&f);
        let formula = fd_inherit_formula(&f.premises);
        println!(
            "== {} ({}) ==",
            f.name,
            d.core()
                .prog
                .provenance
                .iter()
                .map(|p| format!("{}@{}:{}", p.repo, p.commit, p.path))
                .collect::<Vec<_>>()
                .join(", ")
        );
        println!("  model: {}", stats_line(&d.stats()));
        assert!(d.stats().machine_states > 1);
        if f.expect_refuted {
            let viol = refutation(&d, &formula, &want_atoms(&f.premises), true);
            assert!(!viol.is_empty());
            summary.push(format!(
                "{:<24} REFUTED  `{formula}` ({} machine states, {} explored) — {}",
                f.name,
                d.stats().machine_states,
                d.stats().concrete_states,
                viol[0]
            ));
        } else {
            let v = assert_not_refuted(&d, &formula);
            // Not vacuous: a policy child does exec (under the premise) — a
            // refutation of `AG !policy_exec…`, replayed.
            let reach = non_vacuity_formula(&f.premises);
            refutation(&d, &reach, &[premised(property::POLICY_EXEC, &f.premises)], false);
            println!("  ty: {:?}; `{reach}` refuted (a policy child does exec)", v.diagnostics);
            summary.push(format!(
                "{:<24} NOT REFUTED `{formula}` (Unknown: refutation-only; {} machine states, \
                 {} explored); non-vacuous",
                f.name,
                d.stats().machine_states,
                d.stats().concrete_states
            ));
        }
        for n in d.notes() {
            println!("  note: {n}");
        }
    }
    println!("\nSUMMARY");
    for s in summary {
        println!("  {s}");
    }
}

/// Fixture 1's refutation through the racing thread specifically: the
/// bridge child inherits the racer's socketpair end, caught between
/// `socketpair(2)` and std's `FIOCLEX`.
#[test]
fn no_strip_child_inherits_the_racers_pair() {
    let f = fixtures::spawnfd::no_strip();
    let d = derive_fixture(&f);
    let formula = "AG !inherits_race_pair_a";
    let viol = refutation(&d, formula, &["inherits_race_pair_a".to_string()], true);
    assert!(
        viol.iter().any(|v| matches!(v, Violation::Extra { class, .. } if class == "race_pair_a"))
    );
    let trace = check_with_ty(&d, formula).trace.expect("trace");
    let steps = d.explain(&trace).expect("explain");
    let labels: Vec<&str> = steps.iter().map(|s| s.info.text.as_str()).collect();
    let pair = labels.iter().position(|l| l.starts_with("racer:")).expect("the racer acts");
    let fork = steps
        .iter()
        .position(|s| s.info.events.iter().any(|e| e.symbol == "fork"))
        .expect("main forks");
    let fioclex = steps
        .iter()
        .position(|s| s.info.actor == "racer" && s.info.events.iter().any(|e| e.symbol == "ioctl"));
    assert!(pair < fork, "socketpair happens before the fork: {labels:?}");
    assert!(fioclex.is_none_or(|k| k > fork), "the fork lands in the FIOCLEX window: {labels:?}");
}

/// Fixture 3's refutation is the descriptor at or above the strip ceiling.
#[test]
fn strip_first_without_premise_is_refuted_by_the_ceiling() {
    let f = fixtures::spawnfd::strip_first_no_premise();
    let d = derive_fixture(&f);
    let viol = refutation(&d, &fd_inherit_formula(&[]), &[property::VIOLATION.to_string()], false);
    assert!(
        viol.iter().any(|v| matches!(v, Violation::Extra { fd, class, .. }
            if class == "foreign" && *fd >= 65_536)),
        "{viol:?}"
    );
    // ... and the premise is exactly what removes it: under fd-bound, ty
    // finds no counterexample (fixture 2), while the model is the same one.
    assert_not_refuted(&d, &fd_inherit_formula(&[Premise::FdBound]));
}

/// Fixtures 4 and 5 are refuted by a lane closed at exec.
#[test]
fn lane_closed_at_exec_refutes_the_placement_variants() {
    for f in [fixtures::spawnfd::strip_after_placing(), fixtures::spawnfd::no_dupfd_move()] {
        let d = derive_fixture(&f);
        let atom = premised(property::LANE_MISSING, &[Premise::FdBound]);
        let formula = format!("AG !{atom}");
        let viol = refutation(&d, &formula, &[atom], false);
        assert!(
            viol.iter().any(|v| matches!(v, Violation::Missing { fd, .. } if *fd == 3 || *fd == 4)),
            "{}: {viol:?}",
            f.name
        );
    }
}

/// Deleting each fd-hygiene step of a fixed fixture flips it to refuted,
/// and the refutation replays.
#[test]
fn mutant_sweep_every_hygiene_step_is_load_bearing() {
    let mut rows = Vec::new();
    for f in fixtures::all().into_iter().filter(|f| !f.expect_refuted) {
        assert!(!f.hygiene.is_empty(), "{} lists its hygiene steps", f.name);
        for m in &f.hygiene {
            let mutant = f.program.mutate(m).unwrap_or_else(|e| panic!("{}: {e:?}", f.name));
            let d = derive(&mutant, &f.env, &DeriveOptions::default())
                .unwrap_or_else(|e| panic!("{} / {}: {e}", f.name, m.name()));
            let formula = fd_inherit_formula(&f.premises);
            let viol = refutation(&d, &formula, &want_atoms(&f.premises), false);
            rows.push(format!(
                "{:<20} {:<44} REFUTED ({} machine states): {}",
                f.name,
                m.name(),
                d.stats().machine_states,
                viol[0]
            ));
        }
    }
    println!("MUTANT SWEEP");
    for r in rows {
        println!("  {r}");
    }
}

/// A mutation whose tag names nothing is an error, not a silent no-op.
#[test]
fn a_mutation_that_hits_nothing_is_refused() {
    let f = fixtures::spawnfd::strip_first_premise();
    assert!(f.program.mutate(&Mutation::DeleteStmt("no-such-step".to_string())).is_err());
}

// ---------------------------------------------------------------------------
// aterm fix/fd-inherit-ceiling (ef421cedb) against its base (ad35a5d85).
// ---------------------------------------------------------------------------

/// The replay step (index, line) of the first event an `actor` makes whose
/// rendering contains every one of `needles`.
fn first_event(replay: &[(String, String)], actor: &str, needles: &[&str]) -> Option<usize> {
    replay.iter().position(|(a, e)| a == actor && needles.iter().all(|n| e.contains(n)))
}

/// Refute `formula` over `d`, print the replayed trace, and return the
/// violations with the trace as (actor, event) lines.
fn refuted_trace(
    d: &Derived,
    formula: &str,
    want: &str,
) -> (Vec<Violation>, Vec<(String, String)>) {
    let v = check_with_ty(d, formula);
    assert_eq!(v.status, EvidenceStatus::Failed, "{}: `{formula}`: {:?}", d.name(), v.diagnostics);
    let trace = v.trace.expect("a Failed verdict carries a state trace");
    let replay = d.replay(&trace, &[want]).unwrap_or_else(|e| panic!("{}: replay: {e}", d.name()));
    println!("== {}: ty Failed `{formula}`, {} machine states ==", d.name(), trace.len());
    let mut lines = Vec::new();
    for st in &replay.steps {
        for e in &st.events {
            println!("    {e}");
            lines.push((st.actor.clone(), e.clone()));
        }
    }
    for viol in &replay.violations {
        println!("    => {viol}");
    }
    (replay.violations, lines)
}

/// OLD-MAIN BUG 1 (be339c9b2's body, unchanged on ad35a5d85): the 65 536 cap
/// leaves the unflagged descriptor at 70 000 in the bridge child — with no
/// premise, and under the fd-bound premise at the REAL kernel bound 92 160.
#[test]
fn old_main_bug1_the_bridge_inherits_the_descriptor_at_70000() {
    for f in [
        fixtures::spawnfd::strip_first_fd_70000(),
        fixtures::spawnfd::strip_first_fd_70000_kernel_bound(),
    ] {
        let d = derive_fixture(&f);
        let atom = premised("inherits_foreign", &f.premises);
        let (viol, _) = refuted_trace(&d, &format!("AG !{atom}"), &atom);
        assert!(
            viol.iter().any(|v| matches!(v, Violation::Extra { fd, class, cloexec, .. }
                if *fd == 70_000 && class == "foreign" && !cloexec)),
            "{}: {viol:?}",
            f.name
        );
    }
}

/// OLD-MAIN BUG 2: the window. The racer lowers the soft limit to 1024
/// BEFORE main reads the ceiling, raises it to 70 064 and takes fd 2000
/// AFTER, and the fork copies it past a strip that stops at 1024 — under
/// aterm's own fd-bound premise (cap 65 536) and without it.
#[test]
fn old_main_bug2_the_ceiling_read_races_a_limit_raise() {
    let f = fixtures::spawnfd::strip_first_ceiling_window();
    let d = derive_fixture(&f);
    for premises in [vec![Premise::FdBound], Vec::new()] {
        let atom = premised("inherits_race_devnull_low", &premises);
        let (viol, lines) = refuted_trace(&d, &format!("AG !{atom}"), &atom);
        assert!(
            viol.iter().any(|v| matches!(v, Violation::Extra { fd, class, .. }
                if *fd == 2000 && class == "race_devnull_low")),
            "{viol:?}"
        );
        let lowered = first_event(&lines, "window racer", &["setrlimit", "soft 1024"])
            .expect("the racer lowers the limit");
        let read = first_event(&lines, "main", &["getrlimit", "soft 1024"])
            .expect("main reads the lowered limit");
        let raised = first_event(&lines, "window racer", &["setrlimit", "soft 70064"])
            .expect("the racer raises the limit");
        let taken = first_event(&lines, "window racer", &["F_DUPFD", "2000"])
            .expect("the racer takes 2000");
        let fork = first_event(&lines, "main", &["fork()"]).expect("main forks");
        assert!(lowered < read && read < raised && raised < taken && taken < fork, "{lines:?}");
    }
}

/// The OLD PTY copy (aterm-pty, ad35a5d85) has both bugs: in the new PTY
/// fixture's environment a shell inherits a descriptor at or above 65 536,
/// and the window alone (the racer's 2000) leaks too.
#[test]
fn old_main_pty_copy_leaks_into_every_shell() {
    let f = fixtures::pty::main_fd_70000();
    let d = derive_fixture(&f);
    let (viol, _) = refuted_trace(&d, &fd_inherit_formula(&[]), property::VIOLATION);
    assert!(
        viol.iter().any(|v| matches!(v, Violation::Extra { fd, .. } if *fd >= 65_536)),
        "{viol:?}"
    );
    let f = fixtures::pty::main_ceiling_window();
    let d = derive_fixture(&f);
    let (viol, lines) =
        refuted_trace(&d, "AG !inherits_race_devnull_low", "inherits_race_devnull_low");
    assert!(
        viol.iter().any(|v| matches!(v, Violation::Extra { fd, class, .. }
            if *fd == 2000 && class == "race_devnull_low")),
        "{viol:?}"
    );
    let read = first_event(&lines, "main", &["getrlimit", "soft 1024"]).expect("lowered read");
    let fork = first_event(&lines, "main", &["fork()"]).expect("fork");
    assert!(read < fork);
}

/// The NEW bodies (ef421cedb) are not refuted on the very atoms that refute
/// the old ones: no foreign descriptor (70 000 included), neither of the
/// window racer's descriptors, no lane missing or crossed — each `Unknown`
/// (a derived model never proves), and each body's child does exec.
#[test]
fn new_bodies_are_not_refuted_on_the_old_bugs_atoms() {
    for f in [
        fixtures::lane::launch(),
        fixtures::lane::launch_window(),
        fixtures::lane::sources_on_the_targets(),
        fixtures::lane::sources_at_open_max(),
        fixtures::pty::fix_shell(),
        fixtures::pty::fix_shell_window(),
        fixtures::pty::fix_shell_hardened(),
    ] {
        let d = derive_fixture(&f);
        assert!(f.premises.is_empty(), "{}: the new bodies claim no premise", f.name);
        let mut atoms = vec!["inherits_foreign", property::LANE_MISSING, property::LANE_CROSSED];
        if d.vocabulary().contains("inherits_race_devnull_high") {
            atoms.extend(["inherits_race_devnull_low", "inherits_race_devnull_high"]);
        }
        if d.vocabulary().contains("inherits_race_pair_a") {
            atoms.extend(["inherits_race_pair_a", "inherits_race_pair_b"]);
        }
        for atom in atoms {
            assert_not_refuted(&d, &format!("AG !{atom}"));
        }
        refutation(&d, &non_vacuity_formula(&[]), &[property::POLICY_EXEC.to_string()], false);
        println!(
            "{:<32} not refuted on {} atoms; {}",
            f.name,
            d.vocabulary().len(),
            stats_line(&d.stats())
        );
    }
}
