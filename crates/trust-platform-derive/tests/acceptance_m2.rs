//! M2 acceptance (plan §3 M2, bugs 1 and 2): P-LOCK-RELEASE and fd-identity.
//!
//! Every fixture's derived model is checked by trust-router's `NativeTyEngine`
//! — the in-process `ty` primary — through the path a compiler obligation
//! takes (a `TrustObligation` whose metadata carries the refutation-only
//! `TyTemporalModelPayload`). A `Failed` verdict's state trace is mapped back
//! to source events and RE-EXECUTED on the Rust model (`trust_platform::step`,
//! conformance-tested against this Mac), and must end in the refuted
//! proposition. A fixture the plan requires NOT to be refuted comes back
//! `Unknown` (a derived model never proves, SD-8) and its non-vacuity is a
//! replayed refutation: the dangerous situation is reachable (a child holds a
//! copy of a released description; a retired number is taken by a stranger).
//! The mutant sweep deletes each hygiene step of each fixed fixture and
//! requires a replayed refutation.
//!
//! Run with `--nocapture` for the traces.

use trust_platform_derive::derive::{DeriveOptions, Derived, Stats};
use trust_platform_derive::fixtures::{self, M2Fixture, Property};
use trust_platform_derive::program::EventProgram;
use trust_platform_derive::property;
use trust_platform_derive::trace::Replay;
use trust_router::full_verification::NativeTyEngine;
use trust_types::TY_TEMPORAL_MODEL_METADATA_KEY;
use trust_verifier_api::{
    BundleSubject, EvidenceStatus, MetadataEntry, ObligationKind, SourceLocation,
    TrustContractBundle, TrustObligation, VerificationEngine,
};

/// The derivations here hold up to a few hundred thousand explored states;
/// run them one at a time (libtest would run these tests in parallel).
static ONE_AT_A_TIME: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn serial() -> std::sync::MutexGuard<'static, ()> {
    ONE_AT_A_TIME.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
}

struct TyVerdict {
    status: EvidenceStatus,
    trace: Option<Vec<usize>>,
    diagnostics: Vec<String>,
    strength: Option<String>,
}

fn check_with_ty(d: &Derived, property: &str) -> TyVerdict {
    let payload = d.payload(property).unwrap_or_else(|e| panic!("`{property}`: {e}"));
    let obligation = TrustObligation {
        obligation_id: format!("vc:aterm::{}:temporal_safety:{}", d.name(), property.len()),
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
        BundleSubject::Function { crate_name: "aterm".to_string(), path: d.name().clone() },
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
        "{} explored states, {} machine states ({} encoded + rl_init), {} transitions, {} \
         actions, encoding exact: {}, payload {} bytes",
        s.concrete_states,
        s.machine_states,
        s.abstract_states,
        s.machine_transitions,
        s.actions,
        s.encoding_exact,
        s.payload_bytes
    )
}

fn derive(name: &str, program: &EventProgram, f: &M2Fixture) -> Derived {
    trust_platform_derive::derive(program, &f.env, &DeriveOptions::default())
        .unwrap_or_else(|e| panic!("{name}: derivation failed: {e}"))
}

fn formulas(p: Property) -> (String, &'static str, String, &'static str) {
    match p {
        Property::LockRelease => (
            property::lock_release_formula(),
            property::LOCK_LEAK,
            format!("AG !{}", property::RELEASED_SHARED),
            property::RELEASED_SHARED,
        ),
        Property::FdIdentity => (
            property::fd_identity_formula(),
            property::FD_IDENTITY_VIOLATION,
            format!("AG !{}", property::NUMBER_REUSED),
            property::NUMBER_REUSED,
        ),
    }
}

/// Check, explain and replay one refutation.
fn refutation(d: &Derived, formula: &str, want: &str, report: bool) -> Replay {
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
    let replay = d
        .replay(&trace, &[want])
        .unwrap_or_else(|e| panic!("{}: the ty trace must replay on the model: {e}", d.name()));
    assert!(
        replay.steps.iter().all(|s| s.label == "halt" || !s.events.is_empty()),
        "{}: every replayed step names its events",
        d.name()
    );
    if report {
        println!("  ty: Failed `{formula}`; trace of {} machine states:", trace.len());
        for (s, r) in steps.iter().zip(&replay.steps) {
            println!("    [{}] {}", r.actor, s.info.label);
            for e in &r.events {
                println!("        {e}");
            }
        }
        for f in &replay.findings {
            println!("    => {f}");
        }
    }
    replay
}

fn not_refuted(d: &Derived, formula: &str) {
    let v = check_with_ty(d, formula);
    assert_eq!(
        v.status,
        EvidenceStatus::Unknown,
        "{}: `{formula}` must be neither refuted nor proved: {:?}",
        d.name(),
        v.diagnostics
    );
    assert!(v.strength.is_none());
    assert!(v.diagnostics.iter().any(|x| x.contains("refutation-only")), "{:?}", v.diagnostics);
}

#[test]
fn m2_fixtures_through_native_ty() {
    let _serial = serial();
    let mut summary = Vec::new();
    for f in fixtures::m2() {
        let d = derive(f.name, &f.program, &f);
        let (formula, atom, reach, reach_atom) = formulas(f.property);
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
        assert!(d.stats().encoding_exact, "{}: the scalar encoding must be injective", f.name);
        let tag = if f.current_main { " [current aterm main]" } else { "" };
        if f.expect_refuted {
            let r = refutation(&d, &formula, atom, true);
            assert!(!r.findings.is_empty(), "{}: a refutation names its finding", f.name);
            summary.push(format!(
                "{:<30} REFUTED `{formula}` ({} explored, {} machine states){tag} — {}",
                f.name,
                d.stats().concrete_states,
                d.stats().machine_states,
                r.findings[0]
            ));
        } else {
            not_refuted(&d, &formula);
            refutation(&d, &reach, reach_atom, false);
            println!("  ty: Unknown (refutation-only); `{reach}` refuted (non-vacuous)");
            summary.push(format!(
                "{:<30} NOT REFUTED `{formula}` (Unknown; {} explored, {} machine states); \
                 non-vacuous: `{reach}` refuted{tag}",
                f.name,
                d.stats().concrete_states,
                d.stats().machine_states
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

/// Deleting any one hygiene step of a fixed fixture makes it refuted, with a
/// replayed trace.
#[test]
fn m2_mutant_sweep() {
    let _serial = serial();
    let mut lines = Vec::new();
    for f in fixtures::m2() {
        for m in &f.hygiene {
            let program = f.program.mutate(m).unwrap_or_else(|e| panic!("{}: {e:?}", f.name));
            let d = derive(f.name, &program, &f);
            let (formula, atom, _, _) = formulas(f.property);
            let r = refutation(&d, &formula, atom, false);
            lines.push(format!(
                "{:<30} {:<48} REFUTED ({} explored) — {}",
                f.name,
                m.name(),
                d.stats().concrete_states,
                r.findings.first().cloned().unwrap_or_default()
            ));
        }
    }
    assert!(lines.len() >= 6, "{lines:#?}");
    println!("MUTANT SWEEP");
    for l in lines {
        println!("  {l}");
    }
}

/// The bare-close refutation is the CHILD's copy outliving the owner's
/// release: the trace forks a child while the holder's lock is held, the
/// holder closes, and the lock is still on the description the child holds.
#[test]
fn bare_close_is_refuted_by_a_forked_copy() {
    let _serial = serial();
    let f = fixtures::ownerlock::bare_close();
    let d = derive(f.name, &f.program, &f);
    let r = refutation(&d, &property::lock_release_formula(), property::LOCK_LEAK, false);
    let finding = &r.findings[0];
    assert!(finding.contains("holder") && finding.contains("child["), "{finding}");
    let events: Vec<&String> = r.steps.iter().flat_map(|s| &s.events).collect();
    let fork = events.iter().position(|e| e.contains("fork()")).expect("a fork");
    let lock = events
        .iter()
        .position(|e| e.contains("flock(") && e.contains("LOCK_EX"))
        .expect("the lock");
    assert!(lock < fork, "the child forks while the lock is held: {events:#?}");
}

/// The retired-number refutation is the squatter's open landing on the
/// number `adopt` closed, before the test's `F_GETFD` of it.
#[test]
fn retired_number_is_refuted_by_lowest_free_reuse() {
    let _serial = serial();
    let f = fixtures::lifeline::retired_number();
    let d = derive(f.name, &f.program, &f);
    let r =
        refutation(&d, &property::fd_identity_formula(), property::FD_IDENTITY_VIOLATION, false);
    let finding = &r.findings[0];
    assert!(finding.contains("squatter") && finding.contains("closed"), "{finding}");
    let events: Vec<&String> = r.steps.iter().flat_map(|s| &s.events).collect();
    let squat = events.iter().position(|e| e.contains("/dev/null")).expect("the squatter opens");
    let close = events
        .iter()
        .position(|e| e.contains("close(") && e.contains(":276"))
        .expect("adopt's close");
    assert!(close < squat, "the squatter takes the retired number: {events:#?}");
}
