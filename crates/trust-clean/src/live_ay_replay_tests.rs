//! LIVE ay-proof -> trust-clean replay harness (TRUST-22).
//!
//! Every other certification test in this crate replays a HAND-BUILT proof
//! (`e2e_tests` mints `SolverProof`s by hand; `ay_proof_bridge`'s tests translate
//! hand-written rule lists). None of them ever asked the PINNED ay to solve
//! anything, so nothing measured what this crate's replay does with the proof ay
//! actually emits — and `logic_classification` could not say whether a
//! `div`/`mod`-by-numeral step certifies, so it keeps that shape at
//! `SmtLogic::Unknown`.
//!
//! This harness closes the measurement gap, and only that gap:
//!
//! 1. ay (the `first-party/ay` pin, linked in-process) solves each obligation
//!    with `:produce-proofs` on and must answer UNSAT with a strict-verified
//!    proof artifact — otherwise the row measures nothing and the test fails.
//! 2. The artifact's Alethe text is fed through this crate's OWN replay path,
//!    stage by stage: `parse_ay_proof` -> `translate_ay_proof` ->
//!    `reconstruction::reconstruct` -> `clean_bridge::serialize_proof_cert_from_lean_term`
//!    -> `generate_certificate` (the clean-kernel check that mints `Certified`).
//!    The scope gate in `certify_from_solver_proof` is deliberately NOT in this
//!    path: the question is what the replay would do if the scope let it run.
//! 3. The production entry `CertificationPipeline::certify_from_solver_proof` is
//!    also run on the same proof, so the row records what the shipped pipeline
//!    actually returns.
//!
//! A linear (QF_LIA) control rides beside the `div`/`mod` rows. Without it a
//! refusal on the `div` row could be read as "div is the problem" when the
//! replay refuses every live proof.
//!
//! MEASURED 2026-09-23 and re-measured 2026-09-24 (ay pin `9d49d503e`), and
//! recorded in `docs/TCB.md`:
//!
//! * `div-by-2` — ay computes UNSAT, its own mandatory strict certification
//!   rejects the proof ("uses unverified trust rule"), and it answers Unknown
//!   with NO artifact. There is nothing to replay. The same holds with the
//!   obligation declared `QF_LIA` or `ALL` instead of `QF_NIA`.
//! * `mod-by-2` — UNSAT with a strict-verified artifact whose Alethe text carries
//!   the mod lemma as `:rule hole`. The replay does NOT certify it.
//! * `lia-control` — UNSAT, strict-verified, `la_generic` + `th_resolution`. The
//!   replay does NOT certify it either, for two reasons upstream of any theory:
//!   `parse_ay_proof` (trust-proof-cert) predates ay's Alethe export and does not
//!   parse it — it reads the `assume`/`step` command names as rule names — and
//!   `reconstruction::reconstruct` wraps every term in `Trust.VC.mk`, a constant
//!   the kernel environment `clean_bridge` builds never declares, so the kernel
//!   rejects every term from this route (`Unknown constant: Trust.VC.mk`). The
//!   shipped entry falls back to `Trusted`.
//!
//! So the harness answers the div/mod question negatively, and it also shows that
//! this replay certifies no live ay proof at all today — which the `div`/`mod`
//! assertions below do not depend on, and which the control's row prints.
//!
//! NOT feature-gated, deliberately: the pinned ay is ALREADY linked into this
//! crate (`clean-elab` -> `clean-auto` -> `ay`, `default-features = false`), so a
//! gate would buy no build time and would only keep the measurement out of the
//! default test run. The `ay` dev-dependency names that same package with the same
//! features, so it adds nothing to the graph.
//!
//! Run: `targo --unverified test -p trust-clean --lib live_ay_replay -- --nocapture`.

#![cfg(test)]

use std::collections::{BTreeMap, BTreeSet};

use trust_types::{
    Formula, ProofStrength, Sort, SourceSpan, VcKind, VerificationCondition, VerificationResult,
};

use crate::certification::{CertificationPipeline, CertificationResult};
use crate::logic_classification::{SmtLogic, classify_formula};

/// One obligation: the SMT-LIB text ay solves, and the SAME violation as a Trust
/// `Formula` (the VC whose theorem the replayed term must prove). Every dividend is
/// constrained non-negative, where SMT-LIB's Euclidean `div`/`mod` and Rust's
/// truncating `/`/`%` (`Formula::Div`/`Formula::Rem`) agree.
struct Obligation {
    name: &'static str,
    logic: ay::Logic,
    smt2: &'static str,
    formula: Formula,
}

fn x() -> Formula {
    Formula::Var("x".into(), Sort::Int)
}

fn int(n: i128) -> Formula {
    Formula::Int(n)
}

fn obligations() -> Vec<Obligation> {
    vec![
        // CONTROL — pure QF_LIA, Farkas-refutable: x > 2 and x < 1.
        Obligation {
            name: "lia-control",
            logic: ay::Logic::QfLia,
            smt2: "(declare-const x Int)\n(assert (> x 2))\n(assert (< x 1))\n",
            formula: Formula::And(vec![
                Formula::Gt(Box::new(x()), Box::new(int(2))),
                Formula::Lt(Box::new(x()), Box::new(int(1))),
            ]),
        },
        // DIV BY A NUMERAL — x >= 0, x div 2 = 3, x > 7 (div = 3 pins x to {6, 7}).
        Obligation {
            name: "div-by-2",
            logic: ay::Logic::QfNia,
            smt2: "(declare-const x Int)\n(assert (>= x 0))\n(assert (= (div x 2) 3))\n\
                   (assert (> x 7))\n",
            formula: Formula::And(vec![
                Formula::Ge(Box::new(x()), Box::new(int(0))),
                Formula::Eq(
                    Box::new(Formula::Div(Box::new(x()), Box::new(int(2)))),
                    Box::new(int(3)),
                ),
                Formula::Gt(Box::new(x()), Box::new(int(7))),
            ]),
        },
        // MOD BY A NUMERAL — x >= 0 and x mod 2 > 1 (the remainder is 0 or 1).
        Obligation {
            name: "mod-by-2",
            logic: ay::Logic::QfNia,
            smt2: "(declare-const x Int)\n(assert (>= x 0))\n(assert (> (mod x 2) 1))\n",
            formula: Formula::And(vec![
                Formula::Ge(Box::new(x()), Box::new(int(0))),
                Formula::Gt(
                    Box::new(Formula::Rem(Box::new(x()), Box::new(int(2)))),
                    Box::new(int(1)),
                ),
            ]),
        },
    ]
}

/// How far this crate's replay got with one live proof.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Replay {
    /// `generate_certificate` accepted the replayed term: the clean kernel
    /// type-checked it against the VC theorem with an axiom-free closure.
    Certified,
    /// The replay stopped at `stage`, for `reason`.
    Refused { stage: &'static str, reason: String },
}

impl Replay {
    fn is_certified(&self) -> bool {
        matches!(self, Replay::Certified)
    }
}

/// What the pinned ay answered for one obligation.
enum AyAnswer {
    /// UNSAT with an exported proof artifact.
    Unsat(Box<ay::UnsatProofArtifact>),
    /// Anything else — no proof to replay. `reason` is ay's own `get_reason_unknown`.
    NoProof { verdict: String, reason: Option<String> },
}

/// One measured row.
struct Row {
    name: &'static str,
    classified: SmtLogic,
    /// `None` when ay exported no proof; otherwise the artifact's facts.
    proof: Option<ProofFacts>,
    no_proof: Option<String>,
}

/// The facts one live proof yields, and what this crate's replay made of it.
struct ProofFacts {
    strict_verified: bool,
    ay_clean_supported: bool,
    alethe_rules: BTreeMap<String, usize>,
    /// The rule names `parse_ay_proof` read out of the Alethe text.
    parsed_rules: BTreeSet<String>,
    parsed_steps: usize,
    replay: Replay,
    production: String,
}

fn vc(formula: &Formula) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion { message: "live-ay-replay".to_string() },
        function: "live_ay_replay".into(),
        location: SourceSpan::default(),
        formula: formula.clone(),
        contract_metadata: None,
        obligation: None,
    }
}

fn proved() -> VerificationResult {
    VerificationResult::Proved {
        solver: "ay".into(),
        time_ms: 0,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

/// `:rule <name>` occurrences in an Alethe document (plus `assume` lines).
fn alethe_rule_histogram(alethe: &str) -> BTreeMap<String, usize> {
    let mut hist = BTreeMap::new();
    for line in alethe.lines() {
        let line = line.trim();
        if line.starts_with("(assume ") {
            *hist.entry("assume".to_string()).or_insert(0) += 1;
        }
        if let Some(rest) = line.split(":rule ").nth(1) {
            let rule: String =
                rest.chars().take_while(|c| !c.is_whitespace() && *c != ')').collect();
            *hist.entry(rule).or_insert(0) += 1;
        }
    }
    hist
}

/// Solve `ob` with the pinned ay under `:produce-proofs`, declaring `logic`.
fn solve(ob: &Obligation, logic: ay::Logic) -> AyAnswer {
    let mut solver = ay::Solver::new(logic);
    solver.set_produce_proofs(true);
    solver.parse_smtlib2(ob.smt2).unwrap_or_else(|e| panic!("{}: ay parse: {e:?}", ob.name));
    let result = solver.check_sat();
    if result.is_unsat()
        && let Some(artifact) = solver.export_last_unsat_artifact()
    {
        return AyAnswer::Unsat(Box::new(artifact));
    }
    AyAnswer::NoProof { verdict: format!("{result:?}"), reason: solver.get_reason_unknown() }
}

/// The rule names `parse_ay_proof` reads out of `alethe`.
fn parsed_rules(alethe: &str) -> BTreeSet<String> {
    trust_proof_cert::ay_certificate::parse_ay_proof(alethe, [0u8; 32], 0)
        .map(|c| c.proof_steps.into_iter().map(|s| s.rule_name).collect())
        .unwrap_or_default()
}

/// Replay `alethe` through this crate's own path, stage by stage, ending at the
/// clean-kernel check that mints `Certified`.
fn replay(ob: &Obligation, alethe: &str) -> (usize, Replay) {
    let vc = vc(&ob.formula);
    let ay_cert = match trust_proof_cert::ay_certificate::parse_ay_proof(alethe, [0u8; 32], 0) {
        Ok(c) => c,
        Err(e) => return (0, Replay::Refused { stage: "parse_ay_proof", reason: e.to_string() }),
    };
    let parsed = ay_cert.proof_steps.len();
    let solver_proof = match crate::ay_proof_bridge::translate_ay_proof(&ay_cert) {
        Ok(p) => p,
        Err(e) => {
            return (
                parsed,
                Replay::Refused { stage: "translate_ay_proof", reason: e.to_string() },
            );
        }
    };
    let term = match crate::reconstruction::reconstruct(&solver_proof, &vc) {
        Ok(t) => t,
        Err(e) => return (parsed, Replay::Refused { stage: "reconstruct", reason: e.to_string() }),
    };
    let bytes = match crate::clean_bridge::serialize_proof_cert_from_lean_term(&term) {
        Ok(b) => b,
        Err(e) => {
            return (parsed, Replay::Refused { stage: "serialize", reason: e.to_string() });
        }
    };
    match crate::certificate::generate_certificate(&vc, &proved(), bytes, "ay via live-ay-replay") {
        Ok(_) => (parsed, Replay::Certified),
        Err(e) => (parsed, Replay::Refused { stage: "clean kernel", reason: e.to_string() }),
    }
}

/// What the shipped entry `certify_from_solver_proof` returns on the same proof.
fn production(ob: &Obligation, alethe: &str) -> String {
    let Ok(ay_cert) = trust_proof_cert::ay_certificate::parse_ay_proof(alethe, [0u8; 32], 0) else {
        return "parse_ay_proof failed".to_string();
    };
    let Ok(solver_proof) = crate::ay_proof_bridge::translate_ay_proof(&ay_cert) else {
        return "translate_ay_proof failed".to_string();
    };
    match CertificationPipeline::new().certify_from_solver_proof(
        &vc(&ob.formula),
        &proved(),
        &solver_proof,
    ) {
        CertificationResult::Certified { .. } => "Certified".to_string(),
        // `Trusted` carries a certificate, not a reason: it is the
        // `generate_certificate_unchecked` fallback the entry takes when the
        // kernel rejects the reconstructed term.
        CertificationResult::Trusted { .. } => {
            "Trusted (kernel rejected the reconstructed term; unchecked fallback)".to_string()
        }
        CertificationResult::Rejected { reason, .. } => format!("Rejected: {reason}"),
        CertificationResult::Skipped { reason } => format!("Skipped: {reason}"),
    }
}

fn measure(ob: &Obligation) -> Row {
    let classified = classify_formula(&ob.formula);
    match solve(ob, ob.logic) {
        AyAnswer::Unsat(artifact) => {
            let (parsed_steps, replay) = replay(ob, &artifact.alethe);
            Row {
                name: ob.name,
                classified,
                proof: Some(ProofFacts {
                    strict_verified: matches!(
                        artifact.strict_verdict,
                        ay::StrictProofVerdict::Verified(_)
                    ),
                    ay_clean_supported: artifact.clean_supported,
                    alethe_rules: alethe_rule_histogram(&artifact.alethe),
                    parsed_rules: parsed_rules(&artifact.alethe),
                    parsed_steps,
                    replay,
                    production: production(ob, &artifact.alethe),
                }),
                no_proof: None,
            }
        }
        AyAnswer::NoProof { verdict, reason } => Row {
            name: ob.name,
            classified,
            proof: None,
            no_proof: Some(format!("{verdict} reason={reason:?}")),
        },
    }
}

fn row<'a>(rows: &'a [Row], name: &str) -> &'a Row {
    rows.iter().find(|r| r.name == name).unwrap_or_else(|| panic!("no row {name}"))
}

/// THE MEASUREMENT. Prints one row per obligation, then pins what was measured —
/// each assertion is a tripwire that must fail, and send someone back to
/// `classify_formula`'s NONLINEAR arm, the day the fact under it changes.
#[test]
fn live_ay_replay_div_mod_by_numeral_measurement() {
    let rows: Vec<Row> = obligations().iter().map(measure).collect();
    for r in &rows {
        match (&r.proof, &r.no_proof) {
            (Some(p), _) => eprintln!(
                "LIVE-AY-REPLAY {name}: classify={cls} ay=UNSAT strict_verified={sv} \
                 ay.clean_supported={cs} alethe_rules={rules:?} parsed_steps={ps} \
                 parsed_rules={pr:?} replay={replay:?} production={prod}",
                name = r.name,
                cls = r.classified.name(),
                sv = p.strict_verified,
                cs = p.ay_clean_supported,
                rules = p.alethe_rules,
                ps = p.parsed_steps,
                pr = p.parsed_rules,
                replay = p.replay,
                prod = p.production,
            ),
            (None, Some(why)) => eprintln!(
                "LIVE-AY-REPLAY {name}: classify={cls} ay=NO PROOF ({why})",
                name = r.name,
                cls = r.classified.name(),
            ),
            (None, None) => unreachable!("a row is either a proof or its absence"),
        }
    }

    // The control must be a real live proof, or no row below measures the replay.
    let control = row(&rows, "lia-control").proof.as_ref().expect(
        "lia-control: the pinned ay must answer UNSAT with an exported proof — without a \
         live proof of a plain QF_LIA obligation this harness measures nothing",
    );
    assert!(control.strict_verified, "lia-control: ay's proof must be strict-verified");

    // DIV BY A NUMERAL: the pinned ay exports NO proof at all (it computes UNSAT, then
    // its own mandatory strict certification rejects the proof, so it answers Unknown).
    // There is nothing for any replay to reconstruct.
    let div = row(&rows, "div-by-2");
    assert!(
        div.proof.is_none(),
        "div-by-2: the pinned ay now EXPORTS a proof for a div-by-numeral obligation — \
         this harness's replay row for it is now the measurement `classify_formula`'s \
         NONLINEAR arm is waiting for; read it before changing the pin"
    );

    // MOD BY A NUMERAL: ay exports a strict-verified proof, and this crate's replay does
    // NOT certify it.
    let modulo = row(&rows, "mod-by-2").proof.as_ref().expect(
        "mod-by-2: the pinned ay must answer UNSAT with an exported proof (measured \
         2026-09-23); if it no longer does, the replay row below is unmeasured",
    );
    assert!(modulo.strict_verified, "mod-by-2: ay's proof must be strict-verified");
    assert!(
        !modulo.replay.is_certified(),
        "mod-by-2: trust-clean's replay now CERTIFIES a live ay proof of a by-numeral mod \
         obligation — revisit `classify_formula`'s NONLINEAR arm with this measurement \
         ({:?})",
        modulo.replay
    );

    // THE DECLARED LOGIC DOES NOT DECIDE EITHER ANSWER. The rows above declare `QF_NIA`,
    // the logic line `classify_formula`'s NONLINEAR arm keeps for these shapes. The same
    // obligations declared `QF_LIA` and `ALL` get the same answers: no div proof, and a
    // strict-verified mod proof. So a different routing of the logic line would not hand
    // the replay a div proof either.
    for ob in obligations().iter().filter(|ob| ob.name != "lia-control") {
        for (logic_name, logic) in [("QF_LIA", ay::Logic::QfLia), ("ALL", ay::Logic::All)] {
            match (ob.name, solve(ob, logic)) {
                ("div-by-2", AyAnswer::NoProof { .. }) => {}
                ("mod-by-2", AyAnswer::Unsat(a))
                    if matches!(a.strict_verdict, ay::StrictProofVerdict::Verified(_)) => {}
                (name, AyAnswer::Unsat(_)) => {
                    panic!("{name} declared {logic_name}: the answer differs from the QF_NIA row")
                }
                (name, AyAnswer::NoProof { verdict, reason }) => panic!(
                    "{name} declared {logic_name}: no proof ({verdict}, {reason:?}), unlike \
                     the QF_NIA row"
                ),
            }
        }
    }

    // The scope stays where the measurement leaves it.
    for name in ["div-by-2", "mod-by-2"] {
        assert_eq!(
            row(&rows, name).classified,
            SmtLogic::Unknown,
            "{name}: the certification scope moved without a measurement"
        );
    }
}
