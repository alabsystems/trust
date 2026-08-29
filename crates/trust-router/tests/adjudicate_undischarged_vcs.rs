#![cfg(feature = "ay-backend")]
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Trust: ADJUDICATE THE UNDISCHARGED (2026-08-24).
//!
//! `vc_refute` discharges a safety obligation by reconstructing a kernel proof.
//! When it returns `None` the obligation stays undischarged, and the census counts
//! it — but that count mixes two entirely different situations:
//!
//!   * an ENGINE GAP — the obligation is TRUE and the refutation fragment could not
//!     find the contradiction; and
//!   * a CORRECT DECLINE — the obligation is genuinely SATISFIABLE, i.e. the code
//!     really can overflow / index out of bounds. No verifier can or should prove it.
//!
//! `trust-clean` cannot tell them apart: it depends on neither `ay` nor
//! `trust-router`. So it logs the undischarged FORMULAS
//! (`TRUST_UNDISCHARGED_VC_LOG`) and this test adjudicates them with a complete
//! solver on the other side of that dependency edge.
//!
//! Convention (`VerificationCondition::formula`): the formula is ASSERTED and
//! checked for SAT. UNSAT ⇒ the property holds ⇒ the refuter had a gap.
//! SAT ⇒ counterexample ⇒ declining was correct.
//!
//! Point it at a log with `TRUST_ADJUDICATE_VC_LOG=<file>`; without one it is a
//! no-op, so it costs the default suite nothing.

use trust_types::{Formula, SourceSpan, Symbol, VcKind, VerificationCondition, VerificationResult};

#[test]
fn adjudicate_undischarged_vcs() {
    let Ok(path) = std::env::var("TRUST_ADJUDICATE_VC_LOG") else {
        eprintln!("TRUST_ADJUDICATE_VC_LOG unset — nothing to adjudicate");
        return;
    };
    let Ok(text) = std::fs::read_to_string(&path) else {
        panic!("cannot read {path}");
    };
    let router = trust_router::Router::deterministic_in_process_ay(10_000);

    let (mut gap, mut correct, mut unknown, mut skipped) = (0usize, 0usize, 0usize, 0usize);
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let Ok(formula) = serde_json::from_str::<Formula>(line) else {
            skipped += 1;
            continue;
        };
        // A vacuous `true` is trivially SAT and tells us nothing — it is the
        // non-proposition class, already accounted for separately.
        if matches!(&formula, Formula::Bool(true))
            || matches!(&formula, Formula::And(cs) if cs.iter().all(|c| matches!(c, Formula::Bool(true))))
        {
            skipped += 1;
            continue;
        }
        let vc = VerificationCondition {
            kind: VcKind::Assertion { message: "adjudicated".to_string() },
            function: Symbol::intern("adjudicated"),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        };
        match router.verify_one(&vc) {
            VerificationResult::Proved { .. } => {
                gap += 1;
                if let Ok(out) = std::env::var("TRUST_GAP_DUMP") {
                    use std::io::Write;
                    if let Ok(mut fh) =
                        std::fs::OpenOptions::new().create(true).append(true).open(out)
                    {
                        let _ = writeln!(fh, "{line}");
                    }
                }
            }
            VerificationResult::Failed { .. } => correct += 1,
            _ => unknown += 1,
        }
    }
    let decided = gap + correct;
    eprintln!("\n=== adjudicating undischarged safety obligations ===");
    eprintln!("  ENGINE GAP (UNSAT — obligation is TRUE, refuter missed it): {gap}");
    eprintln!("  CORRECT DECLINE (SAT — the code really can fail):           {correct}");
    eprintln!("  undetermined by the solver:                                 {unknown}");
    eprintln!("  skipped (vacuous / unparsable):                             {skipped}");
    if decided > 0 {
        eprintln!(
            "  of the DECIDED: {:.1}% engine gap, {:.1}% correct decline",
            100.0 * gap as f64 / decided as f64,
            100.0 * correct as f64 / decided as f64
        );
    }
}
