// BLOCKER 2 — opaque callee effect summaries, on REAL extracted MIR.
//
// THE MEASURED BLOCKER. With the shipping stage2 toolchain, both functions below
// report IDENTICALLY (`2 proved, 1 unknown`, `unsupported=2`):
//
//     pub fn close_ok(&mut self)  ensures !self.storage.flag {
//         if !self.storage.flag { return; }
//         self.storage.flag = false;
//         self.bump_other();          // does NOT write the flag  -> should PROVE
//     }
//     pub fn close_bad(&mut self) ensures !self.storage.flag {
//         if !self.storage.flag { return; }
//         self.storage.flag = false;
//         self.set_flag();            // DOES write the flag      -> must NOT prove
//     }
//
// The unknown is the visible fail-closed row:
//
//     unsupported MIR `SpecUnverifiable`: … postcondition references
//     `&mut`-parameter place `self*.0.0`, which the body writes but no conjunct
//     pins at the obligation's read version …
//
// Cause: `terminator_def_names` havocs the whole receiver at a Call (the base
// name `self`, a projection ancestor of `self*.0.0`), so the flag's version at
// the exit block is the call's token while its establishing store carries the
// statement's — nothing pins the name the obligation reads. A method that CALLS
// ANYTHING cannot discharge a `&mut self` postcondition. That is the same
// verdict for correct and incorrect code: a discrimination collapse.
//
// THE FIX under test: when the callee's own extracted body is available in the
// summary database, derive its caller-visible WRITE-SET from that MIR and havoc
// only the mapped paths. Both directions are asserted here — a summary lane that
// makes everything prove is worthless.
//
// Fixtures are REAL MIR from `-Ztrust-dump=mir:<dir>` over the source above.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::sync::Arc;

use trust_types::*;
use trust_vcgen::{FunctionSummary, SummaryDatabase};

const CLOSE_OK: &str = include_str!("fixtures/callee_effect_close_ok.json");
const CLOSE_BAD: &str = include_str!("fixtures/callee_effect_close_bad.json");
const HELPER_NO_FLAG: &str = include_str!("fixtures/callee_effect_helper_no_flag.json");
const HELPER_WRITES_FLAG: &str = include_str!("fixtures/callee_effect_helper_writes_flag.json");

fn parse(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture must deserialize")
}

/// A summary database carrying ONE callee's extracted body, keyed by the exact
/// name the extracted `Terminator::Call` carries — the same wiring the compiler
/// performs through `extracted_callee_body_for_tracing`.
fn db_with(callee_json: &str) -> SummaryDatabase {
    let callee = parse(callee_json);
    let mut db = SummaryDatabase::new();
    db.insert(
        FunctionSummary::new(callee.def_path.clone())
            .with_param_names(vec!["self".to_string()])
            .with_extracted_body(Arc::new(callee)),
    );
    db
}

/// Every VC the summary-aware entry produces (solver rows + preclassified rows).
fn all_vcs(func: &VerifiableFunction, db: &SummaryDatabase) -> Vec<VerificationCondition> {
    let (solver, discharged) = trust_vcgen::generate_vcs_with_discharge_and_summaries(func, db);
    solver.into_iter().chain(discharged.into_iter().map(|(vc, _)| vc)).collect()
}

fn spec_unverifiable_rows(vcs: &[VerificationCondition]) -> Vec<String> {
    vcs.iter()
        .filter_map(|vc| match &vc.kind {
            VcKind::UnsupportedMir { kind, detail } if kind == "SpecUnverifiable" => {
                Some(detail.clone())
            }
            _ => None,
        })
        .collect()
}

fn postcondition_formulas(vcs: &[VerificationCondition]) -> Vec<String> {
    vcs.iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .map(|vc| format!("{:?}", vc.formula))
        .collect()
}

fn postconditions(vcs: &[VerificationCondition]) -> Vec<&Formula> {
    vcs.iter().filter(|vc| matches!(vc.kind, VcKind::Postcondition)).map(|vc| &vc.formula).collect()
}

// ----------------------------------------------------------------------
// A real (if tiny) decision procedure for the pure-boolean fragment these
// obligations live in, so the assertions below are SEMANTIC — "this VC has no
// satisfying assignment" — not string matching. Trust's convention is
// SAT ⇔ violation, so UNSAT ⇔ proved.
// ----------------------------------------------------------------------

fn bool_vars(f: &Formula, out: &mut Vec<String>) {
    match f {
        Formula::Var(n, Sort::Bool) => {
            if !out.contains(n) {
                out.push(n.clone());
            }
        }
        _ => {
            for c in f.children() {
                bool_vars(c, out);
            }
        }
    }
}

/// Evaluate `f` under `env`; `None` when `f` leaves the boolean fragment.
fn eval(f: &Formula, env: &[(String, bool)]) -> Option<bool> {
    match f {
        Formula::Bool(b) => Some(*b),
        Formula::Var(n, Sort::Bool) => env.iter().find(|(k, _)| k == n).map(|(_, v)| *v),
        Formula::Not(a) => Some(!eval(a, env)?),
        Formula::And(xs) => {
            let mut acc = true;
            for x in xs {
                acc &= eval(x, env)?;
            }
            Some(acc)
        }
        Formula::Or(xs) => {
            let mut acc = false;
            for x in xs {
                acc |= eval(x, env)?;
            }
            Some(acc)
        }
        Formula::Implies(a, b) => Some(!eval(a, env)? || eval(b, env)?),
        Formula::Eq(a, b) => Some(eval(a, env)? == eval(b, env)?),
        _ => None,
    }
}

/// `Some(true)` = UNSAT (proved), `Some(false)` = SAT (a violation witness
/// exists), `None` = outside the boolean fragment (the test says so explicitly).
fn is_unsat(f: &Formula) -> Option<bool> {
    let mut vars = Vec::new();
    bool_vars(f, &mut vars);
    assert!(vars.len() <= 16, "brute force is only meant for these small VCs");
    for mask in 0u32..(1u32 << vars.len()) {
        let env: Vec<(String, bool)> =
            vars.iter().enumerate().map(|(i, n)| (n.clone(), (mask >> i) & 1 == 1)).collect();
        if eval(f, &env)? {
            return Some(false);
        }
    }
    Some(true)
}

// ======================================================================
// THE BLOCKER, reproduced at the VC layer
// ======================================================================

/// Without a callee body (the state of the world today for an opaque callee) the
/// correct function is NOT provable: the conservative receiver havoc erases the
/// flag store and the fail-closed `SpecUnverifiable` row is emitted.
#[test]
fn without_a_callee_body_the_correct_function_is_not_provable() {
    let vcs = all_vcs(&parse(CLOSE_OK), &SummaryDatabase::new());
    let rows = spec_unverifiable_rows(&vcs);
    assert!(
        rows.iter().any(|d| d.contains("self*.0.0")),
        "the measured blocker must reproduce: expected a SpecUnverifiable row over \
         `self*.0.0`, got {rows:?}"
    );
    // The path THROUGH the call has no dischargeable obligation at all — its
    // clause degenerated into the fail-closed row above. Only the early-return
    // path (which executes no call) survives as a real obligation.
    let posts = postconditions(&vcs);
    assert!(
        posts.len() < 2,
        "the call path's postcondition must have collapsed into the fail-closed row: {:?}",
        postcondition_formulas(&vcs)
    );
}

// ======================================================================
// POSITIVE: the helper does not write the flag -> the clause becomes provable
// ======================================================================

#[test]
fn helper_that_does_not_write_the_flag_makes_the_clause_provable() {
    let func = parse(CLOSE_OK);
    let db = db_with(HELPER_NO_FLAG);
    let vcs = all_vcs(&func, &db);

    let rows = spec_unverifiable_rows(&vcs);
    assert!(
        !rows.iter().any(|d| d.contains("self*.0.0")),
        "the callee's own MIR proves it never writes `self.storage.flag`, so the \
         fail-closed row must be gone; got {rows:?}"
    );

    let dbg = postcondition_formulas(&vcs);
    let posts = postconditions(&vcs);
    assert_eq!(
        posts.len(),
        2,
        "one obligation per return path (early return + the path through the call): {dbg:?}"
    );

    // SEMANTIC check: every path obligation is UNSAT, i.e. no assignment
    // violates the clause. (Trust's convention: SAT ⇔ violation.)
    for (f, d) in posts.iter().zip(dbg.iter()) {
        assert_eq!(
            is_unsat(f),
            Some(true),
            "every postcondition path obligation must be UNSAT (proved): {d}"
        );
    }

    // And the reason the CALL path is now UNSAT is the surviving pin: the
    // body's `self.storage.flag = false` store, at the exact version the
    // obligation reads. That conjunct is what the conservative receiver havoc
    // used to erase.
    assert!(
        dbg.iter().any(|f| f.contains("Eq(Var(\"self*.0.0#") && f.contains("Bool(false)")),
        "the store's pin of the flag must survive the call: {dbg:?}"
    );
}

// ======================================================================
// NEGATIVE: the helper DOES write the flag -> the clause must NOT be provable
// ======================================================================

#[test]
fn helper_that_writes_the_flag_is_never_credited() {
    let func = parse(CLOSE_BAD);
    let db = db_with(HELPER_WRITES_FLAG);
    let vcs = all_vcs(&func, &db);

    // The write-set CONTAINS the flag, so the call still havocs it: the pin
    // dies and the lane falls back to the SAME visible fail-closed row it emits
    // for any opaque callee. What must NEVER happen is a postcondition
    // obligation for the CALL path that comes back UNSAT off the pre-call store.
    let dbg = postcondition_formulas(&vcs);
    let posts = postconditions(&vcs);
    assert!(
        posts.len() < 2,
        "the call path must NOT acquire a dischargeable obligation when the callee \
         writes the very field the clause is about: {dbg:?}"
    );
    let rows = spec_unverifiable_rows(&vcs);
    assert!(
        rows.iter().any(|d| d.contains("self*.0.0")),
        "the violating case must stay fail-closed: rows={rows:?} posts={dbg:?}"
    );
}

/// The two directions must DIFFER. Before this lane they were byte-identical
/// verdicts — the discrimination collapse this work exists to remove.
#[test]
fn the_two_directions_are_distinguished() {
    let ok = all_vcs(&parse(CLOSE_OK), &db_with(HELPER_NO_FLAG));
    let bad = all_vcs(&parse(CLOSE_BAD), &db_with(HELPER_WRITES_FLAG));

    let ok_unverifiable = spec_unverifiable_rows(&ok).iter().any(|d| d.contains("self*.0.0"));
    let bad_unverifiable = spec_unverifiable_rows(&bad).iter().any(|d| d.contains("self*.0.0"));
    assert!(!ok_unverifiable, "the correct function must clear the fail-closed row");
    assert!(bad_unverifiable, "the violating function must keep it");
}

// ======================================================================
// The write-set must be DERIVED, never assumed
// ======================================================================

/// A summary with NO extracted body grants nothing. This is the property that
/// keeps the lane from being an unverified user assertion: absence of a body is
/// "unknown", not "writes nothing".
#[test]
fn a_summary_without_a_body_grants_nothing() {
    let func = parse(CLOSE_OK);
    let callee = parse(HELPER_NO_FLAG);
    let mut db = SummaryDatabase::new();
    db.insert(FunctionSummary::new(callee.def_path.clone()));

    let rows = spec_unverifiable_rows(&all_vcs(&func, &db));
    assert!(
        rows.iter().any(|d| d.contains("self*.0.0")),
        "a body-less summary must leave the conservative havoc in place: {rows:?}"
    );
}

/// A body registered under the WRONG callee name grants nothing either.
#[test]
fn a_body_under_the_wrong_name_grants_nothing() {
    let func = parse(CLOSE_OK);
    let callee = parse(HELPER_NO_FLAG);
    let mut db = SummaryDatabase::new();
    db.insert(
        FunctionSummary::new("p2::G::some_other_method").with_extracted_body(Arc::new(callee)),
    );

    let rows = spec_unverifiable_rows(&all_vcs(&func, &db));
    assert!(
        rows.iter().any(|d| d.contains("self*.0.0")),
        "a misattributed body must not narrow this call: {rows:?}"
    );
}
