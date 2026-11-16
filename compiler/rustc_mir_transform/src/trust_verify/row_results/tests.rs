//! Trust (T3 L4, C07r): [`RowResults`] keeps each results row with its id, reads as the
//! slice it replaced, pairs every row with its id again after a list writer, and a planted
//! misalignment is caught by the seam's row oracle.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::vc_context::{Oracle, ParityCount, VcContext, same_row};
use trust_types::{
    Formula, ProofStrength, Sort, SourceSpan, Symbol, VcKind, VerificationCondition,
    VerificationResult,
};

use super::RowResults;

fn row(message: &str, line: u32, bound: i128) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion { message: message.to_string() },
        function: Symbol::intern("demo::f"),
        location: SourceSpan {
            file: "row_results.rs".to_string(),
            line_start: line,
            col_start: 1,
            line_end: line,
            col_end: 9,
        },
        formula: Formula::Lt(
            Box::new(Formula::Var("x".into(), Sort::Int)),
            Box::new(Formula::Int(bound)),
        ),
        contract_metadata: None,
        obligation: None,
    }
}

fn unknown() -> VerificationResult {
    VerificationResult::Unknown {
        solver: Symbol::intern("row-results-test"),
        time_ms: 0,
        reason: "not asked".to_string(),
    }
}

fn proved() -> VerificationResult {
    VerificationResult::Proved {
        solver: Symbol::intern("row-results-test"),
        time_ms: 0,
        strength: ProofStrength::smt_unsat_strict_checked(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

/// `(message, line, bound)` rows, each with an `Unknown` verdict.
fn unknown_rows(rows: &[(&str, u32, i128)]) -> Vec<(VerificationCondition, VerificationResult)> {
    rows.iter().map(|&(message, line, bound)| (row(message, line, bound), unknown())).collect()
}

#[test]
fn every_row_is_interned_through_the_oracle_and_reads_as_the_slice() {
    let pairs = unknown_rows(&[("a", 1, 1), ("b", 2, 2), ("a", 1, 1)]);
    let mut context = VcContext::new();
    let results = RowResults::intern(&mut context, pairs.clone());
    assert!(results.aligned_in(&context));
    assert!(results.ids().iter().all(Option::is_some));
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 3, mismatches: 0 });
    // A reader sees the rows it was handed, in order, through every read shape.
    assert_eq!(results.len(), pairs.len());
    for ((vc, _), (expected, _)) in results.iter().zip(&pairs) {
        assert!(same_row(vc, expected));
    }
    let slice: &[(VerificationCondition, VerificationResult)] = &results;
    assert_eq!(slice[1].0.location.line_start, 2);
    let mut lines = Vec::new();
    for (vc, _) in &results {
        lines.push(vc.location.line_start);
    }
    assert_eq!(lines, [1, 2, 1]);
    // Two equal rows are two rows (one per results row), over the same formula node.
    let ids = results.ids();
    assert_ne!(ids[0], ids[2]);
    let first = context.row(ids[0].expect("interned")).expect("a row of this context");
    let third = context.row(ids[2].expect("interned")).expect("a row of this context");
    assert_eq!(first.formula(), third.formula());
}

#[test]
fn a_verdict_change_keeps_the_row_and_its_id() {
    let mut context = VcContext::new();
    let mut results = RowResults::intern(&mut context, unknown_rows(&[("a", 1, 1), ("b", 2, 2)]));
    let ids = results.ids().to_vec();
    let previous = results.set_result(1, proved());
    assert!(matches!(previous, Some(VerificationResult::Unknown { .. })));
    assert!(matches!(results[1].1, VerificationResult::Proved { .. }));
    assert!(matches!(results[0].1, VerificationResult::Unknown { .. }));
    assert_eq!(results.ids(), ids.as_slice());
    assert!(results.aligned_in(&context));
    // There is no row 2: nothing changes.
    assert!(results.set_result(2, proved()).is_none());
    assert_eq!(results.len(), 2);
    assert!(results.aligned_in(&context));
}

#[test]
fn the_seam_check_counts_every_row_and_catches_a_misalignment() {
    let mut context = VcContext::new();
    let mut results =
        RowResults::intern(&mut context, unknown_rows(&[("a", 1, 1), ("b", 2, 2), ("c", 3, 3)]));
    results.check_in(&context);
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 6, mismatches: 0 });
    // Negative control: two swapped ids no longer read back as their rows.
    results.misalign_for_test(0, 2);
    assert!(!results.aligned_in(&context));
    results.check_in(&context);
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 9, mismatches: 2 });
    // Nor do ids read in a context other than the one they were interned into.
    let other = VcContext::new();
    let elsewhere = RowResults::intern(&mut VcContext::new(), unknown_rows(&[("a", 1, 1)]));
    assert!(!elsewhere.aligned_in(&other));
    elsewhere.check_in(&other);
    assert_eq!(other.parity(Oracle::Row), ParityCount { rows: 1, mismatches: 1 });
    // The empty carrier is aligned anywhere and counts nothing.
    let empty = RowResults::default();
    assert!(empty.aligned_in(&other));
    empty.check_in(&other);
    assert_eq!(other.parity(Oracle::Row).rows, 1);
}

#[test]
fn a_rewrite_pairs_every_row_with_its_id_again() {
    let mut context = VcContext::new();
    let mut results = RowResults::intern(&mut context, unknown_rows(&[("a", 1, 1), ("b", 2, 2)]));
    let ids = results.ids().to_vec();
    // A verdict-only rewrite keeps every id and counts nothing: no row is joining.
    let seen = results.rewrite(&mut context, |rows, _| {
        rows[1].1 = proved();
        rows.len()
    });
    assert_eq!(seen, 2);
    assert_eq!(results.ids(), ids.as_slice());
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 2, mismatches: 0 });
    assert!(results.aligned_in(&context));
    assert!(matches!(results[1].1, VerificationResult::Proved { .. }));
    // A changed row joins under a new id, an appended row joins, and the rest keep theirs.
    results.rewrite(&mut context, |rows, _| {
        rows[0].0 = row("a2", 1, 7);
        rows.push((row("c", 3, 3), unknown()));
    });
    assert_eq!(results.len(), 3);
    assert_ne!(results.ids()[0], ids[0]);
    assert_eq!(results.ids()[1], ids[1]);
    assert!(results.ids().iter().all(Option::is_some));
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 4, mismatches: 0 });
    assert!(results.aligned_in(&context));
    // An insertion moves every row after it, and each joins again under a new id.
    results.rewrite(&mut context, |rows, _| rows.insert(0, (row("z", 9, 9), unknown())));
    assert_eq!(results.len(), 4);
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 8, mismatches: 0 });
    assert!(results.aligned_in(&context));
    // A writer that interns rows of its own into the context leaves the carrier aligned.
    results.rewrite(&mut context, |rows, context| {
        let _ = context.push_checked_row(&row("probe", 10, 10));
        rows.truncate(2);
    });
    assert_eq!(results.len(), 2);
    assert_eq!(context.parity(Oracle::Row), ParityCount { rows: 9, mismatches: 0 });
    assert!(results.aligned_in(&context));
}
