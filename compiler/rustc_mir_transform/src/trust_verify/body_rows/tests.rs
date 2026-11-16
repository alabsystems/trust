//! Trust (T3 L4, C07): [`BodyRows`] keeps each eager row with its id through every
//! operation the consumed path performs, and a planted misalignment is caught.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::vc_context::{Oracle, ParityCount, VcContext};
use trust_types::{Formula, Sort, SourceSpan, Symbol, VcKind, VerificationCondition};

use super::BodyRows;

fn row(message: &str, line: u32, bound: i128) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion { message: message.to_string() },
        function: Symbol::intern("demo::f"),
        location: SourceSpan {
            file: "body_rows.rs".to_string(),
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

fn generated(rows: &mut VcContext, vcs: Vec<VerificationCondition>) -> BodyRows {
    let ids = vcs.iter().map(|vc| rows.push_checked_row(vc).ok()).collect();
    BodyRows::from_generation(rows, vcs, ids)
}

#[test]
fn rows_and_ids_stay_aligned_through_every_operation() {
    let mut rows = VcContext::new();
    let mut body = generated(
        &mut rows,
        vec![row("a", 1, 1), row("b", 2, 2), row("a", 1, 1), row("c", 3, 3), row("d", 4, 4)],
    );
    assert!(body.aligned_in(&rows));
    // The dedupe keeps the first of each key, with its own id.
    let first_id = body.ids()[0];
    body.dedupe_by(|vc| Some((vc.location.line_start, format!("{:?}", vc.formula))));
    assert_eq!(body.vcs().len(), 4);
    assert_eq!(body.ids()[0], first_id);
    assert!(body.aligned_in(&rows));
    // A filter drops a row and its id together.
    body.filter(|vc| vc.location.line_start != 2);
    assert_eq!(body.vcs().iter().map(|vc| vc.location.line_start).collect::<Vec<_>>(), [1, 3, 4]);
    assert!(body.aligned_in(&rows));
    // A flip that rewrites one row, reorders two and appends one: the untouched first row
    // keeps its id, every other row joins through the oracle.
    let kept_id = body.ids()[0];
    let joined_before = rows.parity(Oracle::Row).rows;
    let label = body.flip(&mut rows, |mut vcs| {
        vcs[1] = row("c", 3, 30);
        vcs.swap(1, 2);
        vcs.push(row("e", 5, 5));
        (vcs, "flipped")
    });
    assert_eq!(label, "flipped");
    assert_eq!(body.ids()[0], kept_id);
    assert!(body.aligned_in(&rows));
    assert_eq!(rows.parity(Oracle::Row).rows, joined_before + 3);
    // Appended rows join through the oracle too.
    body.extend(&mut rows, [row("f", 6, 6), row("g", 7, 7)]);
    assert_eq!(body.vcs().len(), 6);
    assert!(body.aligned_in(&rows));
    // Every join agreed.
    assert_eq!(rows.parity(Oracle::Row).mismatches, 0);
    assert_eq!(rows.parity(Oracle::Row), ParityCount { rows: 5 + 3 + 2, mismatches: 0 });
}

#[test]
fn a_misaligned_id_is_caught() {
    let mut rows = VcContext::new();
    let mut body = generated(&mut rows, vec![row("a", 1, 1), row("b", 2, 2), row("c", 3, 3)]);
    assert!(body.aligned_in(&rows));
    body.misalign_for_test(0, 2);
    assert!(!body.aligned_in(&rows), "swapped ids must not read back as their rows");
    // An id of another context is not this context's row either.
    let mut foreign = VcContext::new();
    let other = generated(&mut foreign, vec![row("a", 1, 1)]);
    assert!(other.aligned_in(&foreign) && !other.aligned_in(&rows));
}

#[test]
fn lists_of_different_lengths_are_interned_again() {
    let mut rows = VcContext::new();
    let vcs = vec![row("a", 1, 1), row("b", 2, 2)];
    let body = BodyRows::from_generation(&mut rows, vcs, Vec::new());
    assert_eq!(body.ids().len(), 2);
    assert!(body.aligned_in(&rows));
}
