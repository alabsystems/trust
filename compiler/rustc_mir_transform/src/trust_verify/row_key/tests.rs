// Tests for `trust_verify::row_key` (T3 L4, C09): the canonical string decides and the
// identity oracle counts every comparison beside it, in either direction (L4-ORACLE-1); a
// seeded disagreement at `matches_row` is counted while the canonical decision stands;
// ROW-IDENTITY-1's negative control; the dedupe's partition; what the oracle cannot judge is
// counted apart (L4-C09-7); a count lands in the running pass's row, and one no row writes
// reaches the crate's (L4-C09-6); the oracle context's life; and the source census that keeps
// every canonical string inside a key.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::BTreeMap;
use std::sync::Arc;

use trust_types::vc_context::{ParityCount, VcContext};
use trust_types::{Formula, Sort, SourceSpan, Symbol, VcKind, VerificationCondition};

use super::super::{BodyRows, ResultProofAuthority, dedupe_exact_vcs, exact_result_row_identity};
use super::{Installed, Ledger, RowKey, Tally, count_partition};

fn span(line: u32) -> SourceSpan {
    SourceSpan {
        file: "t.rs".to_string(),
        line_start: line,
        col_start: 1,
        line_end: line,
        col_end: 9,
    }
}

/// A division-by-zero row at `line` over `d < bound`.
fn vc(line: u32, bound: i128) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: Symbol::intern("demo::f"),
        location: span(line),
        formula: Formula::Lt(
            Box::new(Formula::Var("d".into(), Sort::Int)),
            Box::new(Formula::Int(bound)),
        ),
        contract_metadata: None,
        obligation: None,
    }
}

fn count(rows: u64, mismatches: u64) -> ParityCount {
    ParityCount { rows, mismatches }
}

#[test]
fn the_canonical_string_decides_and_each_comparison_is_counted() {
    let (_installed, context) = Installed::for_test();
    let a = RowKey::of(&vc(1, 0)).expect("a key");
    let again = RowKey::of(&vc(1, 0)).expect("a key");
    let moved = RowKey::of(&vc(2, 0)).expect("a key");
    let other_formula = RowKey::of(&vc(1, 1)).expect("a key");
    assert!(a.is_identified() && moved.is_identified(), "the oracle runs");
    assert!(a == again);
    assert!(a != moved, "the span tells two rows apart");
    assert!(a != other_formula);
    assert_eq!(context.parity(), count(3, 0), "every comparison is counted, and agrees");
}

#[test]
fn nothing_is_identified_or_counted_where_no_oracle_runs() {
    assert!(!super::oracle_runs());
    let a = RowKey::of(&vc(1, 0)).expect("a key");
    assert!(!a.is_identified());
    assert!(a == RowKey::of(&vc(1, 0)).expect("a key"), "the canonical string still decides");
    assert!(a != RowKey::of(&vc(2, 0)).expect("a key"));
}

/// A disagreement seeded into a sealed row (its identity is another row's) is counted at
/// `matches_row`, and the canonical decision stands: the authority still binds its row.
#[test]
fn a_seeded_disagreement_at_matches_row_is_counted_and_the_canonical_decision_stands() {
    let (_installed, context) = Installed::for_test();
    let row_vc = vc(1, 0);
    let elsewhere = exact_result_row_identity(0, &vc(2, 0)).expect("a row");
    let mut row = exact_result_row_identity(0, &row_vc).expect("a row");
    let authority = ResultProofAuthority::InterproceduralCalleeClosure { row: row.clone() };
    assert!(authority.matches_row(0, &row_vc, None), "control");
    assert_eq!(context.parity(), count(1, 0));
    row.canonical_vc = row.canonical_vc.clone().with_identity_of_for_test(&elsewhere.canonical_vc);
    let seeded = ResultProofAuthority::InterproceduralCalleeClosure { row };
    assert!(seeded.matches_row(0, &row_vc, None), "the canonical string decides");
    assert_eq!(context.parity(), count(2, 1), "the identities disagree, and it is counted");
}

/// ROW-IDENTITY-1's negative control: an identity that drops what tells two rows apart (here
/// the span: the second key carries the first's identity) merges two rows the canonical
/// partition separates. The canonical keys still keep them apart, and the oracle counts the
/// disagreement, by a comparison and by a partition.
#[test]
fn negative_control_an_identity_that_drops_the_span_is_counted() {
    let (_installed, context) = Installed::for_test();
    let a = RowKey::of(&vc(1, 0)).expect("a key");
    let dropped = RowKey::of(&vc(2, 0)).expect("a key").with_identity_of_for_test(&a);
    assert!(a != dropped, "the canonical keys keep the rows apart");
    assert_eq!(context.parity(), count(1, 1));
    count_partition([&a, &dropped]);
    assert_eq!(context.parity(), count(3, 2), "the partition counts the merged row");
    // Control: the honest keys partition alike.
    let honest = RowKey::of(&vc(2, 0)).expect("a key");
    count_partition([&a, &honest, &a.clone()]);
    assert_eq!(context.parity(), count(6, 2));
}

/// The dedupe keeps what the canonical keys keep, and counts its identity partition and its
/// lookups, with no disagreement on honest rows.
#[test]
fn the_dedupe_counts_its_identity_partition() {
    let (_installed, context) = Installed::for_test();
    let mut rows_context = VcContext::new();
    let vcs = vec![vc(1, 0), vc(1, 0), vc(2, 0)];
    let ids = vcs.iter().map(|vc| rows_context.push_checked_row(vc).ok()).collect();
    let mut rows = BodyRows::from_generation(&mut rows_context, vcs, ids);
    dedupe_exact_vcs(&mut rows);
    assert_eq!(rows.vcs().len(), 2);
    let parity = context.parity();
    assert!(parity.rows >= 3, "one count per row of the partition, at least: {parity:?}");
    assert_eq!(parity.mismatches, 0);
}

fn tally(judged: ParityCount, unjudged: ParityCount) -> Tally {
    Tally { judged, unjudged }
}

/// A ledger of the test's own, so the crate's is never read by a test.
fn ledger() -> &'static Ledger {
    Box::leak(Box::new(Ledger::new()))
}

/// A binding across two contexts is never one row to the oracle: equal canonical strings
/// are then an UNJUDGED mismatch, counted in the running pass's context and never as an
/// identity disagreement, and the canonical decision stands.
#[test]
fn a_binding_across_two_contexts_is_counted_unjudged() {
    let (first, first_context) = Installed::for_test();
    let sealed = RowKey::of(&vc(1, 0)).expect("a key");
    drop(first);
    let (_second, second_context) = Installed::for_test();
    let current = RowKey::of(&vc(1, 0)).expect("a key");
    assert!(sealed == current, "the canonical string decides");
    assert!(sealed != RowKey::of(&vc(2, 0)).expect("a key"));
    assert_eq!(first_context.tally(), Tally::ZERO, "counted where the comparison runs");
    assert_eq!(
        second_context.tally(),
        tally(count(0, 0), count(2, 1)),
        "two contexts: unjudged, a mismatch exactly when the strings are equal"
    );
}

/// A key made where no context was installed has no identity. Compared with an identified
/// key of the same row, or partitioned beside it whichever comes first, it is unjudged, never
/// an identity mismatch: the identified key's own class is judged against the identified
/// keys alone.
#[test]
fn an_unidentified_key_is_unjudged_never_an_identity_mismatch() {
    let outside = RowKey::of(&vc(1, 0)).expect("a key");
    assert!(!outside.is_identified());
    let (_installed, context) = Installed::for_test();
    let inside = RowKey::of(&vc(1, 0)).expect("a key");
    assert!(inside.is_identified());
    assert!(outside == inside, "the canonical string decides");
    assert_eq!(context.tally(), tally(count(0, 0), count(1, 1)));
    count_partition([&outside, &inside]);
    assert_eq!(
        context.tally(),
        tally(count(1, 0), count(2, 2)),
        "the unidentified key first: it is unjudged, and the identified key agrees with itself"
    );
    // Two unidentified keys compared where an oracle is installed are unjudged too.
    let also_outside = RowKey::unidentified_for_test("not a row");
    assert!(also_outside != outside);
    assert_eq!(context.tally(), tally(count(1, 0), count(3, 2)));
}

/// A comparison is counted into the innermost installed context, whose pass writes it, even
/// when both keys are another live context's: the comparison is judged in the keys' context
/// and counted in the running pass's.
#[test]
fn a_comparison_is_counted_into_the_running_pass() {
    let (callee, callee_context) = Installed::for_test();
    let sealed = RowKey::of(&vc(1, 0)).expect("a key");
    let again = RowKey::of(&vc(1, 0)).expect("a key");
    drop(callee);
    let (_pass, pass_context) = Installed::for_test();
    assert!(sealed == again);
    assert_eq!(callee_context.tally(), Tally::ZERO, "the callee's pass has no row left to write");
    assert_eq!(pass_context.tally(), tally(count(1, 0), count(0, 0)), "judged, and agrees");
}

/// What no body's row writes reaches the crate's rows (the ledger's unwritten count): a
/// collection whose pass never resumes its context, and a count into a context after its last
/// row. What a row wrote is not written again, and a second take is empty.
#[test]
fn a_count_no_row_writes_reaches_the_crate_rows() {
    let ledger = ledger();
    // A collection whose own pass never resumes its context.
    let (collection, collection_context) = Installed::for_test_with(ledger);
    let a = RowKey::of(&vc(1, 0)).expect("a key");
    assert!(a == RowKey::of(&vc(1, 0)).expect("a key"));
    drop(collection);
    assert_eq!(collection_context.tally(), tally(count(1, 0), count(0, 0)));
    assert_eq!(ledger.take_unwritten(), tally(count(1, 0), count(0, 0)), "never resumed");
    assert_eq!(ledger.take_unwritten(), Tally::ZERO, "taken once");
    // A pass that writes its row: its counts are not the crate's.
    let (pass, _pass_context) = Installed::for_test_with(ledger);
    let b = RowKey::of(&vc(2, 0)).expect("a key");
    assert!(b != a);
    assert!(b == RowKey::of(&vc(2, 0)).expect("a key"));
    assert_eq!(
        pass.finish_for_test(),
        tally(count(1, 0), count(1, 0)),
        "the row: one judged comparison, one across two contexts with different strings"
    );
    assert_eq!(ledger.take_unwritten(), Tally::ZERO, "the row wrote them");
    // A count into that context after its last row, with nothing installed.
    assert!(b == RowKey::of(&vc(2, 0)).expect("a key"), "nothing installed: unidentified");
    let b_again = b.clone();
    assert!(b == b_again);
    assert_eq!(ledger.take_unwritten(), tally(count(1, 0), count(1, 1)), "after its last row");
}

/// A collection's context, adopted by the frozen rows, is installed again by the pass that
/// resumes it, so a key sealed in collection and one made in the pass are compared in one
/// context; and it is released with the rows.
#[test]
fn an_adopted_context_is_resumed_and_released_with_its_rows() {
    let ledger = ledger();
    let (collection, context) = Installed::for_test_with(ledger);
    let frozen = VcContext::new();
    collection.adopt(&frozen);
    let sealed = RowKey::of(&vc(1, 0)).expect("a key");
    drop(collection);
    assert!(!super::oracle_runs());
    let weak = Arc::downgrade(&context);
    drop(context);
    assert!(weak.upgrade().is_some(), "the frozen rows hold it");
    let resumed = super::stored(&frozen).expect("the rows keep the context");
    let pass = Installed::install(Some(resumed), None);
    let current = RowKey::of(&vc(1, 0)).expect("a key");
    assert!(sealed == current);
    let held = weak.upgrade().expect("installed");
    assert_eq!(held.parity(), count(1, 0), "one context: the comparison agrees");
    drop(held);
    drop(pass);
    assert_eq!(ledger.take_unwritten(), tally(count(1, 0), count(0, 0)), "no row was written");
    drop(frozen);
    assert!(weak.upgrade().is_none(), "released with the rows");
    assert!(sealed == current, "the canonical string still decides");
    assert_eq!(
        ledger.take_unwritten(),
        tally(count(0, 0), count(1, 1)),
        "a comparison whose context is gone is unjudged, counted straight into the ledger"
    );
}

/// What the census counts in `source`: each call of `canonical_exact_vc_payload` (and each
/// use of it as a value) that is not its definition, and each `.canonical()` read of a key.
/// A line is read up to its first `//`; a call through a macro that renames it is not read.
fn canonical_escapes(source: &str) -> BTreeMap<&'static str, usize> {
    let mut found = BTreeMap::new();
    for line in source.lines() {
        let code = line.split("//").next().unwrap_or_default();
        for (at, _) in code.match_indices("canonical_exact_vc_payload") {
            let before = &code[..at];
            let after = &code[at + "canonical_exact_vc_payload".len()..];
            let whole_word = !before.ends_with(|c: char| c.is_ascii_alphanumeric() || c == '_')
                && !after.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_');
            if whole_word && !before.trim_end().ends_with("fn") {
                *found.entry("canonical_exact_vc_payload").or_default() += 1;
            }
        }
        *found.entry(".canonical()").or_default() += code.matches(".canonical()").count();
    }
    found.retain(|_, count| *count > 0);
    found
}

/// T3 L4, C09 (plan C09 change 2, "a source census"): outside `row_key` and `elide_audit`,
/// this crate's sources read a canonical string out of a key, or compute one, only at the
/// elision audit's row keys, each pinned with its reason. Every other exact comparison holds
/// `RowKey`s and so goes through `RowKey::same`; the string field itself is private to
/// `row_key`, which the compiler enforces.
#[test]
fn canonical_strings_leave_a_row_key_only_at_the_pinned_audit_sites() {
    const PINNED: &[(&str, &str, usize, &str)] = &[
        (
            "trust_verify.rs",
            "canonical_exact_vc_payload",
            2,
            "the elision audit's own rows: `record_row_digests`' ROWDIGEST spelling, and the \
             KEPT row's key (`audit_kept_overflow_check`), written only with the audit on and \
             compared by no site",
        ),
        (
            "trust_verify.rs",
            ".canonical()",
            1,
            "the ELIDED row's key (`elide_kernel_certified_checks`), the audit's spelling of \
             the sealed row, compared by no site",
        ),
    ];
    // Negative control: a planted bare comparison is found.
    let planted = "let same = canonical_exact_vc_payload(a) == canonical_exact_vc_payload(b);\n\
                   let read = key.canonical() == other.canonical();\n\
                   fn canonical_exact_vc_payload(vc: &Vc) -> Option<String> {\n\
                   // canonical_exact_vc_payload(c) in a comment\n\
                   canonical_exact_vc_claim_payload(d);";
    assert_eq!(
        canonical_escapes(planted),
        BTreeMap::from([("canonical_exact_vc_payload", 2), (".canonical()", 2)]),
        "the census finds a planted bypass (negative control)"
    );
    fn walk(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(dir).expect("read a source directory") {
            let path = entry.expect("read a source directory entry").path();
            if path.is_dir() {
                walk(&path, out);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                out.push(path);
            }
        }
    }
    fn is_test_source(relative: &str) -> bool {
        relative.split('/').any(|part| part == "tests")
            || relative
                .rsplit('/')
                .next()
                .is_some_and(|name| name == "tests.rs" || name.ends_with("_tests.rs"))
    }
    let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files = Vec::new();
    walk(&src, &mut files);
    assert!(
        files.iter().any(|file| file.ends_with("trust_verify/row_key.rs")),
        "the census must read this crate's sources (positive control)",
    );
    let mut found: BTreeMap<(String, &'static str), usize> = BTreeMap::new();
    for file in &files {
        let relative = file
            .strip_prefix(&src)
            .expect("a walked file is under src")
            .to_string_lossy()
            .replace('\\', "/");
        if is_test_source(&relative)
            || relative == "trust_verify/row_key.rs"
            || relative == "trust_verify/elide_audit.rs"
        {
            continue;
        }
        let source = std::fs::read_to_string(file).expect("read a source file");
        for (needle, count) in canonical_escapes(&source) {
            found.insert((relative.clone(), needle), count);
        }
    }
    let pinned: BTreeMap<(String, &'static str), usize> = PINNED
        .iter()
        .map(|&(file, needle, count, reason)| {
            assert!(!reason.is_empty(), "{file} {needle}: a pinned site carries its reason");
            ((file.to_string(), needle), count)
        })
        .collect();
    assert_eq!(
        found, pinned,
        "an exact site compares a canonical string only inside a `RowKey` (`RowKey::same`); \
         a new reader of the string must hold the key instead, or be an audit row pinned here \
         with its reason",
    );
}
