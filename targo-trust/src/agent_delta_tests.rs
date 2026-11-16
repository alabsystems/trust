// Unit tests for the changed-only view: the row words and labels, the rows that
// print on every run (with a base and without one, and once with `--all-rows`),
// what `N` and `M` count, grade and basis changes, the per-caller pointers and
// when they move, `--since` for one package, an unusable `--since` or pointer,
// the snapshot's hash check, the 7-day pruning, the pointer that outlives it and
// the one that expires, a view with nowhere to store, and the records delta
// refuses.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;

fn obligation(key: &str, status: &str, stop: &str) -> ObligationRecord {
    ObligationRecord {
        key: key.to_string(),
        kind: "postcondition".to_string(),
        status: status.to_string(),
        stop: stop.to_string(),
        file: Some("src/lib.rs".to_string()),
        line: Some(1),
        col: Some(1),
        encoding: crate::obligations::UNGRADED.to_string(),
        discharge: crate::obligations::UNGRADED.to_string(),
        premises: Vec::new(),
        basis: (status == "failed").then(|| "refuted".to_string()),
    }
}

fn package(rows: &[(&str, &str, &str)], coverage_complete: bool) -> PackageObligations {
    let obligations: Vec<ObligationRecord> =
        rows.iter().map(|(key, status, stop)| obligation(key, status, stop)).collect();
    PackageObligations {
        package: "demo".to_string(),
        lane: "strict".to_string(),
        policy: "strict".to_string(),
        selection: "default".to_string(),
        targo_trust_commit: "c".to_string(),
        profile: "p".to_string(),
        outcome: "measured".to_string(),
        vector: "v".to_string(),
        coverage_complete,
        concluded: true,
        functions: obligations
            .iter()
            .map(|row| (split_obligation_key(&row.key).unwrap().0.to_string(), None))
            .collect(),
        obligations,
        compile_errors: Vec::new(),
        tests: None,
        test_harnesses: Vec::new(),
        test_cases: Vec::new(),
        clean_islands: Default::default(),
    }
}

const A: &str = "demo::a#0000000000000001";
const B: &str = "demo::b#0000000000000002";
const C: &str = "demo::c#0000000000000003";
const D: &str = "demo::d#0000000000000004";
const E: &str = "demo::e#0000000000000005";

/// The first word of each line (`STILL`, `NEW FAILED`, …).
fn words(changes: &Changes) -> Vec<&str> {
    changes.lines.iter().map(|line| line.split("  ").next().unwrap().trim()).collect()
}

/// [`publish`] for a view that was printed: its caller's pointers move.
fn shown(
    target_dir: &Path,
    records: &[(String, String)],
    request: &DeltaRequest,
    caller: Option<&str>,
    list_rows: bool,
) -> DeltaView {
    publish_shown(target_dir, records, request, caller, list_rows)
}

/// [`publish_run`] for a view that was printed: its caller's pointers move.
fn shown_run(
    target_dir: &Path,
    records: &crate::obligations::ObligationRecords,
    request: &DeltaRequest,
    caller: Option<&str>,
) -> DeltaView {
    let view = publish_run(target_dir, records, request, caller);
    assert_eq!(view.commit_pointers(), Vec::<String>::new(), "{view:?}");
    view
}

#[test]
fn each_transition_has_its_word_and_an_unchanged_record_has_none() {
    let base = package(&[(A, "proved", "solved"), (C, "proved", "solved")], true);
    assert_eq!(changed_rows(&base, &base, true), Changes::default());
    let base = package(
        &[(A, "proved", "solved"), (B, "unknown", "solver-incomplete"), (C, "proved", "solved")],
        true,
    );
    let now = package(
        &[
            (A, "failed", "solved"),
            (B, "proved", "solved"),
            (C, "unknown", "wall-backstop"),
            (D, "failed", "solved"),
        ],
        true,
    );
    let changes = changed_rows(&base, &now, true);
    assert_eq!(words(&changes), ["LOST", "NEW FAILED", "NOT MEASURED", "GAINED"], "{changes:?}");
    assert_eq!(changes.rows, 4);
    // Each row carries the listing's label for it now.
    assert!(changes.lines[0].starts_with("LOST        [FAILED]  demo::a#"), "{changes:?}");
    assert!(changes.lines[1].contains("[FAILED]  demo::d#") && changes.lines[1].contains("(new)"));
    assert!(changes.lines[2].contains("[UNKNOWN]  demo::c#"), "{changes:?}");
    assert!(changes.lines[3].contains("[PROVED]  demo::b#"), "{changes:?}");
}

/// With no listing of the command's own, a row that is not plainly proved
/// prints on every run, as its change or as `STILL`, one line per row, and `N`
/// counts only the rows that changed.
#[test]
fn a_row_that_is_not_proved_prints_on_every_run_and_nothing_is_collapsed() {
    let proved =
        package(&[(A, "proved", "solved"), (B, "proved", "solved"), (C, "proved", "solved")], true);
    let refused = package(
        &[
            (A, "failed", "solved"),
            (B, "unknown", "not-dispatched"),
            (C, "unknown", "not-dispatched"),
        ],
        false,
    );
    let broken = changed_rows(&proved, &refused, true);
    assert_eq!(broken.rows, 3, "{broken:?}");
    assert_eq!(words(&broken), ["RUN", "LOST", "LOST", "LOST"], "{broken:?}");
    assert!(broken.lines[0].starts_with("RUN         coverage_complete true -> false"));
    for (line, key) in broken.lines[1..].iter().zip([A, B, C]) {
        assert!(line.contains(key), "one line per row: {broken:?}");
    }

    // The same refused run again: nothing changed, every row still prints.
    let again = changed_rows(&refused, &refused, true);
    assert_eq!(again.rows, 0);
    assert_eq!(words(&again), ["STILL", "STILL", "STILL"], "{again:?}");
    assert!(again.lines[0].starts_with("STILL       [FAILED]  demo::a#"), "{again:?}");
    assert!(again.lines[1].starts_with("STILL       [UNKNOWN]  demo::b#"), "{again:?}");

    let fixed = changed_rows(&refused, &proved, true);
    assert_eq!(fixed.rows, 3);
    assert_eq!(words(&fixed), ["RUN", "GAINED", "GAINED", "GAINED"], "{fixed:?}");

    // Runtime-checked and assumed rows are not plainly proved either, nor is
    // a proved row the listing labels ASSUMED.
    let mut assumed = obligation(D, "unknown", "not-dispatched");
    assumed.kind = "assumption:extern".to_string();
    let mut proved_assumption = obligation(E, "proved", "solved");
    proved_assumption.kind = "assumption:extern".to_string();
    let mut open = package(&[(A, "runtime_checked", "not-dispatched")], true);
    open.functions.insert("demo::d".to_string(), None);
    open.functions.insert("demo::e".to_string(), None);
    open.obligations.push(assumed);
    open.obligations.push(proved_assumption);
    let still = changed_rows(&open, &open, true);
    assert_eq!(still.lines.len(), 3, "{still:?}");
    // Within a word, rows are in line order.
    assert!(still.lines[0].starts_with("STILL       [ASSUMED]  demo::d#"), "{still:?}");
    assert!(still.lines[1].starts_with("STILL       [ASSUMED]  demo::e#"), "{still:?}");
    assert!(still.lines[2].starts_with("STILL       [RUNTIME-CHECKED]  demo::a#"), "{still:?}");

    // Beside a listing of the command's own, which keeps those rows, the view
    // prints no `STILL` rows (`crate::report`, `terminal_lines_with`).
    assert_eq!(changed_rows(&refused, &refused, false), Changes::default());
    assert_eq!(changed_rows(&open, &open, false), Changes::default());
}

/// `N` counts obligation rows, not lines: a `REMOVED` function counts its
/// obligations, and a `MOVED` line counts none (its rows are compared, and
/// counted, on their own lines). `M` counts the base's rows that are gone as
/// well as this run's, so `N` never exceeds it.
#[test]
fn n_counts_obligation_rows_not_lines() {
    const B2: &str = "demo::b#0000000000000006";
    const B3: &str = "demo::b#0000000000000007";
    // `demo::a` renamed `demo::z`, paired by its proved id; `demo::b` removed.
    const Z: &str = "demo::z#0000000000000001";
    let base = package(
        &[
            (A, "proved", "solved"),
            (B, "unknown", "not-dispatched"),
            (B2, "unknown", "not-dispatched"),
            (B3, "unknown", "not-dispatched"),
        ],
        true,
    );
    let now = package(&[(Z, "proved", "solved")], true);
    let changes = changed_rows(&base, &now, true);
    assert_eq!(words(&changes), ["MOVED", "REMOVED"], "{changes:?}");
    assert!(changes.lines[0].contains("demo::a -> demo::z  (paired by ids)"), "{changes:?}");
    assert!(changes.lines[1].contains("demo::b  (3 obligation(s))"), "{changes:?}");
    assert_eq!(changes.rows, 3, "{changes:?}");
    assert_eq!(changes.gone, 3, "{changes:?}");
    let delta = PackageDelta {
        package: "demo".to_string(),
        total: now.obligations.len(),
        compile_errors: 0,
        concluded: true,
        now: Some("t".to_string()),
        since: Some(("b".to_string(), changes)),
        errors: Vec::new(),
        all: Vec::new(),
        tests: Vec::new(),
        test_summary: None,
        islands: Vec::new(),
        island_summary: None,
    };
    assert_eq!(delta.summary_line(), "demo  3 of 4 changed since b  (now t)");
}

/// The proved-id rule pairs a base function only with a function that holds
/// no other unpaired base function's majority: two renamed functions whose
/// proved ids both landed in one function now are both `REMOVED`, and its rows
/// print as new.
#[test]
fn a_function_two_base_functions_claim_by_ids_pairs_with_neither() {
    const C1: &str = "demo::c#0000000000000001";
    const C2: &str = "demo::c#0000000000000002";
    let base = package(&[(A, "proved", "solved"), (B, "proved", "solved")], true);
    let now = package(&[(C1, "proved", "solved"), (C2, "proved", "solved")], true);
    let changes = changed_rows(&base, &now, true);
    assert_eq!(words(&changes), ["GAINED", "GAINED", "REMOVED", "REMOVED"], "{changes:?}");
    assert_eq!((changes.rows, changes.gone), (4, 2), "{changes:?}");
}

/// A grade or failure-basis change with the same status and stop is a
/// `CHANGED` row: a proof that now rests on a new premise, or a failure that
/// is no longer a refutation, is not what the base recorded.
#[test]
fn a_grade_or_basis_change_is_a_changed_row() {
    let graded = |premises: &[&str]| {
        let mut record = package(&[(A, "proved", "solved")], true);
        record.obligations[0].encoding = "unvalidated-encoder".to_string();
        record.obligations[0].discharge = "solver-asserted".to_string();
        record.obligations[0].premises = premises.iter().map(|p| p.to_string()).collect();
        record
    };
    let premise = changed_rows(&graded(&[]), &graded(&["requires-link"]), true);
    assert_eq!(premise.rows, 1, "{premise:?}");
    assert_eq!(words(&premise), ["CHANGED"]);
    assert!(
        premise.lines[0].contains(
            "proved (graded unvalidated-encoder/solver-asserted+requires-link, was \
             unvalidated-encoder/solver-asserted)"
        ),
        "{premise:?}"
    );
    assert_eq!(
        changed_rows(&graded(&["requires-link"]), &graded(&["requires-link"]), true).rows,
        0
    );

    let refuted = package(&[(A, "failed", "solved")], true);
    let mut closed = refuted.clone();
    closed.obligations[0].basis = Some("unproved_fail_closed".to_string());
    let basis = changed_rows(&refuted, &closed, true);
    assert_eq!(basis.rows, 1, "{basis:?}");
    assert!(
        basis.lines[0].starts_with(
            "CHANGED     [FAILED: unproved, no counterexample; failed closed]  demo::a#"
        ) && basis.lines[0].contains("failed (was [FAILED])"),
        "{basis:?}"
    );
}

/// A failed row whose label does not show its basis (`ASSUMED`, `CONTRACT`,
/// `CONDITIONAL`) and whose basis alone changed says what it was.
#[test]
fn a_basis_change_the_label_does_not_show_is_named() {
    let mut refuted = package(&[(A, "failed", "solved")], true);
    refuted.obligations[0].kind = "assumption:extern-call".to_string();
    let mut closed = refuted.clone();
    closed.obligations[0].basis = Some("unproved_fail_closed".to_string());
    assert_eq!(refuted.obligations[0].listing_label(), closed.obligations[0].listing_label());
    let changes = changed_rows(&refuted, &closed, true);
    assert_eq!(words(&changes), ["CHANGED"], "{changes:?}");
    assert_eq!(changes.rows, 1);
    assert!(
        changes.lines[0].starts_with("CHANGED     [ASSUMED]  demo::a#")
            && changes.lines[0].contains("failed (was basis refuted)  solved"),
        "{changes:?}"
    );
}

/// `GAINED` is a proof the base did not have: a row proved on both sides
/// whose stop changed (a record handed to `targo trust delta` can say so) is
/// `CHANGED`.
#[test]
fn a_stop_change_of_a_row_proved_on_both_sides_is_changed_not_gained() {
    let base = package(&[(A, "proved", "solved")], true);
    let now = package(&[(A, "proved", "wall-backstop")], true);
    let changes = changed_rows(&base, &now, true);
    assert_eq!(words(&changes), ["CHANGED"], "{changes:?}");
    assert!(changes.lines[0].contains("proved (was stopped by solved)"), "{changes:?}");
    assert_eq!(changes.rows, 1);
    let unproved = package(&[(A, "unknown", "wall-backstop")], true);
    assert_eq!(words(&changed_rows(&unproved, &now, true)), ["GAINED"]);
}

/// A proved key that vanished is `LOST` when its function's source digest is
/// the same on both sides or is not stated on one of them (a def path several
/// Lean `example`s share states none), and the line says which: a digest not
/// stated shows no edit, but does not show the source unchanged.
#[test]
fn a_lost_row_says_whether_its_functions_source_digest_was_stated() {
    let mut base = package(&[(A, "proved", "solved"), (B, "proved", "solved")], true);
    let mut now = package(&[(B, "proved", "solved")], true);
    now.functions.insert("demo::a".to_string(), None);
    let unstated = changed_rows(&base, &now, true);
    assert_eq!(words(&unstated), ["LOST"], "{unstated:?}");
    assert!(
        unstated.lines[0].contains(
            "vanished (was proved; its function's source digest is not stated on both sides)"
        ),
        "{unstated:?}"
    );
    let digest = Some("0123456789abcdef".repeat(4));
    base.functions.insert("demo::a".to_string(), digest.clone());
    now.functions.insert("demo::a".to_string(), digest);
    let same = changed_rows(&base, &now, true);
    assert_eq!(words(&same), ["LOST"], "{same:?}");
    assert!(
        same.lines[0].contains("vanished (was proved; its function's source did not change)"),
        "{same:?}"
    );
}

fn ndjson(rows: &[(&str, &str, &str)]) -> String {
    ndjson_named("demo", rows)
}

/// The record of package `name`.
fn ndjson_named(name: &str, rows: &[(&str, &str, &str)]) -> String {
    let mut record = package(rows, true);
    record.package = name.to_string();
    let functions = functions_of(&record);
    crate::obligations::render_package_ndjson(
        &crate::obligations::RecordHeader {
            package: &record.package,
            lane: &record.lane,
            policy: &record.policy,
            selection: &record.selection,
            targo_trust_commit: &record.targo_trust_commit,
            profile: &record.profile,
            outcome: &record.outcome,
            vector: &record.vector,
            coverage_complete: true,
            concluded: true,
            degraded_anchors: 0,
        },
        &functions,
    )
}

#[test]
fn each_caller_diffs_against_its_own_last_run_only() {
    let target = tempfile::tempdir().unwrap();
    let request = DeltaRequest::default();
    let first = vec![("demo".to_string(), ndjson(&[(A, "proved", "solved")]))];
    let second = vec![("demo".to_string(), ndjson(&[(A, "failed", "solved")]))];

    let alpha = shown(target.path(), &first, &request, Some("alpha"), false);
    assert!(alpha.packages[0].since.is_none(), "no base on a first run");
    let beta = shown(target.path(), &second, &request, Some("beta"), false);
    assert!(beta.packages[0].since.is_none(), "beta never reads alpha's pointer");
    let alpha_again = shown(target.path(), &second, &request, Some("alpha"), false);
    let (base, changes) = alpha_again.packages[0].since.clone().expect("alpha's base");
    assert_eq!(Some(base), alpha.packages[0].now);
    assert_eq!(changes.rows, 1);
    let beta_again = shown(target.path(), &second, &request, Some("beta"), false);
    assert_eq!(beta_again.packages[0].since.as_ref().unwrap().1.rows, 0);
    assert!(beta_again.replaces_listing());
    // Nothing changed. A check's own listing keeps the failed row
    // (`crate::report`), so its view is the summary line alone; with no
    // listing of the command's own the failed row prints again before it.
    assert_eq!(beta_again.lines().len(), 1, "{beta_again:?}");
    let standalone = shown(target.path(), &second, &request, Some("beta"), true);
    let lines = standalone.lines();
    assert_eq!(lines.len(), 2, "{lines:?}");
    assert!(lines[0].starts_with("STILL       [FAILED]  demo::a#"), "{lines:?}");
    shown(target.path(), &first, &request, Some("gamma"), false);
    let unchanged = shown(target.path(), &first, &request, Some("gamma"), false);
    assert_eq!(unchanged.lines().len(), 1, "an all-proved rerun is one line");

    // No caller: no base, and nothing to point at.
    let anonymous = shown(target.path(), &second, &request, None, false);
    assert!(anonymous.packages[0].since.is_none() && !anonymous.replaces_listing());

    // A pointer is per caller and per measurement.
    let record = parse_package_ndjson(&first[0].1).unwrap();
    let dir = snapshots_dir(target.path());
    assert_ne!(pointer_path(&dir, "alpha", &record), pointer_path(&dir, "beta", &record));
    let mut other_lane = record.clone();
    other_lane.lane = "certify".to_string();
    assert_ne!(pointer_path(&dir, "alpha", &record), pointer_path(&dir, "alpha", &other_lane));
}

/// `publish` stores the snapshot but moves no pointer: the view holds the move
/// until it was printed, so a run whose view is never printed leaves the
/// caller's base at the last token it was shown.
#[test]
fn a_pointer_moves_only_once_its_view_was_printed() {
    let target = tempfile::tempdir().unwrap();
    let request = DeltaRequest::default();
    let proved = vec![("demo".to_string(), ndjson(&[(A, "proved", "solved")]))];
    let failed = vec![("demo".to_string(), ndjson(&[(A, "failed", "solved")]))];

    let unprinted = publish(target.path(), &proved, &request, Some("me"), false);
    let token = unprinted.packages[0].now.clone().unwrap();
    assert!(snapshots_dir(target.path()).join(&token).is_file(), "the snapshot is stored");
    let first = publish(target.path(), &proved, &request, Some("me"), false);
    assert!(first.packages[0].since.is_none(), "still a first run: {first:?}");
    assert!(first.notes.is_empty(), "{first:?}");
    assert_eq!(first.commit_pointers(), Vec::<String>::new());

    // A changed run whose view is not printed moves nothing.
    let lost = publish(target.path(), &failed, &request, Some("me"), false);
    assert_eq!(lost.packages[0].since.as_ref().map(|(base, _)| base), Some(&token));
    let again = publish(target.path(), &failed, &request, Some("me"), false);
    assert_eq!(again.packages[0].since.as_ref().map(|(base, _)| base), Some(&token));
    assert_eq!(again.packages[0].since.as_ref().unwrap().1.rows, 1, "the change still shows");
}

#[test]
fn a_snapshot_unused_for_seven_days_is_pruned_when_a_new_one_is_written() {
    let target = tempfile::tempdir().unwrap();
    let dir = snapshots_dir(target.path());
    let old = store(&dir, b"old record").unwrap();
    let kept = store(&dir, b"recent record").unwrap();
    let week_ago = SystemTime::now() - SNAPSHOT_RETENTION - Duration::from_secs(60);
    std::fs::File::options()
        .write(true)
        .open(dir.join(&old))
        .unwrap()
        .set_modified(week_ago)
        .unwrap();
    // Re-storing an existing record writes nothing new and prunes nothing.
    store(&dir, b"recent record").unwrap();
    assert!(dir.join(&old).is_file());
    store(&dir, b"newer record").unwrap();
    assert!(!dir.join(&old).exists(), "the stale snapshot was kept");
    assert!(dir.join(&kept).is_file());
}

#[test]
fn since_and_all_rows_are_taken_out_and_a_bad_token_is_refused() {
    let mut args: Vec<String> =
        ["-p", "x", "--since", "0123456789abcdef", "--all-rows", "--", "--since"]
            .map(str::to_string)
            .to_vec();
    let request = DeltaRequest::take_from(&mut args).unwrap();
    assert_eq!(request.since.as_deref(), Some("0123456789abcdef"));
    assert!(request.all_rows);
    assert_eq!(args, ["-p", "x", "--", "--since"]);
    let mut bad = vec!["--since=XYZ".to_string()];
    assert!(DeltaRequest::take_from(&mut bad).is_err());
}

/// A snapshot is content-addressed: one whose bytes do not hash to its name is
/// refused, never compared with, and a caller pointer that does not hold a
/// token names no file.
#[test]
fn a_snapshot_whose_bytes_do_not_hash_to_its_token_is_refused() {
    let target = tempfile::tempdir().unwrap();
    let dir = snapshots_dir(target.path());
    let record = vec![("demo".to_string(), ndjson(&[(A, "proved", "solved")]))];
    let request = DeltaRequest::default();
    let first = shown(target.path(), &record, &request, Some("me"), false);
    let token = first.packages[0].now.clone().unwrap();
    // Replace the snapshot's bytes with another valid record.
    std::fs::write(dir.join(&token), ndjson(&[(A, "failed", "solved")])).unwrap();
    let since = DeltaRequest { since: Some(token.clone()), all_rows: false };
    let view = shown(target.path(), &record, &since, None, false);
    assert!(view.packages[0].since.is_none(), "{view:?}");
    assert!(view.notes[0].contains("refused"), "{view:?}");
    // That run stored the record again, over the bytes that did not match.
    let view = shown(target.path(), &record, &request, Some("me"), false);
    assert!(view.packages[0].since.is_some(), "re-storing the record repaired it: {view:?}");

    // A pointer holding a path, not a token.
    let parsed = parse_package_ndjson(&record[0].1).unwrap();
    std::fs::write(pointer_path(&dir, "me", &parsed), "../../escape\n").unwrap();
    let view = shown(target.path(), &record, &request, Some("me"), false);
    assert!(view.packages[0].since.is_none(), "{view:?}");
    assert!(view.notes[0].contains("is not a snapshot token"), "{view:?}");
}

// --- Compile errors ---------------------------------------------------------------

const ERROR_PACKAGE_ID: &str = "path+file:///work/delta-errors#delta-errors@0.1.0";

/// One Cargo `compiler-message` envelope as native Targo emits it for the lib
/// unit of package `delta-errors` (the shape captured from `targo --unverified
/// check --message-format=json` on a crate with these errors, with the
/// explanation text and absolute paths trimmed), carrying an error.
fn cargo_error(code: Option<&str>, message: &str, line: u64, col: u64) -> String {
    let diagnostic = serde_json::json!({
        "$message_type": "diagnostic",
        "level": "error",
        "message": message,
        "code": code.map(|code| serde_json::json!({ "code": code, "explanation": "-" })),
        "spans": [
            { "file_name": "src/lib.rs", "line_start": line, "line_end": line,
              "column_start": col, "column_end": col + 4, "is_primary": true },
            { "file_name": "src/lib.rs", "line_start": line, "line_end": line,
              "column_start": 1, "column_end": 2, "is_primary": false },
        ],
        "children": [],
        "rendered": format!("error: {message}\n"),
    });
    serde_json::json!({
        "reason": "compiler-message",
        "package_id": ERROR_PACKAGE_ID,
        "manifest_path": "/work/delta-errors/Cargo.toml",
        "target": { "kind": ["lib"], "crate_types": ["lib"], "name": "delta_errors",
                    "src_path": "/work/delta-errors/src/lib.rs", "edition": "2021",
                    "doc": true, "doctest": true, "test": true },
        "trust_compile_target": "aarch64-apple-darwin",
        "trust_compile_mode": "check",
        "trust_compile_kind": "target",
        "trust_unit_identity_sha256": "0".repeat(64),
        "message": diagnostic,
    })
    .to_string()
}

/// The rest of such a run's stream: a rustc note (level `failure-note`, not
/// an error), rustc's closing error count, and Cargo's failed
/// `build-finished`.
fn cargo_failure_tail() -> String {
    let message = |level: &str, text: &str| {
        serde_json::json!({
            "reason": "compiler-message",
            "package_id": ERROR_PACKAGE_ID,
            "target": { "kind": ["lib"], "name": "delta_errors" },
            "message": { "level": level, "message": text, "code": null,
                         "spans": [], "children": [], "rendered": format!("{text}\n") },
        })
        .to_string()
    };
    [
        message("failure-note", "Some errors have detailed explanations: E0308, E0425."),
        message("error", "aborting due to 2 previous errors"),
        r#"{"reason":"build-finished","success":false}"#.to_string(),
    ]
    .join("\n")
}

/// The production path of a crate-mode check that did not compile: Cargo's
/// JSON stream through `parse_cargo_json_stdout`, its compile errors through
/// `ObligationRecords::of_rows` (no row, no coverage), giving the record a
/// check writes and snapshots.
fn record_of_cargo_stream(stream: &str) -> crate::obligations::ObligationRecords {
    record_of_run(&compile_errors_of_failed_build(stream), &[], &[])
}

/// The compile errors of a failed build's Cargo stream, read by
/// `parse_cargo_json_stdout`.
fn compile_errors_of_failed_build(stream: &str) -> Vec<crate::obligations::CompileError> {
    let selected: BTreeMap<String, String> =
        [(ERROR_PACKAGE_ID.to_string(), "delta-errors".to_string())].into_iter().collect();
    let evidence = crate::pipeline::transport::parse_cargo_json_stdout(
        std::io::Cursor::new(stream.as_bytes()),
        &selected,
        "session",
        true,
    )
    .expect("a failed build's stream is accepted");
    assert_eq!(evidence.build_succeeded, Some(false));
    evidence.compile_errors
}

/// The records of a crate-mode run of `delta-errors` whose units published
/// `rows` and `coverage` and whose build reported `compile_errors`.
fn record_of_run(
    compile_errors: &[crate::obligations::CompileError],
    rows: &[crate::types::VerificationResult],
    coverage: &[trust_types::CoverageTransportSummary],
) -> crate::obligations::ObligationRecords {
    crate::obligations::ObligationRecords::of_rows(
        rows,
        &crate::obligations::FunctionInventory::of_rows(rows),
        crate::obligations::RunFacts {
            lane: "strict".to_string(),
            policy: "strict".to_string(),
            selection: "default".to_string(),
            targo_trust_commit: "0123456789abcdef0123456789abcdef01234567".to_string(),
            profile: "a".repeat(64),
            worker_threads: 0,
            outcome: trust_types::determinism::UnitOutcome::CouldNotRun,
            vector: "b".repeat(64),
            coverage_complete: false,
            degraded_anchors: 0,
        },
        crate::obligations::RunScope {
            selected: ["delta-errors".to_string()].into_iter().collect(),
            resolved: BTreeSet::new(),
        },
        &crate::package_record::RunCoverage {
            rows: coverage,
            missing: BTreeSet::new(),
            publication_stops: &[],
            compile_errors,
        },
    )
}

const MISMATCH: &str = "mismatched types";
const UNRESOLVED: &str = "cannot find value `not_here` in this scope";

#[test]
fn a_compile_error_is_a_row_keyed_by_file_code_and_message_and_prints_on_every_run() {
    let broken = |mismatch_line: u64| {
        record_of_cargo_stream(
            &[
                cargo_error(Some("E0425"), UNRESOLVED, 11, 5),
                cargo_error(Some("E0308"), MISMATCH, mismatch_line, 18),
                // A second unit of the same file: the same error again.
                cargo_error(Some("E0308"), MISMATCH, mismatch_line, 18),
                cargo_failure_tail(),
            ]
            .join("\n"),
        )
    };
    let records = broken(6);
    let ndjson = records.package_ndjson("delta-errors").expect("the package's record");
    let parsed = parse_package_ndjson(&ndjson).expect("the record reads back");
    // Two errors: the repeated one is one row, and neither the note nor the
    // closing count is one. The package is could-not-run, as before.
    assert_eq!(parsed.compile_errors.len(), 2, "{ndjson}");
    assert_eq!(parsed.outcome, "could-not-run", "{ndjson}");
    assert!(parsed.obligations.is_empty());
    let mismatch =
        crate::obligations::compile_error_key(Some("src/lib.rs"), Some("E0308"), MISMATCH);
    assert!(mismatch.starts_with("src/lib.rs#E0308-"), "{mismatch}");
    assert!(
        parsed.compile_errors.iter().any(|error| {
            error.key == mismatch && error.line == Some(6) && error.col == Some(18)
        })
    );

    let target = tempfile::tempdir().unwrap();
    let request = DeltaRequest::default();
    // No base: every error row prints, then the summary line, which counts them.
    let first = shown_run(target.path(), &records, &request, Some("me"));
    let lines = first.lines();
    let token = first.packages[0].now.clone().unwrap();
    assert_eq!(lines.len(), 3, "{lines:#?}");
    assert_eq!(lines[0], format!("[ERROR E0308]  {mismatch}  {MISMATCH}  src/lib.rs:6:18"));
    assert!(lines[1].starts_with("[ERROR E0425]  src/lib.rs#E0425-"), "{lines:#?}");
    assert_eq!(
        lines[2],
        format!("delta-errors  2 compiler error(s); 0 obligation(s)  (now {token})")
    );

    // A rerun with no edit: nothing changed, and both errors print again.
    // No run of this caller compiled, so the obligations have no base and
    // the check's own listing stays.
    let again = shown_run(target.path(), &records, &request, Some("me"));
    let lines = again.lines();
    assert!(!again.replaces_listing());
    assert_eq!(lines.len(), 3, "{lines:#?}");
    assert!(lines[0].starts_with(&format!("STILL       [ERROR E0308]  {mismatch}  ")));
    assert!(lines[1].starts_with("STILL       [ERROR E0425]  "), "{lines:#?}");
    assert_eq!(
        lines[2],
        format!("delta-errors  2 compiler error(s); 0 obligation(s)  (now {token})")
    );

    // Lines inserted above the error: its key is the same and its line moved,
    // and so did the record's token.
    let moved = shown_run(target.path(), &broken(9), &request, Some("me"));
    let lines = moved.lines();
    assert_eq!(lines.len(), 3, "{lines:#?}");
    assert_eq!(
        lines[0],
        format!("STILL       [ERROR E0308]  {mismatch}  {MISMATCH}  src/lib.rs:9:18")
    );
    let moved_token = moved.packages[0].now.clone().unwrap();
    assert_ne!(moved_token, token, "the record carries each error's location");

    // One error fixed: it is CLEARED, one line, and the other still prints.
    let one = record_of_cargo_stream(
        &[cargo_error(Some("E0425"), UNRESOLVED, 11, 5), cargo_failure_tail()].join("\n"),
    );
    let fixed = shown_run(target.path(), &one, &request, Some("me"));
    let lines = fixed.lines();
    assert_eq!(lines.len(), 3, "{lines:#?}");
    assert!(lines[0].starts_with("STILL       [ERROR E0425]  "), "{lines:#?}");
    assert!(lines[1].starts_with(&format!("CLEARED     [ERROR E0308]  {mismatch}  ")));
    assert!(lines[2].starts_with("delta-errors  1 compiler error(s); 0 obligation(s)  (now "));
}

/// A package outside the run's selection that did not compile (a path
/// dependency) is in the view under its own name, read from its package ID.
#[test]
fn a_dependency_that_did_not_compile_is_in_the_view_under_its_own_name() {
    let dependency = cargo_error(Some("E0308"), MISMATCH, 2, 1)
        .replace(ERROR_PACKAGE_ID, "path+file:///work/dep#helper@0.2.0");
    let records = record_of_cargo_stream(&[dependency, cargo_failure_tail()].join("\n"));
    let target = tempfile::tempdir().unwrap();
    let view = shown_run(target.path(), &records, &DeltaRequest::default(), Some("me"));
    let packages: Vec<&str> = view.packages.iter().map(|p| p.package.as_str()).collect();
    assert_eq!(packages, ["delta-errors", "helper"], "{view:?}");
    assert_eq!(view.packages[1].compile_errors, 1);
    // The selected package reported no error, but it was never built: its
    // record did not conclude, so its obligations are compared with nothing.
    assert_eq!(view.packages[0].compile_errors, 0);
    assert!(!view.packages[0].concluded && !view.packages[1].concluded, "{view:?}");
    let selected = parse_package_ndjson(&records.package_ndjson("delta-errors").unwrap()).unwrap();
    assert!(!selected.concluded);
}

/// An internal compiler error is an error row. rustc spells its level
/// `error: internal compiler error` (`rustc_errors::Level::to_str`), not
/// `error`; read through `parse_cargo_json_stdout`, it is recorded under the
/// key of its file, code and message, led by `internal compiler error: ` as
/// rustc renders it, and prints on every run while it is reported.
#[test]
fn an_internal_compiler_error_is_an_error_row_on_every_run() {
    let ice = cargo_error(None, "unexpected region in trust-ir lowering", 7, 3);
    assert!(ice.contains(r#""level":"error""#), "{ice}");
    let ice = ice.replace(r#""level":"error""#, r#""level":"error: internal compiler error""#);
    let stream = [ice, cargo_failure_tail()].join("\n");
    let errors = compile_errors_of_failed_build(&stream);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert_eq!(
        errors[0].message,
        "internal compiler error: unexpected region in trust-ir lowering"
    );
    let records = record_of_cargo_stream(&stream);
    let read = parse_package_ndjson(&records.package_ndjson("delta-errors").unwrap()).unwrap();
    assert_eq!(read.compile_errors.len(), 1);
    assert_eq!(
        read.compile_errors[0].key,
        crate::obligations::compile_error_key(Some("src/lib.rs"), None, &errors[0].message)
    );
    assert!(!read.concluded, "a crashed compiler published no coverage");

    let target = tempfile::tempdir().unwrap();
    let request = DeltaRequest::default();
    for (run, label) in [(0, "[ERROR]  src/lib.rs#error-"), (1, "STILL       [ERROR]  ")] {
        let lines = shown_run(target.path(), &records, &request, Some("me")).lines();
        assert_eq!(lines.len(), 2, "run {run}: {lines:#?}");
        let row = if run == 0 { lines[0].trim_start() } else { lines[0].as_str() };
        assert!(row.starts_with(label), "run {run}: {lines:#?}");
        assert!(lines[0].contains("internal compiler error: unexpected region"), "{lines:#?}");
        assert!(lines[1].starts_with("delta-errors  1 compiler error(s); "), "{lines:#?}");
    }
}

/// A unit of `delta-errors` that published `function`'s obligation `n`
/// (every function's source is its name, so it does not change).
fn verified_row(
    function: &str,
    n: u32,
    outcome: crate::types::VerificationOutcome,
) -> crate::types::VerificationResult {
    use trust_types::obligation_identity::{ObligationIdentity, function_source_digest, local_id};
    let mut row = crate::types::VerificationResult {
        function: format!("cargo-target(package=\"delta-errors\")::{function}"),
        kind: "overflow:add".to_string(),
        message: "arithmetic overflow (Add)".to_string(),
        outcome,
        backend: "ay".to_string(),
        time_ms: Some(1),
        location: Some(trust_types::SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: 10 + n,
            col_start: 8,
            line_end: 10 + n,
            col_end: 13,
        }),
        counterexample: None,
        reason: None,
        raw_line: String::new(),
    };
    let evidence = crate::types::StructuredTransportEvidence {
        assumes: Vec::new(),
        obligation_id: Some(format!("vc:{function}:arithmetic_safety:{n}")),
        claim_digest_sha256: None,
        original_vc_snapshot: None,
        typed_kind: None,
        design_mandate: false,
        runtime_checks: None,
        native_trust_ir: None,
        proof_evidence: None,
        monitor: None,
        identity: Some(ObligationIdentity {
            key: trust_types::obligation_identity::obligation_key(
                function,
                &local_id("overflow:add", "stmt:0123456789abcdef", n),
            ),
            package: "delta-errors".to_string(),
            function_source_sha256: Some(function_source_digest(function)),
            expanded_function_identity: None,
        }),
        grade: None,
    };
    crate::types::replace_structured_transport_evidence(&mut row, &evidence).expect("serializes");
    row
}

/// The coverage row a unit of `delta-errors` publishes at the end of its
/// verification walk.
fn delta_errors_coverage() -> trust_types::CoverageTransportSummary {
    trust_types::CoverageTransportSummary {
        crate_name: "delta_errors".to_string(),
        package_name: "delta-errors".to_string(),
        primary_package: true,
        verification_session: "session".to_string(),
        eligible: 2,
        processed: 2,
        function_identities: None,
        noted_stops: Vec::new(),
        degraded_anchors: 0,
        memory: trust_types::MemorySummary::default(),
    }
}

/// The verifier reports a refusal as an ordinary compiler error (rustc's
/// `dcx`, level `error`, no code). A package with one still concluded (its
/// unit published its coverage row), so its obligations are compared: a
/// proof that vanished while its function's source did not change prints as
/// `LOST`, a new refutation is not `STILL`, and the verifier's error prints
/// as a row of its own.
#[test]
fn a_verifier_refusal_does_not_stop_the_obligations_being_compared() {
    use crate::types::VerificationOutcome::{Failed, Proved};
    let coverage = [delta_errors_coverage()];
    let base = record_of_run(
        &[],
        &[
            verified_row("delta_errors::f00", 0, Proved),
            verified_row("delta_errors::f01", 0, Proved),
            verified_row("delta_errors::f01", 1, Proved),
        ],
        &coverage,
    );
    let refusal = "Trust strict verification failed for `delta_errors::f00`: 1 obligation(s) \
                   were not fully verified";
    let stream = [
        cargo_error(None, refusal, 10, 1),
        r#"{"reason":"build-finished","success":false}"#.to_string(),
    ]
    .join("\n");
    let now = record_of_run(
        &compile_errors_of_failed_build(&stream),
        &[
            verified_row("delta_errors::f00", 0, Failed),
            verified_row("delta_errors::f01", 0, Proved),
        ],
        &coverage,
    );
    let read = parse_package_ndjson(&now.package_ndjson("delta-errors").unwrap()).unwrap();
    assert_eq!(read.compile_errors.len(), 1, "the verifier's error is recorded");
    assert!(read.concluded, "its unit published coverage: it concluded");

    let target = tempfile::tempdir().unwrap();
    let request = DeltaRequest::default();
    let first = shown_run(target.path(), &base, &request, Some("me"));
    let base_token = first.packages[0].now.clone().unwrap();
    let view = shown_run(target.path(), &now, &request, Some("me"));
    let lines = view.lines();
    assert_eq!(lines.len(), 4, "{lines:#?}");
    assert!(lines[0].starts_with("NEW ERROR   [ERROR]  src/lib.rs#error-"), "{lines:#?}");
    assert!(lines[0].contains(refusal), "{lines:#?}");
    assert!(lines[1].contains("delta_errors::f00#") && !lines[1].starts_with("STILL"));
    assert!(
        lines[2].starts_with("LOST        delta_errors::f01#")
            && lines[2].contains("vanished (was proved; its function's source did not change)"),
        "{lines:#?}"
    );
    let token = view.packages[0].now.clone().unwrap();
    // `M` is this run's two rows and the base's `LOST` row, which has none now.
    assert_eq!(
        lines[3],
        format!(
            "delta-errors  1 compiler error(s); 2 of 3 changed since {base_token}  (now {token})"
        )
    );
    // The run concluded, so it is the next run's base: a rerun prints the
    // error again and changes nothing.
    let again = shown_run(target.path(), &now, &request, Some("me")).lines();
    assert_eq!(again.len(), 2, "{again:#?}");
    assert!(again[0].starts_with("STILL       [ERROR]  "), "{again:#?}");
    assert_eq!(
        again[1],
        format!("delta-errors  1 compiler error(s); 0 of 2 changed since {token}  (now {token})")
    );
}

/// The view's error rows from records alone: new errors and a cleared one;
/// a run that did not compile compares no obligation, so `N` is 0 and only
/// its header facts and (with no listing) its open rows print.
#[test]
fn compile_error_rows_have_their_words_and_a_run_that_did_not_compile_compares_no_obligation() {
    let error = |message: &str, line: u32| crate::obligations::CompileError {
        package: "demo".to_string(),
        file: Some("src/lib.rs".to_string()),
        code: Some("E0308".to_string()),
        message: message.to_string(),
        line: Some(line),
        col: Some(5),
    };
    let mut base = package(&[(A, "proved", "solved")], true);
    base.compile_errors = crate::obligations::key_compile_errors(&[error("a", 3)]);
    let mut now = package(&[(A, "proved", "solved")], true);
    // Two errors of one file, code and message are numbered in source order.
    now.compile_errors = crate::obligations::key_compile_errors(&[error("b", 20), error("b", 10)]);
    assert_eq!(now.compile_errors[1].key, format!("{}~2", now.compile_errors[0].key));
    assert_eq!(now.compile_errors[0].line, Some(10));
    let rows = error_rows(Some(&base), &now);
    let row_words: Vec<&str> =
        rows.iter().map(|line| line.split("  ").next().unwrap().trim()).collect();
    assert_eq!(row_words, ["NEW ERROR", "NEW ERROR", "CLEARED"], "{rows:#?}");
    assert_eq!(error_rows(Some(&now), &now).len(), 2, "an error still reported prints again");
    assert!(
        error_rows(Some(&now), &base)[0]
            .starts_with("NEW ERROR   [ERROR E0308]  src/lib.rs#E0308-")
    );

    // `now` did not compile: its obligations are not compared with the
    // base's, whatever they are; its refuted row prints (with no listing).
    let measured = package(&[(A, "proved", "solved"), (B, "proved", "solved")], true);
    let mut broken = package(&[(A, "failed", "solved")], false);
    broken.compile_errors = now.compile_errors.clone();
    let not_compared = changes(&measured, &broken, true, false);
    assert_eq!(not_compared.rows, 0, "{not_compared:?}");
    assert_eq!(words(&not_compared), ["RUN", "STILL"], "{not_compared:?}");
    assert!(
        not_compared.lines[1].starts_with("STILL       [FAILED]  demo::a#"),
        "{not_compared:?}"
    );
    assert_eq!(changes(&measured, &broken, false, false).lines.len(), 1);
    // A message differing only in whitespace is the same error.
    assert_eq!(
        crate::obligations::compile_error_key(None, None, "a  b\n c"),
        crate::obligations::compile_error_key(None, None, "a b c")
    );
}

/// Compile-error lines out of key order, repeated, or after a function line
/// are not what the writer writes, and the reader refuses them.
#[test]
fn a_misplaced_compile_error_line_is_refused() {
    let header = ndjson(&[]);
    let line = |key: &str| {
        format!(
            "{{\"compile_error\":\"{key}\",\"code\":null,\"message\":\"m\",\"file\":null,\
             \"line\":null,\"col\":null}}\n"
        )
    };
    assert!(parse_package_ndjson(&format!("{header}{}{}", line("a"), line("b"))).is_ok());
    assert!(parse_package_ndjson(&format!("{header}{}{}", line("b"), line("a"))).is_err());
    assert!(parse_package_ndjson(&format!("{header}{}{}", line("a"), line("a"))).is_err());
    let after = format!("{}{}", ndjson(&[(A, "proved", "solved")]), line("a"));
    assert!(parse_package_ndjson(&after).is_err());
}

/// With no base, where the command prints no listing of its own, every row
/// that is not plainly proved prints, as a row of its own; beside a listing of
/// the command's own the listing keeps them; `--all-rows` prints every row.
#[test]
fn with_no_base_every_row_not_plainly_proved_still_prints() {
    let target = tempfile::tempdir().unwrap();
    let request = DeltaRequest::default();
    let record = vec![(
        "demo".to_string(),
        ndjson(&[
            (A, "proved", "solved"),
            (B, "failed", "solved"),
            (C, "unknown", "not-dispatched"),
        ]),
    )];
    let standalone = shown(target.path(), &record, &request, None, true);
    let lines = standalone.lines();
    assert_eq!(lines.len(), 3, "{lines:?}");
    assert!(lines[0].starts_with("[FAILED]  demo::b#"), "{lines:?}");
    assert!(lines[1].starts_with("[UNKNOWN]  demo::c#"), "{lines:?}");
    assert!(lines[2].starts_with("demo  3 obligation(s)  (now "), "{lines:?}");
    // A caller's first run has no base either.
    let first = shown(target.path(), &record, &request, Some("me"), true);
    assert_eq!(first.lines(), lines, "{first:?}");
    let checked = shown(target.path(), &record, &request, None, false);
    assert_eq!(checked.lines().len(), 1, "{checked:?}");
    let all = DeltaRequest { since: None, all_rows: true };
    assert_eq!(shown(target.path(), &record, &all, None, true).lines().len(), 4);
}

/// A `--since` whose snapshot cannot be read leaves the run without a base:
/// the caller's pointer does not stand in for the base the caller named.
#[test]
fn a_since_that_names_no_readable_snapshot_leaves_the_run_without_a_base() {
    let target = tempfile::tempdir().unwrap();
    let record = vec![("demo".to_string(), ndjson(&[(A, "proved", "solved")]))];
    shown(target.path(), &record, &DeltaRequest::default(), Some("me"), false);
    let missing = DeltaRequest { since: Some("0123456789abcdef".to_string()), all_rows: false };
    let view = shown(target.path(), &record, &missing, Some("me"), false);
    assert!(view.packages[0].since.is_none(), "{view:?}");
    assert_eq!(view.notes.len(), 1, "{view:?}");
    // A token never stored here (mistyped, say) is not said to have expired.
    assert!(view.notes[0].contains("(never stored there, or removed since;"), "{view:?}");
    assert!(view.notes[0].ends_with("no base"), "{view:?}");
}

/// A pointer that is there but cannot be read is noted, never silently
/// dropped; one that is not there is a first run and says nothing.
#[test]
fn a_pointer_that_cannot_be_read_is_noted() {
    let target = tempfile::tempdir().unwrap();
    let record = vec![("demo".to_string(), ndjson(&[(A, "proved", "solved")]))];
    let request = DeltaRequest::default();
    let first = shown(target.path(), &record, &request, Some("me"), false);
    assert!(first.notes.is_empty(), "{first:?}");
    let parsed = parse_package_ndjson(&record[0].1).unwrap();
    let pointer = pointer_path(&snapshots_dir(target.path()), "me", &parsed);
    std::fs::write(&pointer, [0xff, 0xfe, b'\n']).unwrap();
    let view = shown(target.path(), &record, &request, Some("me"), false);
    assert!(view.packages[0].since.is_none(), "{view:?}");
    assert!(view.notes[0].starts_with("your pointer `"), "{view:?}");
    assert!(view.notes[0].contains("cannot be read") && view.notes[0].ends_with("no base"));
}

/// Every base of a run is read before any snapshot is stored, so one
/// package's store (and the pruning it does) never removes another package's
/// base before it is compared with.
#[test]
fn every_base_of_a_run_is_read_before_any_snapshot_is_stored() {
    let target = tempfile::tempdir().unwrap();
    let dir = snapshots_dir(target.path());
    let request = DeltaRequest::default();
    let run = |status: &str| {
        vec![
            ("alpha".to_string(), ndjson_named("alpha", &[(A, status, "solved")])),
            ("beta".to_string(), ndjson_named("beta", &[(A, status, "solved")])),
        ]
    };
    let first = shown(target.path(), &run("proved"), &request, Some("me"), false);
    let beta_base = first.packages[1].now.clone().unwrap();
    // beta's base has not been used for more than the retention.
    let week_ago = SystemTime::now() - SNAPSHOT_RETENTION - Duration::from_secs(60);
    std::fs::File::options()
        .write(true)
        .open(dir.join(&beta_base))
        .unwrap()
        .set_modified(week_ago)
        .unwrap();
    // alpha's new snapshot is stored first and prunes; beta's base was read.
    let second = shown(target.path(), &run("failed"), &request, Some("me"), false);
    assert!(second.notes.is_empty(), "{second:?}");
    assert_eq!(second.packages[1].since.as_ref().map(|(token, _)| token), Some(&beta_base));
}

/// With `--all-rows` and a base, where the command prints no listing of its
/// own, the full listing already shows each unchanged row that is not plainly
/// proved, so it prints once, not again as `STILL`.
#[test]
fn with_all_rows_and_a_base_each_row_prints_once() {
    let target = tempfile::tempdir().unwrap();
    let record =
        vec![("demo".to_string(), ndjson(&[(A, "proved", "solved"), (B, "failed", "solved")]))];
    let all = DeltaRequest { since: None, all_rows: true };
    shown(target.path(), &record, &all, Some("me"), true);
    let again = shown(target.path(), &record, &all, Some("me"), true);
    assert!(again.packages[0].since.is_some(), "{again:?}");
    let lines = again.lines();
    assert_eq!(lines.len(), 3, "{lines:?}");
    assert!(lines[0].starts_with("[PROVED]  demo::a#"), "{lines:?}");
    assert!(lines[1].starts_with("[FAILED]  demo::b#"), "{lines:?}");
    assert!(lines.iter().all(|line| !line.starts_with("STILL")), "{lines:?}");
}

/// `--since` gives its snapshot's package that base and every other package of
/// the run none: no pointer stands in for a base the caller did not name.
#[test]
fn a_since_for_one_package_leaves_the_others_without_a_base() {
    let target = tempfile::tempdir().unwrap();
    let run = vec![
        ("alpha".to_string(), ndjson_named("alpha", &[(A, "proved", "solved")])),
        ("beta".to_string(), ndjson_named("beta", &[(A, "proved", "solved")])),
    ];
    let first = shown(target.path(), &run, &DeltaRequest::default(), Some("me"), false);
    let alpha = first.packages[0].now.clone().unwrap();
    let since = DeltaRequest { since: Some(alpha.clone()), all_rows: false };
    let view = shown(target.path(), &run, &since, Some("me"), false);
    assert_eq!(view.packages[0].since.as_ref().map(|(token, _)| token), Some(&alpha));
    assert!(view.packages[1].since.is_none(), "beta's pointer is not used: {view:?}");
    assert!(!view.replaces_listing());
    assert_eq!(view.notes.len(), 1, "{view:?}");
    assert!(view.notes[0].ends_with("the run's other packages have no base"), "{view:?}");

    // A snapshot of a package the run does not snapshot gives no package a base.
    let only_beta = vec![run[1].clone()];
    let view = shown(target.path(), &only_beta, &since, Some("me"), false);
    assert!(view.packages[0].since.is_none(), "{view:?}");
    assert!(view.notes[0].contains("which this run does not snapshot; no base"), "{view:?}");
}

fn age(path: &Path, by: Duration) {
    std::fs::File::options()
        .write(true)
        .open(path)
        .unwrap()
        .set_modified(SystemTime::now() - by)
        .unwrap();
}

/// A pointer is kept longer than the snapshot it names, so a base the 7-day
/// pruning removed is named in a note; a pointer nobody wrote for 30 days is
/// removed by the next prune, and its caller starts again with no base and no
/// note.
#[test]
fn a_pointer_outlives_its_pruned_snapshot_so_the_loss_is_noted() {
    let target = tempfile::tempdir().unwrap();
    let dir = snapshots_dir(target.path());
    let request = DeltaRequest::default();
    let mine = vec![("demo".to_string(), ndjson(&[(A, "proved", "solved")]))];
    let parsed = parse_package_ndjson(&mine[0].1).unwrap();
    let pointer = pointer_path(&dir, "me", &parsed);
    let token =
        shown(target.path(), &mine, &request, Some("me"), false).packages[0].now.clone().unwrap();
    // Neither the snapshot nor the pointer was used for 8 days; another
    // caller's new snapshot prunes the snapshot only.
    let eight_days = SNAPSHOT_RETENTION + Duration::from_secs(24 * 60 * 60);
    age(&dir.join(&token), eight_days);
    age(&pointer, eight_days);
    let theirs = vec![("demo".to_string(), ndjson(&[(A, "failed", "solved")]))];
    shown(target.path(), &theirs, &request, Some("other"), false);
    assert!(!dir.join(&token).exists() && pointer.is_file());
    let view = shown(target.path(), &mine, &request, Some("me"), false);
    assert!(view.packages[0].since.is_none(), "{view:?}");
    assert_eq!(
        view.notes,
        [format!("your previous snapshot {token} of `demo` was removed; no base")],
        "{view:?}"
    );

    // Thirty-one days without a run: the pointer goes too, silently.
    let month = POINTER_RETENTION + Duration::from_secs(24 * 60 * 60);
    age(&dir.join(&token), month);
    age(&pointer, month);
    let newer = vec![("demo".to_string(), ndjson(&[(A, "unknown", "not-dispatched")]))];
    shown(target.path(), &newer, &request, Some("other"), false);
    assert!(!pointer.exists(), "a pointer nobody wrote for 30 days is removed");
    let view = shown(target.path(), &mine, &request, Some("me"), false);
    assert!(view.packages[0].since.is_none() && view.notes.is_empty(), "{view:?}");
}

/// A pointer nobody wrote for 30 days is not read even when no prune has
/// removed it: a caller alone in its target directory, whose pointer and
/// snapshot are both still there, starts again with no base and no note, and
/// so does one whose snapshot alone was pruned.
#[test]
fn a_pointer_nobody_wrote_for_thirty_days_is_not_read_before_any_prune() {
    let target = tempfile::tempdir().unwrap();
    let dir = snapshots_dir(target.path());
    let request = DeltaRequest::default();
    let mine = vec![("demo".to_string(), ndjson(&[(A, "proved", "solved")]))];
    let pointer = pointer_path(&dir, "me", &parse_package_ndjson(&mine[0].1).unwrap());
    let token =
        shown(target.path(), &mine, &request, Some("me"), false).packages[0].now.clone().unwrap();
    let month = POINTER_RETENTION + Duration::from_secs(24 * 60 * 60);
    age(&pointer, month);
    assert!(pointer.is_file() && dir.join(&token).is_file(), "nothing was pruned");
    let view = publish(target.path(), &mine, &request, Some("me"), false);
    assert!(view.packages[0].since.is_none() && view.notes.is_empty(), "{view:?}");

    // The snapshot alone was pruned (another caller's write, between 7 and 30
    // days): the expired pointer gives no `was removed` note either.
    std::fs::remove_file(dir.join(&token)).unwrap();
    let view = publish(target.path(), &mine, &request, Some("me"), false);
    assert!(view.packages[0].since.is_none() && view.notes.is_empty(), "{view:?}");
}

/// With nowhere to keep the records (a `.lean` check that can name no target
/// directory), the view still lists every row that is not plainly proved, with
/// a summary line that names no token, and moves no pointer.
#[test]
fn a_view_with_nowhere_to_store_still_lists_the_rows_not_plainly_proved() {
    let record = vec![(
        "demo".to_string(),
        ndjson(&[
            (A, "proved", "solved"),
            (B, "failed", "solved"),
            (C, "unknown", "not-dispatched"),
        ]),
    )];
    let view = unstored(&record, &DeltaRequest::default());
    assert_eq!(
        view.lines(),
        [
            row("", &obligation(B, "failed", "solved"), None, false),
            row("", &obligation(C, "unknown", "not-dispatched"), None, false),
            "demo  3 obligation(s)  (now not stored)".to_string(),
        ],
        "{view:?}"
    );
    assert!(view.lines()[0].starts_with("[FAILED]  demo::b#"), "{view:?}");
    assert_eq!(view.commit_pointers(), Vec::<String>::new());
    let all = unstored(&record, &DeltaRequest { since: None, all_rows: true });
    assert_eq!(all.lines().len(), 4, "{all:?}");
}

/// `targo trust delta` refuses a record whose rows the view could not show:
/// a key that does not split into def path and id, or a key held twice.
#[test]
fn a_record_with_a_key_that_cannot_be_matched_is_refused() {
    let good = parse_package_ndjson(&ndjson(&[(A, "failed", "solved")])).unwrap();
    assert_eq!(keyed_once(&good), Ok(()));
    let mut unsplit = good.clone();
    unsplit.obligations[0].key = "demo::a#zz".to_string();
    assert!(keyed_once(&unsplit).unwrap_err().contains("`demo::a#zz` is not"));
    let mut twice = good.clone();
    twice.obligations.push(twice.obligations[0].clone());
    assert!(keyed_once(&twice).unwrap_err().ends_with("appears twice"));
}
