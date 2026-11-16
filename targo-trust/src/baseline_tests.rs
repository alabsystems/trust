// Tests for crate::baseline: the byte-deterministic format, merge, the pairing
// of functions, every comparison rule and the exit mapping.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::obligation_identity::{function_source_digest, local_id};

use super::*;
use crate::obligations::{ObligationRecord, ObligationRecords, RunFacts, RunScope};

fn facts() -> RunFacts {
    RunFacts {
        lane: "strict".to_string(),
        policy: "strict".to_string(),
        selection: "--lib".to_string(),
        targo_trust_commit: "0123456789abcdef0123456789abcdef01234567".to_string(),
        profile: "p".repeat(64),
        worker_threads: 0,
        outcome: UnitOutcome::Measured,
        vector: "v".repeat(64),
        coverage_complete: true,
        degraded_anchors: 0,
    }
}

fn id(n: u32) -> String {
    local_id("divzero", "stmt:0000000000000000", n)
}

fn record(def_path: &str, n: u32, status: &str) -> ObligationRecord {
    ObligationRecord {
        key: obligation_key(def_path, &id(n)),
        kind: "divzero".to_string(),
        status: status.to_string(),
        stop: if status == "proved" { "solved" } else { "effort" }.to_string(),
        file: Some("src/lib.rs".to_string()),
        line: Some(3 + n),
        col: Some(4),
        encoding: crate::obligations::UNGRADED.to_string(),
        discharge: crate::obligations::UNGRADED.to_string(),
        premises: Vec::new(),
        basis: (status == "failed").then(|| "refuted".to_string()),
    }
}

/// One function of a test run: `(package, def path, source text, [(n, status)])`.
type FunctionSpec<'a> = (&'a str, &'a str, &'a str, &'a [(u32, &'a str)]);

/// A run of `functions`.
fn run(functions: &[FunctionSpec<'_>]) -> ObligationRecords {
    let mut packages: BTreeMap<String, crate::obligations::PackageRecords> = BTreeMap::new();
    for (package, def_path, source, rows) in functions {
        let records = rows.iter().map(|(n, status)| record(def_path, *n, status)).collect();
        packages.entry((*package).to_string()).or_default().insert(
            (*def_path).to_string(),
            function_records(Some(&function_source_digest(source)), records),
        );
    }
    ObligationRecords {
        facts: facts(),
        scope: RunScope::default(),
        packages,
        unkeyed_functions: Vec::new(),
        conflicting_functions: Vec::new(),
        units: BTreeMap::new(),
        compile_errors: BTreeMap::new(),
        tests: None,
        test_arguments: Vec::new(),
        clean_islands: BTreeMap::new(),
    }
}

/// `records` with the obligation `key` of `package` given `status` and `stop`.
fn with_stop(
    mut records: ObligationRecords,
    package: &str,
    def_path: &str,
    n: u32,
    status: &str,
    stop: &str,
) -> ObligationRecords {
    let record = records
        .packages
        .get_mut(package)
        .and_then(|functions| functions.get_mut(def_path))
        .and_then(|function| function.obligations.get_mut(&id(n)))
        .expect("the record exists");
    record.status = status.to_string();
    record.stop = stop.to_string();
    records
}

fn scope(selected: &[&str], resolved: &[&str]) -> RunScope {
    RunScope {
        selected: selected.iter().map(ToString::to_string).collect(),
        resolved: resolved.iter().map(ToString::to_string).collect(),
    }
}

const F: &str = "pub fn f(a: u64, b: u64) -> u64 { a / b }";
const F_EDITED: &str = "pub fn f(a: u64, b: u64) -> u64 { a / (b | 1) }";
const G: &str = "pub fn g(a: u64) -> u64 { a / 3 }";

#[test]
fn saving_twice_is_byte_identical_and_parses_back() {
    let records = run(&[
        ("demo", "demo::g", G, &[(0, "proved")]),
        ("demo", "demo::f", F, &[(1, "proved"), (0, "proved"), (2, "unknown")]),
        ("aaa", "aaa::h", G, &[(0, "proved")]),
    ]);
    let first = Baseline::project(&records).render();
    let second = Baseline::project(&records).render();
    assert_eq!(first, second);
    // Sorted bytewise, LF only, proved ids only, unproved ids absent.
    assert!(
        first.starts_with("trust-baseline v1\nlane strict\npolicy strict\nselection --lib\n"),
        "{first}"
    );
    assert!(first.find("package aaa").unwrap() < first.find("package demo").unwrap());
    assert!(first.find("\tdemo::f\t").unwrap() < first.find("\tdemo::g\t").unwrap());
    assert!(!first.contains(&id(2)), "an unproved key is not in the baseline");
    let mut ids = [id(0), id(1)];
    ids.sort();
    assert!(first.contains(&format!("{} {}\n", ids[0], ids[1])), "{first}");
    assert!(!first.contains('\r'));
    let parsed = Baseline::parse(&first).expect("parses");
    assert_eq!(parsed, Baseline::project(&records));
    assert_eq!(parsed.render(), first);
}

#[test]
fn the_parser_refuses_anything_but_the_canonical_form() {
    let good = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])])).render();
    for bad in [
        good.replace("trust-baseline v1", "trust-baseline v0"),
        good.replace('\n', "\r\n"),
        good.trim_end().to_string(),
        good.replace("lane strict\n", ""),
        good.replace("policy strict\n", ""),
        format!("{good}\n"),
        good.replace(&id(0), "XYZ"),
        format!("{good}package demo\n"),
        good.replace("fn\t", "fn "),
    ] {
        assert!(Baseline::parse(&bad).is_err(), "{bad:?}");
    }
}

#[test]
fn merge_keeps_packages_the_run_did_not_select() {
    let existing = Baseline::project(&run(&[
        ("a", "a::f", F, &[(0, "proved")]),
        ("b", "b::g", G, &[(0, "proved")]),
    ]));
    let rerun_a = Baseline::project(&run(&[("a", "a::f", F, &[(0, "proved"), (1, "proved")])]));
    let merged = merge(&existing, &rerun_a, &scope(&["a"], &["a", "b"])).expect("same lane");
    assert_eq!(merged.baseline.packages["b"], existing.packages["b"], "b is kept verbatim");
    assert_eq!(merged.baseline.packages["a"], rerun_a.packages["a"], "a is replaced");
    assert!(merged.dropped.is_empty());

    let a_scope = scope(&["a"], &["a", "b"]);
    let mut other_lane = rerun_a.clone();
    other_lane.lane = "advisory".to_string();
    assert!(merge(&existing, &other_lane, &a_scope).is_err());
    let mut other_policy = rerun_a.clone();
    other_policy.policy = "advisory".to_string();
    assert!(merge(&existing, &other_policy, &a_scope).is_err(), "--survey is not --allow-l0-gaps");
    let mut other_build = rerun_a.clone();
    other_build.targo_trust_commit = "f".repeat(40);
    assert!(merge(&existing, &other_build, &a_scope).is_err(), "a half-re-based file is refused");
    let mut whole = Baseline::project(&run(&[
        ("a", "a::f", F, &[(0, "proved")]),
        ("b", "b::g", G, &[(0, "proved")]),
    ]));
    whole.targo_trust_commit = "f".repeat(40);
    let merged = merge(&existing, &whole, &scope(&["a", "b"], &["a", "b"])).expect("a re-base");
    assert_eq!(merged.baseline, whole);
}

#[test]
fn merge_drops_a_selected_package_without_records_and_a_package_gone_from_the_resolve() {
    let existing = Baseline::project(&run(&[
        ("a", "a::f", F, &[(0, "proved")]),
        ("b", "b::g", G, &[(0, "proved")]),
        ("gone", "gone::h", G, &[(0, "proved")]),
    ]));
    // The run selected `a` and `b` but holds a record of `a` alone; `gone` is
    // in the resolve no more.
    let run_a = Baseline::project(&run(&[("a", "a::f", F, &[(0, "proved")])]));
    let merged = merge(&existing, &run_a, &scope(&["a", "b"], &["a", "b"])).expect("merges");
    assert_eq!(merged.baseline.packages.keys().collect::<Vec<_>>(), ["a"]);
    let dropped: Vec<&str> = merged.dropped.iter().map(|(p, _)| p.as_str()).collect();
    assert_eq!(dropped, ["b", "gone"]);
    // An unselected package the resolve still has — a path dependency, say —
    // is kept, member or not.
    let merged = merge(&existing, &run_a, &scope(&["a"], &["a", "b", "gone"])).expect("merges");
    assert!(merged.baseline.packages.contains_key("gone"));
    // Outside Cargo nothing is known about the resolve: an unselected package
    // is kept.
    let merged = merge(&existing, &run_a, &scope(&["a"], &[])).expect("merges");
    assert!(merged.baseline.packages.contains_key("gone"));
}

#[test]
fn an_unchanged_run_loses_nothing_and_passes() {
    let records = run(&[("demo", "demo::f", F, &[(0, "proved"), (1, "unknown")])]);
    let baseline = Baseline::project(&records);
    let comparison = compare(&baseline, &records, None);
    assert_eq!(comparison, Comparison::default());
    assert_eq!(exit_status(&comparison, &records), 0);
}

#[test]
fn a_present_key_that_is_no_longer_proved_is_lost() {
    let baseline = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let now = run(&[("demo", "demo::f", F, &[(0, "unknown")])]);
    let comparison = compare(&baseline, &now, None);
    assert_eq!(comparison.lost.len(), 1);
    assert_eq!(comparison.lost[0].reason, LostReason::NotProved);
    let line = comparison.lost[0].line();
    assert!(
        line.starts_with(&format!("demo demo::f #{} divzero unknown effort src/lib.rs:3:4", id(0))),
        "{line}"
    );
    assert_eq!(exit_status(&comparison, &now), EXIT_LOST);
}

#[test]
fn a_key_vanished_from_unchanged_source_is_lost() {
    let baseline = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let now = run(&[("demo", "demo::f", F, &[])]);
    let comparison = compare(&baseline, &now, None);
    assert_eq!(comparison.lost.len(), 1);
    assert_eq!(comparison.lost[0].reason, LostReason::VanishedFromUnchangedSource);
    assert_eq!(exit_status(&comparison, &now), EXIT_LOST);
}

#[test]
fn a_key_vanished_with_an_edit_of_its_function_is_accepted() {
    let baseline = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let now = run(&[("demo", "demo::f", F_EDITED, &[(5, "unknown")])]);
    let comparison = compare(&baseline, &now, None);
    assert!(comparison.lost.is_empty(), "{:?}", comparison.lost);
    assert_eq!(
        comparison.vanished_with_edit,
        [("demo".to_string(), obligation_key("demo::f", &id(0)))]
    );
    assert_eq!(exit_status(&comparison, &now), 0);
}

#[test]
fn a_vanished_key_without_a_source_digest_on_either_side_is_lost() {
    let baseline = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let mut now = run(&[("demo", "demo::f", F_EDITED, &[])]);
    now.packages.get_mut("demo").unwrap().get_mut("demo::f").unwrap().source = None;
    let comparison = compare(&baseline, &now, None);
    assert_eq!(comparison.lost.len(), 1, "an unstated digest cannot show an edit");
}

#[test]
fn a_function_that_publishes_no_rows_under_unchanged_source_loses_every_key() {
    // `f` had three proved keys; now the compiler verified it and published
    // only the elided inventory row — every obligation vanished from source
    // that did not change (a callee that became `-> !`, a new seal).
    let baseline = Baseline::project(&run(&[(
        "demo",
        "demo::f",
        F,
        &[(0, "proved"), (1, "proved"), (2, "proved")],
    )]));
    let now = run(&[("demo", "demo::f", F, &[])]);
    let comparison = compare(&baseline, &now, None);
    assert_eq!(comparison.lost.len(), 3, "{comparison:?}");
    assert!(
        comparison.lost.iter().all(|lost| lost.reason == LostReason::VanishedFromUnchangedSource)
    );
    assert!(comparison.removed_functions.is_empty(), "a verified function is not removed");
    assert_eq!(exit_status(&comparison, &now), EXIT_LOST);
    // With its source edited, the same loss is accepted — and named.
    let edited = run(&[("demo", "demo::f", F_EDITED, &[])]);
    let comparison = compare(&baseline, &edited, None);
    assert_eq!(comparison.vanished_with_edit.len(), 3);
    assert_eq!(exit_status(&comparison, &edited), 0);
    let text = render_terminal(&comparison, &baseline, &edited);
    assert!(
        text.contains(&format!("VANISHED demo {}", obligation_key("demo::f", &id(0)))),
        "{text}"
    );
}

#[test]
fn a_closure_renumbered_by_an_inserted_closure_is_compared_with_itself() {
    const C0: &str = "|x: u64| x / 3";
    const NEW: &str = "|y: u64| y + 1";
    // `f::{closure#0}` proved key 0; a closure inserted before it renumbers it
    // to `{closure#1}`, and its proof is lost on the way.
    let baseline =
        Baseline::project(&run(&[("demo", "demo::f::{closure#0}", C0, &[(0, "proved")])]));
    let now = run(&[
        ("demo", "demo::f::{closure#0}", NEW, &[(5, "proved")]),
        ("demo", "demo::f::{closure#1}", C0, &[(0, "unknown")]),
    ]);
    let comparison = compare(&baseline, &now, None);
    assert_eq!(comparison.lost.len(), 1, "{comparison:?}");
    assert_eq!(comparison.lost[0].reason, LostReason::NotProved);
    assert_eq!(
        comparison.moved_functions,
        [(
            "demo".to_string(),
            "demo::f::{closure#0}".to_string(),
            "demo::f::{closure#1}".to_string(),
            PairedBy::Source
        )]
    );
    assert!(comparison.vanished_with_edit.is_empty(), "the old closure was not edited");
    assert_eq!(exit_status(&comparison, &now), EXIT_LOST);
}

#[test]
fn a_renamed_and_edited_function_is_paired_by_its_proved_ids() {
    let baseline = Baseline::project(&run(&[(
        "demo",
        "demo::f",
        F,
        &[(0, "proved"), (1, "proved"), (2, "proved")],
    )]));
    // Renamed to `g` (so its source digest moved) and one proof lost.
    let now = run(&[("demo", "demo::g", G, &[(0, "proved"), (1, "proved"), (2, "unknown")])]);
    let comparison = compare(&baseline, &now, None);
    assert_eq!(
        comparison.moved_functions,
        [("demo".to_string(), "demo::f".to_string(), "demo::g".to_string(), PairedBy::Ids)]
    );
    assert_eq!(comparison.lost.len(), 1);
    assert_eq!(comparison.lost[0].id, id(2));
    assert!(comparison.removed_functions.is_empty());
    assert_eq!(exit_status(&comparison, &now), EXIT_LOST);
    // A minority of the ids is no pairing: the function is removed, by name.
    let unrelated = run(&[("demo", "demo::g", G, &[(0, "proved"), (7, "proved"), (8, "proved")])]);
    let comparison = compare(&baseline, &unrelated, None);
    assert_eq!(comparison.removed_functions, [("demo".to_string(), "demo::f".to_string())]);
    let text = render_terminal(&comparison, &baseline, &unrelated);
    assert!(text.contains("REMOVED demo demo::f\n"), "{text}");
}

#[test]
fn a_key_stopped_by_a_non_reproducible_cause_is_not_measured_not_lost() {
    let baseline = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let now = with_stop(
        run(&[("demo", "demo::f", F, &[(0, "unknown")])]),
        "demo",
        "demo::f",
        0,
        "unknown",
        "wall-backstop",
    );
    let comparison = compare(&baseline, &now, None);
    assert!(comparison.lost.is_empty(), "a clock decides nothing: {comparison:?}");
    assert_eq!(comparison.unmeasured_keys.len(), 1);
    assert_eq!(exit_status(&comparison, &now), EXIT_NOT_MEASURED);
    let text = render_terminal(&comparison, &baseline, &now);
    assert!(text.contains("NOT MEASURED demo demo::f#"), "{text}");
    // A deterministic stop (the effort count) is a loss.
    let effort = with_stop(
        run(&[("demo", "demo::f", F, &[(0, "unknown")])]),
        "demo",
        "demo::f",
        0,
        "unknown",
        "effort",
    );
    assert_eq!(exit_status(&compare(&baseline, &effort, None), &effort), EXIT_LOST);
}

#[test]
fn new_code_is_named_and_a_refutation_in_it_fails() {
    let baseline = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let now = run(&[
        ("demo", "demo::f", F, &[(0, "proved")]),
        ("demo", "demo::g", G, &[(0, "unknown"), (1, "failed")]),
    ]);
    let comparison = compare(&baseline, &now, None);
    assert!(comparison.lost.is_empty());
    assert_eq!(comparison.new_failed().count(), 1);
    assert_eq!(exit_status(&comparison, &now), EXIT_LOST, "a counterexample is not a gap");
    let text = render_terminal(&comparison, &baseline, &now);
    assert!(
        text.contains(&format!("NEW FAILED demo {}", obligation_key("demo::g", &id(1)))),
        "{text}"
    );
    assert!(text.contains(&format!("NEW demo {}", obligation_key("demo::g", &id(0)))), "{text}");
    // An unproved key in an EDITED held function is new code too.
    let edited = run(&[("demo", "demo::f", F_EDITED, &[(0, "proved"), (3, "unknown")])]);
    let comparison = compare(&baseline, &edited, None);
    assert_eq!(comparison.new_unproved.len(), 1);
    assert_eq!(exit_status(&comparison, &edited), 0);
    // A refutation in an unchanged held function is named, not a new failure.
    let unchanged = run(&[("demo", "demo::f", F, &[(0, "proved"), (3, "failed")])]);
    let comparison = compare(&baseline, &unchanged, None);
    assert_eq!(comparison.failed_unchanged.len(), 1);
    assert_eq!(exit_status(&comparison, &unchanged), 0);
    let json = render_json(&comparison, &unchanged, 0);
    assert_eq!(json["failed_unchanged"].as_array().map(Vec::len), Some(1));
}

#[test]
fn a_removed_function_is_accepted() {
    let baseline = Baseline::project(&run(&[
        ("demo", "demo::f", F, &[(0, "proved")]),
        ("demo", "demo::g", G, &[(0, "proved")]),
    ]));
    let now = run(&[("demo", "demo::g", G, &[(0, "proved")])]);
    let comparison = compare(&baseline, &now, None);
    assert!(comparison.lost.is_empty());
    assert_eq!(comparison.removed_functions, [("demo".to_string(), "demo::f".to_string())]);
    assert_eq!(exit_status(&comparison, &now), 0);
}

#[test]
fn a_moved_function_is_matched_by_its_source_digest() {
    let baseline =
        Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved"), (1, "proved")])]));
    // Same source under a new path, one proof lost on the way.
    let now = run(&[("demo", "demo::inner::f", F, &[(0, "proved"), (1, "unknown")])]);
    let comparison = compare(&baseline, &now, None);
    assert_eq!(
        comparison.moved_functions,
        [(
            "demo".to_string(),
            "demo::f".to_string(),
            "demo::inner::f".to_string(),
            PairedBy::Source
        )]
    );
    assert_eq!(comparison.lost.len(), 1, "a move is compared, not excused");
    assert_eq!(comparison.lost[0].id, id(1));
    assert!(comparison.gained.is_empty(), "the moved function's kept proof is not a gain");

    // Two candidates with the same digest: no move by digest, and the ids are
    // in both, so no move by ids either — removed.
    let ambiguous = run(&[
        ("demo", "demo::a::f", F, &[(0, "proved"), (1, "proved")]),
        ("demo", "demo::b::f", F, &[(0, "proved"), (1, "proved")]),
    ]);
    let comparison = compare(&baseline, &ambiguous, None);
    assert!(comparison.moved_functions.is_empty());
    assert_eq!(comparison.removed_functions.len(), 1);
}

#[test]
fn gains_and_new_code_are_accepted_and_reported() {
    let baseline =
        Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved"), (1, "unknown")])]));
    let now = run(&[
        ("demo", "demo::f", F, &[(0, "proved"), (1, "proved")]),
        ("demo", "demo::g", G, &[(0, "proved"), (1, "unknown")]),
        ("fresh", "fresh::h", G, &[(0, "unknown")]),
    ]);
    let comparison = compare(&baseline, &now, None);
    assert!(comparison.lost.is_empty());
    let gained: Vec<&str> = comparison.gained.iter().map(|(_, r)| r.key.as_str()).collect();
    assert!(gained.contains(&obligation_key("demo::f", &id(1)).as_str()));
    assert!(gained.contains(&obligation_key("demo::g", &id(0)).as_str()));
    let new: Vec<&str> = comparison.new_unproved.iter().map(|(_, r)| r.key.as_str()).collect();
    assert_eq!(new.len(), 2, "{new:?}");
    // `f`'s key 1 was unproved in the baseline and its source is unchanged:
    // not new, so not listed.
    assert!(!new.contains(&obligation_key("demo::f", &id(1)).as_str()));
    assert_eq!(exit_status(&comparison, &now), 0);
}

#[test]
fn the_exit_status_maps_lost_then_not_measured() {
    let baseline = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let mut not_measured = run(&[("demo", "demo::f", F, &[(0, "proved")])]);
    not_measured.facts.outcome = UnitOutcome::NotReproducible;
    let comparison = compare(&baseline, &not_measured, None);
    assert_eq!(exit_status(&comparison, &not_measured), EXIT_NOT_MEASURED);

    let mut incomplete = run(&[("demo", "demo::f", F, &[(0, "proved")])]);
    incomplete.facts.coverage_complete = false;
    assert_eq!(exit_status(&compare(&baseline, &incomplete, None), &incomplete), EXIT_NOT_MEASURED);

    // A loss outranks the missing measurement.
    let mut lost_and_unmeasured = run(&[("demo", "demo::f", F, &[(0, "unknown")])]);
    lost_and_unmeasured.facts.outcome = UnitOutcome::CouldNotRun;
    let comparison = compare(&baseline, &lost_and_unmeasured, None);
    assert_eq!(exit_status(&comparison, &lost_and_unmeasured), EXIT_LOST);

    // A baseline package the run did not measure.
    let other = run(&[("other", "other::f", F, &[(0, "proved")])]);
    let comparison = compare(&baseline, &other, None);
    assert_eq!(comparison.unmeasured_packages, ["demo"]);
    assert_eq!(exit_status(&comparison, &other), EXIT_NOT_MEASURED);
    // ...unless the diff was scoped away from it.
    let scope: BTreeSet<String> = ["other".to_string()].into();
    let comparison = compare(&baseline, &other, Some(&scope));
    assert!(comparison.unmeasured_packages.is_empty());
    assert_eq!(exit_status(&comparison, &other), 0);
}

#[test]
fn only_a_measurement_is_saved() {
    let mut records = run(&[("demo", "demo::f", F, &[(0, "proved")])]);
    assert_eq!(save_refusal(&records), None);
    records.facts.outcome = UnitOutcome::NotReproducible;
    assert!(save_refusal(&records).is_some());
    records.facts.outcome = UnitOutcome::Measured;
    records.facts.coverage_complete = false;
    assert!(save_refusal(&records).is_some());
    records.facts.coverage_complete = true;
    records.unkeyed_functions.push("demo::g".to_string());
    assert!(save_refusal(&records).is_some());
}

#[test]
fn a_lane_policy_or_selection_mismatch_is_named() {
    let baseline = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let mut facts = facts();
    assert_eq!(lane_mismatch(&baseline, &facts), None);
    facts.selection = "--all-targets".to_string();
    assert!(lane_mismatch(&baseline, &facts).unwrap().contains("--all-targets"));
    let mut facts = self::facts();
    facts.targo_trust_commit = "another".to_string();
    assert_eq!(lane_mismatch(&baseline, &facts), None, "a new build is what a diff is for");
    // A `--release` baseline is not a default-profile one, and a `--survey`
    // baseline is not an `--allow-l0-gaps` one.
    let args = |list: &[&str]| list.iter().map(ToString::to_string).collect::<Vec<_>>();
    let mut release = self::facts();
    release.selection = crate::obligations::canonical_selection(&args(&["check", "--lib", "-r"]));
    assert_eq!(release.selection, "--lib --profile=release");
    assert!(lane_mismatch(&baseline, &release).is_some());
    let mut survey = self::facts();
    survey.lane = "advisory".to_string();
    survey.policy = "advisory".to_string();
    let mut gaps = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    gaps.lane = "advisory".to_string();
    assert!(lane_mismatch(&gaps, &survey).unwrap().contains("policy `advisory`"));
}

#[test]
fn a_diff_check_inherits_the_baselines_packages_selection_and_lane() {
    let mut baseline = Baseline::project(&run(&[
        ("a", "a::f", F, &[(0, "proved")]),
        ("b", "b::g", G, &[(0, "proved")]),
    ]));
    baseline.lane = "advisory".to_string();
    let args: Vec<String> = ["--baseline", "trust.baseline", "--format", "json"]
        .iter()
        .map(ToString::to_string)
        .collect();
    let check = diff_check_args(&args, &baseline, false);
    assert_eq!(
        check,
        ["--format", "json", "-p", "a", "-p", "b", "--lib", "--allow-l0-gaps"]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
    );
    // A survey baseline re-runs as a survey, and its profile comes along.
    baseline.policy = "advisory".to_string();
    baseline.selection = "--lib --profile=release".to_string();
    let check = diff_check_args(&args, &baseline, false);
    assert!(check.ends_with(&[
        "--lib".to_string(),
        "--profile=release".to_string(),
        "--survey".to_string()
    ]));
    assert_eq!(lane_flags("advisory", "certify"), None, "no flag set selects that pair");
    // Explicit packages, selection and lane are the caller's.
    let args: Vec<String> = ["--baseline=x", "-p", "a", "--all-targets", "--certify"]
        .iter()
        .map(ToString::to_string)
        .collect();
    let check = diff_check_args(&args, &baseline, true);
    assert_eq!(check, ["-p", "a", "--all-targets", "--certify"]);
    assert_eq!(explicit_packages(&check), ["a".to_string()].into());
}

#[test]
fn key_delta_names_lost_and_gained_keys() {
    let before = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let after = Baseline::project(&run(&[("demo", "demo::f", F, &[(1, "proved")])]));
    let (lost, gained) = key_delta(&before, &after);
    assert_eq!(lost, [format!("demo {}", obligation_key("demo::f", &id(0)))]);
    assert_eq!(gained, [format!("demo {}", obligation_key("demo::f", &id(1)))]);
}

#[test]
fn the_reports_render() {
    let baseline = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let now = run(&[("demo", "demo::f", F, &[(0, "unknown")])]);
    let comparison = compare(&baseline, &now, None);
    let text = render_terminal(&comparison, &baseline, &now);
    assert!(text.contains("LOST demo demo::f #"), "{text}");
    assert!(text.contains("Baseline: 1 lost, 0 new failed, 0 not measured, 0 gained"), "{text}");
    let json = render_json(&comparison, &now, EXIT_LOST);
    assert_eq!(json["exit"], 1);
    assert_eq!(json["lost"][0]["reason"], "not-proved");
}

#[test]
fn a_conflicting_or_unkeyed_function_keeps_the_run_from_being_a_measurement() {
    let baseline = Baseline::project(&run(&[("demo", "demo::f", F, &[(0, "proved")])]));
    let mut now = run(&[("demo", "demo::f", F, &[(0, "proved")])]);
    now.conflicting_functions.push("demo demo::run".to_string());
    let comparison = compare(&baseline, &now, None);
    assert_eq!(exit_status(&comparison, &now), EXIT_NOT_MEASURED);
    assert!(save_refusal(&now).is_some_and(|why| why.contains("demo demo::run")));
    assert!(render_terminal(&comparison, &baseline, &now).contains("NOT MEASURED demo demo::run"));
}
