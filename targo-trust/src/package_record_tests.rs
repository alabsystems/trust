// Tests for crate::package_record: the `trust.package.v1` record, its
// agreement with the obligation record header and the run's `Summary:` line,
// per-package attribution, and the removal of a selected package's records.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::determinism::{BudgetProfile, NotedStop, StopCause, UnitOutcome, short_id};
use trust_types::obligation_identity::{ObligationIdentity, function_source_digest, local_id};

use super::*;
use crate::obligations::{FunctionInventory, ObligationRecords, RunScope};
use crate::types::{StructuredTransportEvidence, VerificationOutcome};

/// The checkout path a Cargo package ID and a function label embed in a real
/// run; no record may carry it.
const CHECKOUT: &str = "<home>/checkout-a";

fn run_facts(outcome: UnitOutcome, vector: String) -> RunFacts {
    RunFacts {
        lane: "strict".to_string(),
        policy: "strict".to_string(),
        selection: "--lib".to_string(),
        targo_trust_commit: "0123456789abcdef0123456789abcdef01234567".to_string(),
        profile: BudgetProfile::builtin().id(),
        worker_threads: 0,
        outcome,
        vector,
        coverage_complete: true,
        degraded_anchors: 0,
    }
}

/// A published row of `package`'s `function`, keyed as the compiler keys it,
/// with the function label a Cargo run gives it (which embeds the package ID).
fn row(
    package: &str,
    function: &str,
    n: u32,
    outcome: VerificationOutcome,
    reason: Option<&str>,
) -> VerificationResult {
    let mut row = VerificationResult {
        function: format!(
            "cargo-target(package_id=\"path+file://{CHECKOUT}/{package}#0.1.0\")::{function}"
        ),
        kind: "overflow:add".to_string(),
        message: "arithmetic overflow (Add)".to_string(),
        outcome,
        backend: "ay".to_string(),
        time_ms: Some(7),
        location: Some(trust_types::SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: 10 + n,
            col_start: 8,
            line_end: 10 + n,
            col_end: 13,
        }),
        counterexample: None,
        reason: reason.map(str::to_string),
        raw_line: String::new(),
    };
    let evidence = StructuredTransportEvidence {
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
            package: package.to_string(),
            function_source_sha256: Some(function_source_digest(function)),
            expanded_function_identity: None,
        }),
        grade: None,
    };
    crate::types::replace_structured_transport_evidence(&mut row, &evidence).expect("serializes");
    row
}

fn coverage(package: &str, eligible: usize, processed: usize) -> CoverageTransportSummary {
    CoverageTransportSummary {
        crate_name: package.replace('-', "_"),
        package_name: package.to_string(),
        primary_package: true,
        verification_session: "session".to_string(),
        eligible,
        processed,
        function_identities: None,
        noted_stops: Vec::new(),
        degraded_anchors: 0,
        memory: trust_types::MemorySummary::default(),
    }
}

/// The records of a run of `rows` and `coverage_rows`, as `run_compiler`
/// builds them: the run facts from the run's own determinism.
fn records(
    rows: &[VerificationResult],
    coverage_rows: &[CoverageTransportSummary],
    selected: &[&str],
    missing: &[&str],
) -> ObligationRecords {
    let noted = merged_noted_stops(coverage_rows);
    let run = UnitDeterminism::of_rows(rows, &noted);
    ObligationRecords::of_rows(
        rows,
        &FunctionInventory::of_rows(rows),
        run_facts(run.outcome, run.vector.digest()),
        RunScope {
            selected: selected.iter().map(ToString::to_string).collect(),
            resolved: BTreeSet::new(),
        },
        &RunCoverage {
            rows: coverage_rows,
            publication_stops: &[],
            missing: missing.iter().map(ToString::to_string).collect(),
            compile_errors: &[],
        },
    )
}

fn json(text: &str) -> serde_json::Value {
    serde_json::from_str(text).expect("a JSON record")
}

fn header(records: &ObligationRecords, package: &str) -> serde_json::Value {
    let ndjson = records.package_ndjson(package).expect("an obligation record");
    json(ndjson.lines().next().expect("a header line"))
}

fn record(records: &ObligationRecords, package: &str) -> serde_json::Value {
    json(&records.package_record_json(package).expect("a package record"))
}

#[test]
fn a_record_is_canonical_json_naming_every_field() {
    let rows = [row("demo", "demo::f", 0, VerificationOutcome::Proved, None)];
    let records = records(&rows, &[coverage("demo", 1, 1)], &["demo"], &[]);
    let text = records.package_record_json("demo").expect("demo");
    assert!(text.ends_with("}\n") && text.matches('\n').count() == 1, "{text}");
    let value = json(&text);
    assert_eq!(
        trust_types::digest::canonical_json_bytes(&value).expect("canonical"),
        text.trim_end().as_bytes(),
        "keys sorted, no insignificant whitespace"
    );
    let keys: Vec<&str> =
        value.as_object().expect("an object").keys().map(String::as_str).collect();
    let mut expected = vec![
        "conflicting_def_paths",
        "cost",
        "counts",
        "coverage",
        "degraded_anchors",
        "lane",
        "memory_need",
        "noted_stops",
        "outcome",
        "package",
        "policy",
        "profile",
        "provenance",
        "result_key",
        "schema",
        "seal",
        "selection",
        "stop_causes",
        "targo_trust_commit",
        "unkeyed_functions",
        "vector",
        "volatile_keys",
        "worker_threads",
    ];
    expected.sort_unstable();
    let mut keys_sorted = keys.clone();
    keys_sorted.sort_unstable();
    assert_eq!(keys_sorted, expected);
    assert_eq!(value["schema"], PACKAGE_RECORD_SCHEMA);
    assert_eq!(value["package"], "demo");
    assert_eq!(value["outcome"], "measured");
    assert_eq!(value["stop_causes"], serde_json::json!({ "solved": 1 }));
    // The worker-thread cap the run passed, beside the profile whose id omits it.
    assert_eq!(value["worker_threads"], 0);
    assert_eq!(
        value["coverage"],
        serde_json::json!({ "complete": true, "eligible": 1, "processed": 1 })
    );
    // The counts are the `Summary:` line's partition of the package's rows.
    let (counts, _) = partition_outcome_counts(&rows);
    assert_eq!(value["counts"]["total"], 1);
    assert_eq!(value["counts"]["proved"], counts.proved);
    assert_eq!(value["counts"]["unknown"], counts.unknown);
    assert_eq!(
        value["counts"].as_object().map(|counts| counts.keys().cloned().collect::<Vec<_>>()),
        Some(
            [
                "assumed",
                "contract_panics",
                "failed",
                "mandated",
                "proved",
                "runtime_checked",
                "total",
                "unknown",
            ]
            .map(String::from)
            .to_vec()
        )
    );
    assert_eq!(value["cost"], serde_json::json!({ "wall_clock_ms": 7 }));
    // What the toolchain cannot fill yet is marked absent, naming its item.
    // The seal's identity is not the commit targo-trust was built from: two
    // seals cut from one commit share that commit, so it is stated under its
    // own name and the seal is absent until A8.
    assert_eq!(value["seal"]["absent"], "A8");
    assert_eq!(value["targo_trust_commit"], records.facts.targo_trust_commit);
    assert_eq!(value["memory_need"]["absent"], "T3");
    assert_eq!(value["result_key"]["absent"], "T10");
    assert_eq!(value["provenance"]["absent"], "T10");
    for field in ["seal", "memory_need", "result_key", "provenance"] {
        assert!(value[field]["until"].as_str().is_some_and(|until| !until.is_empty()), "{field}");
    }
    // No absolute path and no package ID, though every row's label has both.
    assert!(!text.contains(CHECKOUT), "{text}");
    assert!(!text.contains("path+file"), "{text}");
}

/// One source of truth: a package's record, its obligation record header and,
/// in a one-package run, the run's own `Summary:` suffix and counts read the
/// same outcome, profile, vector and coverage.
#[test]
fn the_record_the_obligation_header_and_the_summary_agree() {
    let rows = [
        row("demo", "demo::f", 0, VerificationOutcome::Proved, None),
        row("demo", "demo::f", 1, VerificationOutcome::Unknown, Some("search ended [stop:effort]")),
        row("demo", "demo::g", 0, VerificationOutcome::Failed, None),
    ];
    let coverage_rows = [coverage("demo", 2, 2)];
    let records = records(&rows, &coverage_rows, &["demo"], &[]);
    let record = record(&records, "demo");
    let header = header(&records, "demo");

    // The run's own accounting, as the report's Summary line and gate make it.
    let run = UnitDeterminism::of_rows(&rows, &merged_noted_stops(&coverage_rows));
    let (counts, _) = partition_outcome_counts(&rows);
    let profile = BudgetProfile::builtin();
    let summary_suffix = run.summary_suffix(&profile);

    for value in [&record, &header] {
        assert_eq!(value["outcome"], run.outcome.as_str());
        assert_eq!(value["vector"], run.vector.digest());
        assert_eq!(value["profile"], profile.id());
        assert_eq!(value["lane"], "strict");
        assert_eq!(value["seal"]["absent"], "A8");
        assert_eq!(value["targo_trust_commit"], records.facts.targo_trust_commit);
    }
    assert_eq!(header["coverage_complete"], record["coverage"]["complete"]);
    assert_eq!(header["degraded_anchors"], record["degraded_anchors"]);
    assert_eq!(
        summary_suffix,
        format!(
            "; {}; profile {}; vector {}",
            record["outcome"].as_str().unwrap(),
            short_id(record["profile"].as_str().unwrap()),
            short_id(record["vector"].as_str().unwrap()),
        )
    );
    assert_eq!(record["counts"]["proved"], counts.proved);
    assert_eq!(record["counts"]["failed"], counts.failed);
    assert_eq!(record["counts"]["unknown"], counts.unknown);
    assert_eq!(record["counts"]["total"], counts.total);
    assert_eq!(record["stop_causes"], serde_json::to_value(&run.tally).unwrap());
    // ... and the run facts the baseline reads are the same in a one-package run.
    assert_eq!(records.facts.outcome.as_str(), record["outcome"]);
    assert_eq!(records.facts.vector, record["vector"]);
}

#[test]
fn each_package_is_accounted_for_on_its_own_share() {
    let mut clocked = coverage("slow", 1, 1);
    clocked.noted_stops = vec![NotedStop {
        lane: "router".to_string(),
        cause: StopCause::WallBackstop,
        item: None,
        count: 2,
    }];
    let rows = [
        row("fast", "fast::f", 0, VerificationOutcome::Proved, None),
        row("slow", "slow::g", 0, VerificationOutcome::Proved, None),
    ];
    let coverage_rows = [coverage("fast", 1, 1), clocked];
    let records = records(&rows, &coverage_rows, &["fast", "slow"], &[]);
    let fast = record(&records, "fast");
    let slow = record(&records, "slow");
    assert_eq!(fast["outcome"], "measured", "a backstop in another package is not this one's");
    assert_eq!(slow["outcome"], "not-reproducible");
    assert_eq!(slow["noted_stops"][0]["cause"], "wall-backstop");
    assert_eq!(fast["noted_stops"], serde_json::json!([]));
    assert_ne!(fast["vector"], slow["vector"]);
    assert_eq!(fast["counts"]["total"], 1);
    // The run is as reproducible as its least reproducible package.
    assert_eq!(records.facts.outcome, UnitOutcome::NotReproducible);
    // Each package's header is its own.
    assert_eq!(header(&records, "fast")["outcome"], "measured");
    assert_eq!(header(&records, "slow")["outcome"], "not-reproducible");
}

/// A row with no stable key names no package. It makes every package
/// could-not-run, as it makes the run, and is in no package's counts, stop
/// causes or cost: a keyless refutation is no package's `failed`, and the
/// packages' counts never sum to more than the run's. Each package states the
/// keyless rows as the run does: a compiler row as a function that published
/// no stable key, a row targo synthesized as the transport defect it is.
#[test]
fn a_row_without_a_stable_key_makes_every_package_could_not_run() {
    let mut keyless = row("fast", "fast::k", 0, VerificationOutcome::Failed, None);
    keyless.raw_line = String::new();
    let defect = VerificationResult {
        function: "<transport>".to_string(),
        kind: "transport:malformed".to_string(),
        message: "malformed transport line".to_string(),
        outcome: VerificationOutcome::Unknown,
        backend: "targo-trust".to_string(),
        time_ms: None,
        location: None,
        counterexample: None,
        reason: Some("expected value at line 1 column 1".to_string()),
        raw_line: String::new(),
    };
    let rows = [
        row("fast", "fast::f", 0, VerificationOutcome::Proved, None),
        row("slow", "slow::g", 0, VerificationOutcome::Proved, None),
        keyless,
        defect,
    ];
    let records = records(&rows, &[coverage("fast", 2, 2), coverage("slow", 1, 1)], &[], &[]);
    assert_eq!(records.facts.outcome, UnitOutcome::CouldNotRun, "the run could not run");
    let run = UnitDeterminism::of_rows(&rows, &[]);
    assert_eq!(run.unkeyed_published_functions.len(), 1, "the compiler's keyless row");
    assert_eq!(run.transport_defects.len(), 1, "targo's own row");
    let mut total = 0;
    for package in ["fast", "slow"] {
        let unit = &records.units[package].determinism;
        assert_eq!(unit.unkeyed_functions, run.unkeyed_functions, "{package}");
        assert_eq!(unit.unkeyed_published_functions, run.unkeyed_published_functions, "{package}");
        assert_eq!(unit.transport_defects, run.transport_defects, "{package}");
        assert_eq!(unit.could_not_run_line(), run.could_not_run_line(), "{package}");
        let record = record(&records, package);
        assert_eq!(record["outcome"], "could-not-run", "{package}");
        assert_eq!(header(&records, package)["outcome"], "could-not-run", "{package}");
        assert_eq!(record["unkeyed_functions"], 2, "{package}");
        assert_eq!(record["counts"]["failed"], 0, "the keyless refutation is not {package}'s");
        assert_eq!(record["counts"]["total"], 1, "{package}: its own row alone");
        assert_eq!(record["stop_causes"], serde_json::json!({ "solved": 1 }), "{package}");
        assert_eq!(record["cost"]["wall_clock_ms"], 7, "{package}");
        total += record["counts"]["total"].as_u64().expect("a count");
    }
    let (run_counts, _) = partition_outcome_counts(&rows);
    assert!(total <= run_counts.total as u64, "the packages' counts are within the run's");
}

#[test]
fn coverage_is_the_packages_own_and_a_unit_without_one_leaves_it_incomplete() {
    let rows = [
        row("a", "a::f", 0, VerificationOutcome::Proved, None),
        row("b", "b::g", 0, VerificationOutcome::Proved, None),
    ];
    let coverage_rows = [coverage("a", 3, 3), coverage("b", 2, 1)];
    let records = records(&rows, &coverage_rows, &["a", "b"], &[]);
    assert_eq!(
        record(&records, "a")["coverage"],
        serde_json::json!({ "complete": true, "eligible": 3, "processed": 3 })
    );
    assert_eq!(record(&records, "b")["coverage"]["complete"], false);
    assert_eq!(header(&records, "b")["coverage_complete"], false);

    // A unit of `a` concluded without publishing coverage.
    let records = records_with_missing(&rows, &coverage_rows);
    assert_eq!(record(&records, "a")["coverage"]["complete"], false);
    assert_eq!(header(&records, "a")["coverage_complete"], false);
}

fn records_with_missing(
    rows: &[VerificationResult],
    coverage_rows: &[CoverageTransportSummary],
) -> ObligationRecords {
    records(rows, coverage_rows, &["a", "b"], &["a"])
}

#[test]
fn a_selected_package_that_published_nothing_still_has_both_records() {
    let rows = [row("demo", "demo::f", 0, VerificationOutcome::Proved, None)];
    let records = records(&rows, &[coverage("demo", 1, 1)], &["demo", "quiet"], &[]);
    let quiet = record(&records, "quiet");
    assert_eq!(quiet["coverage"], serde_json::Value::Null, "no unit of it published coverage");
    assert_eq!(quiet["counts"]["total"], 0);
    // It was never measured (no unit of it concluded), so it is not a
    // measured empty result: an empty vector is not a measurement of it.
    assert_eq!(quiet["outcome"], "could-not-run");
    assert_eq!(header(&records, "quiet")["outcome"], "could-not-run");
    assert_eq!(record(&records, "demo")["outcome"], "measured", "its sibling was measured");
    // A package whose rows arrived with no coverage row of any unit of it is
    // no measurement either.
    let uncovered = self::records(&rows, &[], &["demo"], &[]);
    assert_eq!(record(&uncovered, "demo")["outcome"], "could-not-run");
    let ndjson = records.package_ndjson("quiet").expect("an obligation record");
    assert_eq!(ndjson.lines().count(), 1, "a header and no function: {ndjson}");
    assert_eq!(header(&records, "quiet")["coverage_complete"], false);
    assert!(records.package_record_json("never-mentioned").is_none());
}

#[test]
fn cost_is_wall_clock_and_outside_every_digest() {
    let fast = [row("demo", "demo::f", 0, VerificationOutcome::Proved, None)];
    let mut slow = fast.clone();
    slow[0].time_ms = Some(9_000);
    let a = record(&records(&fast, &[coverage("demo", 1, 1)], &["demo"], &[]), "demo");
    let b = record(&records(&slow, &[coverage("demo", 1, 1)], &["demo"], &[]), "demo");
    assert_ne!(a["cost"], b["cost"]);
    let without_cost = |mut value: serde_json::Value| {
        value.as_object_mut().expect("an object").remove("cost");
        value
    };
    assert_eq!(without_cost(a), without_cost(b), "only `cost` moves with the clock");
}

#[test]
fn records_do_not_depend_on_the_order_of_the_rows() {
    let rows = [
        row("demo", "demo::f", 0, VerificationOutcome::Proved, None),
        row("other", "other::h", 0, VerificationOutcome::Unknown, Some("[stop:effort]")),
        row("demo", "demo::g", 1, VerificationOutcome::Failed, None),
    ];
    let coverage_rows = [coverage("demo", 2, 2), coverage("other", 1, 1)];
    let forward = records(&rows, &coverage_rows, &["demo", "other"], &[]);
    let mut reversed_rows = rows.to_vec();
    reversed_rows.reverse();
    let mut reversed_coverage = coverage_rows.to_vec();
    reversed_coverage.reverse();
    let reversed = records(&reversed_rows, &reversed_coverage, &["other", "demo"], &[]);
    for package in ["demo", "other"] {
        assert_eq!(forward.package_record_json(package), reversed.package_record_json(package));
        assert_eq!(forward.package_ndjson(package), reversed.package_ndjson(package));
    }
}

#[test]
fn removing_records_takes_only_the_selected_packages() {
    let dir = tempfile::tempdir().expect("tempdir");
    let rows = [
        row("demo", "demo::f", 0, VerificationOutcome::Proved, None),
        row("other", "other::h", 0, VerificationOutcome::Proved, None),
    ];
    let records = records(&rows, &[], &["demo", "other"], &[]);
    let written = records.write_records(dir.path()).expect("write");
    assert_eq!(written.len(), 4);
    let removed =
        remove_records(dir.path(), &["demo".to_string(), "absent".to_string()].into()).expect("rm");
    assert_eq!(
        removed,
        [
            crate::obligations::records_dir(dir.path()).join("demo.ndjson"),
            package_records_dir(dir.path()).join("demo.json"),
        ]
    );
    assert!(package_records_dir(dir.path()).join("other.json").is_file());
    assert!(crate::obligations::records_dir(dir.path()).join("other.ndjson").is_file());
}

#[test]
fn publication_elision_stops_reach_exact_package_records_without_new_obligations() {
    for owner in [Some("a"), None] {
        let rows = vec![
            row("a", "f", 0, VerificationOutcome::Proved, None),
            row("b", "g", 0, VerificationOutcome::Proved, None),
        ];
        let coverage_rows = vec![coverage("a", 1, 1), coverage("b", 1, 1)];
        let notes = vec![crate::types::PublicationStop {
            package: owner.map(str::to_string),
            stop: NotedStop {
                lane: "publication-alias-elision".into(),
                cause: StopCause::WallBackstop,
                item: None,
                count: 1,
            },
        }];
        let all_notes = crate::determinism_report::noted_stops_with_publication(&[], &notes, None);
        let run = UnitDeterminism::of_rows(&rows, &all_notes);
        let records = ObligationRecords::of_rows(
            &rows,
            &FunctionInventory::of_rows(&rows),
            run_facts(run.outcome, run.vector.digest()),
            RunScope::default(),
            &RunCoverage {
                rows: &coverage_rows,
                missing: BTreeSet::new(),
                publication_stops: &notes,
                compile_errors: &[],
            },
        );
        let a = record(&records, "a");
        let b = record(&records, "b");
        assert_eq!(a["outcome"], "not-reproducible");
        assert_eq!(b["outcome"], if owner.is_some() { "measured" } else { "not-reproducible" });
        // This identity-only fixture omits the required typed overflow kind:
        // its favorable label earns no proof credit, with or without notes.
        for package in [&a, &b] {
            assert_eq!(package["counts"]["proved"], 0);
            assert_eq!(package["counts"]["unknown"], 1);
            assert_eq!(package["counts"]["total"], 1);
        }
        assert_eq!(a["noted_stops"][0]["cause"], "wall-backstop");
        assert_eq!(header(&records, "a")["outcome"], a["outcome"]);
        assert_eq!(header(&records, "b")["outcome"], b["outcome"]);
    }
}
