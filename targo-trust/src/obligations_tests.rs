// Tests for crate::obligations: the compact record's header, order and size,
// the function inventory, and the canonical selection.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::obligation_identity::{ObligationIdentity, function_source_digest, local_id};

use super::*;
use crate::package_record::RunCoverage;
use crate::types::{StructuredTransportEvidence, VerificationOutcome};

fn facts() -> RunFacts {
    RunFacts {
        lane: "strict".to_string(),
        policy: "strict".to_string(),
        selection: "--lib".to_string(),
        targo_trust_commit: "0123456789abcdef0123456789abcdef01234567".to_string(),
        profile: "a".repeat(64),
        worker_threads: 0,
        outcome: UnitOutcome::Measured,
        vector: "b".repeat(64),
        coverage_complete: true,
        degraded_anchors: 0,
    }
}

/// The records of `rows`, over the inventory of the same rows, with one
/// complete coverage row for each package the rows name (every verified unit
/// publishes one; a package without one was not measured).
fn records_of(rows: &[VerificationResult]) -> ObligationRecords {
    let packages: BTreeSet<String> = rows
        .iter()
        .filter_map(|row| structured_transport_evidence(row).and_then(|e| e.identity))
        .map(|identity| identity.package)
        .collect();
    let coverage: Vec<trust_types::CoverageTransportSummary> = packages
        .into_iter()
        .map(|package| trust_types::CoverageTransportSummary {
            crate_name: package.replace('-', "_"),
            package_name: package,
            primary_package: true,
            verification_session: "session".to_string(),
            eligible: 1,
            processed: 1,
            function_identities: None,
            noted_stops: Vec::new(),
            degraded_anchors: 0,
            memory: trust_types::MemorySummary::default(),
        })
        .collect();
    ObligationRecords::of_rows(
        rows,
        &FunctionInventory::of_rows(rows),
        facts(),
        RunScope::default(),
        &RunCoverage {
            rows: &coverage,
            missing: BTreeSet::new(),
            publication_stops: &[],
            compile_errors: &[],
        },
    )
}

fn row(package: &str, function: &str, n: u32, outcome: VerificationOutcome) -> VerificationResult {
    row_with_source(package, function, function, n, outcome)
}

fn row_with_source(
    package: &str,
    function: &str,
    source: &str,
    n: u32,
    outcome: VerificationOutcome,
) -> VerificationResult {
    let mut row = VerificationResult {
        function: format!("cargo-target(package={package:?})::{function}"),
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
            function_source_sha256: Some(function_source_digest(source)),
            expanded_function_identity: None,
        }),
        grade: None,
    };
    crate::types::replace_structured_transport_evidence(&mut row, &evidence).expect("serializes");
    row
}

#[test]
fn records_group_by_package_and_function_and_carry_the_header() {
    let rows = [
        row("demo", "demo::g", 0, VerificationOutcome::Proved),
        row("demo", "demo::f", 1, VerificationOutcome::Unknown),
        row("demo", "demo::f", 0, VerificationOutcome::Proved),
        row("other", "other::h", 0, VerificationOutcome::Failed),
    ];
    let records = records_of(&rows);
    assert_eq!(records.packages.keys().collect::<Vec<_>>(), ["demo", "other"]);
    assert!(records.unkeyed_functions.is_empty());
    let ndjson = records.package_ndjson("demo").expect("demo present");
    let lines: Vec<serde_json::Value> =
        ndjson.lines().map(|line| serde_json::from_str(line).expect("json line")).collect();
    let header = &lines[0];
    for field in [
        "schema",
        "package",
        "lane",
        "policy",
        "selection",
        "seal",
        "targo_trust_commit",
        "profile",
        "outcome",
        "vector",
        "degraded_anchors",
    ] {
        assert!(header.get(field).is_some(), "header field {field}");
    }
    assert_eq!(header["schema"], OBLIGATIONS_SCHEMA);
    assert_eq!(header["package"], "demo");
    // The outcome is the package's own (T7c): `demo::f`'s unknown row states
    // no stop, so `demo` is not reproducible, while `other`'s one refuted row
    // is solved and `other` is measured.
    assert_eq!(header["outcome"], "not-reproducible");
    let other = records.package_ndjson("other").expect("other present");
    let other_header: serde_json::Value =
        serde_json::from_str(other.lines().next().expect("header")).expect("json");
    assert_eq!(other_header["outcome"], "measured");
    // fn lines in def-path order, each followed by its obligations in key order.
    assert_eq!(lines[1]["fn"], "demo::f");
    assert_eq!(lines[1]["source"], function_source_digest("demo::f"));
    let f_keys: Vec<&str> = lines[2..4].iter().map(|l| l["key"].as_str().unwrap()).collect();
    let mut sorted = f_keys.clone();
    sorted.sort_unstable();
    assert_eq!(f_keys, sorted);
    assert_eq!(lines[4]["fn"], "demo::g");
    assert_eq!(lines[5]["status"], "proved");
    assert_eq!(lines[5]["stop"], "solved");
    assert_eq!(lines[5]["line"], 10);
    // The order is a property of the content, not of the row order.
    let mut reversed = rows.to_vec();
    reversed.reverse();
    assert_eq!(records_of(&reversed).package_ndjson("demo"), Some(ndjson));
}

#[test]
fn a_record_is_compact() {
    let rows: Vec<VerificationResult> = (0..50)
        .map(|n| {
            row("demo", "demo::a_function_with_a_realistic_name", n, VerificationOutcome::Proved)
        })
        .collect();
    let ndjson = records_of(&rows).package_ndjson("demo").expect("demo");
    let obligation_lines: Vec<&str> = ndjson.lines().filter(|l| l.contains("\"key\"")).collect();
    assert_eq!(obligation_lines.len(), 50);
    for line in obligation_lines {
        assert!(line.len() < 512, "{} bytes: {line}", line.len());
    }
}

#[test]
fn a_key_seen_twice_keeps_its_worst_status_and_a_keyless_row_is_named() {
    let mut keyless = row("demo", "demo::k", 0, VerificationOutcome::Proved);
    keyless.raw_line = String::new();
    let rows = [
        row("demo", "demo::f", 0, VerificationOutcome::Proved),
        row("demo", "demo::f", 0, VerificationOutcome::Unknown),
        keyless,
    ];
    let records = records_of(&rows);
    let function = &records.packages["demo"]["demo::f"];
    assert_eq!(function.obligations.len(), 1);
    assert_eq!(function.obligations.values().next().unwrap().status, "unknown");
    assert_eq!(records.unkeyed_functions.len(), 1);
}

#[test]
fn records_are_written_one_file_per_package() {
    let dir = tempfile::tempdir().expect("tempdir");
    let rows = [
        row("demo", "demo::f", 0, VerificationOutcome::Proved),
        row("other", "other::h", 0, VerificationOutcome::Proved),
    ];
    let records = records_of(&rows);
    let obligations = records_dir(dir.path());
    let packages = crate::package_record::package_records_dir(dir.path());
    let written = records.write_records(dir.path()).expect("write");
    assert_eq!(
        written,
        [
            obligations.join("demo.ndjson"),
            packages.join("demo.json"),
            obligations.join("other.ndjson"),
            packages.join("other.json"),
        ]
    );
    assert_eq!(
        std::fs::read_to_string(&written[0]).expect("read"),
        records.package_ndjson("demo").unwrap()
    );
    assert_eq!(
        std::fs::read_to_string(&written[1]).expect("read"),
        records.package_record_json("demo").unwrap()
    );
}

#[test]
fn the_selection_is_canonical() {
    let args = |list: &[&str]| list.iter().map(ToString::to_string).collect::<Vec<_>>();
    assert_eq!(canonical_selection(&args(&["check", "-p", "x", "--workspace"])), "default");
    assert_eq!(
        canonical_selection(&args(&["check", "--tests", "--lib", "-F", "a,b", "--bin=tool"])),
        "--bin=tool --features=a,b --lib --tests"
    );
    assert_eq!(
        canonical_selection(&args(&["check", "--lib", "--", "--tests"])),
        "--lib",
        "arguments after `--` are the program's"
    );
    assert_eq!(selection_args("--features=a --lib"), ["--features=a", "--lib"]);
    assert!(selection_args("default").is_empty());
    // The profile, `--config` values and `-Z` options decide what is compiled.
    assert_eq!(
        canonical_selection(&args(&["check", "--lib", "--release"])),
        canonical_selection(&args(&["check", "--profile", "release", "--lib"]))
    );
    assert_eq!(canonical_selection(&args(&["check", "-r"])), "--profile=release");
    assert_eq!(
        canonical_selection(&args(&[
            "check",
            "--config",
            "profile.dev.opt-level=2",
            "-Z",
            "build-std",
            "--config=b=1",
            "-Zunstable-options",
        ])),
        "-Zbuild-std -Zunstable-options --config=profile.dev.opt-level=2 --config=b=1"
    );
    assert_eq!(
        selection_args("--lib --profile=release --config=a=1"),
        ["--lib", "--profile=release", "--config=a=1"]
    );
}

#[test]
fn a_function_with_every_row_elided_is_still_in_the_records() {
    // The authenticated rows held `demo::f`'s only row, which publication
    // elided as inventory; `demo::g` published a row.
    let authenticated = [
        row("demo", "demo::f", 0, VerificationOutcome::Proved),
        row("demo", "demo::g", 0, VerificationOutcome::Proved),
    ];
    let published = [authenticated[1].clone()];
    let records = ObligationRecords::of_rows(
        &published,
        &FunctionInventory::of_rows(&authenticated),
        facts(),
        RunScope::default(),
        &RunCoverage::default(),
    );
    let f = &records.packages["demo"]["demo::f"];
    assert!(f.obligations.is_empty(), "f is present, with no obligation");
    assert_eq!(f.source.as_deref(), Some(function_source_digest("demo::f").as_str()));
    let ndjson = records.package_ndjson("demo").expect("demo");
    assert!(ndjson.contains("{\"fn\":\"demo::f\""), "{ndjson}");
}

#[test]
fn a_def_path_with_two_source_digests_is_named_and_a_duplicate_key_is_chosen_by_content() {
    // A library and a binary of one package both define `demo::run`.
    let rows = [
        row_with_source("demo", "demo::run", "fn run() { lib }", 0, VerificationOutcome::Proved),
        row_with_source("demo", "demo::run", "fn run() { bin }", 1, VerificationOutcome::Proved),
    ];
    let records = records_of(&rows);
    assert_eq!(records.conflicting_functions, ["demo demo::run"]);
    assert_eq!(records.packages["demo"]["demo::run"].source, None);

    // One key published by two units with two different unproved records:
    // whichever arrives first, the same record is kept.
    let mut timeout = row("demo", "demo::f", 0, VerificationOutcome::Timeout);
    timeout.reason = Some("deadline".to_string());
    let unknown = row("demo", "demo::f", 0, VerificationOutcome::Unknown);
    let forward = records_of(&[timeout.clone(), unknown.clone()]);
    let backward = records_of(&[unknown, timeout]);
    assert_eq!(forward.package_ndjson("demo"), backward.package_ndjson("demo"));
}

// The reader the stability verb compares records with reads back exactly what
// the writer writes, and nothing else: another schema, an unknown field, a
// line that is neither a function nor an obligation are each refused by line.
#[test]
fn a_record_reads_back_as_written_and_nothing_else_is_read() {
    let rows = [
        row("demo", "demo::g", 0, VerificationOutcome::Proved),
        row("demo", "demo::f", 1, VerificationOutcome::Unknown),
        row("demo", "demo::f", 0, VerificationOutcome::Proved),
    ];
    let records = records_of(&rows);
    let ndjson = records.package_ndjson("demo").expect("demo present");
    let read = parse_package_ndjson(&ndjson).expect("reads back");
    let facts = &records.units["demo"];
    assert_eq!(read.package, "demo");
    assert_eq!(read.lane, records.facts.lane);
    assert_eq!(read.selection, records.facts.selection);
    assert_eq!(read.profile, records.facts.profile);
    assert_eq!(read.outcome, facts.determinism.outcome.as_str());
    assert_eq!(read.vector, facts.vector_digest());
    assert_eq!(read.coverage_complete, facts.coverage_complete());
    assert!(read.concluded, "a package whose unit published its coverage row concluded");
    let written: Vec<&ObligationRecord> = records.packages["demo"]
        .values()
        .flat_map(|function| function.obligations.values())
        .collect();
    assert_eq!(read.obligations.iter().collect::<Vec<_>>(), written);

    let header = ndjson.lines().next().expect("a header");
    for (text, refusal) in [
        (String::new(), "empty"),
        (ndjson.replacen(OBLIGATIONS_SCHEMA, "trust.obligations.v0", 1), "names schema"),
        (ndjson.replacen("\"lane\"", "\"extra\":1,\"lane\"", 1), "line 1"),
        (format!("{header}\n{{\"neither\":true}}\n"), "line 2 is not an obligation line"),
        (
            format!("{header}\n{{\"fn\":\"f\",\"source\":null,\"x\":1}}\n"),
            "line 2 is not a function line",
        ),
        (format!("{header}\nnot json\n"), "line 2 is not JSON"),
    ] {
        let error = parse_package_ndjson(&text).expect_err(refusal);
        assert!(error.contains(refusal), "{refusal}: {error}");
    }
}

/// `row`, with the compiler-stated grade `grade` on its transport evidence.
fn graded_row(
    function: &str,
    n: u32,
    grade: trust_types::authority_grade::ObligationGrade,
) -> VerificationResult {
    let mut row = row("demo", function, n, VerificationOutcome::Proved);
    let mut evidence = structured_transport_evidence(&row).expect("structured evidence");
    evidence.grade = Some(grade);
    crate::types::replace_structured_transport_evidence(&mut row, &evidence).expect("serializes");
    row
}

/// VF1: every obligation line carries the three grade fields, the compiler's
/// grade when it stated one and `ungraded` otherwise, and they read back.
#[test]
fn every_obligation_line_carries_its_grade() {
    use trust_types::authority_grade::{
        GradeDischarge, GradeEncoding, GradePremise, ObligationGrade,
    };
    let rows = [
        graded_row(
            "demo::cited",
            0,
            ObligationGrade::new(
                GradeEncoding::E6Reflector,
                GradeDischarge::KernelReconstructed,
                &[GradePremise::ParameterView],
            ),
        ),
        row("demo", "demo::plain", 0, VerificationOutcome::Unknown),
    ];
    let records = records_of(&rows);
    let ndjson = records.package_ndjson("demo").expect("demo");
    let lines: Vec<serde_json::Value> =
        ndjson.lines().map(|line| serde_json::from_str(line).expect("json")).collect();
    let obligation = |key_fn: &str| {
        lines
            .iter()
            .find(|line| line["key"].as_str().is_some_and(|key| key.starts_with(key_fn)))
            .unwrap_or_else(|| panic!("no obligation line for {key_fn}"))
    };
    let cited = obligation("demo::cited#");
    assert_eq!(cited["encoding"], "e6-reflector");
    assert_eq!(cited["discharge"], "kernel-reconstructed");
    assert_eq!(cited["premises"], serde_json::json!(["parameter-view"]));
    let plain = obligation("demo::plain#");
    assert_eq!(plain["encoding"], UNGRADED);
    assert_eq!(plain["discharge"], UNGRADED);
    assert_eq!(plain["premises"], serde_json::json!([]));
    let read = parse_package_ndjson(&ndjson).expect("reads back");
    assert!(
        read.obligations.iter().any(
            |record| record.encoding == "e6-reflector" && record.premises == ["parameter-view"]
        )
    );
}

/// VF1's schema test: a `trust.obligations.v1` obligation line without any one
/// of its grade fields is refused, as is a grade outside the vocabulary. The
/// unedited record reads, so each refusal is the edit's.
#[test]
fn an_obligation_line_without_its_grade_fields_is_refused() {
    let rows = [row("demo", "demo::f", 0, VerificationOutcome::Proved)];
    let ndjson = records_of(&rows).package_ndjson("demo").expect("demo");
    parse_package_ndjson(&ndjson).expect("the unedited record reads");
    let lines: Vec<&str> = ndjson.lines().collect();
    assert_eq!(lines.len(), 3, "header, function line, one obligation line: {ndjson}");
    let obligation: serde_json::Value = serde_json::from_str(lines[2]).expect("json");
    assert_eq!(obligation["encoding"], UNGRADED);
    // The record with its obligation line edited by `edit`.
    let edited = |edit: &dyn Fn(&mut serde_json::Map<String, serde_json::Value>)| {
        let mut line = obligation.as_object().expect("an object").clone();
        edit(&mut line);
        format!("{}\n{}\n{}\n", lines[0], lines[1], serde_json::Value::Object(line))
    };
    let set = |encoding: &'static str, discharge: &'static str, premises: &'static [&str]| {
        move |line: &mut serde_json::Map<String, serde_json::Value>| {
            line.insert("encoding".into(), encoding.into());
            line.insert("discharge".into(), discharge.into());
            line.insert("premises".into(), serde_json::json!(premises));
        }
    };
    let cases: Vec<(String, &str)> = vec![
        (edited(&|line| drop(line.remove("encoding"))), "missing field `encoding`"),
        (edited(&|line| drop(line.remove("discharge"))), "missing field `discharge`"),
        (edited(&|line| drop(line.remove("premises"))), "missing field `premises`"),
        (
            edited(&|line| {
                for field in ["encoding", "discharge", "premises"] {
                    line.remove(field);
                }
            }),
            "missing field",
        ),
        (
            edited(&set("certified", "kernel-reconstructed", &[])),
            "unknown grade encoding `certified`",
        ),
        (
            edited(&set("unvalidated-encoder", "kernel-checked", &[])),
            "unknown grade discharge `kernel-checked`",
        ),
        (
            edited(&set("unvalidated-encoder", "kernel-reconstructed", &["trust-me"])),
            "unknown grade premise `trust-me`",
        ),
        (edited(&set(UNGRADED, UNGRADED, &["parameter-view"])), "an ungraded row"),
        (edited(&set("unvalidated-encoder", UNGRADED, &[])), "an ungraded row"),
        // VF1 review: a grade no compiler states. Calculus credit not VF5's,
        // an incoherent pair, repeated or unordered premises.
        (
            edited(&set("proven-calculus", "kernel-reconstructed", &[])),
            "no proof authority states encoding `proven-calculus`",
        ),
        (
            edited(&set("e6-reflector", "assumed", &[])),
            "no proof authority states encoding `e6-reflector` with discharge `assumed`",
        ),
        (
            edited(&set(
                "e6-reflector",
                "kernel-reconstructed",
                &["parameter-view", "parameter-view"],
            )),
            "not in declaration order without repeats",
        ),
        (
            edited(&set(
                "unvalidated-encoder",
                "compiler-composed",
                &["sibling-rows", "panic-free-callee-registry"],
            )),
            "not in declaration order without repeats",
        ),
        // A grade its status does not admit: a refuted, timed-out or
        // runtime-checked row carries none, an unknown row only an assumption.
        (
            edited(&|line| {
                set("unvalidated-encoder", "kernel-reconstructed", &[])(line);
                line.insert("status".into(), "failed".into());
            }),
            "a `failed` row cannot carry a `kernel-reconstructed` grade",
        ),
        (
            edited(&|line| {
                set("unvalidated-encoder", "solver-asserted", &[])(line);
                line.insert("status".into(), "unknown".into());
            }),
            "a `unknown` row cannot carry a `solver-asserted` grade",
        ),
        (
            edited(&|line| {
                set("not-encoded", "assumed", &["user-assume-total"])(line);
                line.insert("status".into(), "runtime_checked".into());
            }),
            "a `runtime_checked` row cannot carry a `assumed` grade",
        ),
    ];
    // Controls for the status rule: the same grades on a status that admits
    // them read.
    parse_package_ndjson(&edited(&|line| {
        set("not-encoded", "assumed", &["user-assume-total"])(line);
        line.insert("status".into(), "unknown".into());
    }))
    .expect("an assumption on an unknown line reads");
    parse_package_ndjson(&edited(&set(
        "unvalidated-encoder",
        "compiler-composed",
        &["panic-free-callee-registry", "sibling-rows"],
    )))
    .expect("ordered premises read");
    // The controls: a full grade in the vocabulary reads.
    parse_package_ndjson(&edited(&set(
        "unvalidated-encoder",
        "kernel-reconstructed",
        &["argument-premise"],
    )))
    .expect("a graded line reads");
    for (text, refusal) in cases {
        let error = parse_package_ndjson(&text).expect_err(refusal);
        assert!(error.contains("line 3 is not an obligation line"), "{refusal}: {error}");
        assert!(error.contains(refusal), "{refusal}: {error}");
    }
}

/// The demo row `function`#`n` as the compiler transports it: an exact typed
/// division-by-zero row with `outcome` and `grade`, and (when `split_brain`) a
/// description that disagrees with its typed kind, which targo demotes.
fn transported_row(
    function: &str,
    n: u32,
    outcome: trust_types::Outcome,
    grade: Option<trust_types::authority_grade::ObligationGrade>,
    split_brain: bool,
) -> VerificationResult {
    let kind = trust_types::VcKind::DivisionByZero;
    let transport = trust_types::TransportObligationResult {
        assumes: Vec::new(),
        gap_class: None,
        obligation_id: Some(format!("vc:{function}:division_by_zero:{n}")),
        claim_digest_sha256: None,
        original_vc_snapshot: None,
        kind: kind.transport_tag(),
        typed_kind: Some(Box::new(kind.clone())),
        description: if split_brain {
            "a different obligation".to_string()
        } else {
            kind.description()
        },
        location: None,
        outcome,
        solver: "ay".to_string(),
        time_ms: 1,
        counterexample: None,
        counterexample_model: None,
        reason: None,
        design_mandate: false,
        native_trust_ir: None,
        proof_evidence: None,
        monitor: None,
        grade,
    };
    let identity = ObligationIdentity {
        key: trust_types::obligation_identity::obligation_key(
            function,
            &local_id("div:zero", "stmt:0123456789abcdef", n),
        ),
        package: "demo".to_string(),
        function_source_sha256: Some(function_source_digest(function)),
        expanded_function_identity: None,
    };
    crate::types::transport_to_verification_result(
        &format!("cargo-target(package=\"demo\")::{function}"),
        &transport,
        None,
        Some(identity),
    )
}

/// VF1 review: the compiler's grade reaches the obligation line through the
/// transport conversion (`StructuredTransportEvidence::from_transport`), and
/// is written only while the final status admits it: a row targo demoted
/// (split-brain typed kind) and a refuted row are written `ungraded`, though
/// the compiler graded both; a compiler `skipped` assumption row (filed
/// `unknown`) keeps its `assumed` grade.
#[test]
fn the_compiler_grade_reaches_the_line_only_while_the_status_admits_it() {
    use trust_types::Outcome;
    use trust_types::authority_grade::{
        GradeDischarge, GradeEncoding, GradePremise, ObligationGrade,
    };
    let kernel = ObligationGrade::new(
        GradeEncoding::UnvalidatedEncoder,
        GradeDischarge::KernelReconstructed,
        &[],
    );
    let assumed = ObligationGrade::new(
        GradeEncoding::NotEncoded,
        GradeDischarge::Assumed,
        &[GradePremise::UserAssumeTotal],
    );
    let rows = [
        transported_row("demo::proved", 0, Outcome::Proved, Some(kernel.clone()), false),
        transported_row("demo::demoted", 0, Outcome::Proved, Some(kernel.clone()), true),
        transported_row("demo::refuted", 0, Outcome::Failed, Some(kernel.clone()), false),
        transported_row("demo::assumed", 0, Outcome::Skipped, Some(assumed), false),
    ];
    assert_eq!(rows[1].outcome, VerificationOutcome::Unknown, "the split-brain row is demoted");
    let ndjson = records_of(&rows).package_ndjson("demo").expect("demo");
    let lines: Vec<serde_json::Value> =
        ndjson.lines().map(|line| serde_json::from_str(line).expect("json")).collect();
    let grade_of = |function: &str| {
        let line = lines
            .iter()
            .find(|line| {
                line["key"].as_str().is_some_and(|key| key.starts_with(&format!("{function}#")))
            })
            .unwrap_or_else(|| panic!("no obligation line for {function}: {ndjson}"));
        (
            line["status"].as_str().unwrap_or_default().to_string(),
            line["encoding"].as_str().unwrap_or_default().to_string(),
            line["discharge"].as_str().unwrap_or_default().to_string(),
            line["premises"].clone(),
        )
    };
    let graded = |status: &str, encoding: &str, discharge: &str, premises: serde_json::Value| {
        (status.to_string(), encoding.to_string(), discharge.to_string(), premises)
    };
    assert_eq!(
        grade_of("demo::proved"),
        graded("proved", "unvalidated-encoder", "kernel-reconstructed", serde_json::json!([]))
    );
    assert_eq!(
        grade_of("demo::demoted"),
        graded("unknown", UNGRADED, UNGRADED, serde_json::json!([]))
    );
    assert_eq!(
        grade_of("demo::refuted"),
        graded("failed", UNGRADED, UNGRADED, serde_json::json!([]))
    );
    assert_eq!(
        grade_of("demo::assumed"),
        graded("unknown", "not-encoded", "assumed", serde_json::json!(["user-assume-total"]))
    );
    parse_package_ndjson(&ndjson).expect("the written record reads back");
}

/// VF5: the calculus authority's grade (`proven-calculus` through the
/// reference entry, with its three premises) is written on a proved line and
/// read back; the same grade with a premise dropped, or on an `unknown` line,
/// is written `ungraded`, and a hand-edited line claiming it is refused.
#[test]
fn the_calculus_grade_is_written_only_whole_and_only_on_a_proved_line() {
    use trust_types::authority_grade::{
        CALCULUS_ROW_PREMISES, GradeDischarge, GradeEncoding, GradePremise, ObligationGrade,
    };
    let calculus = ObligationGrade::new(
        GradeEncoding::ProvenCalculus,
        GradeDischarge::KernelReferenceChecked,
        &CALCULUS_ROW_PREMISES,
    );
    let (encoding, discharge, premises) = grade_fields(Some(&calculus), "proved");
    assert_eq!(
        (encoding.as_str(), discharge.as_str()),
        ("proven-calculus", "kernel-reference-checked")
    );
    assert_eq!(premises, ["semr-translation", "target-kappa", "closed-world-entry"]);
    assert_eq!(check_grade_fields("proved", &encoding, &discharge, &premises), Ok(()));
    assert_eq!(grade_fields(Some(&calculus), "unknown").0, UNGRADED);
    let dropped = ObligationGrade::new(
        GradeEncoding::ProvenCalculus,
        GradeDischarge::KernelReferenceChecked,
        &[GradePremise::SemrTranslation, GradePremise::TargetKappa],
    );
    assert_eq!(grade_fields(Some(&dropped), "proved").0, UNGRADED);
    let edited = ["semr-translation".to_string(), "target-kappa".to_string()];
    assert!(
        check_grade_fields("proved", "proven-calculus", "kernel-reference-checked", &edited)
            .unwrap_err()
            .contains("states the premises")
    );
}

/// VF1 review: a grade no compiler states never reaches a line, even on a
/// proved row: calculus credit by any discharge but the reference entry's is
/// written `ungraded`.
#[test]
fn a_grade_no_compiler_states_is_written_ungraded() {
    use trust_types::authority_grade::{GradeDischarge, GradeEncoding, ObligationGrade};
    let calculus = ObligationGrade::new(
        GradeEncoding::ProvenCalculus,
        GradeDischarge::KernelReconstructed,
        &[],
    );
    assert_eq!(grade_fields(Some(&calculus), "proved").0, UNGRADED);
    // Control: an admitted grade on the same status is written.
    let kernel = ObligationGrade::new(
        GradeEncoding::UnvalidatedEncoder,
        GradeDischarge::KernelReconstructed,
        &[],
    );
    assert_eq!(grade_fields(Some(&kernel), "proved").0, "unvalidated-encoder");
}

/// A `failed` line states its basis — refuted, or failed closed with nothing
/// refuting it — and no other line states one; the reader refuses anything
/// else. The basis is what the listing's `FAILED`/`FAILED: …` label reads.
#[test]
fn a_failed_line_states_its_basis_and_no_other_line_does() {
    let rows = [
        row("demo", "demo::f", 0, VerificationOutcome::Failed),
        row("demo", "demo::g", 0, VerificationOutcome::Proved),
    ];
    let records = records_of(&rows);
    let ndjson = records.package_ndjson("demo").expect("demo present");
    let read = parse_package_ndjson(&ndjson).expect("reads back");
    let failed = read.obligations.iter().find(|row| row.is_failed()).expect("a failed row");
    assert_eq!(failed.basis.as_deref(), Some("refuted"));
    assert_eq!(failed.listing_label(), "FAILED");
    let proved = read.obligations.iter().find(|row| row.is_proved()).expect("a proved row");
    assert_eq!(proved.basis, None);
    assert_eq!(proved.listing_label(), "PROVED");
    assert_eq!(ndjson.matches("\"basis\"").count(), 1, "{ndjson}");

    let closed = ndjson.replace("\"basis\":\"refuted\"", "\"basis\":\"unproved_fail_closed\"");
    let read = parse_package_ndjson(&closed).expect("the other basis reads");
    let failed = read.obligations.iter().find(|row| row.is_failed()).unwrap();
    assert_eq!(failed.listing_label(), "FAILED: unproved, no counterexample; failed closed");

    for (text, refusal) in [
        (
            ndjson.replace(",\"basis\":\"refuted\"", "").replace("\"basis\":\"refuted\",", ""),
            "a `failed` row states its `basis`",
        ),
        (
            ndjson.replace("\"basis\":\"refuted\"", "\"basis\":\"guessed\""),
            "unknown failure basis `guessed`",
        ),
        (
            ndjson.replacen(
                "\"status\":\"proved\"",
                "\"basis\":\"refuted\",\"status\":\"proved\"",
                1,
            ),
            "a `proved` row cannot carry a basis",
        ),
    ] {
        let error = parse_package_ndjson(&text).expect_err(refusal);
        assert!(error.contains(refusal), "{refusal}: {error}");
    }
}

/// A Cargo error diagnostic becomes a keyed compile-error line of its
/// package's record and reads back; a warning and rustc's closing count do
/// not; the key holds no line; and the package is could-not-run.
#[test]
fn a_compile_error_is_a_keyed_line_of_its_packages_record() {
    let diagnostic = |level: &str, message: &str, line: u64| {
        serde_json::json!({
            "level": level,
            "message": message,
            "code": { "code": "E0308", "explanation": null },
            "spans": [{ "file_name": "src/lib.rs", "line_start": line, "column_start": 9,
                        "is_primary": true }],
        })
    };
    let error = |line| CompileError::of_cargo_diagnostic("demo", &diagnostic("error", "x", line));
    assert!(CompileError::of_cargo_diagnostic("demo", &diagnostic("warning", "w", 1)).is_none());
    for level in ["failure-note", "help", "note", "errors", "warning: error"] {
        assert!(CompileError::of_cargo_diagnostic("demo", &diagnostic(level, "w", 1)).is_none());
    }
    let ice = CompileError::of_cargo_diagnostic(
        "demo",
        &diagnostic("error: internal compiler error", "boom", 1),
    )
    .expect("an internal compiler error is an error");
    assert_eq!(ice.message, "internal compiler error: boom");
    let closing = serde_json::json!({
        "level": "error", "message": "aborting due to 1 previous error", "code": null, "spans": []
    });
    assert!(CompileError::of_cargo_diagnostic("demo", &closing).is_none());
    let first = error(3).expect("an error");
    let moved = error(30).expect("an error");
    assert_eq!(first.line, Some(3));
    let errors = [first.clone(), moved, first];
    let keyed = key_compile_errors(&errors);
    assert_eq!(keyed.len(), 2, "the repeated error is one row: {keyed:?}");
    assert_eq!(keyed[0].key, compile_error_key(Some("src/lib.rs"), Some("E0308"), "x"));
    assert_eq!(keyed[0].line, Some(3));
    assert_eq!(keyed[1].key, format!("{}~2", keyed[0].key));

    let records = ObligationRecords::of_rows(
        &[],
        &FunctionInventory::default(),
        facts(),
        RunScope { selected: ["demo".to_string()].into_iter().collect(), ..RunScope::default() },
        &RunCoverage { compile_errors: &errors[..1], ..RunCoverage::default() },
    );
    let ndjson = records.package_ndjson("demo").expect("the package's record");
    let line: serde_json::Value = serde_json::from_str(ndjson.lines().nth(1).unwrap()).unwrap();
    assert_eq!(
        line,
        serde_json::json!({ "compile_error": keyed[0].key, "code": "E0308", "message": "x",
                            "file": "src/lib.rs", "line": 3, "col": 9 })
    );
    let read = parse_package_ndjson(&ndjson).expect("the record reads back");
    assert_eq!(read.outcome, "could-not-run");
    assert!(!read.concluded, "no unit published coverage: the record did not conclude");
    assert_eq!(read.compile_errors, keyed[..1]);
}

/// The verifier reports a refusal as an ordinary compiler error. A package
/// that reported one but whose unit published its coverage row concluded:
/// its record carries the error line and its obligations, and is compared
/// (`crate::agent_delta`). Concluding is read from the coverage row, never
/// from whether an error was reported.
#[test]
fn a_package_with_a_verifier_error_and_its_coverage_row_concluded() {
    let rows = [row("demo", "demo::f", 0, VerificationOutcome::Failed)];
    let refusal = CompileError {
        package: "demo".to_string(),
        file: Some("src/lib.rs".to_string()),
        code: None,
        message: "Trust strict verification failed for `demo::f`: 1 obligation(s) were not \
                  fully verified"
            .to_string(),
        line: Some(10),
        col: Some(1),
    };
    let coverage = [trust_types::CoverageTransportSummary {
        crate_name: "demo".to_string(),
        package_name: "demo".to_string(),
        primary_package: true,
        verification_session: "session".to_string(),
        eligible: 1,
        processed: 1,
        function_identities: None,
        noted_stops: Vec::new(),
        degraded_anchors: 0,
        memory: trust_types::MemorySummary::default(),
    }];
    let records = ObligationRecords::of_rows(
        &rows,
        &FunctionInventory::of_rows(&rows),
        facts(),
        RunScope::default(),
        &RunCoverage {
            rows: &coverage,
            missing: BTreeSet::new(),
            publication_stops: &[],
            compile_errors: std::slice::from_ref(&refusal),
        },
    );
    let read =
        parse_package_ndjson(&records.package_ndjson("demo").expect("demo")).expect("reads back");
    assert!(read.concluded);
    assert_eq!(read.compile_errors.len(), 1);
    assert_eq!(read.obligations.len(), 1);
}

/// rustc writes a closure's or coroutine's source position into its type's
/// name; the key cuts it to the file, so an edit above the closure keeps the
/// error's key. Nothing else in a message is touched.
#[test]
fn a_compile_error_key_ignores_the_positions_in_closure_and_coroutine_types() {
    let at = |line: u32| {
        format!(
            "the trait bound `{{closure@src/lib.rs:{line}:13: {line}:15}}: Foo` is not \
             satisfied by `{{async block@src/lib.rs:{line}:5: {}:6}}`",
            line + 2
        )
    };
    assert_eq!(
        without_type_positions(&at(5)),
        "the trait bound `{closure@src/lib.rs}: Foo` is not satisfied by \
         `{async block@src/lib.rs}`"
    );
    let key = |message: &str| compile_error_key(Some("src/lib.rs"), Some("E0277"), message);
    assert_eq!(key(&at(5)), key(&at(41)), "the key moved with the closure");
    assert_ne!(key(&at(5)), key(&at(5).replace("Foo", "Bar")), "another message, another key");
    // A position-free form, a single position, an `@` that is no position.
    for message in [
        "no method named `x` found for closure `{closure@src/main.rs:2:13}`",
        "{coroutine@src/lib.rs:7:1: 9:2}",
        "package `serde@1.0.0` is not a position",
        "mail@host: 12 is not one either",
        "C:\\x@C:\\y.rs:3",
    ] {
        let once = without_type_positions(message);
        assert_eq!(without_type_positions(&once), once, "{message}");
    }
    assert_eq!(
        without_type_positions(
            "no method named `x` found for closure `{closure@src/main.rs:2:13}`"
        ),
        "no method named `x` found for closure `{closure@src/main.rs}`"
    );
    assert_eq!(without_type_positions("{coroutine@src/lib.rs:7:1: 9:2}"), "{coroutine@src/lib.rs}");
    assert_eq!(
        without_type_positions("package `serde@1.0.0` is not a position"),
        "package `serde@1.0.0` is not a position"
    );
    assert_eq!(
        without_type_positions("mail@host: 12 is not one either"),
        "mail@host: 12 is not one either"
    );
}

// --- Clean islands --------------------------------------------------------------

/// One unit's island rows of crate `demo`: `(name, status, stop, basis)`.
fn island_unit(
    phase: trust_types::clean_island_rows::CleanIslandPhase,
    problems: &[&str],
    rows: &[(&str, &str, &str, Option<&str>)],
) -> trust_types::clean_island_rows::CleanIslandRowsTransport {
    let mut rows: Vec<trust_types::clean_island_rows::CleanIslandRow> = rows
        .iter()
        .map(|(name, status, stop, basis)| trust_types::clean_island_rows::CleanIslandRow {
            key: format!("demo::{name}#{:016x}", name.len()),
            kind: "lean:theorem".to_string(),
            status: (*status).to_string(),
            stop: (*stop).to_string(),
            basis: basis.map(str::to_string),
            file: "src/lib.rs".to_string(),
            line: 3,
            col: 1,
            source: None,
        })
        .collect();
    rows.sort();
    let unit = trust_types::clean_island_rows::CleanIslandRowsTransport {
        schema: trust_types::clean_island_rows::CLEAN_ISLAND_ROWS_SCHEMA_V1.to_string(),
        crate_name: "demo".to_string(),
        package_name: "demo".to_string(),
        verification_session: "session".to_string(),
        primary_package: true,
        phase,
        islands: 1,
        complete: problems.is_empty(),
        problems: problems.iter().map(|problem| (*problem).to_string()).collect(),
        rows,
    };
    unit.validate().expect("a unit an honest producer writes");
    unit
}

const P: (&str, &str, Option<&str>) = ("proved", "solved", None);
const F: (&str, &str, Option<&str>) = ("failed", "solver-incomplete", Some("unproved_fail_closed"));
const U: (&str, &str, Option<&str>) = ("unknown", "not-dispatched", None);

fn r<'a>(
    name: &'a str,
    (s, t, b): (&'a str, &'a str, Option<&'a str>),
) -> (&'a str, &'a str, &'a str, Option<&'a str>) {
    (name, s, t, b)
}

#[test]
fn island_rows_are_a_section_that_reads_back_and_moves_no_fact_vector_or_baseline() {
    use trust_types::clean_island_rows::CleanIslandPhase::Verified;
    let rows = [row("demo", "demo::f", 0, VerificationOutcome::Proved)];
    let without = records_of(&rows);
    // The library proves `Lib.a` and `Lib.b`; its own test unit refused `Lib.b`'s
    // proof and has a declaration of its own.
    let lib = island_unit(Verified, &[], &[r("Lib.a", P), r("Lib.b", P)]);
    let test = island_unit(Verified, &[], &[r("Lib.b", F), r("Lib.c", P)]);
    let with = without
        .clone()
        .with_clean_islands(Some(&["demo", "demo"]), [("demo", &lib), ("demo", &test)]);
    let section = &with.clean_islands["demo"].sections["demo"];
    let statuses: Vec<(&str, &str)> = section
        .rows
        .values()
        .map(|decl| (decl.record.key.as_str(), decl.record.status.as_str()))
        .collect();
    assert_eq!(
        statuses,
        [
            ("demo::Lib.a#0000000000000005", "proved"),
            ("demo::Lib.b#0000000000000005", "failed"),
            ("demo::Lib.c#0000000000000005", "proved"),
        ]
    );
    // Disclosure: the facts, the package record and the baseline are the
    // run's without islands; the record's other lines are the same lines.
    assert_eq!(with.units, without.units);
    assert_eq!(with.package_record_json("demo"), without.package_record_json("demo"));
    assert_eq!(
        crate::baseline::Baseline::project(&with),
        crate::baseline::Baseline::project(&without)
    );
    let bytes = with.package_ndjson("demo").unwrap();
    let plain = without.package_ndjson("demo").unwrap();
    let is_island = |line: &&str| {
        line.contains("\"clean_island_units\":")
            || line.contains("\"clean_islands\":")
            || line.contains("\"clean_decl\":")
    };
    let island_lines: Vec<&str> = bytes.lines().filter(is_island).collect();
    assert_eq!(island_lines.len(), 5, "{bytes}");
    let rest: Vec<&str> = bytes.lines().filter(|line| !is_island(line)).collect();
    assert_eq!(rest, plain.lines().collect::<Vec<_>>());
    // After the header and before the first function line: the units line,
    // then the crate's.
    assert_eq!(
        bytes.lines().nth(1).unwrap(),
        "{\"clean_island_units\":2,\"proof_units\":2}",
        "{bytes}"
    );
    assert!(bytes.lines().nth(2).unwrap().contains("\"clean_islands\":\"demo\""), "{bytes}");
    let read = parse_package_ndjson(&bytes).unwrap();
    let plain = parse_package_ndjson(&plain).unwrap();
    assert_eq!(read.clean_islands, with.clean_islands["demo"]);
    assert_eq!(
        (read.vector, read.coverage_complete, read.obligations),
        (plain.vector, plain.coverage_complete, plain.obligations)
    );
}

#[test]
fn a_merge_with_a_unit_that_is_not_a_measurement_proves_nothing() {
    use trust_types::clean_island_rows::CleanIslandPhase::{FrontEndError, Verified};
    let lib = island_unit(Verified, &[], &[r("Lib.a", P), r("Lib.b", P)]);
    let incomplete = island_unit(Verified, &["island 2 was not enumerated"], &[r("Lib.b", U)]);
    let records = records_of(&[])
        .with_clean_islands(Some(&["demo", "demo"]), [("demo", &lib), ("demo", &incomplete)]);
    let section = &records.clean_islands["demo"].sections["demo"];
    assert!(!section.complete);
    assert!(section.rows.values().all(|decl| !decl.record.is_proved()), "{section:?}");
    let stopped = island_unit(FrontEndError, &[], &[r("Lib.a", F)]);
    let records = records_of(&[])
        .with_clean_islands(Some(&["demo", "demo"]), [("demo", &lib), ("demo", &stopped)]);
    let section = &records.clean_islands["demo"].sections["demo"];
    assert_eq!(section.phase, FrontEndError);
    assert!(section.rows.values().all(|decl| !decl.record.is_proved()), "{section:?}");
}

#[test]
fn an_island_line_no_writer_writes_is_refused() {
    use trust_types::clean_island_rows::CleanIslandPhase::Verified;
    let lib = island_unit(Verified, &[], &[r("Lib.a", P), r("Lib.b", F)]);
    let good = records_of(&[row("demo", "demo::f", 0, VerificationOutcome::Proved)])
        .with_clean_islands(Some(&["demo"]), [("demo", &lib)])
        .package_ndjson("demo")
        .unwrap();
    assert!(parse_package_ndjson(&good).is_ok());
    let section = good.lines().find(|line| line.contains("\"clean_islands\":")).unwrap();
    let proved = good
        .lines()
        .find(|line| line.contains("\"status\":\"proved\"") && line.contains("\"clean_decl\":"))
        .unwrap();
    let refuse = |text: String, why: &str| {
        let error = parse_package_ndjson(&text).expect_err(why);
        assert!(error.contains(why), "{why}: {error}");
    };
    // A proved row in a section that is not a measurement.
    refuse(
        good.replace(
            section,
            &section.replace("\"phase\":\"verified\"", "\"phase\":\"front-end-error\""),
        ),
        "is a proved island declaration in a section that is front-end-error",
    );
    refuse(
        good.replace(
            section,
            &section
                .replace("\"complete\":true", "\"complete\":false")
                .replace("\"problems\":[]", "\"problems\":[\"x\"]"),
        ),
        "is a proved island declaration in a section that is verified and incomplete",
    );
    refuse(
        good.replace(section, &section.replace("\"complete\":true", "\"complete\":false")),
        "problems do not match `complete`",
    );
    // A verdict no island row states.
    for (from, to) in [
        ("\"stop\":\"solved\"", "\"stop\":\"timeout\""),
        ("\"status\":\"proved\"", "\"status\":\"runtime_checked\""),
    ] {
        refuse(good.replace(proved, &proved.replace(from, to)), "which no island row can state");
    }
    refuse(
        good.replace(proved, &proved.replace("\"status\":\"proved\"", "\"status\":\"failed\"")),
        "which no island row can state",
    );
    // A row before its crate's line, of another crate, or out of order.
    refuse(good.replace(&format!("{section}\n"), ""), "before any island-section line");
    refuse(
        good.replace(proved, &proved.replace("demo::Lib.a", "other::Lib.a")),
        "names no declaration of crate `demo`",
    );
    let rows: Vec<&str> = good.lines().filter(|line| line.contains("\"clean_decl\":")).collect();
    refuse(
        good.replace(&format!("{}\n{}", rows[0], rows[1]), &format!("{}\n{}", rows[1], rows[0])),
        "out of key order",
    );
    // After a function line.
    let is_island =
        |line: &&str| line.contains("\"clean_islands\":") || line.contains("\"clean_decl\":");
    let moved: Vec<&str> = good
        .lines()
        .filter(|line| !is_island(line))
        .chain(good.lines().filter(is_island))
        .collect();
    refuse(moved.join("\n") + "\n", "is an island line after a function line");
}

#[test]
fn a_package_a_unit_of_which_published_no_island_row_proves_none_and_says_so() {
    use trust_types::clean_island_rows::CleanIslandPhase::Verified;
    // The library and a binary of `demo` are proof units; the binary stopped
    // on a Rust parse error before its islands were read, so it published
    // nothing. The library's rows are no measurement of the package: a key
    // the binary shares is not proved by the library alone.
    let lib = island_unit(Verified, &[], &[r("Lib.a", P), r("Lib.b", F)]);
    let records = records_of(&[row("demo", "demo::f", 0, VerificationOutcome::Proved)])
        .with_clean_islands(Some(&["demo", "demo"]), [("demo", &lib)]);
    let islands = &records.clean_islands["demo"];
    assert_eq!(
        islands.units,
        Some(super::clean_islands::CleanIslandUnits { published: 1, proof_units: Some(2) })
    );
    assert!(!islands.units_whole() && !islands.measured());
    assert_eq!(
        islands.units_problem().as_deref(),
        Some("1 of 2 compilation unit(s) of the package published no island rows")
    );
    let statuses: Vec<&str> =
        islands.sections["demo"].rows.values().map(|decl| decl.record.status.as_str()).collect();
    assert_eq!(statuses, ["unknown", "failed"]);
    let bytes = records.package_ndjson("demo").unwrap();
    assert_eq!(parse_package_ndjson(&bytes).unwrap().clean_islands, *islands);
    // Every unit published: the same rows are a measurement, and a verified,
    // complete unit with no island adds its count and no section.
    let mut none = island_unit(Verified, &[], &[]);
    none.islands = 0;
    let records = records_of(&[])
        .with_clean_islands(Some(&["demo", "demo"]), [("demo", &lib), ("demo", &none)]);
    let islands = &records.clean_islands["demo"];
    assert!(islands.measured(), "{islands:?}");
    assert_eq!(islands.sections.len(), 1);
    assert!(islands.sections["demo"].rows.values().any(|decl| decl.record.is_proved()));
    // A run that declared no proof unit cannot say its units are whole.
    let records = records_of(&[]).with_clean_islands(None, [("demo", &lib)]);
    assert!(!records.clean_islands["demo"].units_whole());
}

#[test]
fn an_island_units_line_no_writer_writes_is_refused() {
    use trust_types::clean_island_rows::CleanIslandPhase::Verified;
    let lib = island_unit(Verified, &[], &[r("Lib.a", P)]);
    let good = records_of(&[row("demo", "demo::f", 0, VerificationOutcome::Proved)])
        .with_clean_islands(Some(&["demo"]), [("demo", &lib)])
        .package_ndjson("demo")
        .unwrap();
    assert!(parse_package_ndjson(&good).is_ok());
    let units = "{\"clean_island_units\":1,\"proof_units\":1}";
    assert!(good.contains(units), "{good}");
    let refuse = |text: String, why: &str| {
        let error = parse_package_ndjson(&text).expect_err(why);
        assert!(error.contains(why), "{why}: {error}");
    };
    // No units line: a section is not read without it.
    refuse(good.replace(&format!("{units}\n"), ""), "before the island-units line");
    // Twice, or after a section line.
    refuse(good.replace(units, &format!("{units}\n{units}")), "is not the first island line");
    // No unit, or more published than the package has.
    refuse(
        good.replace(units, "{\"clean_island_units\":0,\"proof_units\":1}"),
        "counting 0 published unit(s)",
    );
    refuse(
        good.replace(units, "{\"clean_island_units\":2,\"proof_units\":1}"),
        "counting 2 published unit(s)",
    );
    // A proved row in a package whose units are not whole.
    refuse(
        good.replace(units, "{\"clean_island_units\":1,\"proof_units\":2}"),
        "in a package whose units did not all publish island rows",
    );
    refuse(
        good.replace(units, "{\"clean_island_units\":1,\"proof_units\":null}"),
        "in a package whose units did not all publish island rows",
    );
}
