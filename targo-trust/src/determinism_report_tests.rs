// Tests for crate::determinism_report.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use super::*;

/// The stable key a test row carries: `<function>#<local id of (kind, nth)>`.
fn test_key(function: &str, kind: &str, nth: u32) -> String {
    trust_types::obligation_identity::obligation_key(
        function,
        &trust_types::obligation_identity::local_id(kind, "none:test", nth),
    )
}

/// The structured evidence of a keyed test row: its identity and nothing else.
fn identity_evidence(
    function: &str,
    kind: &str,
    nth: u32,
) -> crate::types::StructuredTransportEvidence {
    crate::types::StructuredTransportEvidence {
        assumes: Vec::new(),
        obligation_id: None,
        claim_digest_sha256: None,
        original_vc_snapshot: None,
        typed_kind: None,
        design_mandate: false,
        runtime_checks: None,
        native_trust_ir: None,
        proof_evidence: None,
        monitor: None,
        identity: Some(trust_types::obligation_identity::ObligationIdentity {
            key: test_key(function, kind, nth),
            package: "m".to_string(),
            function_source_sha256: None,
            expanded_function_identity: None,
        }),
        grade: None,
    }
}

/// A published row with no stable key, as an older compiler (or a transport
/// defect row targo synthesized) leaves it.
fn unkeyed_row(
    function: &str,
    kind: &str,
    outcome: VerificationOutcome,
    reason: Option<&str>,
) -> VerificationResult {
    VerificationResult {
        function: function.to_string(),
        kind: kind.to_string(),
        message: format!("{kind} in {function}"),
        outcome,
        backend: "ay-in-process".to_string(),
        time_ms: Some(1),
        location: None,
        counterexample: None,
        reason: reason.map(str::to_string),
        raw_line: String::new(),
    }
}

/// The `nth` row of `kind` in `function`, carrying its stable key.
fn keyed_row(
    function: &str,
    kind: &str,
    nth: u32,
    outcome: VerificationOutcome,
    reason: Option<&str>,
) -> VerificationResult {
    let mut row = unkeyed_row(function, kind, outcome, reason);
    crate::types::replace_structured_transport_evidence(
        &mut row,
        &identity_evidence(function, kind, nth),
    )
    .expect("evidence serializes");
    row
}

fn row(
    function: &str,
    kind: &str,
    outcome: VerificationOutcome,
    reason: Option<&str>,
) -> VerificationResult {
    keyed_row(function, kind, 0, outcome, reason)
}

#[test]
fn the_default_configuration_is_the_builtin_profile() {
    let config = TrustConfig::default();
    let profile = budget_profile(&config);
    assert_eq!(profile.name, "builtin");
    assert_eq!(profile, BudgetProfile::builtin());
    // The built-in backstop reproduces the clocks targo always passed.
    assert_eq!(
        (profile.backstop.vc_clock_ms(), profile.backstop.function_clock_ms()),
        (5_000, 120_000)
    );
    assert_eq!(profile.worker_threads, 0);
}

/// The id is the effort scale and the backstop: either moves it, and the
/// worker-thread count — recorded, not a bound — does not.
#[test]
fn the_workspace_budgets_reach_the_profile_and_worker_threads_stay_out_of_the_id() {
    let mut config = TrustConfig::default();
    let base = budget_profile(&config);
    let serial = budget_profile(&TrustConfig { worker_threads: 1, ..config.clone() });
    assert_eq!(serial.name, "builtin");
    assert_eq!(serial.id(), base.id());
    assert!(
        serial.header_line().ends_with("worker_threads=1 frontend_threads=1 (pinned)"),
        "{}",
        serial.header_line()
    );

    config.backstop = trust_types::determinism::Backstop { per_mille: 2000 };
    let slower = budget_profile(&config);
    assert_eq!(slower.name, "configured");
    assert_ne!(slower.id(), base.id());

    config.backstop = trust_types::determinism::Backstop::BUILTIN;
    config.effort = trust_types::determinism::EffortScale::BUILTIN;
    assert_eq!(budget_profile(&config).id(), base.id(), "restating the builtin keeps the id");
}

#[test]
fn each_published_row_names_its_stop() {
    use VerificationOutcome::*;
    let stamped = StopCause::Effort.stamp("in-process ay returned unknown: resourceout");
    let cases = [
        (row("m::f", "overflow:add", Proved, None), StopCause::Solved),
        (row("m::f", "overflow:add", Failed, Some("anything")), StopCause::Solved),
        (row("m::f", "overflow:add", Unknown, Some(&stamped)), StopCause::Effort),
        (row("m::f", "overflow:add", RuntimeChecked, Some(&stamped)), StopCause::Effort),
        (row("m::f", "overflow:add", Timeout, Some("solver timed out")), StopCause::WallBackstop),
        (
            row("m::f", "overflow:add", Unknown, Some("solver returned unknown")),
            StopCause::Unclassified,
        ),
        (row("m::f", "overflow:add", Unknown, None), StopCause::Unclassified),
        (row("m::f", "assumption:entry", Unknown, None), StopCause::NotDispatched),
    ];
    for (row, expected) in cases {
        assert_eq!(row_stop_cause(&row), expected, "{row:?}");
    }
    // Review finding (2026-09-29): a timeout row stays a clock whatever its
    // reason states, and a wrapper cannot launder a clock under it.
    let laundered = StopCause::Solved.stamp(&StopCause::WallBackstop.stamp("deadline"));
    assert_eq!(
        row_stop_cause(&row("m::f", "overflow:add", Timeout, Some(&stamped))),
        StopCause::WallBackstop
    );
    assert_eq!(
        row_stop_cause(&row("m::f", "overflow:add", Unknown, Some(&laundered))),
        StopCause::WallBackstop
    );
    let mut admission = row("m::f", "overflow:add", Unknown, None);
    admission.message = format!(
        "{}trustd refused the reservation",
        trust_types::VcKind::memory_admission_message_prefix()
    );
    assert_eq!(row_stop_cause(&admission), StopCause::AdmissionRefused);
}

#[test]
fn the_vector_depends_on_verdicts_not_on_function_order() {
    use VerificationOutcome::*;
    let effort = StopCause::Effort.stamp("resourceout");
    let f0 = row("m::f", "overflow:add", Proved, None);
    let f1 = keyed_row("m::f", "overflow:add", 1, Unknown, Some(&effort));
    let g0 = row("m::g", "bounds", Failed, None);
    let forward = UnitDeterminism::of_rows(&[f0.clone(), f1.clone(), g0.clone()], &[]);
    // Another function finishing first reorders the report, never the vector.
    let reordered = UnitDeterminism::of_rows(&[g0.clone(), f0.clone(), f1.clone()], &[]);
    assert_eq!(forward.vector.digest(), reordered.vector.digest());
    assert_eq!(forward.outcome, UnitOutcome::Measured);
    assert_eq!(forward.tally.render(), "effort=1 solved=2");
    let keys: Vec<&str> =
        forward.vector.entries().iter().map(|entry| entry.obligation.as_str()).collect();
    let mut expected = vec![
        test_key("m::f", "overflow:add", 0),
        test_key("m::f", "overflow:add", 1),
        test_key("m::g", "bounds", 0),
    ];
    expected.sort();
    assert_eq!(keys, expected, "the vector keys on the stable `<def_path>#<id>` key");

    // The same obligations with one verdict moved by a clock: a different
    // vector, and a unit that is no longer a measurement.
    let clocked = keyed_row("m::f", "overflow:add", 1, Timeout, Some("solver timed out"));
    let loaded = UnitDeterminism::of_rows(&[f0, clocked, g0], &[]);
    assert_ne!(loaded.vector.digest(), forward.vector.digest());
    assert_eq!(loaded.outcome, UnitOutcome::NotReproducible);
    assert!(loaded.stop_cause_line().contains("NOT REPRODUCIBLE"));
}

#[test]
fn an_admission_refusal_makes_the_unit_could_not_run() {
    use VerificationOutcome::*;
    let refused = StopCause::AdmissionRefused
        .stamp("memory admission failed before solver spawn: trustd unreachable");
    let unit = UnitDeterminism::of_rows(
        &[
            row("m::f", "overflow:add", Proved, None),
            row("m::f", "overflow:add", Unknown, Some(&refused)),
        ],
        &[],
    );
    assert_eq!(unit.outcome, UnitOutcome::CouldNotRun);
    assert_eq!(unit.admission_refusals(), 1);
    assert!(unit.stop_cause_line().contains("COULD NOT RUN"));
}

#[test]
fn a_volatile_obligation_key_keeps_the_unit_from_being_measured() {
    let volatile = row(
        "<home>/checkout/src/lib.rs",
        "overflow:add",
        VerificationOutcome::Proved,
        None,
    );
    let unit = UnitDeterminism::of_rows(&[volatile], &[]);
    assert_eq!(unit.volatile_keys.len(), 1);
    assert_eq!(unit.outcome, UnitOutcome::NotReproducible);
    assert!(unit.stop_cause_line().contains("volatile identity"));
}

#[test]
fn the_summary_suffix_names_outcome_profile_and_vector() {
    let profile = budget_profile(&TrustConfig::default());
    let unit =
        UnitDeterminism::of_rows(&[row("m::f", "bounds", VerificationOutcome::Proved, None)], &[]);
    let suffix = unit.summary_suffix(&profile);
    assert_eq!(
        suffix,
        format!(
            "; measured; profile {}; vector {}",
            short_id(&profile.id()),
            short_id(&unit.vector.digest())
        )
    );
    let block = unit.gate_block(&profile);
    assert_eq!(block.outcome, UnitOutcome::Measured);
    assert_eq!(block.budget_profile_id, profile.id());
    assert_eq!(block.vector_digest, unit.vector.digest());
    assert_eq!(block.vector.len(), 1);
}

/// Review finding (2026-09-29): a backstop that fired in work the compiler
/// consumed without publishing a row (the R1 harvest, a refutation attempt, S1
/// revalidation) reaches the unit through the backstop ledger — the rows alone
/// would read `measured`.
#[test]
fn a_backstop_outside_the_rows_makes_the_unit_not_reproducible() {
    use VerificationOutcome::*;
    let rows = [row("m::f", "overflow:add", Proved, None), row("m::g", "bounds", Failed, None)];
    let clean = UnitDeterminism::of_rows(&rows, &[]);
    assert_eq!(clean.outcome, UnitOutcome::Measured);
    let noted = [NotedStop {
        lane: "per-function budget clock".to_string(),
        cause: StopCause::WallBackstop,
        item: None,
        count: 1,
    }];
    let clocked = UnitDeterminism::of_rows(&rows, &noted);
    assert_eq!(clocked.outcome, UnitOutcome::NotReproducible);
    assert_eq!(
        clocked.vector.digest(),
        clean.vector.digest(),
        "the ledger is not part of the vector: the verdicts agree, the measurement does not"
    );
    let line = clocked.stop_cause_line();
    assert!(line.contains("backstops fired: per-function budget clock wall-backstop=1"), "{line}");
    assert!(line.contains("NOT REPRODUCIBLE"), "{line}");
    let block = clocked.gate_block(&budget_profile(&TrustConfig::default()));
    assert_eq!(block.noted_stops, noted);
    assert_eq!(block.outcome, UnitOutcome::NotReproducible);

    let refused = [NotedStop {
        lane: "subprocess ay".to_string(),
        cause: StopCause::AdmissionRefused,
        item: None,
        count: 3,
    }];
    let could_not_run = UnitDeterminism::of_rows(&rows, &refused);
    assert_eq!(could_not_run.outcome, UnitOutcome::CouldNotRun);
    assert_eq!(could_not_run.admission_refusals(), 0, "no ROW was refused");
    assert_eq!(could_not_run.noted_admission_refusals(), 3);
}

#[test]
fn the_ledgers_of_every_unit_merge_by_lane_and_cause() {
    let coverage = |stops: Vec<NotedStop>| trust_types::CoverageTransportSummary {
        crate_name: "c".to_string(),
        package_name: "p".to_string(),
        primary_package: true,
        verification_session: "s".to_string(),
        eligible: 1,
        processed: 1,
        function_identities: None,
        noted_stops: stops,
        degraded_anchors: 0,
        memory: trust_types::MemorySummary::default(),
    };
    let stop =
        |lane: &str, cause, count| NotedStop { lane: lane.to_string(), cause, item: None, count };
    let merged = merged_noted_stops(&[
        coverage(vec![stop("router", StopCause::WallBackstop, 2)]),
        coverage(vec![]),
        coverage(vec![
            stop("router", StopCause::WallBackstop, 1),
            stop("in-process ay", StopCause::Unclassified, 4),
        ]),
    ]);
    assert_eq!(
        merged,
        vec![
            stop("in-process ay", StopCause::Unclassified, 4),
            stop("router", StopCause::WallBackstop, 3),
        ]
    );
}

/// Review finding (2026-09-29, blocker): the type-lowering budget poll trips on
/// the step COUNT or the wall CLOCK, and the marker it leaves became an
/// `UnsupportedMir` row read as the deterministic `unsupported`. The marker's
/// detail now carries the trip's stamp (trust-mir-extract `ty_convert`), and a
/// clock trip must survive into the row's stop cause.
#[test]
fn an_unsupported_marker_left_by_a_clock_trip_is_not_reproducible() {
    let marker = |detail: String, reason: Option<&str>| {
        let kind = trust_types::VcKind::UnsupportedMir { kind: "TyKind".to_string(), detail };
        let tag = kind.transport_tag();
        let mut unsupported = unkeyed_row("m::f", &tag, VerificationOutcome::Unknown, reason);
        let evidence = crate::types::StructuredTransportEvidence {
            original_vc_snapshot: None,
            typed_kind: Some(Box::new(kind)),
            ..identity_evidence("m::f", &tag, 0)
        };
        crate::types::replace_structured_transport_evidence(&mut unsupported, &evidence)
            .expect("evidence serializes");
        unsupported
    };
    let budget = "local _3: type lowering exceeded the per-function verification budget";
    let clock = marker(StopCause::WallBackstop.stamp(budget), None);
    assert_eq!(row_stop_cause(&clock), StopCause::WallBackstop);
    let steps = marker(StopCause::Steps.stamp(budget), None);
    assert_eq!(row_stop_cause(&steps), StopCause::Steps);
    let plain = marker("local _3: dyn Trait".to_string(), None);
    assert_eq!(row_stop_cause(&plain), StopCause::Unsupported);
    // The router's own `unsupported` stamp on the reason cannot launder the
    // clock recorded in the marker.
    let wrapped = StopCause::Unsupported.stamp("unsupported MIR TyKind preserved in TrustIr");
    let clock_wrapped = marker(StopCause::WallBackstop.stamp(budget), Some(&wrapped));
    assert_eq!(row_stop_cause(&clock_wrapped), StopCause::WallBackstop);
    assert_eq!(
        UnitDeterminism::of_rows(&[clock_wrapped], &[]).outcome,
        UnitOutcome::NotReproducible
    );
    assert_eq!(UnitDeterminism::of_rows(&[steps], &[]).outcome, UnitOutcome::Measured);
}

/// Plan-critique P1 ledger items (2026-09-30): the named stops are counted by
/// name, beside the stop causes, from the rows and from the ledger; a
/// deterministic named stop in the ledger is counted, never graded.
#[test]
fn named_stops_are_counted_by_name() {
    use VerificationOutcome::*;
    let cancelled = StopCause::WallBackstop.stamp_item(
        StopItem::StrictCheckCancelled,
        "UNSAT but strict proof verdict rejected: proof validation cancelled by the caller",
    );
    let trust_rule = StopCause::Unclassified
        .stamp_item(StopItem::UnverifiedTrustRule, "step t5 uses unverified trust rule");
    let invalid_model = StopCause::SolverIncomplete
        .stamp_item(StopItem::ModelValidationViolated, "model validation violated: Assertion: x");
    let unit = UnitDeterminism::of_rows(
        &[
            row("m::f", "overflow:add", Unknown, Some(&cancelled)),
            row("m::f", "overflow:add", Unknown, Some(&trust_rule)),
            row("m::g", "bounds", Unknown, Some(&trust_rule)),
            row("m::h", "bounds", Unknown, Some(&invalid_model)),
        ],
        &[],
    );
    assert_eq!(unit.items.count(StopItem::UnverifiedTrustRule), 2);
    assert_eq!(unit.items.count(StopItem::StrictCheckCancelled), 1);
    assert_eq!(unit.tally.render(), "solver-incomplete=1 unclassified=2 wall-backstop=1");
    let line = unit.stop_cause_line();
    assert!(
        line.contains(
            "; named: model-validation-violated=1 strict-check-cancelled=1 unverified-trust-rule=2"
        ),
        "{line}"
    );
    let block = unit.gate_block(&budget_profile(&TrustConfig::default()));
    assert_eq!(block.stop_items, unit.items);
    let json = serde_json::to_string(&block).unwrap();
    assert!(json.contains(r#""stop_items":{"model-validation-violated":1"#), "{json}");

    // Only the model-validation row: deterministic, so the unit is measured,
    // and a deterministic named stop in the ledger does not change that.
    let noted = [NotedStop {
        lane: "in-process ay".to_string(),
        cause: StopCause::SolverIncomplete,
        item: Some(StopItem::ModelValidationViolated),
        count: 7,
    }];
    let measured =
        UnitDeterminism::of_rows(&[row("m::h", "bounds", Unknown, Some(&invalid_model))], &noted);
    assert_eq!(measured.outcome, UnitOutcome::Measured);
    let line = measured.stop_cause_line();
    assert!(
        line.contains(
            "counted and named stops the lanes saw: in-process ay \
             solver-incomplete[model-validation-violated]=7"
        ),
        "{line}"
    );
    assert!(!line.contains("backstops fired"), "{line}");

    // Review 2026-09-30: the solver count is counted in the ledger wherever
    // the stopped work went (a bridged solve whose row another lane produced),
    // by every lane that saw it. It shows beside the named stops, never as a
    // backstop, and keeps the unit measured.
    let counted = [
        NotedStop {
            lane: "in-process ay".to_string(),
            cause: StopCause::Effort,
            item: None,
            count: 3,
        },
        NotedStop {
            lane: "subprocess ay".to_string(),
            cause: StopCause::Effort,
            item: None,
            count: 2,
        },
    ];
    let capped =
        UnitDeterminism::of_rows(&[row("m::h", "bounds", Unknown, Some(&invalid_model))], &counted);
    assert_eq!(capped.outcome, UnitOutcome::Measured);
    let line = capped.stop_cause_line();
    assert!(
        line.contains(
            "counted and named stops the lanes saw: in-process ay effort=3, subprocess ay \
             effort=2"
        ),
        "{line}"
    );
    assert!(!line.contains("backstops fired"), "{line}");

    let coverage = |stops: Vec<NotedStop>| trust_types::CoverageTransportSummary {
        crate_name: "c".to_string(),
        package_name: "p".to_string(),
        primary_package: true,
        verification_session: "s".to_string(),
        eligible: 1,
        processed: 1,
        function_identities: None,
        noted_stops: stops,
        degraded_anchors: 0,
        memory: trust_types::MemorySummary::default(),
    };
    let merged = merged_noted_stops(&[coverage(noted.to_vec()), coverage(noted.to_vec())]);
    assert_eq!(merged.len(), 1);
    assert_eq!(merged[0].count, 14);
    assert_eq!(merged[0].item, Some(StopItem::ModelValidationViolated));
}

/// T9: a row without a stable key is a producer defect. The unit is
/// could-not-run, the function is named, and no ordinal fallback key exists —
/// not even the compiler's private `obligation_id`, which is a binding token.
#[test]
fn a_row_without_a_stable_key_makes_the_unit_could_not_run_naming_its_function() {
    use VerificationOutcome::*;
    let mut ordinal_only = unkeyed_row("m::g", "bounds", Proved, None);
    let evidence = crate::types::StructuredTransportEvidence {
        obligation_id: Some("vc:m__g:bounds_check:0".to_string()),
        identity: None,
        ..identity_evidence("m::g", "bounds", 0)
    };
    crate::types::replace_structured_transport_evidence(&mut ordinal_only, &evidence)
        .expect("evidence serializes");
    let unit = UnitDeterminism::of_rows(
        &[
            row("m::f", "overflow:add", Proved, None),
            ordinal_only,
            unkeyed_row("m::h", "divzero", Proved, None),
        ],
        &[],
    );
    assert_eq!(unit.outcome, UnitOutcome::CouldNotRun);
    assert_eq!(unit.unkeyed_functions, ["m::g", "m::h"]);
    assert_eq!(unit.vector.entries().len(), 1, "only the keyed row is in the vector");
    assert!(
        unit.vector.entries().iter().all(|entry| !entry.obligation.starts_with("vc:")),
        "the ordinal obligation_id is never a vector key"
    );
    let line = unit.could_not_run_line().expect("a could-not-run line");
    assert!(line.contains("2 function(s) published obligations with no stable key"), "{line}");
    assert!(line.contains("m::g, m::h"), "{line}");
    assert!(!line.contains("refused solver admission"), "{line}");
    let block = unit.gate_block(&budget_profile(&TrustConfig::default()));
    assert_eq!(block.unkeyed_functions, ["m::g", "m::h"]);
    assert_eq!(block.outcome, UnitOutcome::CouldNotRun);
}

/// The admission-refusal line is the one consumers already read.
#[test]
fn the_admission_could_not_run_line_is_unchanged() {
    use VerificationOutcome::*;
    let refused = StopCause::AdmissionRefused.stamp("memory admission failed before solver spawn");
    let unit =
        UnitDeterminism::of_rows(&[row("m::f", "overflow:add", Unknown, Some(&refused))], &[]);
    assert_eq!(
        unit.could_not_run_line().as_deref(),
        Some(
            "COULD NOT RUN: verification did not run to a measurement: 1 obligation(s) were \
             refused solver admission (trustd / the memory jobserver; 0 refused solver attempt(s) \
             in all, counting work that published no row), so this run has no counts"
        )
    );
    let measured = UnitDeterminism::of_rows(&[row("m::f", "overflow:add", Proved, None)], &[]);
    assert_eq!(measured.could_not_run_line(), None);
}

/// A keyless row targo synthesized for a transport defect is named as that
/// defect, with its reason: no function "published obligations with no stable
/// key". The rows here are the real ones — `parse_compiler_stderr` over an
/// envelope whose counters disagree with its rows, a crate summary that
/// disagrees with them, and a line that does not parse. The unit is
/// could-not-run all the same, the phrase consumers key on ("verification did
/// not run") stays, the gate's JSON block is unchanged, and a compiler row
/// without a key keeps the sentence it had.
#[test]
fn a_synthesized_transport_defect_is_named_with_its_reason_in_the_could_not_run_line() {
    use VerificationOutcome::*;
    let function = serde_json::json!({
        "type": "function_result",
        "function": "demo::midpoint",
        "crate_name": "demo",
        "stable_ids": ["388bd8e24055a2b0"],
        "results": [{
            "kind": "divzero",
            "description": "division by zero",
            "outcome": "unknown",
            "solver": "ay-smtlib",
            "time_ms": 0
        }],
        "proved": 0,
        "failed": 0,
        "unknown": 2,
        "runtime_checked": 0,
        "total": 2
    });
    let crate_summary = serde_json::json!({
        "type": "crate_summary",
        "crate_name": "demo",
        "functions_analyzed": 1,
        "functions_verified": 0,
        "total_proved": 0,
        "total_failed": 0,
        "total_unknown": 2,
        "total_runtime_checked": 0,
        "total_obligations": 2
    });
    let prefix = trust_types::TRANSPORT_PREFIX;
    let stderr = format!("{prefix}{function}\n{prefix}{{not json\n{prefix}{crate_summary}\n");
    let rows = crate::pipeline::parse_compiler_stderr(std::io::Cursor::new(stderr), false)
        .verification_results;
    assert_eq!(
        rows.iter().map(|row| row.kind.as_str()).collect::<Vec<_>>(),
        [
            "divzero",
            "transport:summary-accounting",
            "transport:malformed",
            "transport:crate-summary-accounting"
        ],
        "one keyed compiler row and three rows targo synthesized"
    );

    let unit = UnitDeterminism::of_rows(&rows, &[]);
    assert_eq!(unit.outcome, UnitOutcome::CouldNotRun, "a keyless row is a keyless row");
    assert_eq!(unit.unkeyed_functions, ["<crate:demo>", "<transport>", "demo::midpoint"]);
    let line = unit.could_not_run_line().expect("a could-not-run line");
    assert!(
        line.starts_with(
            "COULD NOT RUN: verification did not run to a measurement: targo-trust found 3 \
             transport defect(s) and reports each as a row of its own, which has no stable key, \
             so the unit's verdicts cannot be compared: `transport:summary-accounting`: function \
             transport summary for `demo::midpoint` does not match result rows: total rows=1 \
             summary=2, unknown rows=1 summary=2 (filed under demo::midpoint); \
             `transport:malformed`: "
        ),
        "{line}"
    );
    assert!(
        line.ends_with(
            "; `transport:crate-summary-accounting`: crate transport summary for `demo` does not \
             match function result rows: total rows=1 summary=2, unknown rows=1 summary=2 (filed \
             under <crate:demo>), so this run has no counts"
        ),
        "{line}"
    );
    assert!(line.contains(" (filed under <transport>); "), "{line}");
    assert!(!line.contains("published obligations with no stable key"), "{line}");
    let block = unit.gate_block(&budget_profile(&TrustConfig::default()));
    assert_eq!(block.unkeyed_functions, ["<crate:demo>", "<transport>", "demo::midpoint"]);
    assert_eq!(block.outcome, UnitOutcome::CouldNotRun);

    // Beside a compiler row with no key: both causes, each in its own words.
    let unit = UnitDeterminism::of_rows(
        &[unkeyed_row("m::h", "divzero", Proved, None), rows[1].clone()],
        &[],
    );
    assert_eq!(unit.unkeyed_functions, ["demo::midpoint", "m::h"]);
    let line = unit.could_not_run_line().expect("a could-not-run line");
    assert!(line.contains("targo-trust found 1 transport defect(s)"), "{line}");
    assert!(
        line.contains(
            "; 1 function(s) published obligations with no stable key, so no verdict of theirs \
             can be compared: m::h, so this run has no counts"
        ),
        "{line}"
    );

    // Lookalikes are not targo's rows, and keep the sentence they had: the
    // kind from another backend, targo's backend under another kind, and a
    // row spelling both that arrived in a compiler envelope (it carries
    // structured evidence; here, as an older compiler leaves it, no key).
    let mut enveloped = VerificationResult {
        backend: "targo-trust".to_string(),
        ..unkeyed_row("m::i", "transport:summary-accounting", Unknown, None)
    };
    let evidence = crate::types::StructuredTransportEvidence {
        identity: None,
        ..identity_evidence("m::i", "x", 0)
    };
    crate::types::replace_structured_transport_evidence(&mut enveloped, &evidence)
        .expect("evidence serializes");
    let unit = UnitDeterminism::of_rows(
        &[
            unkeyed_row("m::g", "transport:summary-accounting", Unknown, Some("reason")),
            VerificationResult {
                backend: "targo-trust".to_string(),
                ..unkeyed_row("m::h", "assertion", Unknown, None)
            },
            enveloped,
        ],
        &[],
    );
    let line = unit.could_not_run_line().expect("a could-not-run line");
    assert!(
        line.contains(
            "3 function(s) published obligations with no stable key, so no verdict of theirs can \
             be compared: m::g, m::h, m::i"
        ),
        "{line}"
    );
    assert!(!line.contains("transport defect"), "{line}");
}
