// REGRESSION PIN, from a reviewer's MEASUREMENT.
//
// `trust_report::build_json_report` is the crate's canonical builder and runs
// `RuntimeCheckPolicy::Auto` with `overflow_checks = true`. Auto's ONLY
// downgrade condition is `VcKind::has_runtime_fallback_in`, so anything that
// predicate learns to answer changes what this function prints — for every
// caller, with no flag involved.
//
// Commit e4ae63e373 widened that predicate to answer the hardened
// `mir_assert::*` panic subfamily `true`, on the correct measured ground that
// the `unix_hardened` profile does not touch codegen. Its commit message as
// first written claimed "The only observable change is through the EXPLICIT
// `--test-target-panics=runtime-checked` flag" — that sentence was false and has
// since been struck from the message. MEASURED here, A/B, at d29192bd4f vs
// e4ae63e373, with no flag anywhere in the call:
//
//   mir_assert::BoundsCheck + Timeout   BEFORE  Timeout { timeout_ms: 1 }
//                                       AFTER   Unknown { reason: "deserialized
//                                               runtime_checked outcome has no live
//                                               authenticated compiler/monitor
//                                               capability; …" }
//   mir_assert::BoundsCheck + Unknown   BEFORE  Unknown { reason: "probe" }
//                                       AFTER   Unknown { reason: "deserialized …" }
//
// The mechanism: Auto relabelled the row `RuntimeChecked`, and
// `sanitize_deserialized` (the report's fail-closed publication gate) then
// scrubbed that label back to `Unknown` — losing `timeout_ms`, replacing the
// solver's own reason with a monitor-authority message that is FALSE for a row
// built in-process, and moving the crate summary's `total_timeout` /
// `total_unknown` counts, which it recomputes from the scrubbed outcomes.
//
// The authority was reverted for the hardened family and the measured fact
// given its own name (`VcKind::site_retains_language_check_in`). This test
// holds the report end of that: a hardened boundary's report row is whatever
// the solver said, byte for byte.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    Formula, HardenedVcCategory, ObligationOutcome, SourceSpan, Symbol, VcKind,
    VerificationCondition, VerificationResult,
};

fn vc(kind: VcKind) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: Symbol::from("probe::f"),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    }
}

fn boundary(category: HardenedVcCategory, callee: &str) -> VcKind {
    VcKind::HardenedBoundary {
        category,
        callee: callee.to_string(),
        detail: "MIR assert can panic".to_string(),
    }
}

/// Every `callee` the hardened lane can mint, across both halves of the family.
const CALLEES: [&str; 11] = [
    // Raised over a rustc-inserted `Terminator::Assert`. rustc's check IS still
    // in the program — and it is the panic the boundary objects to.
    "mir_assert::BoundsCheck",
    "mir_assert::DivisionByZero",
    "mir_assert::RemainderByZero",
    "mir_assert::Overflow(Add)",
    "mir_assert::Overflow(Mul)",
    "mir_assert::Overflow(Shl)",
    "mir_assert::OverflowNeg",
    // Raised over a CALL. rustc inserts nothing at the site at all.
    "std::option::Option::<T>::unwrap",
    "std::result::Result::<T, E>::expect",
    "std::fs::rename",
    // Not anchored: a real path that merely embeds the marker.
    "wrapper::mir_assert::Overflow(Add)",
];

#[test]
fn a_timed_out_hardened_boundary_keeps_its_timeout_and_its_timeout_ms() {
    for callee in CALLEES {
        for category in [HardenedVcCategory::PanicBoundary, HardenedVcCategory::UnsafeOperation] {
            let result =
                VerificationResult::Timeout { solver: Symbol::from("ay"), timeout_ms: 4321 };
            let report = trust_report::build_json_report(
                "probe",
                &[(vc(boundary(category, callee)), result)],
            );
            let outcome = &report.functions[0].obligations[0].outcome;
            match outcome {
                ObligationOutcome::Timeout { timeout_ms } => assert_eq!(
                    *timeout_ms, 4321,
                    "{category:?} over `{callee}` must keep its exact timeout_ms"
                ),
                other => panic!(
                    "{category:?} over `{callee}` must report Timeout, not {other:?} — a hardened \
                     boundary is not discharged by the panic it objects to"
                ),
            }
            assert_eq!(report.summary.total_timed_out, 1, "{category:?} over `{callee}`");
            assert_eq!(report.summary.total_runtime_checked, 0, "{category:?} over `{callee}`");
        }
    }
}

#[test]
fn an_unknown_hardened_boundary_keeps_the_solvers_own_reason() {
    for callee in CALLEES {
        for category in [HardenedVcCategory::PanicBoundary, HardenedVcCategory::UnsafeOperation] {
            let result = VerificationResult::Unknown {
                solver: Symbol::from("ay"),
                time_ms: 1,
                reason: "incomplete quantifier reasoning".to_string(),
            };
            let report = trust_report::build_json_report(
                "probe",
                &[(vc(boundary(category, callee)), result)],
            );
            let outcome = &report.functions[0].obligations[0].outcome;
            match outcome {
                ObligationOutcome::Unknown { reason } => assert_eq!(
                    reason, "incomplete quantifier reasoning",
                    "{category:?} over `{callee}`: the solver's reason must survive verbatim. A \
                     monitor-authority downgrade message here means the Auto policy relabelled \
                     the row `RuntimeChecked` and the publication gate scrubbed it back."
                ),
                other => panic!("{category:?} over `{callee}` must report Unknown, not {other:?}"),
            }
            assert_eq!(report.summary.total_unknown, 1, "{category:?} over `{callee}`");
            assert_eq!(report.summary.total_runtime_checked, 0, "{category:?} over `{callee}`");
        }
    }
}

/// CONTROL. The report path is not simply refusing to relabel anything: a
/// PRIMARY obligation whose own guard rustc emits still takes the Auto
/// downgrade, so a blanket regression in `classify_runtime_disposition` cannot
/// hide behind the two tests above.
#[test]
fn a_primary_bounds_obligation_still_takes_the_auto_runtime_checked_path() {
    let result = VerificationResult::Unknown {
        solver: Symbol::from("ay"),
        time_ms: 1,
        reason: "incomplete quantifier reasoning".to_string(),
    };
    let report =
        trust_report::build_json_report("probe", &[(vc(VcKind::IndexOutOfBounds), result)]);
    let outcome = &report.functions[0].obligations[0].outcome;
    // The publication gate scrubs the `RuntimeChecked` label itself (no live
    // monitor capability on a freshly built report), so what is pinned here is
    // that the row took the POLICY path at all — its reason is the gate's
    // message, not the solver's.
    match outcome {
        ObligationOutcome::Unknown { reason } => assert_ne!(
            reason, "incomplete quantifier reasoning",
            "IndexOutOfBounds must still be relabelled by the Auto policy before the \
             publication gate scrubs it; an unchanged reason means the policy path went dead"
        ),
        other => panic!("expected the gated Unknown, got {other:?}"),
    }
}
