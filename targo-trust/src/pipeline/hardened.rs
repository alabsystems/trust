// Hardened-profile gating: select the tracked compiler profile, classify
// verification outcomes, and evaluate the hardened proof-evidence gate
// that blocks publication unless every hardened obligation carries publishable
// native proof evidence.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::config::{DEFAULT_TRUST_PROFILE, TrustConfig};
use crate::report::{CompilerDiagnostic, LiveTransportAuthority, ReportConfig, VerificationReport};
use crate::types::{VerificationOutcome, VerificationResult};

pub(super) fn hardened_profile_name<'a>(
    hardened: bool,
    trust_profile: Option<&'a str>,
) -> Option<&'a str> {
    if !hardened {
        return None;
    }

    Some(
        trust_profile.filter(|profile| !profile.trim().is_empty()).unwrap_or(DEFAULT_TRUST_PROFILE),
    )
}

pub(super) fn compiler_verification_success(
    compiler_exit: i32,
    total: usize,
    failed: usize,
    unknown: usize,
    runtime_checked: usize,
) -> bool {
    compiler_exit == 0 && total > 0 && failed == 0 && unknown == 0 && runtime_checked == 0
}

// ---------------------------------------------------------------------------
// Trust (green front door, Stage 2): the tiered exit-code gate.
//
// `compiler_verification_success` above is INTENTIONALLY KEPT VERBATIM. Its
// second consumer is the rewrite loop (`rewrite_iteration_success`,
// `run.rs`): the loop must NOT stop strengthening a crate just because it
// reached a *conditional* pass — an `assumption:*`/mandate/runtime-checked row
// is still a strengthening target, so the loop keeps the strict predicate. The
// explicit broad-advisory front-door lane, by contrast, treats those ledger
// rows as a conditional pass. Hence `evaluate_verification_gate` remains
// alongside the old predicate rather than mutating it.
// ---------------------------------------------------------------------------

/// The disjoint outcome partition of a run's transport rows. Built by
/// `partition_outcome_counts`; `total == proved + failed + unknown +
/// runtime_checked + assumed + mandated + contract_panics`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct OutcomeCounts {
    pub(crate) total: usize,
    pub(crate) proved: usize,
    pub(crate) failed: usize,
    pub(crate) unknown: usize,
    pub(crate) runtime_checked: usize,
    pub(crate) assumed: usize,
    pub(crate) mandated: usize,
    /// Trust (T9 contract-panic): rows whose kind starts with `contract-panic:`
    /// — the compiler's rewrite of a FAILED panic-freedom row whose panic was
    /// annotated `#[trust(contract_panic(message_contains = "..."))]` AND
    /// message-matched. Conditional-pass-eligible in the default lane, folded
    /// to failure in the strict lane, never proof credit, always visible.
    pub(crate) contract_panics: usize,
}

/// Which exit-code gate lane a run is evaluated under.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GateLane {
    /// Explicit broad advisory policy (`--allow-l0-gaps` / survey): ledger
    /// rows (assumed / mandated / runtime-checked) yield a conditional pass.
    Advisory,
    /// Narrow `--memory-safe` result policy. Only compiler-authenticated
    /// safe-code demotion assumptions may conditionally pass; every other
    /// non-proved bucket remains inconclusive or failed.
    MemorySafe,
    /// Canonical batteries-on strict result lane, and the DEFAULT.
    ///
    /// Since the completeness-gap ruling (Andrew, 2026-07-25) this lane no longer
    /// fails on a `runtime_checked` row. Such a row is an obligation the compiler
    /// could not prove statically but whose operation KEEPS the runtime check
    /// rustc already emits — the shipped program has vanilla Rust semantics, so
    /// failing the command buys no safety and costs drop-in. Every other
    /// non-proved bucket stays fatal, including a refutation and any row with no
    /// runtime fallback.
    Strict,
    /// Full static discharge — the release gate (`targo trust --certify`).
    /// Identical to the historical `Strict` predicate: EVERY non-proved bucket is
    /// fatal, `runtime_checked` included.
    Certify,
}

impl GateLane {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            GateLane::Advisory => "advisory",
            GateLane::MemorySafe => "memory-safe",
            GateLane::Strict => "strict",
            GateLane::Certify => "certify",
        }
    }
}

/// The exit-code gate decision for a run. `Pass`/`ConditionalPass` are the only
/// success states; `Inconclusive`/`Fail` both exit nonzero.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GateDecision {
    /// Every row proved (and no label-driving ledger entry). Bare PASS.
    Pass,
    /// No refutation, no genuine unknown, at least one EXPLICIT ledger row
    /// (assumption / design mandate / runtime-checked / contract-panic). Exits 0.
    ConditionalPass {
        assumed: usize,
        mandated: usize,
        runtime_checked: usize,
        /// Trust (T9 contract-panic): annotated, message-matched intentional
        /// panics — visible conditions of the pass, never proof credit.
        contract_panics: usize,
    },
    /// A genuine unknown (or no obligations at all): nothing was refuted, but
    /// the run cannot claim a (conditional) pass. Exits nonzero.
    Inconclusive,
    /// A refutation, or a nonzero compiler exit. Exits nonzero.
    Fail,
}

impl GateDecision {
    /// Whether this decision exits 0.
    pub(crate) fn is_success(self) -> bool {
        matches!(self, GateDecision::Pass | GateDecision::ConditionalPass { .. })
    }

    pub(crate) fn as_str(self) -> &'static str {
        match self {
            GateDecision::Pass => "pass",
            GateDecision::ConditionalPass { .. } => "conditional-pass",
            GateDecision::Inconclusive => "inconclusive",
            GateDecision::Fail => "fail",
        }
    }
}

/// Partition a run's transport rows into the disjoint outcome buckets that back
/// the exit-code gate. Returns the counts plus any transport-defect diagnostics
/// (one per defective `assumption:*` row).
///
/// The three-way partition of INCONCLUSIVE rows is the load-bearing rule:
///   * `assumed`   — an explicit `assumption:*` ledger row.
///   * `mandated`  — the compiler's `design_mandate` bit (NEVER inferred from
///                   row text; read only from structured transport evidence).
///   * `unknown`   — every other inconclusive row (timeouts included).
/// A DEFECTIVE assumption row — one whose `kind` starts with `assumption:` yet
/// whose wire outcome claims Proved or RuntimeChecked — is fail-closed to
/// `unknown` (never proof credit) and reported as a transport defect. When in
/// doubt, a row is `unknown`, never `assumed`.
pub(crate) fn partition_outcome_counts(
    results: &[VerificationResult],
) -> (OutcomeCounts, Vec<String>) {
    let mut counts = OutcomeCounts { total: results.len(), ..OutcomeCounts::default() };
    let mut defects = Vec::new();

    for result in results {
        if result.kind.starts_with("assumption:") {
            if result.outcome.is_proved() || result.outcome.is_runtime_checked() {
                // Fail-closed: an assumption row claiming proof/runtime-check
                // would launder an unverified assumption into green. Count it
                // as a genuine unknown and surface the transport defect.
                counts.unknown += 1;
                let subject = if result.function.is_empty() {
                    result.kind.as_str()
                } else {
                    result.function.as_str()
                };
                defects.push(format!(
                    "transport defect: `{}` row for `{subject}` claims {} — a recorded assumption carries no proof; counting it as a genuine unknown",
                    result.kind,
                    result.outcome.label(),
                ));
            } else {
                counts.assumed += 1;
            }
            continue;
        }

        // Trust (T9 contract-panic): the compiler's rewrite of an annotated,
        // message-matched FAILED panic row. Counted into its own always-visible
        // bucket. Classified by the SINGLE SOURCE OF TRUTH
        // (`trust_types::tolerance`) — the same classifier the compiler's verify
        // pass uses to mint these rows — never by re-deriving the kind prefix
        // here (four uncoordinated re-derivations of this decision were the
        // drift that broke `ArrayVec::push`). Projecting the row MESSAGE as well
        // as the kind also classifies a marker-stamped row whose kind was not
        // rewritten (e.g. an older cached transport) exactly as the compiler
        // would. Fail-closed clause copied from the assumption rows above: a
        // contract-panic row claiming Proved or RuntimeChecked would launder an
        // intentional panic into proof credit — count it as a genuine unknown
        // and surface the transport defect. (`ContractPanicClass::Unused` is NOT
        // declared, so an unused annotation falls through below as a genuine
        // `failed` row: it never conditional-passes.)
        let contract_panic_class = trust_types::tolerance::classify_contract_panic(
            &trust_types::tolerance::ContractPanicView {
                text: &result.message,
                row_kind: Some(&result.kind),
            },
        );
        if contract_panic_class.is_declared() {
            if result.outcome.is_proved() || result.outcome.is_runtime_checked() {
                counts.unknown += 1;
                let subject = if result.function.is_empty() {
                    result.kind.as_str()
                } else {
                    result.function.as_str()
                };
                defects.push(format!(
                    "transport defect: `{}` row for `{subject}` claims {} — a contract-panic row records an intentional reachable panic and carries no proof; counting it as a genuine unknown",
                    result.kind,
                    result.outcome.label(),
                ));
            } else {
                counts.contract_panics += 1;
            }
            continue;
        }

        match result.outcome {
            VerificationOutcome::Proved => counts.proved += 1,
            VerificationOutcome::Failed => counts.failed += 1,
            VerificationOutcome::RuntimeChecked => counts.runtime_checked += 1,
            VerificationOutcome::Unknown | VerificationOutcome::Timeout => {
                if crate::report::transport_design_mandate(result) {
                    counts.mandated += 1;
                } else {
                    counts.unknown += 1;
                }
            }
        }
    }

    debug_assert_eq!(
        counts.proved
            + counts.failed
            + counts.runtime_checked
            + counts.assumed
            + counts.mandated
            + counts.contract_panics
            + counts.unknown,
        counts.total,
        "outcome partition buckets must be disjoint and cover every row",
    );

    (counts, defects)
}

/// Restrict the memory-safe lane to rows the compiler explicitly stamped as a
/// safe/no-inlined-unsafe demotion. Transport authentication proves the row
/// came from the compiler; this marker proves the narrow memory-safe policy,
/// rather than survey or an unconditional assumption, produced it.
pub(crate) fn memory_safe_gate_counts(
    results: &[VerificationResult],
    mut counts: OutcomeCounts,
) -> (OutcomeCounts, Vec<String>) {
    let mut defects = Vec::new();
    for result in results {
        let counted_as_assumption = result.kind.starts_with("assumption:")
            && !result.outcome.is_proved()
            && !result.outcome.is_runtime_checked();
        if counted_as_assumption
            && result.backend != trust_types::assumption::MEMORY_SAFE_ASSUMPTION_ROW_SOURCE
        {
            counts.assumed = counts.assumed.saturating_sub(1);
            counts.unknown = counts.unknown.saturating_add(1);
            defects.push(format!(
                "memory-safe policy rejected unmarked assumption `{}` for `{}`; expected compiler source `{}`",
                result.kind,
                result.function,
                trust_types::assumption::MEMORY_SAFE_ASSUMPTION_ROW_SOURCE,
            ));
        }
    }
    (counts, defects)
}

/// Evaluate the tiered exit-code gate per the Stage-2 contract table.
///
/// Advisory lane (Part III of the green-front-door plan):
///   E != 0                                  -> Fail          (exit E)
///   F  > 0                                  -> Fail          (exit 1)
///   U  > 0                                  -> Inconclusive  (exit 1)
///   T == 0                                 -> Inconclusive  (exit 1)
///   A + M + RC + CP > 0 (F = U = 0, T > 0) -> ConditionalPass (exit 0)
///   else (all proved, T > 0)               -> Pass          (exit 0)
///
/// Strict lane: byte-identical to `compiler_verification_success` — every
/// one of A, M, RC, CP, U, T=0, F, E!=0 fails. `ConditionalPass` is unreachable.
pub(crate) fn evaluate_verification_gate(
    lane: GateLane,
    compiler_exit: i32,
    counts: OutcomeCounts,
) -> GateDecision {
    match lane {
        GateLane::Advisory => {
            if compiler_exit != 0 {
                GateDecision::Fail
            } else if counts.failed > 0 {
                GateDecision::Fail
            } else if counts.unknown > 0 {
                GateDecision::Inconclusive
            } else if counts.total == 0 {
                GateDecision::Inconclusive
            } else if counts.assumed
                + counts.mandated
                + counts.runtime_checked
                + counts.contract_panics
                > 0
            {
                GateDecision::ConditionalPass {
                    assumed: counts.assumed,
                    mandated: counts.mandated,
                    runtime_checked: counts.runtime_checked,
                    contract_panics: counts.contract_panics,
                }
            } else {
                GateDecision::Pass
            }
        }
        GateLane::MemorySafe => {
            if compiler_exit != 0 {
                GateDecision::Fail
            } else if counts.failed > 0 {
                GateDecision::Fail
            } else if counts.total == 0
                || counts.unknown
                    + counts.mandated
                    + counts.runtime_checked
                    + counts.contract_panics
                    > 0
            {
                GateDecision::Inconclusive
            } else if counts.assumed > 0 {
                GateDecision::ConditionalPass {
                    assumed: counts.assumed,
                    mandated: 0,
                    runtime_checked: 0,
                    contract_panics: 0,
                }
            } else {
                GateDecision::Pass
            }
        }
        GateLane::Strict => {
            // Strict: fold the explicit ledger buckets back into the unknown
            // count so the predicate is byte-identical to the historical
            // `compiler_verification_success`. A refutation or nonzero exit is a
            // FAIL; every other non-proved state is an INCONCLUSIVE. `is_success`
            // matches `compiler_verification_success(exit, T, F, U+A+M, RC)`.
            // Trust (T9 contract-panic): `contract_panics` joins the fold — a
            // contract-panic row (which should never be minted under the strict
            // compiler lane, but must not slip through if one arrives) folds to
            // a nonzero exit exactly like every other non-proved bucket. For
            // every pre-T9 input (contract_panics == 0) this arm is
            // byte-identical to the historical predicate.
            if compiler_exit != 0 {
                GateDecision::Fail
            } else if counts.failed > 0 {
                GateDecision::Fail
            } else if counts.total == 0
                || counts.unknown
                    + counts.assumed
                    + counts.mandated
                    + counts.contract_panics
                    > 0
            {
                // NOTE `runtime_checked` is deliberately NOT in this sum any
                // more; see the `Strict` doc comment. It remains in the
                // `Certify` fold below, which is the historical predicate.
                GateDecision::Inconclusive
            } else {
                GateDecision::Pass
            }
        }
        GateLane::Certify => {
            // The historical `compiler_verification_success` predicate, kept
            // verbatim: every non-proved bucket is fatal, `runtime_checked`
            // included. This is the release gate the completeness-gap ruling
            // makes load-bearing — development may proceed on a runtime-checked
            // gap, shipping may not.
            if compiler_exit != 0 {
                GateDecision::Fail
            } else if counts.failed > 0 {
                GateDecision::Fail
            } else if counts.total == 0
                || counts.unknown
                    + counts.assumed
                    + counts.mandated
                    + counts.runtime_checked
                    + counts.contract_panics
                    > 0
            {
                GateDecision::Inconclusive
            } else {
                GateDecision::Pass
            }
        }
    }
}

/// Trust (assertion-grade coverage, roadmap §4.1): fold the run's
/// `coverage_summary` transport rows (one per verified crate/session) into the
/// single coverage record for the report and the gate. `None` (no rows) =
/// coverage UNKNOWN — an older compiler that emits no coverage row; reported as
/// such but never a gate failure on absence alone. The aggregate is complete
/// only when EVERY row is complete: one crate's over-count must never be netted
/// against another crate's shortfall.
pub(crate) fn aggregate_coverage(
    rows: &[trust_types::CoverageTransportSummary],
) -> Option<trust_types::VerificationCoverage> {
    if rows.is_empty() {
        return None;
    }
    let mut overflowed = false;
    let mut sum = |values: &mut dyn Iterator<Item = usize>| {
        values.fold(0usize, |total, value| match total.checked_add(value) {
            Some(total) => total,
            None => {
                overflowed = true;
                usize::MAX
            }
        })
    };
    let eligible = sum(&mut rows.iter().map(|row| row.eligible));
    let processed = sum(&mut rows.iter().map(|row| row.processed));
    Some(trust_types::VerificationCoverage {
        eligible,
        processed,
        coverage_complete: !overflowed
            && rows.iter().all(trust_types::CoverageTransportSummary::is_complete),
    })
}

/// Trust (assertion-grade coverage, roadmap §4.1): cap the gate decision on a
/// coverage shortfall. A run whose compiler reports `processed < eligible` has
/// functions that were NEVER verified — however green the verified subset, it
/// must not read as a pass: `Pass`/`ConditionalPass` are demoted to
/// `Inconclusive` (exit nonzero). Fail-closed and monotone in one direction
/// only — an already-failing decision (`Fail`/`Inconclusive`) is never changed,
/// and complete coverage never alters the decision. When `required` is true,
/// an absent row is also inconclusive: current strict compilers promise this
/// inventory, so accepting a legacy/omitted row would allow subset evidence to
/// masquerade as whole-crate proof. Advisory compatibility lanes may set
/// `required` false and continue to report coverage as unknown.
pub(crate) fn apply_coverage_gate(
    decision: GateDecision,
    coverage: Option<&trust_types::VerificationCoverage>,
    required: bool,
) -> GateDecision {
    match coverage {
        Some(cov) if !cov.coverage_complete && decision.is_success() => GateDecision::Inconclusive,
        None if required && decision.is_success() => GateDecision::Inconclusive,
        _ => decision,
    }
}

/// Evaluate one authenticated compiler run, including the whole-target
/// coverage cap and the compiler's typed zero-obligation function inventory.
///
/// An empty obligation vector is a pass only when it is explained completely:
/// the compiler exited successfully, every completed target supplied coverage,
/// coverage is complete and non-empty, and the distinct authenticated
/// zero-obligation function inventory accounts for every eligible function.
/// Coverage alone is not proof that all visited functions had no obligations.
pub(crate) fn evaluate_run_gate(
    lane: GateLane,
    compiler_exit: i32,
    counts: OutcomeCounts,
    coverage: Option<&trust_types::VerificationCoverage>,
    missing_target_coverage: bool,
    require_coverage: bool,
    zero_obligation_function_count: usize,
) -> GateDecision {
    let complete_zero_obligation_inventory = counts.total == 0
        && compiler_exit == 0
        && !missing_target_coverage
        && zero_obligation_function_count > 0
        && coverage.is_some_and(|coverage| {
            coverage.coverage_complete
                && coverage.eligible == zero_obligation_function_count
                && coverage.processed == coverage.eligible
        });
    let outcome_decision = if complete_zero_obligation_inventory {
        GateDecision::Pass
    } else {
        evaluate_verification_gate(lane, compiler_exit, counts)
    };
    let coverage = if missing_target_coverage { None } else { coverage };
    apply_coverage_gate(outcome_decision, coverage, require_coverage)
}

pub(super) fn hardened_proof_gate_failure_for_results(
    results: &[VerificationResult],
    compiler_diagnostics: &[CompilerDiagnostic],
    report_subject: &str,
    zero_obligation_functions: &[String],
    live_transport_authority: Option<&LiveTransportAuthority>,
    config: &TrustConfig,
    hardened: bool,
    trust_profile: Option<&str>,
) -> Option<crate::report::HardenedProofGateFailure> {
    let hardened_profile = hardened_profile_name(hardened, trust_profile);
    let (counts, _defects) = partition_outcome_counts(results);
    let report = VerificationReport {
        report_subject: report_subject.to_string(),
        success: true,
        exit_code: 0,
        proved: counts.proved,
        failed: counts.failed,
        unknown: counts.unknown,
        runtime_checked: counts.runtime_checked,
        assumed: counts.assumed,
        mandated: counts.mandated,
        contract_panics: counts.contract_panics,
        cached: 0,
        total: counts.total,
        results: results.to_vec(),
        zero_obligation_functions: zero_obligation_functions.to_vec(),
        compiler_diagnostics: compiler_diagnostics.to_vec(),
        duration_ms: 0,
        config: ReportConfig {
            level: config.level.clone(),
            timeout_ms: config.timeout_ms,
            function_budget_ms: config.function_budget_ms,
            enabled: config.enabled,
            hardened,
            trust_profile: hardened_profile.map(str::to_string),
        },
        dep_assumptions: Vec::new(),
        gate: None,
        coverage: None,
        test_execution: None,
        cargo_proof_inventory: None,
        proof_artifact_root: None,
        live_transport_authority: live_transport_authority.cloned(),
    };
    report.hardened_proof_gate_failure()
}
