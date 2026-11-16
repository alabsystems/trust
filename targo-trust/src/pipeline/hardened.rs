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

pub(crate) fn hardened_profile_name(hardened: bool, trust_profile: Option<&str>) -> Option<&str> {
    if !hardened {
        return None;
    }

    Some(
        trust_profile.filter(|profile| !profile.trim().is_empty()).unwrap_or(DEFAULT_TRUST_PROFILE),
    )
}

#[cfg(test)]
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
// `compiler_verification_success` above is the test oracle for the historic
// strict predicate. The rewrite loop (`rewrite_iteration_success`, `run.rs`)
// must NOT stop strengthening a crate just because it
// reached a *conditional* pass — an `assumption:*`/mandate/runtime-checked row
// is still a strengthening target, so the loop keeps the strict predicate. The
// explicit broad-advisory front-door lane, by contrast, treats those ledger
// rows as a conditional pass. Hence `evaluate_verification_gate` remains
// alongside the old predicate rather than mutating it.
// ---------------------------------------------------------------------------

/// The disjoint outcome partition of a run's transport rows. Built by
/// `partition_outcome_counts`; `total == proved + failed + unknown +
/// runtime_checked + assumed + mandated + contract_panics`. `excluded` is
/// OUTSIDE that sum: rows count there, never in `total`.
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
    /// Trust (CB4): bodies EXCLUDED from the proof inventory because rustc's
    /// libtest harness synthesized them (`trust_types::exclusion`). Not part of
    /// `total`, never proof credit, never a condition of a pass either: nothing
    /// about any user body rests on them. The partition counts an exact row it
    /// sees here; the publication path elides those rows first and the caller
    /// adds the authenticated inventory (`authenticated_test_harness_exclusions`).
    pub(crate) excluded: usize,
}

/// Which exit-code gate lane a run is evaluated under.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GateLane {
    /// Explicit broad advisory policy (`--allow-l0-gaps` / survey): the RAMP.
    /// Ledger rows (assumed / mandated / runtime-checked / contract-panic) AND
    /// genuine unknowns yield a conditional pass — the lane REPORTS an unproved
    /// obligation instead of failing on it, which is what "allow L0 gaps"
    /// says. A refutation or a nonzero compiler exit still fails, and zero
    /// obligations is still inconclusive (a vacuous run is not a gap, it is
    /// verification not having happened). Before 2026-09-07 an unknown was
    /// fatal here too, so `--allow-l0-gaps` could not pass any real crate and
    /// the fleet ramp had no gate; the strict/certify lanes are the
    /// DESTINATION and keep every unknown fatal.
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
    /// failing the command buys no safety and costs drop-in.
    ///
    /// Since 2026-09-16 the same holds for the two LEDGER buckets the canonical
    /// report already grades `conditional-pass` (`report.success`): `assumed`
    /// (a compiler-published, disclosed conditional discharge — the vacuous
    /// `GlobalAlloc::dealloc` contract, a `#[trust::assume_total]` axiom — and,
    /// since 2026-09-24, only in a shape the STRICT policy publishes; see
    /// [`strict_gate_counts`]) and
    /// `mandated` (a hardened profile's opaque DESIGN REQUIREMENT, which the
    /// compiler now reports rather than fails under its default policy). The
    /// terminal gate used to fold both back into `unknown`, so a program that
    /// dropped a `String` or called `std::env::args` under the default
    /// `unix_hardened` profile was INCONCLUSIVE here while the compiler had
    /// tolerated it and the report said conditional-pass. Every bucket still
    /// appears in the `ConditionalPass` decision and the report, so nothing is
    /// claimed that was not established. A refutation, a genuine unknown, a
    /// contract-panic row, an empty inventory and a nonzero compiler exit stay
    /// fatal; `Certify` keeps the historical predicate.
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
    /// No refutation, and at least one row that is not a proof: an EXPLICIT
    /// ledger row (assumption / design mandate / runtime-checked /
    /// contract-panic) in any lane that admits it, or — in the advisory lane
    /// only — a genuine unknown. Every count is carried so the conditions are
    /// visible; none is proof credit. Exits 0.
    ConditionalPass {
        assumed: usize,
        mandated: usize,
        runtime_checked: usize,
        /// Trust (T9 contract-panic): annotated, message-matched intentional
        /// panics — visible conditions of the pass, never proof credit.
        contract_panics: usize,
        /// Genuine unknowns (timeouts included) the advisory lane reported
        /// instead of failing on. Always 0 outside that lane: strict, certify,
        /// and memory-safe keep an unknown fatal.
        unknown: usize,
    },
    /// No obligations at all, or — outside the advisory lane — a genuine
    /// unknown: nothing was refuted, but the run cannot claim a (conditional)
    /// pass. Exits nonzero.
    Inconclusive,
    /// A refutation, or a nonzero compiler exit. Exits nonzero.
    Fail,
    /// The run produced no measurement, and no row was refuted: its outcome is
    /// `could-not-run` or `not-reproducible` (plan §2), so its counts are no
    /// verdict in either direction. Never computed by the lane gate from
    /// counts; the run's exit (`EXIT_COULD_NOT_RUN`, 3) publishes it.
    CouldNotRun,
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
            GateDecision::CouldNotRun => "could-not-run",
        }
    }
}

/// Partition a run's transport rows into the disjoint outcome buckets that back
/// the exit-code gate. Returns the counts plus any transport-defect diagnostics
/// (one per defective `assumption:*` row).
///
/// The three-way partition of INCONCLUSIVE rows is the load-bearing rule:
/// - `assumed`   — an explicit `assumption:*` ledger row.
/// - `mandated`  — the compiler's `design_mandate` bit (NEVER inferred from
///   row text; read only from structured transport evidence).
/// - `unknown`   — every other inconclusive row (timeouts included).
///
/// A DEFECTIVE assumption row — one whose `kind` starts with `assumption:` yet
/// whose wire outcome claims Proved or RuntimeChecked — is fail-closed to
/// `unknown` (never proof credit) and reported as a transport defect. When in
/// doubt, a row is `unknown`, never `assumed`.
/// Exact shape check for a `contract:coroutine-resume-state` row: the
/// compiler-pinned solver label, the exact pinned reason, a description whose
/// state set round-trips through the shared trust-types parser, and no
/// counterexample. Anything else is a defect — a row cannot claim the kind and
/// green without the full compiler-minted shape.
fn verification_result_is_coroutine_resume_contract_row(
    result: &crate::types::VerificationResult,
) -> bool {
    result.kind == trust_types::assumption::COROUTINE_RESUME_CONTRACT_ROW_KIND
        && result.backend == trust_types::assumption::COROUTINE_RESUME_CONTRACT_ROW_SOLVER
        && result.reason.as_deref()
            == Some(trust_types::assumption::COROUTINE_RESUME_CONTRACT_ROW_REASON)
        && result.counterexample.is_none()
        && trust_types::assumption::parse_coroutine_resume_contract_row_description(&result.message)
            .is_some()
}

/// Exact shape check for a DISCHARGED `contract:global-alloc-dealloc-panic-free`
/// row: the compiler-pinned solver label, the exact pinned discharged reason,
/// and no counterexample. Anything else is a defect — a row cannot claim the
/// discharged kind without the full compiler-minted shape.
fn verification_result_is_global_alloc_dealloc_discharged_row(
    result: &crate::types::VerificationResult,
) -> bool {
    result.kind == trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_KIND
        && result.backend == trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_SOLVER
        && result.reason.as_deref()
            == Some(trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_DISCHARGED_REASON)
        && result.counterexample.is_none()
}

/// Does the EXIT-CODE GATE count this row as a design mandate?
///
/// Deliberately implemented by running the row through `partition_outcome_counts`
/// itself rather than by restating its conditions. Restating them is what broke:
/// the canonical projection counted every authorized row carrying the compiler's
/// `design_mandate` bit, while the partition counts one only when the row is ALSO
/// inconclusive (`Unknown`/`Timeout`) and survived the `assumption:*`,
/// coroutine-contract, global-alloc-dealloc, coroutine-conditional and contract-panic branches — every one of
/// which `continue`s before the mandate test is ever reached.
///
/// A row that carries the bit and is Proved/Failed/RuntimeChecked therefore
/// counted on one side and not the other. MEASURED on trust-wp 2026-09-13: 116
/// authorized mandates against 78 partitioned ones, so `mandated.checked_sub`
/// underflowed and the publication seal refused a run whose compile was clean —
/// with no explanation, because that arm was a bare `return false`.
///
/// Two predicates over the same rows must not be maintained in two places. This
/// one cannot drift from the partition because it IS the partition.
pub(crate) fn counts_as_design_mandate(result: &VerificationResult) -> bool {
    let (counts, _defects) = partition_outcome_counts(std::slice::from_ref(result));
    counts.mandated == 1
}

/// Does the EXIT-CODE GATE treat this row as CONDITIONAL EVIDENCE — an
/// `assumption:*` ledger entry, a published coroutine resume-state contract, a
/// row discharged under that contract, or a declared contract panic?
///
/// The gate diverts every one of these into `assumed`/`contract_panics` BEFORE
/// the outcome match, so its wire outcome never reaches a bucket.
/// `canonical_report_state_divergence` then expects to find them among the
/// canonical UNKNOWNs — `expected_unknown` is literally
/// `unknown + assumed + contract_panics + unauthorized_mandated`.
///
/// The canonical projection only special-cased declared contract panics, so an
/// assumption row whose wire outcome was Failed became a canonical FAILURE while
/// the gate counted it as `assumed`. Conditional evidence is not a refutation:
/// publishing it as one would report a proof obligation as violated on the
/// strength of a row that carries no proof either way.
///
/// Same construction as [`counts_as_design_mandate`]: it asks the partition
/// rather than restating it, so the two cannot drift.
pub(crate) fn counts_as_conditional_evidence(result: &VerificationResult) -> bool {
    let (counts, _defects) = partition_outcome_counts(std::slice::from_ref(result));
    counts.assumed == 1 || counts.contract_panics == 1
}

/// Does the EXIT-CODE GATE count this row in the `failed` bucket? Asks the
/// partition itself, like [`counts_as_conditional_evidence`], so the
/// failure-site accounting (`trust_types::failure_sites`) reconciles with
/// `counts.failed` by construction. No lane transform moves a row into or out
/// of `failed` (`strict_gate_counts` / `memory_safe_gate_counts` only move
/// `assumed` rows to `unknown`).
pub(crate) fn counts_as_failed(result: &VerificationResult) -> bool {
    let (counts, _defects) = partition_outcome_counts(std::slice::from_ref(result));
    counts.failed == 1
}

pub(crate) fn partition_outcome_counts<'a>(
    results: impl IntoIterator<Item = &'a VerificationResult>,
) -> (OutcomeCounts, Vec<String>) {
    let mut counts = OutcomeCounts::default();
    let mut defects = Vec::new();
    let mut rows = 0usize;

    for result in results {
        rows += 1;
        // Trust (CB4): a test-harness exclusion row. Checked FIRST, because its
        // kind is claimed by no other arm and its outcome (`skipped`) would
        // otherwise land in `unknown`. An exact row bound to a test-harness
        // Cargo unit is inventory: it counts in `excluded`, outside `total`, so
        // it can neither add proof nor a condition. Every other row of this kind
        // — a favorable outcome, any field off the compiler's exact shape, a
        // non-test unit, an unscoped raw compile — is a genuine unknown.
        if trust_types::exclusion::is_test_harness_exclusion_row_kind(&result.kind) {
            if crate::types::test_harness_exclusion_of(result).is_some() {
                counts.excluded += 1;
            } else {
                counts.unknown += 1;
                let subject = if result.function.is_empty() {
                    result.kind.as_str()
                } else {
                    result.function.as_str()
                };
                defects.push(format!(
                    "transport defect: `{}` row for `{subject}` ({}) is not the compiler's exact \
                     test-harness exclusion bound to a `test`/`check-test` Cargo unit — an \
                     exclusion is never proof and may only name rustc-synthesized libtest \
                     harness code; counting it as a genuine unknown",
                    result.kind,
                    result.outcome.label(),
                ));
            }
            continue;
        }

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

        // Trust (coroutine resume-state contract): the compiler-published
        // exported-contract row for a coroutine resume body whose ResumedAfter*
        // sentinels were solver-proved under the resume-state entry
        // precondition (verified-modulo-callers). Deliberately NOT an
        // `assumption:*` row — the sentinels carry real proofs — but for
        // COUNTING it is conditional evidence exactly like the assumption
        // ledger (the proof is conditional on callers), so a well-formed row
        // shares the `assumed` bucket; the distinct kind string preserves its
        // identity in every rendered row. Fail-closed twice over: a row
        // claiming Proved/RuntimeChecked would launder the contract into proof
        // credit, and a row that fails the exact shape check (compiler-pinned
        // solver + reason + parseable state set) is a DEFECT lacking the
        // bridge-evidence provenance — both count as genuine unknowns.
        if result.kind == trust_types::assumption::COROUTINE_RESUME_CONTRACT_ROW_KIND {
            let subject = if result.function.is_empty() {
                result.kind.as_str()
            } else {
                result.function.as_str()
            };
            if result.outcome.is_proved() || result.outcome.is_runtime_checked() {
                counts.unknown += 1;
                defects.push(format!(
                    "transport defect: `{}` row for `{subject}` claims {} — a published contract \
                     is conditional evidence and carries no proof; counting it as a genuine unknown",
                    result.kind,
                    result.outcome.label(),
                ));
            } else if verification_result_is_coroutine_resume_contract_row(result) {
                counts.assumed += 1;
            } else {
                counts.unknown += 1;
                defects.push(format!(
                    "transport defect: `{}` row for `{subject}` lacks the compiler's exact \
                     contract-row shape (solver/reason/state-set); counting it as a genuine unknown",
                    result.kind,
                ));
            }
            continue;
        }

        // Trust (global-alloc dealloc contract, 2026-09-16): the compiler-published
        // `GlobalAlloc::dealloc` panic-freedom contract in its DISCHARGED state —
        // no `#[global_allocator]` in the crate graph, so every dealloc is
        // `Global`'s std chain. Same rule as the coroutine row above: conditional
        // evidence (on the final link), never proof credit, so a well-formed row
        // shares the `assumed` bucket; a row claiming Proved/RuntimeChecked, or one
        // that does not carry the compiler's exact solver + reason, is a defect
        // counted as a genuine unknown. The REFUSED spelling is a distinct kind and
        // takes the default arm (unknown). Before this arm every program that drops
        // a `String`/`Vec` was INCONCLUSIVE under `targo trust build` although the
        // compiler had tolerated it.
        if result.kind == trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_KIND {
            let subject = if result.function.is_empty() {
                result.kind.as_str()
            } else {
                result.function.as_str()
            };
            if result.outcome.is_proved() || result.outcome.is_runtime_checked() {
                counts.unknown += 1;
                defects.push(format!(
                    "transport defect: `{}` row for `{subject}` claims {} — a published contract \
                     is conditional evidence and carries no proof; counting it as a genuine unknown",
                    result.kind,
                    result.outcome.label(),
                ));
            } else if verification_result_is_global_alloc_dealloc_discharged_row(result) {
                counts.assumed += 1;
            } else {
                counts.unknown += 1;
                defects.push(format!(
                    "transport defect: `{}` row for `{subject}` lacks the compiler's exact \
                     discharged-contract shape (solver/reason); counting it as a genuine unknown",
                    result.kind,
                ));
            }
            continue;
        }

        // Trust (D2 part B): a row whose violation formula CONSUMED the bridge's
        // entry `Assume(resume_state ∈ live_states)` without being one of the
        // marked sentinel rows the contract describes. The compiler stamps this
        // kind onto the row ITSELF — that is the link that was missing. Before
        // D2 the whole-function panic-freedom aggregate reached here with
        // `kind: "assert"` and `outcome: "proved"`, carrying a `Certified`
        // grade and a CIC term byte-identical to the sentinel row's ex-falso
        // derivation, and nothing connected it to the sibling
        // `contract:coroutine-resume-state` row that held the conditionality —
        // so it was counted as ordinary proof credit.
        //
        // Conditional evidence shares the `assumed` bucket with the assumption
        // ledger and the published contract row; the distinct kind preserves the
        // row's identity (the original kind survives after the prefix). Same
        // fail-closed clause as its neighbours: the compiler strips
        // `proof_evidence` and drops the outcome to `skipped` when it stamps
        // this, so a row that still CLAIMS proof is a transport defect and
        // counts as a genuine unknown.
        if trust_types::assumption::is_coroutine_resume_conditional_row_kind(&result.kind) {
            if result.outcome.is_proved() || result.outcome.is_runtime_checked() {
                let subject = if result.function.is_empty() {
                    result.kind.as_str()
                } else {
                    result.function.as_str()
                };
                counts.unknown += 1;
                defects.push(format!(
                    "transport defect: `{}` row for `{subject}` claims {} — an obligation \
                     discharged under the coroutine resume-state entry assumption is conditional \
                     evidence and carries no proof; counting it as a genuine unknown",
                    result.kind,
                    result.outcome.label(),
                ));
            } else {
                counts.assumed += 1;
            }
            continue;
        }

        // Trust (TINV step 10.7, DECISION_QUEUE TINV-29): a row whose verdict rests on a
        // certified type invariant (its transport carries `assumes type_invariant(S)#k`).
        // The compiler grades it `Trusted` (`TypeInvariantComposed`) and discloses the
        // premise; for COUNTING it is conditional evidence exactly like the coroutine
        // and instance-discharge rows above, so a row that claims Proved lands in the
        // `assumed` bucket, never in `proved`. Any other outcome is counted as what it
        // is (the premise cannot make an unproved row better or worse).
        if result.outcome.is_proved() && !crate::report::transport_assumes(result).is_empty() {
            counts.assumed += 1;
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

        // Trust (OD-1 phase 1, 2026-10-04): the compiler's instance DISCHARGE row
        // (`trust_types::assumption::INSTANCE_HYPOTHESIS_DISCHARGE_ROW_KIND`) reports
        // the RESOLVED callee's own verdict for one (site, instance) of a definition
        // that carries an instance hypothesis. Its `proved` carries no credit of its
        // own — the callee's own rows carry the proof — so an exact row claiming
        // `proved` is conditional evidence (`assumed`), never proof; `failed` and
        // `runtime_checked` count as themselves. A row of this kind from any other
        // source is a genuine unknown.
        if result.kind == trust_types::assumption::INSTANCE_HYPOTHESIS_DISCHARGE_ROW_KIND {
            let subject = if result.function.is_empty() {
                result.kind.as_str()
            } else {
                result.function.as_str()
            };
            if !trust_types::assumption::is_instance_hypothesis_discharge_row(
                &result.kind,
                &result.backend,
            ) {
                counts.unknown += 1;
                defects.push(format!(
                    "transport defect: `{}` row for `{subject}` from `{}` is not the compiler's \
                     exact instance-discharge row; counting it as a genuine unknown",
                    result.kind, result.backend,
                ));
            } else {
                match result.outcome {
                    VerificationOutcome::Proved => counts.assumed += 1,
                    VerificationOutcome::Failed => counts.failed += 1,
                    VerificationOutcome::RuntimeChecked => counts.runtime_checked += 1,
                    VerificationOutcome::Unknown | VerificationOutcome::Timeout => {
                        counts.unknown += 1
                    }
                }
            }
            continue;
        }

        // Trust (unsupported MIR): a row the report classifies as `UnsupportedMir`
        // has no proof lane and no runtime-check fallback. Three other places
        // already refuse it credit — `authorizes_proved_row` withholds proof
        // evidence, `attach_live_transport_evidence` rewrites the row to
        // Unknown, and `report_vc_kind` picks the no-fallback carrier
        // deliberately. This partition, which feeds the EXIT-CODE GATE, was the
        // one place that still counted the claim as `proved`/`runtime_checked`.
        // The divergence does not surface as a wrong number: the gate publishes
        // a proof count the canonical projection will not back, and the run dies
        // at the final publication seal with "the canonical projection does not
        // match the internal state row-for-row" — hours of verification ending
        // in an unattributable refusal (ay's release gate, 2026-09-12). Fail
        // closed in the same direction as every sibling, and say why.
        if matches!(
            crate::report::report_vc_kind(result),
            trust_types::VcKind::UnsupportedMir { .. }
        ) && (result.outcome.is_proved() || result.outcome.is_runtime_checked())
        {
            let subject = if result.function.is_empty() {
                result.kind.as_str()
            } else {
                result.function.as_str()
            };
            counts.unknown += 1;
            defects.push(format!(
                "transport defect: unsupported MIR row for `{subject}` claims {} — an unsupported \
                 MIR classification cannot carry proof or runtime-check authority; counting it as \
                 a genuine unknown",
                result.outcome.label(),
            ));
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

    counts.total = rows - counts.excluded;
    debug_assert_eq!(
        counts.proved
            + counts.failed
            + counts.runtime_checked
            + counts.assumed
            + counts.mandated
            + counts.contract_panics
            + counts.unknown,
        counts.total,
        "outcome partition buckets must be disjoint and cover every non-excluded row",
    );

    (counts, defects)
}

/// Restrict the memory-safe lane to rows the compiler explicitly stamped as a
/// safe/no-inlined-unsafe demotion. Transport authentication proves the row
/// came from the compiler; this marker proves the narrow memory-safe policy,
/// rather than survey or an unconditional assumption, produced it.
///
/// One other shape is admitted: the D9 `assumption:termination-unmeasured` charge
/// (ruled 2026-09-27, docs/DECISION_QUEUE.md "D9"), in its exact (kind, solver)
/// pair — `trust_types::assumption::is_termination_unmeasured_assumption_row`, the
/// same predicate the compiler's memory-safe admission
/// (`memory_safe_artifacts_have_non_demotable_failure`) reads. It is a disclosed
/// termination premise, not a memory-safety gap; the compiler publishes it under
/// memory-safe policy and does not abort, and a function that carries it compiled
/// under memory-safe before the charge existed, so refusing it here would be a
/// capability loss nobody ratified. The same kind from any other solver is still
/// a genuine unknown.
///
/// And the SAFETY-ASSUME-1 `assumption:safety-comment` charge (ruled 2026-10-17,
/// docs/DECISION_QUEUE.md "SAFETY-ASSUME-1"), in its exact (kind, solver) pair —
/// `trust_types::assumption::is_safety_comment_assumption_row`. It is published only
/// for a body that contains a user `unsafe { }` block, which the compiler never
/// judges by its memory-safe demotion gate (that gate is for unsafe-free bodies), so
/// the compiler's memory-safe run treats it as the default lane does: it records the
/// row and passes CONDITIONALLY. Counting it a genuine unknown here would make the
/// memory-safe lane stricter than the compiler it reads about a row that is, by
/// construction, a disclosed assumption. It stays in the `assumed` bucket: never
/// proved, and `--certify` refuses it.
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
            && !trust_types::assumption::is_termination_unmeasured_assumption_row(
                &result.kind,
                &result.backend,
            )
            && !trust_types::assumption::is_safety_comment_assumption_row(
                &result.kind,
                &result.backend,
            )
        {
            counts.assumed = counts.assumed.saturating_sub(1);
            counts.unknown = counts.unknown.saturating_add(1);
            defects.push(format!(
                "memory-safe policy rejected unmarked assumption `{}` for `{}`; expected compiler source `{}`",
                result.kind,
                result.function,
                trust_types::assumption::MEMORY_SAFE_ASSUMPTION_ROW_SOURCE,
            ));
        } else if result.outcome.is_proved()
            && trust_types::assumption::is_instance_hypothesis_discharge_row(
                &result.kind,
                &result.backend,
            )
        {
            // Trust (OD-1 phase 1): the partition counts a `proved` instance-discharge
            // row `assumed`; it rests on an instance hypothesis, which the compiler's
            // memory-safe policy refuses, and it carries no memory-safe stamp. An
            // unmarked assumption is a genuine unknown on this lane.
            counts.assumed = counts.assumed.saturating_sub(1);
            counts.unknown = counts.unknown.saturating_add(1);
            defects.push(format!(
                "memory-safe policy rejected instance-discharge row `{}` for `{}`: it is conditional \
                 on an instance hypothesis, which memory-safe policy refuses",
                result.kind, result.function,
            ));
        }
    }
    (counts, defects)
}

/// Does the EXIT-CODE GATE count this row in the `assumed` bucket? Asks the
/// partition itself, like [`counts_as_design_mandate`], so it cannot drift from it.
fn counts_as_assumed(result: &VerificationResult) -> bool {
    let (counts, _defects) = partition_outcome_counts(std::slice::from_ref(result));
    counts.assumed == 1
}

/// Restrict the default strict lane's `assumed` bucket to the rows the compiler's
/// STRICT policy publishes as tolerated conditional evidence. Every other row the
/// partition counts as `assumed` becomes a genuine unknown, with a named defect.
///
/// The strict lane grades an `assumed` row a conditional pass (2026-09-16) on one
/// premise: under strict policy the only assumptions the compiler TOLERATES are its
/// own conditional evidence. Every other skip a strict compiler meets is refused
/// with a build-failing error — and since the skip taxonomy (2026-09-27,
/// RECORD-THEN-RULE) that refusal is accompanied by the `assumption:*` row of the
/// premise it refused (`#[trust::skip]` as `assumption:user-opt-out`, a classifier
/// gap, an unreachable start), so a strict run's skips are enumerable. Such a row
/// always sits beside a non-zero compiler exit, which fails every lane on its own;
/// it is still counted a genuine unknown here, like any row the strict policy
/// does not publish as conditional evidence. Unaudited assumptions become
/// TOLERATED rows only under advisory or memory-safe policy, and those lanes keep
/// their own gates. The lane follows the CLI flags; `TRUSTFLAGS` could once set
/// `-Ztrust-policy` for one run (refused from 2026-10-01, not read since T7a).
/// MEASURED 2026-09-24 with the toolchain built from 450403669e, which carries the
/// 2026-09-16 gate, on a crate whose only function is a `#[trust::skip]` `x + 1`.
/// `targo trust check` failed: strict policy refuses the skip with a compile error.
/// `TRUSTFLAGS=-Ztrust-policy=advisory targo trust check` compiled it, published
/// `assumption:user-opt-out` from source `trust-policy`, and exited 0 with
/// `Gate: CONDITIONAL-PASS [strict lane, exit 0]`. The fake toolchain in
/// `tests/full_verifier_flag.rs` replays that row. An advisory-only row is not an
/// unknown under advisory policy, so the strict lane has to recognize it by its
/// shape, whatever route brings it.
///
/// Admitted: `trust_types::assumption::strict_policy_publishes_assumption_row`,
/// the single table of strict shapes (definition-entry `requires`,
/// `#[trust::assume_total]`, the b59 `fmt::format` leg), plus the discharged
/// `contract:global-alloc-dealloc-panic-free` row, which the partition admits only
/// in its exact compiler shape. The `contract:coroutine-resume-state` row is NOT
/// admitted. The compiler publishes it only under the explicit advisory policy
/// (D2: in a fail-closed lane it would turn an undischarged premise into silence).
/// Rows stamped conditional on it appear under strict policy only beside the
/// build-aborting coroutine premise.
pub(crate) fn strict_gate_counts(
    results: &[VerificationResult],
    mut counts: OutcomeCounts,
) -> (OutcomeCounts, Vec<String>) {
    let mut defects = Vec::new();
    for result in results {
        if !counts_as_assumed(result) {
            continue;
        }
        let admitted = result.kind
            == trust_types::assumption::GLOBAL_ALLOC_DEALLOC_CONTRACT_ROW_KIND
            // OD-1 phase 1: a well-formed `proved` instance-discharge row, which the
            // partition counts as conditional evidence (the strict compiler publishes
            // it and does not abort on it).
            || trust_types::assumption::is_instance_hypothesis_discharge_row(
                &result.kind,
                &result.backend,
            )
            || trust_types::assumption::strict_policy_publishes_assumption_row(
                &result.kind,
                &result.backend,
                &result.message,
            );
        if admitted {
            continue;
        }
        // Trust (TINV step 10.7, TINV-29): a row proved under a certified type invariant
        // is disclosed conditional evidence, and the strict lane withholds it exactly as
        // it withholds the other `Trusted` assumption-bearing grades (the E6 view and
        // the under-`requires` discharges ship no publishable evidence either).
        if !crate::report::transport_assumes(result).is_empty() {
            counts.assumed = counts.assumed.saturating_sub(1);
            counts.unknown = counts.unknown.saturating_add(1);
            defects.push(format!(
                "strict policy withholds `{}` for `{}`: its proof rests on a certified type \
                 invariant ({}); a TINV-composed row is `Trusted` conditional evidence, never \
                 strict proof credit (DECISION_QUEUE TINV-29); counting it as a genuine unknown",
                result.kind,
                result.function,
                crate::report::transport_assumes(result).join("; "),
            ));
            continue;
        }
        counts.assumed = counts.assumed.saturating_sub(1);
        counts.unknown = counts.unknown.saturating_add(1);
        defects.push(format!(
            "strict policy rejected assumption `{}` (source `{}`) for `{}`: the compiler's strict \
             policy never publishes this row as conditional evidence — a strict compiler records \
             such a row only beside the build-failing error that refuses the skip, and otherwise \
             it comes from a nonfatal policy or another producer; counting it as a genuine \
             unknown",
            result.kind, result.backend, result.function,
        ));
    }
    (counts, defects)
}

/// Evaluate the tiered exit-code gate per the Stage-2 contract table.
///
/// Advisory lane (Part III of the green-front-door plan, `git show
/// 6ba5324748^:docs/design-notes/2026-07-02-green-front-door-plan.md`; ramp
/// since 2026-09-07):
///   E != 0                                  -> Fail          (exit E)
///   F  > 0                                  -> Fail          (exit 1)
///   T == 0                                 -> Inconclusive  (exit 1)
///   U + A + M + RC + CP > 0 (F = 0, T > 0) -> ConditionalPass (exit 0),
///                                             every bucket carried, U included
///   else (all proved, T > 0)               -> Pass          (exit 0)
///
/// The U row used to read `-> Inconclusive (exit 1)`, which made
/// `--allow-l0-gaps` fail on exactly the gaps it exists to allow: no real crate
/// could pass the advisory lane, so the fleet ramp had no gate at all.
///
/// Strict lane (the default): E != 0 / F > 0 -> Fail; U > 0 / CP > 0 / T == 0 ->
/// Inconclusive; A + M + RC > 0 -> ConditionalPass; else Pass. Certify lane:
/// byte-identical to the historical `compiler_verification_success` — every one
/// of A, M, RC, CP, U, T=0, F, E!=0 fails; `ConditionalPass` is unreachable.
pub(crate) fn evaluate_verification_gate(
    lane: GateLane,
    compiler_exit: i32,
    counts: OutcomeCounts,
) -> GateDecision {
    match lane {
        GateLane::Advisory => {
            if compiler_exit != 0 || counts.failed > 0 {
                GateDecision::Fail
            } else if counts.total == 0 {
                GateDecision::Inconclusive
            } else if counts.unknown
                + counts.assumed
                + counts.mandated
                + counts.runtime_checked
                + counts.contract_panics
                > 0
            {
                // A genuine unknown is a CONDITION of the pass here, never a
                // failure: this lane exists to report L0 gaps, and the count is
                // carried so nothing about the pass is silent.
                GateDecision::ConditionalPass {
                    assumed: counts.assumed,
                    mandated: counts.mandated,
                    runtime_checked: counts.runtime_checked,
                    contract_panics: counts.contract_panics,
                    unknown: counts.unknown,
                }
            } else {
                GateDecision::Pass
            }
        }
        GateLane::MemorySafe => {
            if compiler_exit != 0 || counts.failed > 0 {
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
                    unknown: 0,
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
            if compiler_exit != 0 || counts.failed > 0 {
                GateDecision::Fail
            } else if counts.total == 0 || counts.unknown + counts.contract_panics > 0 {
                // NOTE `runtime_checked` (2026-07-25 ruling), `assumed` and
                // `mandated` (2026-09-16) are deliberately NOT in this sum; see
                // the `Strict` doc comment. All three remain in the `Certify`
                // fold below, which is the historical predicate.
                GateDecision::Inconclusive
            } else if counts.assumed + counts.mandated + counts.runtime_checked > 0 {
                GateDecision::ConditionalPass {
                    assumed: counts.assumed,
                    mandated: counts.mandated,
                    runtime_checked: counts.runtime_checked,
                    contract_panics: 0,
                    unknown: 0,
                }
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
            if compiler_exit != 0 || counts.failed > 0 {
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
pub(crate) fn aggregate_coverage<'a>(
    rows: impl IntoIterator<Item = &'a trust_types::CoverageTransportSummary>,
) -> Option<trust_types::VerificationCoverage> {
    let mut any = false;
    let mut overflowed = false;
    let mut every_row_complete = true;
    let mut add = |total: usize, value: usize| match total.checked_add(value) {
        Some(total) => total,
        None => {
            overflowed = true;
            usize::MAX
        }
    };
    let (mut eligible, mut processed) = (0usize, 0usize);
    for row in rows {
        any = true;
        eligible = add(eligible, row.eligible);
        processed = add(processed, row.processed);
        every_row_complete &= row.is_complete();
    }
    any.then_some(trust_types::VerificationCoverage {
        eligible,
        processed,
        coverage_complete: !overflowed && every_row_complete,
        excluded: 0,
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
///
/// Trust (CB4): in a test-harness build some eligible functions are the bodies
/// rustc's libtest harness synthesized, which the compiler EXCLUDES (one exact
/// row each, `excluded_functions`). They are accounted for, but not by the
/// zero-obligation inventory, so before CB4 a test crate whose user bodies had
/// no obligations could never satisfy `eligible == zero_obligation` and fell
/// through to `T == 0 -> Inconclusive`. The rule is now
/// `eligible == |zero_obligation| + |excluded|` over DISJOINT identity sets
/// (a function cannot be both), and at least one zero-obligation USER body is
/// still required: a run whose only accounted bodies are exclusions proves
/// nothing and stays inconclusive.
#[allow(clippy::too_many_arguments)]
pub(crate) fn evaluate_run_gate(
    lane: GateLane,
    compiler_exit: i32,
    counts: OutcomeCounts,
    coverage: Option<&trust_types::VerificationCoverage>,
    missing_target_coverage: bool,
    require_coverage: bool,
    zero_obligation_functions: &[String],
    excluded_functions: &[String],
) -> GateDecision {
    let zero_obligation =
        zero_obligation_functions.iter().collect::<std::collections::BTreeSet<_>>();
    let excluded = excluded_functions.iter().collect::<std::collections::BTreeSet<_>>();
    let inventory_is_exact = zero_obligation.len() == zero_obligation_functions.len()
        && excluded.len() == excluded_functions.len()
        && zero_obligation.is_disjoint(&excluded);
    let accounted = zero_obligation.len().checked_add(excluded.len());
    let complete_zero_obligation_inventory = counts.total == 0
        && compiler_exit == 0
        && !missing_target_coverage
        && inventory_is_exact
        && !zero_obligation.is_empty()
        && coverage.is_some_and(|coverage| {
            coverage.coverage_complete
                && Some(coverage.eligible) == accounted
                && coverage.processed == coverage.eligible
        });
    let outcome_decision = if complete_zero_obligation_inventory {
        GateDecision::Pass
    } else {
        evaluate_verification_gate(lane, compiler_exit, counts)
    };
    let coverage = if missing_target_coverage { None } else { coverage };
    // Trust (the ramp may not pass on unproved rows it cannot scope): the
    // advisory lane is the ONE lane that makes the coverage row OPTIONAL
    // (`require_coverage = strict_artifact_policy`, false here), so
    // `apply_coverage_gate`'s `None if required` arm never fires for it, and
    // `missing_target_coverage` above has just discarded whatever aggregate
    // there was. Before the ramp that was harmless: `unknown > 0` was already
    // `Inconclusive`, so no absent row could manufacture a pass. Now it can —
    // a run whose proof unit legally ends without a `coverage_summary` would
    // exit 0 reporting `0 proved … N unknown` and `Coverage: unknown`, i.e. a
    // pass over an unknown denominator. A pass that RESTS ON unproved rows has
    // to be able to say what fraction of the crate it looked at.
    //
    // Scoped to exactly that: a decision carrying no unknowns is untouched, so
    // this neither tightens the pre-ramp behaviour of any other lane nor of an
    // advisory run that actually proved its rows.
    let rests_on_unproved_rows = matches!(
        outcome_decision,
        GateDecision::ConditionalPass { unknown, .. } if unknown > 0
    );
    if rests_on_unproved_rows && coverage.is_none() {
        return GateDecision::Inconclusive;
    }
    apply_coverage_gate(outcome_decision, coverage, require_coverage)
}

pub(super) struct HardenedProofGateInput<'a> {
    pub(super) results: &'a [VerificationResult],
    pub(super) compiler_diagnostics: &'a [CompilerDiagnostic],
    pub(super) report_subject: &'a str,
    pub(super) zero_obligation_functions: &'a [String],
    pub(super) test_harness_exclusions: &'a [trust_types::GateExclusionReport],
    pub(super) live_transport_authority: Option<&'a LiveTransportAuthority>,
    pub(super) config: &'a TrustConfig,
    pub(super) hardened: bool,
    pub(super) trust_profile: Option<&'a str>,
}

pub(super) fn hardened_proof_gate_failure_for_results(
    input: HardenedProofGateInput<'_>,
) -> Option<crate::report::HardenedProofGateFailure> {
    let HardenedProofGateInput {
        results,
        compiler_diagnostics,
        report_subject,
        zero_obligation_functions,
        test_harness_exclusions,
        live_transport_authority,
        config,
        hardened,
        trust_profile,
    } = input;
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
        // Trust (#220): this is an internal gate PROBE over an already-published
        // vector, never rendered to a terminal — there is no publication pass
        // here whose boundary could be reported, so it is honestly unmeasured.
        publication_boundary: None,
        zero_obligation_functions: zero_obligation_functions.to_vec(),
        compiler_diagnostics: compiler_diagnostics.to_vec(),
        duration_ms: 0,
        config: ReportConfig {
            level: config.level.clone(),
            // An internal probe over already-published rows: never rendered,
            // and no budget bounds it; the configured profile is recorded.
            budget_profile: crate::determinism_report::budget_profile(config),
            enabled: config.enabled,
            hardened,
            trust_profile: hardened_profile.map(str::to_string),
            project_requirements: None,
        },
        dep_assumptions: Vec::new(),
        gate: None,
        noted_stops: Vec::new(),
        coverage: None,
        coverage_dropped: Vec::new(),
        test_execution: None,
        cargo_proof_inventory: None,
        proof_artifact_root: None,
        live_transport_authority: live_transport_authority.cloned(),
        test_harness_exclusions: test_harness_exclusions.to_vec(),
    };
    report.hardened_proof_gate_failure()
}
