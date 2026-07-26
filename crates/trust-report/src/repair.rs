//! Stable, machine-readable repair report for AI-in-the-loop source repair.
//!
//! This is the canonical interface an LLM repair agent (driving `trust-backprop`)
//! consumes. It flattens the rich [`JsonProofReport`] into a stable, per-obligation
//! list with exactly the fields a repair agent needs to act:
//!
//! ```text
//! { function, location, kind, status, sort, counterexample, unsupported_reason }
//! ```
//!
//! The schema is intentionally *narrower* and *flatter* than the full proof
//! report: an agent should not have to learn the full evidence/transport tree to
//! decide what to fix. Two design choices make this AI-friendly:
//!
//! 1. **`unsupported_reason` is a classified enum, not free text.** The verifier
//!    threads a human string (e.g. `"unsupported MIR `Rvalue::Aggregate` ..."`,
//!    `"calls callback (non-local state havoced)"`, `"nonlinear arithmetic ..."`).
//!    Those strings drift and are hard to branch on. [`UnsupportedReason`]
//!    classifies them into a stable closed set so the agent can map a category to
//!    a repair strategy (add a spec, replace checked arith, split a call, etc.).
//!    The original string is preserved in `detail` for the agent's prompt context.
//!
//! 2. **`sort` is the obligation's proof level** (`safety` / `functional` /
//!    `domain`), so an agent can prioritize L0 safety gaps over L2 domain ones.
//!
//! The schema is versioned independently of the full report
//! ([`REPAIR_SCHEMA_VERSION`]) because repair agents pin to it.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use serde::{Deserialize, Serialize};
use trust_types::{
    CounterexampleReport, JsonProofReport, ObligationOutcome, ObligationReport, ProofLevel,
    SourceSpan,
};

/// Schema version for the repair report. Repair agents pin to this; bump on any
/// backward-incompatible change to [`RepairReport`] / [`RepairObligation`].
pub const REPAIR_SCHEMA_VERSION: &str = "trust.repair.v1";

/// Top-level repair report: a flat, stable view of every actionable obligation.
///
/// `PartialEq` is intentionally not derived: [`CounterexampleReport`] (reachable
/// via [`RepairObligation::counterexample`]) does not implement it. Compare
/// reports by their serialized JSON instead.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RepairReport {
    /// Schema version a repair agent can pin to (see [`REPAIR_SCHEMA_VERSION`]).
    pub schema_version: String,
    /// Crate this report covers.
    pub crate_name: String,
    /// Every obligation that did not prove, in deterministic order. Proved
    /// obligations are omitted by default (see [`build_repair_report`]); use
    /// [`build_repair_report_full`] to include them.
    pub obligations: Vec<RepairObligation>,
    /// Roll-up counts so an agent can decide whether repair is even needed.
    pub summary: RepairSummary,
}

/// One actionable obligation, flattened for repair tooling.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RepairObligation {
    /// Fully-qualified function the obligation belongs to.
    pub function: String,
    /// Source location of the obligation, when known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceSpan>,
    /// Stable machine kind tag (e.g. `"arithmetic_overflow_add"`, `"precondition"`).
    pub kind: String,
    /// Verification status, as a stable lowercase tag.
    pub status: RepairStatus,
    /// Proof level / severity, so agents can prioritize safety over domain.
    pub sort: RepairSort,
    /// Structured counterexample for `failed` obligations (named, typed vars).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub counterexample: Option<CounterexampleReport>,
    /// **Why** an obligation could not be proved — classified so the agent can
    /// pick a repair strategy. Present for `unknown` / `timeout` obligations.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unsupported_reason: Option<UnsupportedReasonReport>,
    /// Design-mandate text for `design_requirement` obligations: what the
    /// source must move away from (e.g. a raw path or process call). This is
    /// not an unsupported reason — the obligation is undischargeable by
    /// construction and only a source change satisfies it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub design_requirement_detail: Option<String>,
}

/// Stable status tag for a repair obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum RepairStatus {
    /// Property proved — no repair needed (only present in the full variant).
    Proved,
    /// Property violated — a counterexample is available.
    Failed,
    /// Solver could not decide — an `unsupported_reason` explains why.
    Unknown,
    /// Solver timed out.
    Timeout,
    /// Checked dynamically at runtime instead of proved statically.
    RuntimeChecked,
    /// A hardened-boundary design mandate: the source must move off a
    /// raw/opaque API. This is NOT a proof failure and never inflates
    /// `failed`/`unknown` (mirrors `ObligationOutcome::DesignRequirement`).
    /// The mandate text is in [`RepairObligation::design_requirement_detail`].
    DesignRequirement,
}

/// Proof level / severity tier, named for repair prioritization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum RepairSort {
    /// L0: memory/arithmetic safety (overflow, bounds, div-by-zero, ...).
    Safety,
    /// L1: functional correctness (pre/postconditions, assertions).
    Functional,
    /// L2: domain-specific properties.
    Domain,
}

impl From<ProofLevel> for RepairSort {
    fn from(level: ProofLevel) -> Self {
        match level {
            ProofLevel::L0Safety => RepairSort::Safety,
            ProofLevel::L1Functional => RepairSort::Functional,
            // Any current/future higher tier maps to domain.
            _ => RepairSort::Domain,
        }
    }
}

/// A classified reason an obligation could not be proved, with the raw text
/// preserved for prompt context.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UnsupportedReasonReport {
    /// Stable category an agent branches on to choose a repair strategy.
    pub category: UnsupportedReason,
    /// Original verifier-provided text (for the agent's prompt / human display).
    pub detail: String,
}

/// Stable, closed classification of *why* a function could not be verified.
///
/// This is the field an LLM repair agent keys its strategy on. The mapping from
/// free text lives in [`classify_unsupported_reason`] and is the single source
/// of truth; new verifier reason strings should be added there, not invented by
/// the agent.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
#[non_exhaustive]
pub enum UnsupportedReason {
    /// A call's result was havoced (no callee spec / opaque/extern callee).
    /// Repair: supply or strengthen the callee contract so the result is modeled.
    HavocedCall,
    /// Nonlinear integer arithmetic (mul/div/mod/`pow` of two variables) the
    /// solver can't decide. Repair: bound operands, factor, or assert a lemma.
    NonlinearArithmetic,
    /// Aliasing / pointer indirection prevented precise modeling.
    /// Repair: tighten aliasing (split borrows) or add an aliasing assumption.
    AliasType,
    /// A MIR construct whose precise semantics are not yet modeled
    /// (`UnsupportedMir`). Repair: usually out of agent scope — flag for compiler.
    UnsupportedMir,
    /// Unbounded loop / missing loop invariant. Repair: synthesize an invariant.
    LoopInvariant,
    /// A required SMT theory/feature is unsupported (e.g. arrays, quantifiers,
    /// floats, `AUFLIRA`). Repair: reformulate to a supported theory.
    UnsupportedTheory,
    /// The solver hit a resource limit (memory/OOM) before deciding.
    /// Repair: split the obligation or raise the limit — not a source fix.
    ResourceLimit,
    /// Trust (R1 corpus): the native full-verification lane had no usable typed
    /// input for this obligation — module/typed-CHC lowering fallthrough
    /// ("direct typed trust_mc CHC/PDR input required", "contains no TrustVc
    /// requests", "no full-verification primary owner", canonical transport
    /// parse failures). A pipeline gap, not a source problem: flag for the
    /// compiler, and read the leading "(root cause)" detail when present.
    NativeInputUnavailable,
    /// Solver returned `unknown` without a more specific cause.
    SolverUnknown,
    /// Reason text did not match any known category. Inspect `detail`.
    Other,
}

impl UnsupportedReason {
    /// Whether a source-repair agent can plausibly act on this category.
    ///
    /// `false` means the gap is a compiler/solver limitation (unsupported MIR,
    /// resource limits) that source edits won't fix — the agent should skip it.
    #[must_use]
    pub fn is_source_actionable(self) -> bool {
        !matches!(
            self,
            UnsupportedReason::UnsupportedMir
                | UnsupportedReason::ResourceLimit
                | UnsupportedReason::UnsupportedTheory
                | UnsupportedReason::NativeInputUnavailable
        )
    }
}

/// Classify a free-text verifier reason into a stable [`UnsupportedReason`].
///
/// This is the single source of truth for reason normalization. The verifier
/// currently emits these as human strings (see `trust-vcgen::generate` and the
/// router backends); centralizing the mapping here means a repair agent never
/// branches on raw text. Matching is case-insensitive and substring-based so it
/// is robust to minor wording drift.
#[must_use]
pub fn classify_unsupported_reason(reason: &str) -> UnsupportedReason {
    let r = reason.to_ascii_lowercase();
    // Trust (R1 corpus, F6): unwrap the reporting ENVELOPES before keyword
    // matching. Strict-mode rows arrive as "`#[trust(static)]` requires a
    // static proof, but the solver returned unknown: <inner>" and native rows
    // as "native full verifier evidence status: <status>; <inner>" — on the
    // first corpus sweep 84% of external unknowns classified `solver_unknown`
    // off the envelope's "unknown" instead of the inner root cause, and the
    // envelope word "budget" in lowering details misclassified the two biggest
    // in-family clusters as `resource_limit`. Classification must key on the
    // INNER detail.
    let r = match r.split_once("but the solver returned unknown:") {
        Some((envelope, inner)) if envelope.contains("#[trust(static)]") => inner.to_string(),
        _ => r,
    };
    let r = match r.split_once("native full verifier evidence status:") {
        Some((_, tail)) => match tail.split_once(';') {
            Some((_status, inner)) => inner.to_string(),
            None => tail.to_string(),
        },
        None => r,
    };

    // Trust (R1 corpus): NATIVE-LOWERING root causes outrank the resource-limit
    // bucket — the recursive-ADT detail "type lowering exceeded production
    // budget" contains "budget" but is a lowering gap for the compiler, not a
    // solver resource limit an agent could re-run with a bigger box.
    if r.contains("failed to lower")
        || r.contains("cannot be soundly lowered")
        || r.contains("unsupported operation:")
        || r.contains("type lowering exceeded")
        || r.contains("setdiscriminant")
    {
        return UnsupportedReason::UnsupportedMir;
    }
    // Trust (R1 corpus): native-lane input fallthrough — the obligation never
    // received a usable typed solve (adapter/router/transport pipeline gap).
    if r.contains("typed chc input unavailable (root cause)")
        || r.contains("direct typed trust_mc chc/pdr input required")
        || r.contains("typed-input-required")
        || r.contains("contains no trustvc requests")
        || r.contains("no full-verification primary owner")
        || r.contains("canonical trust json transport parse failed")
    {
        return UnsupportedReason::NativeInputUnavailable;
    }

    // Order matters: check the most specific signals first.
    //
    // (1) Resource-limit skips. The memory guard / per-function budget lanes
    // annotate obligations they never dispatched (e.g. "memory guard skipped
    // solver dispatch before proof evidence was produced", "memory limit
    // exceeded: .. — skipping solver dispatch", "resource limit {..} skipped
    // solver dispatch ..", "per-function wall-clock verification budget
    // exceeded .."). These must win even when appended context mentions other
    // categories (the release-blocking wrapper concatenates reasons).
    if r.contains("skipped solver dispatch")
        || r.contains("skipping solver dispatch")
        || r.contains("memory guard")
        || r.contains("memory limit")
        || r.contains("resource limit")
        || r.contains("oom")
        || r.contains("out of memory")
        || r.contains("rlimit")
        || r.contains("budget")
        || r.contains("timed out")
        || r.contains("deadline")
    {
        UnsupportedReason::ResourceLimit
    }
    // (2) The router wraps every `VcKind::UnsupportedMir` obligation as
    // "unsupported MIR {kind} [..] preserved in TrustIr: {detail}". The
    // envelope dominates the detail text: e.g. the type-lowering detail
    // "alias could not be normalized" is about type-system aliases, not
    // pointer aliasing, and must not leak into source-actionable buckets.
    else if r.contains("unsupported mir") || r.contains("preserved in trustir") {
        UnsupportedReason::UnsupportedMir
    } else if r.contains("havoc")
        || r.contains("opaque callee")
        || r.contains("extern call")
        || r.contains("unmodeled external call")
        || r.contains("unmodeled-call")
        || r.contains("panic-freedom is not modeled")
    {
        UnsupportedReason::HavocedCall
    } else if r.contains("nonlinear") || r.contains("non-linear") || r.contains("nia") {
        UnsupportedReason::NonlinearArithmetic
    } else if r.contains("alias") || r.contains("points-to") || r.contains("provenance") {
        UnsupportedReason::AliasType
    } else if r.contains("loop invariant")
        || r.contains("unbounded loop")
        || r.contains("widen")
        || r.contains("cannot prove the allocation is bounded")
    {
        UnsupportedReason::LoopInvariant
    } else if r.contains("theory")
        || r.contains("quantif")
        || r.contains("array")
        || r.contains("auflira")
        || r.contains("uninterpreted")
        || r.contains("float")
    {
        UnsupportedReason::UnsupportedTheory
    } else if r.contains("unknown")
        || r.contains("incomplete")
        || r.contains("unsupported feature")
        || r.contains("inconclusive")
        || r.contains("no backend")
        || r.contains("returned no evidence")
        || r.contains("evidence status")
    {
        UnsupportedReason::SolverUnknown
    } else {
        UnsupportedReason::Other
    }
}

/// Roll-up counts for the repair report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct RepairSummary {
    /// Obligations with a counterexample (definite bugs / spec violations).
    pub failed: usize,
    /// Obligations the solver could not decide (have an `unsupported_reason`).
    pub unknown: usize,
    /// Obligations that timed out.
    pub timeout: usize,
    /// Obligations checked at runtime instead of statically proved.
    pub runtime_checked: usize,
    /// Hardened-boundary design mandates (source must move off a raw/opaque
    /// API). Tracked in their own bucket — they never inflate `failed` or
    /// `unknown` (mirrors the `ObligationOutcome::DesignRequirement` contract).
    #[serde(default)]
    pub design_requirements: usize,
    /// Of the non-proved obligations, how many a source-repair agent can act on.
    pub source_actionable: usize,
}

/// Build the repair report from a full [`JsonProofReport`], including only
/// obligations that did not prove (the actionable set).
///
/// This is the default an agent driving `trust-backprop` should consume.
#[must_use]
pub fn build_repair_report(report: &JsonProofReport) -> RepairReport {
    build_repair_report_inner(report, false)
}

/// Like [`build_repair_report`] but also includes `proved` obligations, for
/// agents that want the complete picture (e.g. to diff before/after a repair).
#[must_use]
pub fn build_repair_report_full(report: &JsonProofReport) -> RepairReport {
    build_repair_report_inner(report, true)
}

fn build_repair_report_inner(report: &JsonProofReport, include_proved: bool) -> RepairReport {
    let mut obligations = Vec::new();
    let mut summary = RepairSummary::default();

    for func in &report.functions {
        for ob in &func.obligations {
            let Some(repair) = repair_obligation(&func.function, ob, include_proved) else {
                continue;
            };

            match repair.status {
                RepairStatus::Failed => summary.failed += 1,
                RepairStatus::Unknown => summary.unknown += 1,
                RepairStatus::Timeout => summary.timeout += 1,
                RepairStatus::RuntimeChecked => summary.runtime_checked += 1,
                RepairStatus::DesignRequirement => summary.design_requirements += 1,
                RepairStatus::Proved => {}
            }
            // Design requirements are source mandates by definition: the only
            // way to satisfy one is a source change, so they always count as
            // source-actionable.
            if repair.unsupported_reason.as_ref().is_some_and(|u| u.category.is_source_actionable())
                || matches!(repair.status, RepairStatus::Failed | RepairStatus::DesignRequirement)
            {
                summary.source_actionable += 1;
            }

            obligations.push(repair);
        }
    }

    RepairReport {
        schema_version: REPAIR_SCHEMA_VERSION.to_string(),
        crate_name: report.crate_name.clone(),
        obligations,
        summary,
    }
}

/// Convert one [`ObligationReport`] into a [`RepairObligation`], or `None` when
/// it is `proved` and `include_proved` is false.
fn repair_obligation(
    function: &str,
    ob: &ObligationReport,
    include_proved: bool,
) -> Option<RepairObligation> {
    let (status, counterexample, unsupported_reason, design_requirement_detail) = match &ob.outcome
    {
        ObligationOutcome::Proved { .. } => {
            if !include_proved {
                return None;
            }
            (RepairStatus::Proved, None, None, None)
        }
        ObligationOutcome::Failed { counterexample } => {
            (RepairStatus::Failed, counterexample.clone(), None, None)
        }
        ObligationOutcome::Unknown { reason } => (
            RepairStatus::Unknown,
            None,
            Some(UnsupportedReasonReport {
                category: classify_unsupported_reason(reason),
                detail: reason.clone(),
            }),
            None,
        ),
        ObligationOutcome::Timeout { timeout_ms } => (
            RepairStatus::Timeout,
            None,
            Some(UnsupportedReasonReport {
                category: UnsupportedReason::ResourceLimit,
                detail: format!("solver timed out after {timeout_ms}ms"),
            }),
            None,
        ),
        ObligationOutcome::RuntimeChecked { .. } => {
            (RepairStatus::RuntimeChecked, None, None, None)
        }
        // A design mandate rides its own channel: it is not a proof failure
        // and must never be folded into `unknown`/`failed` (trust-types
        // `ObligationOutcome::DesignRequirement` contract).
        ObligationOutcome::DesignRequirement { detail } => {
            (RepairStatus::DesignRequirement, None, None, Some(detail.clone()))
        }
        // Future outcome variants: surface as unknown rather than dropping.
        _ => (
            RepairStatus::Unknown,
            None,
            Some(UnsupportedReasonReport {
                category: UnsupportedReason::Other,
                detail: "unhandled obligation outcome".to_string(),
            }),
            None,
        ),
    };

    Some(RepairObligation {
        function: function.to_string(),
        location: ob.location.clone(),
        kind: ob.kind.clone(),
        status,
        sort: RepairSort::from(ob.proof_level),
        counterexample,
        unsupported_reason,
        design_requirement_detail,
    })
}

#[cfg(test)]
mod tests {
    use trust_types::{
        CrateSummary, CrateVerdict, FunctionProofReport, FunctionSummary, FunctionVerdict,
        ProofStrength, ReportMetadata,
    };

    use super::*;

    fn empty_func_summary(verdict: FunctionVerdict) -> FunctionSummary {
        FunctionSummary {
            total_obligations: 0,
            proved: 0,
            runtime_checked: 0,
            failed: 0,
            unknown: 0,
            timed_out: 0,
            design_requirements: 0,
            unattributed_failed: 0,
            unattributed_unknown: 0,
            unattributed_proved: 0,
            total_time_ms: 0,
            max_proof_level: None,
            verdict,
        }
    }

    fn ob(kind: &str, level: ProofLevel, outcome: ObligationOutcome) -> ObligationReport {
        ObligationReport {
            obligation_id: None,
            description: kind.to_string(),
            kind: kind.to_string(),
            proof_level: level,
            location: Some(SourceSpan {
                file: "src/lib.rs".to_string(),
                line_start: 10,
                col_start: 5,
                line_end: 10,
                col_end: 20,
            }),
            outcome,
            solver: "ay".to_string(),
            time_ms: 1,
            evidence: None,
            proof_evidence: None,
            transport_evidence: None,
        }
    }

    fn report_with(obligations: Vec<ObligationReport>) -> JsonProofReport {
        JsonProofReport {
            metadata: ReportMetadata {
                schema_version: "x".to_string(),
                trust_version: "x".to_string(),
                timestamp: "0".to_string(),
                total_time_ms: 0,
                timeout_ms: None,
                function_budget_ms: None,
            },
            crate_name: "demo".to_string(),
            summary: CrateSummary {
                functions_analyzed: 1,
                functions_verified: 0,
                functions_runtime_checked: 0,
                functions_with_violations: 0,
                functions_inconclusive: 0,
                total_obligations: obligations.len(),
                total_proved: 0,
                total_runtime_checked: 0,
                total_failed: 0,
                total_unknown: 0,
                total_timed_out: 0,
                total_design_requirements: 0,
                total_unattributed_failed: 0,
                total_unattributed_unknown: 0,
                total_unattributed_proved: 0,
                proof_grade_engine_statuses: Vec::new(),
                verdict: CrateVerdict::Inconclusive,
            },
            functions: vec![FunctionProofReport {
                function: "demo::f".to_string(),
                summary: empty_func_summary(FunctionVerdict::Inconclusive),
                obligations,
            }],
            hardened: None,
            assumptions: Vec::new(),
            verification_gate: None,
            cargo_proof_inventory: None,
        }
    }

    #[test]
    fn classifies_havoc_nonlinear_alias() {
        assert_eq!(
            classify_unsupported_reason("calls callback (non-local state havoced)"),
            UnsupportedReason::HavocedCall
        );
        assert_eq!(
            classify_unsupported_reason("nonlinear arithmetic: x * y"),
            UnsupportedReason::NonlinearArithmetic
        );
        assert_eq!(classify_unsupported_reason("may alias with p"), UnsupportedReason::AliasType);
        assert_eq!(
            classify_unsupported_reason("unsupported MIR `Rvalue::Aggregate` preserved in TrustIr"),
            UnsupportedReason::UnsupportedMir
        );
        assert_eq!(
            classify_unsupported_reason("unsupported theory: AUFLIRA"),
            UnsupportedReason::UnsupportedTheory
        );
        assert_eq!(
            classify_unsupported_reason("memory limit exceeded (OOM)"),
            UnsupportedReason::ResourceLimit
        );
        assert_eq!(
            classify_unsupported_reason("solver returned unknown"),
            UnsupportedReason::SolverUnknown
        );
        assert_eq!(
            classify_unsupported_reason("something totally novel"),
            UnsupportedReason::Other
        );
    }

    // Trust (R1 corpus, F6): the classifier must key on the INNER root cause,
    // not the strict-mode / native-evidence envelopes, and must route the
    // live corpus cluster strings to the right buckets.
    #[test]
    fn classifies_corpus_envelopes_and_native_fallthrough() {
        // Envelope-wrapped trust-mc fallthrough (574-row corpus cluster) — was
        // solver_unknown off the envelope's "unknown".
        assert_eq!(
            classify_unsupported_reason(
                "`#[trust(static)]` requires a static proof, but the solver returned unknown: native full verifier evidence status: Unsupported; direct typed trust_mc CHC/PDR input required as ContractPredicate::MathIr"
            ),
            UnsupportedReason::NativeInputUnavailable
        );
        // Canonical transport parse failure (317-row corpus cluster).
        assert_eq!(
            classify_unsupported_reason(
                "`#[trust(static)]` requires a static proof, but the solver returned unknown: canonical Trust JSON transport parse failed; lossy transport cannot prove obligations"
            ),
            UnsupportedReason::NativeInputUnavailable
        );
        // Router ownership gap (94-row corpus cluster), now carrying the
        // obligation description.
        assert_eq!(
            classify_unsupported_reason(
                "native full verifier evidence status: Unsupported; no full-verification primary owner is defined for obligation kind Custom { namespace: \"trust.vc\", name: \"unsupported_mir\" }; obligation: unsupported MIR `Call`: opaque callee"
            ),
            UnsupportedReason::NativeInputUnavailable
        );
        // trust-vc Tmir rejection (44-row corpus cluster).
        assert_eq!(
            classify_unsupported_reason(
                "native full verifier evidence status: Unsupported; native trust_vc Tmir proof-certificate evidence rejected: trust-vc rejected native Tmir bundle input: native TrustIr bundle for module `f` contains no TrustVc requests"
            ),
            UnsupportedReason::NativeInputUnavailable
        );
        // Recursive-ADT lowering budget (290-row in-family cluster) — was
        // resource_limit off the word "budget"; it is a lowering gap.
        assert_eq!(
            classify_unsupported_reason(
                "native full verifier evidence status: Unsupported; compiler full verification requires typed TrustIr native evidence: failed to lower `f` and its local callees into typed TrustIr NativeVerificationBundle input: recursive ADT (degraded: type lowering exceeded produced-node budget)"
            ),
            UnsupportedReason::UnsupportedMir
        );
        // SetDiscriminant lowering gap (139-row cluster).
        assert_eq!(
            classify_unsupported_reason(
                "`#[trust(static)]` requires a static proof, but the solver returned unknown: native full verifier evidence status: Unsupported; failed to lower `f`: unsupported operation: SetDiscriminant is modeled only for tagged ADTs"
            ),
            UnsupportedReason::UnsupportedMir
        );
        // A genuine resource-limit skip must STILL win (the wrapper text
        // mentions no lowering/native markers).
        assert_eq!(
            classify_unsupported_reason(
                "`#[trust(static)]` requires a static proof, but the solver returned unknown: memory guard skipped solver dispatch before proof evidence was produced"
            ),
            UnsupportedReason::ResourceLimit
        );
        // Bare solver unknown keeps its bucket.
        assert_eq!(
            classify_unsupported_reason("solver returned unknown"),
            UnsupportedReason::SolverUnknown
        );
    }

    #[test]
    fn proved_obligations_excluded_by_default() {
        let report = report_with(vec![ob(
            "arithmetic_overflow_add",
            ProofLevel::L0Safety,
            ObligationOutcome::Proved { strength: ProofStrength::smt_unsat() },
        )]);
        let repair = build_repair_report(&report);
        assert!(repair.obligations.is_empty());
        assert_eq!(repair.schema_version, REPAIR_SCHEMA_VERSION);
    }

    #[test]
    fn unknown_obligation_carries_classified_reason_and_sort() {
        let report = report_with(vec![ob(
            "postcondition",
            ProofLevel::L1Functional,
            ObligationOutcome::Unknown { reason: "x * y nonlinear".to_string() },
        )]);
        let repair = build_repair_report(&report);
        assert_eq!(repair.obligations.len(), 1);
        let o = &repair.obligations[0];
        assert_eq!(o.function, "demo::f");
        assert_eq!(o.status, RepairStatus::Unknown);
        assert_eq!(o.sort, RepairSort::Functional);
        let reason = o.unsupported_reason.as_ref().unwrap();
        assert_eq!(reason.category, UnsupportedReason::NonlinearArithmetic);
        assert!(reason.category.is_source_actionable());
        assert_eq!(repair.summary.unknown, 1);
        assert_eq!(repair.summary.source_actionable, 1);
    }

    #[test]
    fn unsupported_mir_is_not_source_actionable() {
        let report = report_with(vec![ob(
            "unsupported_mir",
            ProofLevel::L0Safety,
            ObligationOutcome::Unknown {
                reason: "unsupported MIR `Rvalue::ThreadLocalRef` preserved in TrustIr".to_string(),
            },
        )]);
        let repair = build_repair_report(&report);
        let o = &repair.obligations[0];
        assert_eq!(
            o.unsupported_reason.as_ref().unwrap().category,
            UnsupportedReason::UnsupportedMir
        );
        assert_eq!(repair.summary.source_actionable, 0);
    }

    #[test]
    fn failed_obligation_is_actionable() {
        let report = report_with(vec![ob(
            "division_by_zero",
            ProofLevel::L0Safety,
            ObligationOutcome::Failed { counterexample: None },
        )]);
        let repair = build_repair_report(&report);
        assert_eq!(repair.obligations[0].status, RepairStatus::Failed);
        assert_eq!(repair.summary.failed, 1);
        assert_eq!(repair.summary.source_actionable, 1);
    }

    #[test]
    fn report_roundtrips_through_json() {
        let report = report_with(vec![ob(
            "precondition",
            ProofLevel::L1Functional,
            ObligationOutcome::Unknown { reason: "havoced call result".to_string() },
        )]);
        let repair = build_repair_report(&report);
        let json = serde_json::to_string(&repair).unwrap();
        let back: RepairReport = serde_json::from_str(&json).unwrap();
        // CounterexampleReport has no PartialEq; compare via re-serialization.
        assert_eq!(json, serde_json::to_string(&back).unwrap());
    }

    #[test]
    fn design_requirement_rides_its_own_bucket() {
        let report = report_with(vec![
            ob(
                "arithmetic_overflow_add",
                ProofLevel::L0Safety,
                ObligationOutcome::Proved { strength: ProofStrength::smt_unsat() },
            ),
            ob(
                "hardened_boundary",
                ProofLevel::L2Domain,
                ObligationOutcome::DesignRequirement {
                    detail: "move off the raw process-spawn API".to_string(),
                },
            ),
        ]);

        let repair = build_repair_report(&report);
        assert_eq!(repair.obligations.len(), 1, "design requirements are actionable, not proved");
        let o = &repair.obligations[0];
        assert_eq!(o.status, RepairStatus::DesignRequirement);
        assert_eq!(o.sort, RepairSort::Domain);
        assert_eq!(
            o.design_requirement_detail.as_deref(),
            Some("move off the raw process-spawn API")
        );
        assert!(o.unsupported_reason.is_none(), "a design mandate is not an unsupported reason");
        assert!(o.counterexample.is_none());

        // The trust-types contract: DesignRequirement never inflates failed/unknown.
        assert_eq!(repair.summary.design_requirements, 1);
        assert_eq!(repair.summary.unknown, 0, "design requirement must never inflate unknown");
        assert_eq!(repair.summary.failed, 0, "design requirement must never inflate failed");
        assert_eq!(repair.summary.timeout, 0);
        assert_eq!(repair.summary.source_actionable, 1, "a design mandate is a source mandate");

        // Stable wire tag.
        let json = serde_json::to_value(o).unwrap();
        assert_eq!(json["status"], "design_requirement");
    }

    fn func_report(name: &str, obligations: Vec<ObligationReport>) -> FunctionProofReport {
        FunctionProofReport {
            function: name.to_string(),
            summary: empty_func_summary(FunctionVerdict::Inconclusive),
            obligations,
        }
    }

    fn report_with_functions(functions: Vec<FunctionProofReport>) -> JsonProofReport {
        let mut report = report_with(Vec::new());
        report.functions = functions;
        report
    }

    fn counterexample() -> CounterexampleReport {
        CounterexampleReport {
            variables: vec![trust_types::CounterexampleVariable {
                name: "a".to_string(),
                value: "255".to_string(),
                value_type: "uint".to_string(),
                display: "a = 255".to_string(),
            }],
        }
    }

    fn one_of_each_outcome() -> Vec<ObligationReport> {
        vec![
            ob(
                "arithmetic_overflow_add",
                ProofLevel::L0Safety,
                ObligationOutcome::Proved { strength: ProofStrength::smt_unsat() },
            ),
            ob(
                "index_out_of_bounds",
                ProofLevel::L0Safety,
                ObligationOutcome::Failed { counterexample: Some(counterexample()) },
            ),
            ob(
                "postcondition",
                ProofLevel::L1Functional,
                ObligationOutcome::Unknown { reason: "x * y nonlinear".to_string() },
            ),
            ob(
                "precondition",
                ProofLevel::L1Functional,
                ObligationOutcome::Timeout { timeout_ms: 30_000 },
            ),
            ob(
                "arithmetic_overflow_mul",
                ProofLevel::L0Safety,
                ObligationOutcome::RuntimeChecked { note: Some("overflow-checks".to_string()) },
            ),
            ob(
                "hardened_boundary",
                ProofLevel::L2Domain,
                ObligationOutcome::DesignRequirement { detail: "move off raw path".to_string() },
            ),
        ]
    }

    /// Corpus of canonical reports the repair view must reconcile against.
    fn corpus() -> Vec<JsonProofReport> {
        vec![
            // Empty report.
            report_with(Vec::new()),
            // Single proved obligation.
            report_with(vec![ob(
                "division_by_zero",
                ProofLevel::L0Safety,
                ObligationOutcome::Proved { strength: ProofStrength::smt_unsat() },
            )]),
            // Every outcome variant in one function.
            report_with(one_of_each_outcome()),
            // Multiple functions with mixed outcomes.
            report_with_functions(vec![
                func_report("demo::alpha", one_of_each_outcome()),
                func_report("demo::beta", vec![
                    ob(
                        "assertion",
                        ProofLevel::L1Functional,
                        ObligationOutcome::Failed { counterexample: None },
                    ),
                    ob(
                        "slice_bounds_check",
                        ProofLevel::L0Safety,
                        ObligationOutcome::Unknown {
                            reason: "memory guard skipped solver dispatch before proof evidence was produced"
                                .to_string(),
                        },
                    ),
                ]),
                func_report("demo::gamma", Vec::new()),
            ]),
        ]
    }

    /// Hard contract: the repair view is a *view*. For any canonical report it
    /// must never invent, drop, or reclassify an obligation — counts reconcile
    /// exactly, per obligation and in the summary.
    #[test]
    fn bucket_identity_repair_view_never_invents_drops_or_reclassifies() {
        for (i, report) in corpus().iter().enumerate() {
            let full = build_repair_report_full(report);
            let canonical: Vec<(&str, &ObligationReport)> = report
                .functions
                .iter()
                .flat_map(|f| f.obligations.iter().map(move |o| (f.function.as_str(), o)))
                .collect();

            assert_eq!(
                full.obligations.len(),
                canonical.len(),
                "corpus[{i}]: full repair view must carry every canonical obligation"
            );

            let (mut proved, mut failed, mut unknown, mut timeout, mut runtime, mut design) =
                (0usize, 0usize, 0usize, 0usize, 0usize, 0usize);
            for (repair, (function, ob)) in full.obligations.iter().zip(canonical.iter()) {
                assert_eq!(&repair.function, function, "corpus[{i}]: function preserved");
                assert_eq!(repair.kind, ob.kind, "corpus[{i}]: kind preserved");
                assert_eq!(
                    serde_json::to_value(&repair.location).unwrap(),
                    serde_json::to_value(&ob.location).unwrap(),
                    "corpus[{i}]: location preserved"
                );
                let expected = match &ob.outcome {
                    ObligationOutcome::Proved { .. } => RepairStatus::Proved,
                    ObligationOutcome::Failed { .. } => RepairStatus::Failed,
                    ObligationOutcome::Unknown { .. } => RepairStatus::Unknown,
                    ObligationOutcome::Timeout { .. } => RepairStatus::Timeout,
                    ObligationOutcome::RuntimeChecked { .. } => RepairStatus::RuntimeChecked,
                    ObligationOutcome::DesignRequirement { .. } => RepairStatus::DesignRequirement,
                    _ => RepairStatus::Unknown,
                };
                assert_eq!(
                    repair.status, expected,
                    "corpus[{i}]: outcome maps 1:1, never reclassified"
                );
                match expected {
                    RepairStatus::Proved => proved += 1,
                    RepairStatus::Failed => failed += 1,
                    RepairStatus::Unknown => unknown += 1,
                    RepairStatus::Timeout => timeout += 1,
                    RepairStatus::RuntimeChecked => runtime += 1,
                    RepairStatus::DesignRequirement => design += 1,
                }
            }

            assert_eq!(full.summary.failed, failed, "corpus[{i}]");
            assert_eq!(full.summary.unknown, unknown, "corpus[{i}]");
            assert_eq!(full.summary.timeout, timeout, "corpus[{i}]");
            assert_eq!(full.summary.runtime_checked, runtime, "corpus[{i}]");
            assert_eq!(full.summary.design_requirements, design, "corpus[{i}]");
            assert_eq!(
                failed + unknown + timeout + runtime + design + proved,
                canonical.len(),
                "corpus[{i}]: every obligation lands in exactly one bucket"
            );

            // The default (actionable) view is exactly the full view minus proved,
            // with an identical summary.
            let actionable = build_repair_report(report);
            assert_eq!(
                actionable.obligations.len(),
                canonical.len() - proved,
                "corpus[{i}]: actionable view omits exactly the proved obligations"
            );
            assert!(
                actionable.obligations.iter().all(|o| o.status != RepairStatus::Proved),
                "corpus[{i}]"
            );
            assert_eq!(
                serde_json::to_value(&actionable.summary).unwrap(),
                serde_json::to_value(&full.summary).unwrap(),
                "corpus[{i}]: summary must not depend on include_proved"
            );
        }
    }

    /// Golden test: the `trust.repair.v1` wire schema. Field names, status/sort
    /// tags, and nesting are locked — repair agents pin to this. Any change
    /// here is a schema change and requires bumping [`REPAIR_SCHEMA_VERSION`].
    #[test]
    fn trust_repair_v1_schema_golden() {
        let report = report_with(one_of_each_outcome());
        let repair = build_repair_report_full(&report);
        let actual = serde_json::to_value(&repair).unwrap();

        let expected = serde_json::json!({
            "schema_version": "trust.repair.v1",
            "crate_name": "demo",
            "obligations": [
                {
                    "function": "demo::f",
                    "location": {
                        "file": "src/lib.rs",
                        "line_start": 10,
                        "col_start": 5,
                        "line_end": 10,
                        "col_end": 20
                    },
                    "kind": "arithmetic_overflow_add",
                    "status": "proved",
                    "sort": "safety"
                },
                {
                    "function": "demo::f",
                    "location": {
                        "file": "src/lib.rs",
                        "line_start": 10,
                        "col_start": 5,
                        "line_end": 10,
                        "col_end": 20
                    },
                    "kind": "index_out_of_bounds",
                    "status": "failed",
                    "sort": "safety",
                    "counterexample": {
                        "variables": [
                            {
                                "name": "a",
                                "value": "255",
                                "value_type": "uint",
                                "display": "a = 255"
                            }
                        ]
                    }
                },
                {
                    "function": "demo::f",
                    "location": {
                        "file": "src/lib.rs",
                        "line_start": 10,
                        "col_start": 5,
                        "line_end": 10,
                        "col_end": 20
                    },
                    "kind": "postcondition",
                    "status": "unknown",
                    "sort": "functional",
                    "unsupported_reason": {
                        "category": "nonlinear_arithmetic",
                        "detail": "x * y nonlinear"
                    }
                },
                {
                    "function": "demo::f",
                    "location": {
                        "file": "src/lib.rs",
                        "line_start": 10,
                        "col_start": 5,
                        "line_end": 10,
                        "col_end": 20
                    },
                    "kind": "precondition",
                    "status": "timeout",
                    "sort": "functional",
                    "unsupported_reason": {
                        "category": "resource_limit",
                        "detail": "solver timed out after 30000ms"
                    }
                },
                {
                    "function": "demo::f",
                    "location": {
                        "file": "src/lib.rs",
                        "line_start": 10,
                        "col_start": 5,
                        "line_end": 10,
                        "col_end": 20
                    },
                    "kind": "arithmetic_overflow_mul",
                    "status": "runtime_checked",
                    "sort": "safety"
                },
                {
                    "function": "demo::f",
                    "location": {
                        "file": "src/lib.rs",
                        "line_start": 10,
                        "col_start": 5,
                        "line_end": 10,
                        "col_end": 20
                    },
                    "kind": "hardened_boundary",
                    "status": "design_requirement",
                    "sort": "domain",
                    "design_requirement_detail": "move off raw path"
                }
            ],
            "summary": {
                "failed": 1,
                "unknown": 1,
                "timeout": 1,
                "runtime_checked": 1,
                "design_requirements": 1,
                "source_actionable": 3
            }
        });

        assert_eq!(actual, expected, "trust.repair.v1 wire schema drifted");
    }

    /// Live reason-string corpus, surveyed from the tree (trust_verify.rs,
    /// trust-vcgen, trust-router, trust-verifier-api). Keeps the classifier
    /// honest against the strings the verifier actually emits today.
    #[test]
    fn classifies_live_reason_string_corpus() {
        let cases: &[(&str, UnsupportedReason)] = &[
            // Resource-limit family (memory guard / budgets / dispatch skips).
            (
                "memory guard skipped solver dispatch before proof evidence was produced",
                UnsupportedReason::ResourceLimit,
            ),
            (
                "resource limit ExecutionSeconds(30) skipped solver dispatch before proof evidence was produced",
                UnsupportedReason::ResourceLimit,
            ),
            (
                "release-blocking proof gap: memory guard skipped solver dispatch; may alias with p",
                UnsupportedReason::ResourceLimit,
            ),
            (
                "memory limit exceeded: 3072MB used, 4096MB limit (peak: 3080MB) — skipping solver dispatch",
                UnsupportedReason::ResourceLimit,
            ),
            (
                "per-function wall-clock verification budget exceeded before dispatching obligation for demo::f",
                UnsupportedReason::ResourceLimit,
            ),
            (
                "function demo::f exceeds the VC-generation budget (recursive-datatype aggregate explosion); its obligations are left Unknown (fail-closed) to keep the rest of the crate verifiable",
                UnsupportedReason::ResourceLimit,
            ),
            ("solver execution timed out after 30000ms", UnsupportedReason::ResourceLimit),
            ("resource limit exceeded: address-space rlimit", UnsupportedReason::ResourceLimit),
            // UnsupportedMir envelope dominates its detail text — a type-system
            // alias detail must not classify as pointer aliasing.
            (
                "unsupported MIR TyUnsupported [unsupported_mir] preserved in TrustIr: alias could not be normalized in this typing env",
                UnsupportedReason::UnsupportedMir,
            ),
            (
                "unsupported MIR Retag [unsupported_mir] preserved in TrustIr: bb0 stmt1 Stacked Borrows retag requires provenance semantics for raw-pointer or unresolved places",
                UnsupportedReason::UnsupportedMir,
            ),
            (
                "unsupported MIR StatementKind::Intrinsic [unsupported_mir] preserved in TrustIr: bb0 stmt2 intrinsic copy_nonoverlapping requires intrinsic-specific semantics",
                UnsupportedReason::UnsupportedMir,
            ),
            // Havoced / unmodeled calls.
            (
                "an unmodeled external call (or other unlowerable MIR construct) leaves a panic path unverified; strict verification requires complete native evidence — model the call as total, or rewrite it to a verifiable form",
                UnsupportedReason::HavocedCall,
            ),
            (
                "bb0: core::option::Option::<i32>::unwrap panics on None/Err and its panic-freedom is not modeled — match / if let to prove it; use an explicit survey policy only for non-proof triage",
                UnsupportedReason::HavocedCall,
            ),
            ("calls callback (non-local state havoced)", UnsupportedReason::HavocedCall),
            // Nonlinear arithmetic.
            (
                "bb3: signed 128-bit Mul overflow is nonlinear (NIA) and not decidable on the Int path; the BV path declines width > 64 → fail-closed to runtime-check",
                UnsupportedReason::NonlinearArithmetic,
            ),
            // Unbounded allocation rides the loop/bound bucket.
            (
                "bulk allocation alloc::vec::from_elem recognized but element count not derivable from optimized MIR (size operand absent at index 1); cannot prove the allocation is bounded",
                UnsupportedReason::LoopInvariant,
            ),
            // Solver-side inconclusive family.
            ("no backend can handle this VC", UnsupportedReason::SolverUnknown),
            ("no backend produced a verification result", UnsupportedReason::SolverUnknown),
            ("verification inconclusive (exit code 2)", UnsupportedReason::SolverUnknown),
            (
                "engine returned no evidence for requested obligation",
                UnsupportedReason::SolverUnknown,
            ),
            ("incomplete quantifier reasoning", UnsupportedReason::UnsupportedTheory),
        ];

        for (reason, expected) in cases {
            assert_eq!(
                classify_unsupported_reason(reason),
                *expected,
                "reason string misclassified: {reason:?}"
            );
        }
    }
}
