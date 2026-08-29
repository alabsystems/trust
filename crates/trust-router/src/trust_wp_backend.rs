// trust-router/src/trust_wp_backend.rs: trust-wp deductive backend for the
// per-VC router.
//
// R4 driver flip (2026-08-20, design gate in
// docs/design/2026-07-09-two-language-spec-surface.md, audit
// docs/audits/2026-08-20-r-phase-reaudit.md): this backend is NATIVE-BACKED.
// It routes every non-constant contract VC through trust-wp's typed in-process
// `TrustWpVerificationEngine` (`trust_wp::verifier_api`) — the same adapter the
// full-verification engine registry ships in trustc — and NEVER spawns the
// `trust_wp` subprocess. The retired lane parsed a text protocol
// (`TRUST_WP_RESULT:v1` on stderr) into per-VC verdicts; a compiler verdict
// must not be minted from parsed subprocess text. The subprocess `CliBackend`
// remains in `crates/trust-wp` solely for standalone (non-compiler) callers.
//
// Seal against reintroduction: nothing in this module imports `CliBackend`,
// `verify_with_contracts`, or `TrustWpConfig`, and the `route_is_invariant_to_
// trust_wp_path_env` test pins that verdicts do not change when `TRUST_WP_PATH`
// points at a binary that would have satisfied the old text protocol.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use trust_types::{
    ContractMetadata, Formula, ProofStrength, VcKind, VerificationCondition, VerificationResult,
};
use trust_verifier_api::{
    BundleSubject, ContractKind, ContractPredicate, EvidenceStatus, ObligationKind, SourceLocation,
    TrustContract, TrustContractBundle, TrustObligation, VerificationEngine as _,
};
use trust_wp::TrustWpVerificationEngine;

use crate::{BackendRole, VerificationBackend, unsupported_mir_unknown};

/// Default per-obligation budget when the compiler does not supply one
/// (matches the previous `TrustWpConfig` default).
const DEFAULT_TIMEOUT_MS: u64 = 60_000;

/// Router backend delegating to trust-wp's typed in-process engine.
///
/// trust-wp understands Rust ownership and contracts natively, and its
/// strongest-postcondition reasoning discharges obligations that need an
/// invariant the pure-SMT path cannot synthesize (e.g. a struct invariant
/// relating a pointer field to a length field). It is the right home for
/// contract/assertion VCs; non-contract VCs fall through to other backends.
///
/// Verdict discipline (fail-closed): a `Proved` can only come from the native
/// engine's evidence with publication-grade deductive strength — today that
/// requires the full native replay metadata the compiler's API-obligation lane
/// attaches (`trust.trust-wp.native-*.v1`), which this bare per-VC carrier does
/// not fabricate, so non-constant VCs report `Unknown` with the exact missing
/// step named in the reason (v7/D3). No subprocess, no `TRUST_WP_PATH`, no
/// text-protocol parsing anywhere on this route.
pub struct TrustWpRouterBackend {
    timeout_ms: u64,
}

impl TrustWpRouterBackend {
    const NAME: &'static str = "trust-wp";

    /// Create a backend with the default per-obligation budget.
    #[must_use]
    pub fn new() -> Self {
        Self { timeout_ms: DEFAULT_TIMEOUT_MS }
    }

    /// Create a backend with a per-obligation timeout (milliseconds). The
    /// native engine is in-process; the budget is reported on `Timeout`
    /// evidence and reserved for deadline plumbing into the native lane.
    #[must_use]
    pub fn with_timeout(timeout_ms: u64) -> Self {
        Self { timeout_ms }
    }
}

impl Default for TrustWpRouterBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for TrustWpRouterBackend {
    fn name(&self) -> &str {
        Self::NAME
    }

    fn role(&self) -> BackendRole {
        BackendRole::Deductive
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        // Deductive contract obligations are trust-wp's lane. Two gates, both
        // needed for NON-REGRESSING registration:
        //  (1) a contract-shaped VC kind, and
        //  (2) actual contract metadata present.
        // Gate (2) is what keeps trust-wp off the bare sep-engine `Assertion`s
        // (alloc/overlap checks, which carry no contract metadata) that ay
        // already discharges — otherwise a spurious trust-wp `Failed` on one of
        // those could collide with ay's `Proved` and the aggregator's
        // disagreement rule would downgrade a real proof to `Unknown`.
        matches!(
            vc.kind,
            VcKind::Precondition { .. } | VcKind::Postcondition | VcKind::Assertion { .. }
        ) && vc.contract_metadata.as_ref().is_some_and(ContractMetadata::has_any)
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        // Respect the shared "unsupported MIR ⇒ unknown" gate so an
        // unrepresentable VC never yields a false verdict.
        if let Some(result) = unsupported_mir_unknown(vc, self.name(), 0) {
            return result;
        }
        if !self.can_handle(vc) {
            return VerificationResult::Unknown {
                solver: self.name().into(),
                time_ms: 0,
                reason: format!("trust-wp cannot handle VC kind {:?}", vc.kind),
            };
        }

        // Constant obligations are decided without invoking the prover. `vc.formula`
        // IS the VIOLATION condition (vc.rs: UNSAT => property holds, SAT =>
        // counterexample), so the polarity MUST match the canonical convention
        // (constant_folder.rs:109-116, the reference every backend follows):
        //   Bool(false) violation => UNSAT => property holds        => Proved
        //   Bool(true)  violation => always violated => property fails => Failed
        // (This was previously INVERTED, which reported a Bool(true) — i.e. an
        // always-violated / fail-closed — obligation as a vacuous false PROVED.)
        match vc.formula {
            Formula::Bool(false) => {
                return VerificationResult::Proved {
                    solver: self.name().into(),
                    time_ms: 0,
                    strength: ProofStrength::deductive(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                };
            }
            Formula::Bool(true) => {
                return VerificationResult::Failed {
                    solver: self.name().into(),
                    time_ms: 0,
                    counterexample: None,
                };
            }
            _ => {}
        }

        verify_vc_via_native_trust_wp_engine(self.name(), vc, self.timeout_ms)
    }
}

/// Verify one router VC through trust-wp's typed in-process engine.
///
/// Shared by [`TrustWpRouterBackend`] and trust-strengthen's CEGIS oracle so
/// there is exactly one compiler-reachable trust-wp lane and it is native.
///
/// The VC's violation formula is negated into the PROPERTY goal and carried as
/// a typed `trust-types.Formula@1` contract predicate inside a synthetic
/// single-obligation `TrustContractBundle`; the engine's own fail-closed
/// lowering (`trust_wp.trust-formula.v1` envelope: int/bool fragment only,
/// arithmetic refused per the #29 amendment) decides whether the claim is even
/// representable. Every outcome that is not checked native evidence maps to
/// `Unknown` with the engine's own diagnostics as the actionable reason.
///
/// SOUNDNESS — why every routed goal is encoded as `Postcondition`/`Ensures`:
/// the per-VC route asks exactly one question, "is `¬violation` VALID"
/// (violation UNSAT ⇔ property holds — the same convention ay answers on the
/// same formula). A bare Ensures claim is that question. Deliberately NOT
/// `ObligationKind::Precondition`: trust-wp-core's native replay discharges a
/// contract-linked Precondition as the definition-site requires ECHO
/// (`assume(P) ⊢ P`, see `trust_wp_obligation_kind` in trust-wp's
/// verifier_api) — reflexively, without proving P. That is correct for a
/// definition-site echo and a FALSE ACCEPT for the router's call-site
/// precondition VCs, so this carrier makes the echo unreachable by
/// construction. Likewise NOT `LoopInvariant`: the native loop lane assumes
/// compiler-supplied initiation/consecution context this carrier does not
/// provide.
#[must_use]
pub fn verify_vc_via_native_trust_wp_engine(
    solver_name: &str,
    vc: &VerificationCondition,
    timeout_ms: u64,
) -> VerificationResult {
    // `vc.formula` is the VIOLATION; the claim asserts the PROPERTY
    // (`¬violation`), consistent with the constant short-circuit above and the
    // violation convention. Lowering the raw violation would ask trust-wp to
    // prove the violation HOLDS — the inverted polarity.
    let goal = Formula::Not(Box::new(vc.formula.clone()));
    let goal_value = match serde_json::to_value(&goal) {
        Ok(value) => value,
        Err(error) => {
            return VerificationResult::Unknown {
                solver: solver_name.into(),
                time_ms: 0,
                reason: format!(
                    "trust-wp native route could not serialize the goal formula as \
                     `trust-types.Formula@1` (fail-closed): {error}"
                ),
            };
        }
    };

    let kind_tag = match &vc.kind {
        VcKind::Precondition { .. } => "precondition",
        VcKind::Postcondition => "postcondition",
        VcKind::Assertion { message } if message.contains("[loop:invariant]") => "loop-invariant",
        VcKind::Assertion { .. } => "assertion",
        other => {
            // Defensive: `can_handle` filters these before dispatch; a direct
            // caller still gets a closed refusal, never a verdict.
            return VerificationResult::Unknown {
                solver: solver_name.into(),
                time_ms: 0,
                reason: format!("trust-wp cannot handle VC kind {other:?}"),
            };
        }
    };

    let function: &str = vc.function.as_ref();
    let function = if function.trim().is_empty() { "unknown-function" } else { function };
    let function_component = trust_types::canonical_artifact_id_component(function);
    let obligation_id = format!("trust-wp-router:{kind_tag}:{function_component}");
    let contract_id = format!("{obligation_id}:contract");
    let source = source_location_from_span(&vc.location);

    let mut bundle = TrustContractBundle::empty(
        format!("trust-wp-router:{function_component}"),
        BundleSubject::Function {
            crate_name: "trust-router-vc".to_string(),
            path: function.to_string(),
        },
    );
    bundle.contracts.push(TrustContract {
        contract_id: contract_id.clone(),
        kind: ContractKind::Ensures,
        predicate: ContractPredicate::CanonicalJson {
            schema: trust_types::TRUST_SYMBOLIC_FORMULA_SCHEMA.to_string(),
            value: goal_value,
        },
        source: source.clone(),
        metadata: Vec::new(),
    });
    bundle.obligations.push(TrustObligation {
        obligation_id: obligation_id.clone(),
        kind: ObligationKind::Postcondition,
        contract_id: Some(contract_id),
        proof_item_id: None,
        source,
        description: format!(
            "per-VC router goal ({kind_tag}): property = negated violation formula"
        ),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: Vec::new(),
    });

    // The public `VerificationEngine::verify` wrapper re-validates the bundle
    // and the requested subset; an invalid synthetic carrier yields no
    // evidence, which maps to `Unknown` below (fail-closed, never a verdict).
    let engine = TrustWpVerificationEngine::new();
    let evidence = engine.verify(&bundle, &bundle.obligations);
    let Some(row) = evidence.into_iter().find(|row| row.obligation_id == obligation_id) else {
        return VerificationResult::Unknown {
            solver: solver_name.into(),
            time_ms: 0,
            reason: "trust-wp native engine returned no evidence row for the routed VC \
                     (synthetic carrier failed bundle validation); fail-closed"
                .to_string(),
        };
    };

    match row.status {
        EvidenceStatus::Proved => {
            // Only checked native replay evidence with publication-grade
            // deductive strength may become a router `Proved`. Anything weaker
            // is DOWNGRADED — a Proved row without that grade would be exactly
            // the unaudited-claim channel this flip retired.
            if row.proof_strength.as_ref() == Some(&trust_verifier_api::ProofStrength::deductive())
                && row.is_unbounded_proof()
            {
                VerificationResult::Proved {
                    solver: solver_name.into(),
                    time_ms: 0,
                    strength: ProofStrength::deductive(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                }
            } else {
                VerificationResult::Unknown {
                    solver: solver_name.into(),
                    time_ms: 0,
                    reason: format!(
                        "trust-wp native evidence reported Proved without publication-grade \
                         deductive strength and checked replay artifacts; downgraded fail-closed \
                         (strength: {:?})",
                        row.proof_strength
                    ),
                }
            }
        }
        // A refutation from the native lane is a real bug report: the typed
        // claim (¬violation) was refuted, i.e. the violation is satisfiable —
        // the same SAT-of-violation meaning every backend on this route uses.
        // The API counterexample payload has no lossless representation in
        // `trust_types::Counterexample` assignments, so it is omitted rather
        // than approximated (the retired subprocess lane also carried `None`).
        EvidenceStatus::Failed => VerificationResult::Failed {
            solver: solver_name.into(),
            time_ms: 0,
            counterexample: None,
        },
        EvidenceStatus::Timeout => {
            VerificationResult::Timeout { solver: solver_name.into(), timeout_ms }
        }
        EvidenceStatus::Unsupported | EvidenceStatus::Unknown | EvidenceStatus::Canceled => {
            VerificationResult::Unknown {
                solver: solver_name.into(),
                time_ms: 0,
                reason: summarize_native_diagnostics(&row.diagnostics),
            }
        }
        // `EvidenceStatus` is #[non_exhaustive] for dependents: any future
        // status stays fail-closed here.
        _ => VerificationResult::Unknown {
            solver: solver_name.into(),
            time_ms: 0,
            reason: "trust-wp native engine returned an unrecognized evidence status; fail-closed"
                .to_string(),
        },
    }
}

fn source_location_from_span(span: &trust_types::SourceSpan) -> SourceLocation {
    SourceLocation {
        file: (!span.file.trim().is_empty()).then(|| span.file.clone()),
        line: (span.line_start > 0).then_some(span.line_start),
        column: (span.col_start > 0).then_some(span.col_start),
        end_line: (span.line_end > 0).then_some(span.line_end),
        end_column: (span.col_end > 0).then_some(span.col_end),
    }
}

/// Compress the native engine's diagnostics into one bounded `Unknown` reason,
/// keeping the leading (most specific) lines — the engine puts the actionable
/// blocker first, per v7/D3.
fn summarize_native_diagnostics(diagnostics: &[String]) -> String {
    const MAX_LINES: usize = 3;
    const MAX_BYTES: usize = 1200;
    if diagnostics.is_empty() {
        return "trust-wp native engine returned no diagnostics; fail-closed".to_string();
    }
    let mut reason = String::from("trust-wp native lane fail-closed: ");
    for (index, diagnostic) in diagnostics.iter().take(MAX_LINES).enumerate() {
        if index > 0 {
            reason.push_str(" | ");
        }
        reason.push_str(diagnostic);
        if reason.len() >= MAX_BYTES {
            break;
        }
    }
    if reason.len() > MAX_BYTES {
        // Truncate on a char boundary.
        let mut cut = MAX_BYTES;
        while !reason.is_char_boundary(cut) {
            cut -= 1;
        }
        reason.truncate(cut);
        reason.push_str(" …");
    }
    reason
}

#[cfg(test)]
mod tests {
    use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationResult};

    use super::*;

    /// A bare VC with no contract metadata (like the sep-engine's safety VCs).
    fn vc(kind: VcKind, formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// A contract-bearing VC (carries an `ensures`), i.e. genuinely trust-wp's lane.
    fn contract_vc(kind: VcKind, formula: Formula) -> VerificationCondition {
        let md = ContractMetadata { has_ensures: true, ..ContractMetadata::default() };
        VerificationCondition { contract_metadata: Some(md), ..vc(kind, formula) }
    }

    #[test]
    fn name_and_role_advertise_deductive() {
        let b = TrustWpRouterBackend::new();
        assert_eq!(b.name(), "trust-wp");
        assert!(matches!(b.role(), BackendRole::Deductive));
    }

    #[test]
    fn can_handle_only_contract_bearing_obligations() {
        let b = TrustWpRouterBackend::new();
        // Contract kind WITH contract metadata: trust-wp's lane.
        assert!(b.can_handle(&contract_vc(VcKind::Postcondition, Formula::Bool(true))));
        assert!(b.can_handle(&contract_vc(
            VcKind::Assertion { message: "x".into() },
            Formula::Bool(true)
        )));
        // NON-REGRESSION: a contract-shaped VC with NO metadata (a bare sep-engine
        // assertion) must be DECLINED, so ay keeps handling it.
        assert!(!b.can_handle(&vc(VcKind::Postcondition, Formula::Bool(true))));
        assert!(!b.can_handle(&vc(VcKind::Assertion { message: "x".into() }, Formula::Bool(true))));
        // A raw bounds VC is never trust-wp's lane regardless of metadata.
        assert!(!b.can_handle(&vc(
            VcKind::CopyBoundsViolation {
                callee: "from_raw_parts".into(),
                direction: "src".into(),
                detail: String::new(),
            },
            Formula::Bool(true)
        )));
    }

    #[test]
    fn constant_false_violation_proves_without_solver() {
        // `vc.formula` is the VIOLATION: Bool(false) violation is UNSAT, so the
        // property holds => Proved (canonical convention, constant_folder.rs:109).
        let b = TrustWpRouterBackend::new();
        let r = b.verify(&contract_vc(VcKind::Postcondition, Formula::Bool(false)));
        assert!(matches!(r, VerificationResult::Proved { .. }), "got {r:?}");
    }

    #[test]
    fn constant_true_violation_fails_without_solver() {
        // Bool(true) violation always holds => property fails => Failed. This is
        // the case the previously-inverted polarity reported as a vacuous PROVED.
        let b = TrustWpRouterBackend::new();
        let r = b.verify(&contract_vc(VcKind::Postcondition, Formula::Bool(true)));
        assert!(matches!(r, VerificationResult::Failed { .. }), "got {r:?}");
        assert!(
            !matches!(r, VerificationResult::Proved { .. }),
            "an always-violated obligation must NEVER be Proved (vacuous): got {r:?}"
        );
    }

    #[test]
    fn declined_kind_is_unknown_not_false() {
        let b = TrustWpRouterBackend::new();
        let r = b.verify(&vc(
            VcKind::CopyBoundsViolation {
                callee: "from_raw_parts".into(),
                direction: "src".into(),
                detail: String::new(),
            },
            Formula::Bool(true),
        ));
        assert!(matches!(r, VerificationResult::Unknown { .. }), "got {r:?}");
    }

    #[test]
    fn bare_assertion_without_contract_is_declined() {
        // The sep-engine emits VcKind::Assertion safety VCs with no contract
        // metadata; trust-wp must return Unknown (decline), never Failed, so it
        // cannot collide with ay's verdict in the aggregator.
        let b = TrustWpRouterBackend::new();
        let r = b.verify(&vc(
            VcKind::Assertion { message: "[unsafe:sep:alloc] null check".into() },
            Formula::Bool(false),
        ));
        assert!(matches!(r, VerificationResult::Unknown { .. }), "got {r:?}");
    }

    #[test]
    fn native_lane_is_fail_closed_for_symbolic_goals() {
        // A symbolic (non-constant) contract VC must go to the native engine
        // and come back Unknown until real native replay evidence exists —
        // never Proved from a synthetic carrier, never a subprocess verdict.
        let b = TrustWpRouterBackend::new();
        let r = b.verify(&contract_vc(
            VcKind::Postcondition,
            Formula::Not(Box::new(Formula::Var("ok".into(), Sort::Bool))),
        ));
        let VerificationResult::Unknown { reason, .. } = &r else {
            panic!("symbolic goal must be Unknown on the bare per-VC carrier, got {r:?}");
        };
        // v7/D3: the refusal carries the engine's actionable blocker, not a
        // bare "unsupported".
        assert!(
            reason.contains("trust-wp native lane fail-closed"),
            "reason must carry the native engine diagnostics: {reason}"
        );
    }

    #[test]
    fn lowers_arithmetic_goals_fail_closed_not_false_proved() {
        // `4 * len > 64` (a byte-extent bounds obligation): the retired string
        // lane lowered this for the subprocess; the native lane REFUSES
        // arithmetic (#29 amendment — unbounded-Int would false-prove
        // `(x+1) > x` at u64::MAX) and must land on Unknown, never Proved.
        let f = Formula::Gt(
            Box::new(Formula::Mul(
                Box::new(Formula::Int(4)),
                Box::new(Formula::Var("len".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(64)),
        );
        let b = TrustWpRouterBackend::new();
        let r = b.verify(&contract_vc(VcKind::Postcondition, f));
        assert!(matches!(r, VerificationResult::Unknown { .. }), "got {r:?}");
    }
}
