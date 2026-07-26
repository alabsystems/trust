// trust-router/src/trust_wp_backend.rs: trust-wp deductive backend for the
// per-VC router.
//
// Registers trust-wp (weakest-precondition / strongest-postcondition deductive
// verification, layered on ay) as a first-class `VerificationBackend` so the
// compiler's router dispatches contract/assertion obligations to it instead of
// approximating deductive reasoning in the SMT layer alone. Ported from the
// proven `trust-strengthen/src/trust_wp_oracle.rs` template (which already
// drives trust-wp through the CEGIS loop), with arithmetic lowering added so
// bounds obligations carrying `+`/`-`/`*` (e.g. the byte-extent slice/copy
// obligations) translate.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use trust_types::{
    ContractMetadata, Formula, ProofStrength, VcKind, VerificationCondition, VerificationResult,
};
use trust_wp::{Contract, ContractSet, TrustWpConfig, TrustWpLibError, verify_with_contracts};

use crate::{BackendRole, VerificationBackend, unsupported_mir_unknown};

/// Router backend delegating to trust-wp's deductive engine.
///
/// trust-wp understands Rust ownership and contracts natively, and its
/// strongest-postcondition reasoning discharges obligations that need an
/// invariant the pure-SMT path cannot synthesize (e.g. a struct invariant
/// relating a pointer field to a length field). It is the right home for
/// contract/assertion VCs; non-contract VCs fall through to other backends.
pub struct TrustWpRouterBackend {
    config: TrustWpConfig,
}

impl TrustWpRouterBackend {
    const NAME: &'static str = "trust-wp";

    /// Create a backend with trust-wp's default configuration.
    #[must_use]
    pub fn new() -> Self {
        Self { config: TrustWpConfig::new() }
    }

    /// Create a backend with a per-obligation timeout (milliseconds).
    #[must_use]
    pub fn with_timeout(timeout_ms: u64) -> Self {
        Self { config: TrustWpConfig::new().with_timeout(timeout_ms) }
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

        let Some(contracts) = vc_to_trust_wp_contracts(vc) else {
            return VerificationResult::Unknown {
                solver: self.name().into(),
                time_ms: 0,
                reason: "trust-wp cannot translate this VC formula to contracts".into(),
            };
        };

        match verify_with_contracts(vc.function.as_ref(), &contracts, &self.config) {
            Ok(result) => result.to_verification_result(),
            Err(TrustWpLibError::Timeout { timeout_ms }) => {
                VerificationResult::Timeout { solver: self.name().into(), timeout_ms }
            }
            Err(err) => VerificationResult::Unknown {
                solver: self.name().into(),
                time_ms: 0,
                reason: format!("trust-wp unavailable or inconclusive: {err}"),
            },
        }
    }
}

/// Build a trust-wp contract set from a VC, mapping the obligation's kind to the
/// appropriate clause (requires / ensures / invariant).
fn vc_to_trust_wp_contracts(vc: &VerificationCondition) -> Option<ContractSet> {
    // `vc.formula` is the VIOLATION; the contract clause must assert the PROPERTY
    // (`¬violation`), so it stays consistent with the constant short-circuit above
    // and the violation convention. Lowering the raw violation would ask trust-wp
    // to prove the violation HOLDS — the inverted polarity.
    let goal = Formula::Not(Box::new(vc.formula.clone()));
    let expr = formula_to_trust_wp_expr(&goal)?;
    let contracts = match &vc.kind {
        VcKind::Precondition { .. } => ContractSet::new().with_requires(Contract::requires(expr)),
        VcKind::Postcondition => ContractSet::new().with_ensures(Contract::ensures(expr)),
        VcKind::Assertion { message } if message.contains("[loop:invariant]") => {
            ContractSet::new().with_invariant(Contract::invariant(expr))
        }
        VcKind::Assertion { .. } => ContractSet::new().with_ensures(Contract::ensures(expr)),
        _ => return None,
    };
    Some(contracts)
}

/// Lower a `Formula` to trust-wp's contract expression syntax. Returns `None`
/// for any construct trust-wp's surface cannot express, so the caller stays
/// fail-closed (`Unknown`) rather than asserting a wrong contract.
fn formula_to_trust_wp_expr(formula: &Formula) -> Option<String> {
    match formula {
        Formula::Bool(true) => Some("true".to_string()),
        Formula::Bool(false) => Some("false".to_string()),
        // A variable name is valid both as a boolean atom and inside an
        // arithmetic subexpression.
        Formula::Var(name, _) => Some(name.clone()),
        Formula::Not(inner) => Some(format!("!({})", formula_to_trust_wp_expr(inner)?)),
        Formula::And(terms) => terms
            .iter()
            .map(formula_to_trust_wp_expr)
            .collect::<Option<Vec<_>>>()
            .map(|terms| terms.join(" && ")),
        Formula::Or(terms) => terms
            .iter()
            .map(formula_to_trust_wp_expr)
            .collect::<Option<Vec<_>>>()
            .map(|terms| terms.join(" || ")),
        Formula::Implies(lhs, rhs) => Some(format!(
            "({}) ==> ({})",
            formula_to_trust_wp_expr(lhs)?,
            formula_to_trust_wp_expr(rhs)?
        )),
        Formula::Eq(lhs, rhs) => Some(format!(
            "({}) == ({})",
            formula_to_trust_wp_expr(lhs)?,
            formula_to_trust_wp_expr(rhs)?
        )),
        Formula::Lt(lhs, rhs) => Some(format!(
            "({}) < ({})",
            formula_to_trust_wp_expr(lhs)?,
            formula_to_trust_wp_expr(rhs)?
        )),
        Formula::Le(lhs, rhs) => Some(format!(
            "({}) <= ({})",
            formula_to_trust_wp_expr(lhs)?,
            formula_to_trust_wp_expr(rhs)?
        )),
        Formula::Gt(lhs, rhs) => Some(format!(
            "({}) > ({})",
            formula_to_trust_wp_expr(lhs)?,
            formula_to_trust_wp_expr(rhs)?
        )),
        Formula::Ge(lhs, rhs) => Some(format!(
            "({}) >= ({})",
            formula_to_trust_wp_expr(lhs)?,
            formula_to_trust_wp_expr(rhs)?
        )),
        // Arithmetic — needed so byte-extent bounds obligations (`stride * len`,
        // `offset + len`) translate, not just pure-boolean contracts.
        Formula::Add(lhs, rhs) => Some(format!(
            "({}) + ({})",
            formula_to_trust_wp_expr(lhs)?,
            formula_to_trust_wp_expr(rhs)?
        )),
        Formula::Sub(lhs, rhs) => Some(format!(
            "({}) - ({})",
            formula_to_trust_wp_expr(lhs)?,
            formula_to_trust_wp_expr(rhs)?
        )),
        Formula::Mul(lhs, rhs) => Some(format!(
            "({}) * ({})",
            formula_to_trust_wp_expr(lhs)?,
            formula_to_trust_wp_expr(rhs)?
        )),
        Formula::Int(value) => Some(value.to_string()),
        Formula::UInt(value) => Some(value.to_string()),
        _ => None,
    }
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
    fn lowers_arithmetic_byte_extent() {
        // `4 * len > 64` (a byte-extent bounds obligation) must translate, not
        // fall to None.
        let f = Formula::Gt(
            Box::new(Formula::Mul(
                Box::new(Formula::Int(4)),
                Box::new(Formula::Var("len".into(), Sort::Int)),
            )),
            Box::new(Formula::Int(64)),
        );
        let s = formula_to_trust_wp_expr(&f).expect("arithmetic must lower");
        assert!(s.contains('*') && s.contains('>') && s.contains("len") && s.contains("64"));
    }
}
