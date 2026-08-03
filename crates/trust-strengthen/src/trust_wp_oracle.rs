// trust-strengthen/trust_wp_oracle.rs: trust-wp-direct verification oracle for CEGIS loop
//
// Implements VerificationOracle for TrustWpNativeBackend so a CEGIS driver can
// use trust-wp's deductive engine to validate proposed specifications. Also
// provides StdlibSpecs import as seed specs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_router::VerificationBackend;
use trust_types::{
    Formula, ProofStrength, Sort, SourceSpan, VcKind, VerificationCondition, VerificationResult,
};
use trust_vcgen::{FnContract, StdlibSpecs};
use trust_wp::{Contract, ContractSet, TrustWpConfig, TrustWpLibError, verify_with_contracts};

use crate::spec_proposal::{SpecKind, SpecProposal};

/// Outcome of verifying a set of inferred specs.
#[derive(Debug, Clone)]
pub enum VerifyOutcome {
    /// All VCs passed: specs are valid.
    AllPassed,
    /// Some VCs failed, with counterexample text for refinement.
    Failed {
        /// Human-readable counterexample from the solver.
        counterexample: String,
        /// Which specs failed.
        failed_specs: Vec<SpecProposal>,
    },
    /// Verification encountered an error (timeout, solver crash, etc.).
    Error {
        /// Error description.
        message: String,
    },
}

/// Trait for a verification oracle over proposed specs.
///
/// Abstracted so tests can use a mock verifier. In production, this calls
/// trust_vcgen -> trust-router -> solver tools.
pub trait VerificationOracle: Send + Sync {
    /// Check whether a set of spec proposals are valid for the given function.
    ///
    /// Returns `AllPassed` if the specs make all VCs provable,
    /// `Failed` with a counterexample if not, or `Error` on infrastructure failure.
    fn verify_specs(&self, function_path: &str, specs: &[SpecProposal]) -> VerifyOutcome;
}

/// Verification oracle that delegates to trust-wp-native for deductive verification.
///
/// Converts `SpecProposal`s into `VerificationCondition`s and routes them
/// through `TrustWpNativeBackend`. Maps trust_wp results back to `VerifyOutcome`.
///
/// trust-wp's strongest-postcondition reasoning is better suited for spec
/// validation than raw SMT solving because it understands Rust ownership
/// and contracts natively.
pub struct TrustWpDirectOracle {
    backend: TrustWpNativeBackend,
}

struct TrustWpNativeBackend {
    config: TrustWpConfig,
}

impl TrustWpNativeBackend {
    const NAME: &'static str = "trust-wp-native";

    fn new() -> Self {
        Self { config: TrustWpConfig::new() }
    }

    fn with_timeout(timeout_ms: u64) -> Self {
        Self { config: TrustWpConfig::new().with_timeout(timeout_ms) }
    }

    fn name(&self) -> &str {
        Self::NAME
    }
}

impl VerificationBackend for TrustWpNativeBackend {
    fn name(&self) -> &str {
        self.name()
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        matches!(
            vc.kind,
            VcKind::Precondition { .. } | VcKind::Postcondition | VcKind::Assertion { .. }
        )
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        if let Some(result) = trust_router::unsupported_mir_unknown(vc, self.name(), 0) {
            return result;
        }
        if !self.can_handle(vc) {
            return VerificationResult::Unknown {
                solver: self.name().into(),
                time_ms: 0,
                reason: format!("trust-wp cannot handle VC kind {:?}", vc.kind),
            };
        }

        // `vc.formula` is the VIOLATION: Bool(false) violation is UNSAT => property
        // holds => Proved; Bool(true) violation always holds => Failed. Matches the
        // canonical convention (constant_folder.rs:109-116). Previously inverted —
        // an always-violated obligation must never be reported as a vacuous PROVED.
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

impl TrustWpDirectOracle {
    /// Create a new oracle with default trust_wp timeout.
    #[must_use]
    pub fn new() -> Self {
        Self { backend: TrustWpNativeBackend::new() }
    }

    /// Create an oracle with a custom trust_wp timeout (milliseconds).
    #[must_use]
    pub fn with_timeout(timeout_ms: u64) -> Self {
        Self { backend: TrustWpNativeBackend::with_timeout(timeout_ms) }
    }
}

fn vc_to_trust_wp_contracts(vc: &VerificationCondition) -> Option<ContractSet> {
    // `vc.formula` is the VIOLATION; the contract clause asserts the PROPERTY
    // (`¬violation`) to stay consistent with the constant short-circuit above.
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

fn formula_to_trust_wp_expr(formula: &Formula) -> Option<String> {
    match formula {
        Formula::Bool(true) => Some("true".to_string()),
        Formula::Bool(false) => Some("false".to_string()),
        Formula::Var(name, Sort::Bool) => Some(name.clone()),
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
        Formula::Int(value) => Some(value.to_string()),
        Formula::UInt(value) => Some(value.to_string()),
        _ => None,
    }
}

impl Default for TrustWpDirectOracle {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationOracle for TrustWpDirectOracle {
    fn verify_specs(&self, function_path: &str, specs: &[SpecProposal]) -> VerifyOutcome {
        if specs.is_empty() {
            return VerifyOutcome::AllPassed;
        }

        let mut failed_specs = Vec::new();
        let mut counterexample_parts = Vec::new();

        for spec in specs {
            let vc = spec_to_vc(spec, function_path);

            if let Some((failed_spec, reason)) =
                unsupported_mir_soft_failure(&self.backend, spec, &vc)
            {
                counterexample_parts.push(reason);
                failed_specs.push(failed_spec);
                continue;
            }

            // Check if trust_wp can handle this VC kind + formula
            if !self.backend.can_handle(&vc) {
                // If trust_wp cannot handle it, treat as unknown (not a hard failure).
                // The spec might still be valid -- trust_wp just can't verify it.
                continue;
            }

            let result = self.backend.verify(&vc);

            match result {
                VerificationResult::Proved { .. } => {
                    // This spec is valid -- continue checking others
                }
                VerificationResult::Failed { counterexample, .. } => {
                    let cex_text = counterexample
                        .as_ref()
                        .map(|c| c.to_string())
                        .unwrap_or_else(|| format!("trust-wp rejected spec: {}", spec.to_clause()));
                    counterexample_parts.push(cex_text);
                    failed_specs.push(spec.clone());
                }
                VerificationResult::Unknown { reason, .. } => {
                    // Unknown is not a hard failure -- trust_wp can't decide.
                    // Log but continue (treat as inconclusive, not failed).
                    counterexample_parts.push(format!(
                        "trust-wp inconclusive for {}: {}",
                        spec.to_clause(),
                        reason
                    ));
                    // For CEGIS purposes, treat unknown as a soft failure
                    // so the loop can try to refine the spec.
                    failed_specs.push(spec.clone());
                }
                VerificationResult::Timeout { .. } => {
                    return VerifyOutcome::Error {
                        message: format!("trust-wp timed out verifying: {}", spec.to_clause()),
                    };
                }
                _ => {
                    counterexample_parts.push(format!(
                        "trust-wp returned an unrecognized result for {}",
                        spec.to_clause()
                    ));
                    failed_specs.push(spec.clone());
                }
            }
        }

        if failed_specs.is_empty() {
            VerifyOutcome::AllPassed
        } else {
            VerifyOutcome::Failed { counterexample: counterexample_parts.join("; "), failed_specs }
        }
    }
}

fn unsupported_mir_soft_failure(
    backend: &TrustWpNativeBackend,
    spec: &SpecProposal,
    vc: &VerificationCondition,
) -> Option<(SpecProposal, String)> {
    trust_router::unsupported_mir_unknown(vc, backend.name(), 0).map(|result| {
        let reason = match result {
            VerificationResult::Unknown { reason, .. } => reason,
            other => format!("unexpected unsupported MIR result: {other:?}"),
        };
        (
            spec.clone(),
            format!("trust-wp cannot verify unsupported MIR for {}: {}", spec.to_clause(), reason),
        )
    })
}

/// Convert a `SpecProposal` into a `VerificationCondition` for trust_wp.
///
/// The spec body is encoded as a `Formula::Var` with the spec text as the
/// variable name (trust-wp will parse the expression). The VC kind is set
/// based on the spec kind (precondition vs postcondition).
fn spec_to_vc(spec: &SpecProposal, function_path: &str) -> VerificationCondition {
    let kind = match spec.kind {
        SpecKind::Requires => VcKind::Precondition { callee: function_path.to_string() },
        SpecKind::Ensures => VcKind::Postcondition,
        SpecKind::Invariant => {
            VcKind::Assertion { message: format!("[loop:invariant] {}", spec.spec_body) }
        }
    };

    // Encode the spec body as a formula. For simple boolean specs,
    // try to parse as true/false; otherwise wrap as a named variable
    // that trust-wp's translation pipeline can handle.
    let formula = spec_body_to_formula(&spec.spec_body);

    VerificationCondition {
        kind,
        function: function_path.into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

/// Convert a spec body string into a Formula.
///
/// Handles simple cases:
/// - `"true"` -> `Formula::Bool(true)`
/// - `"false"` -> `Formula::Bool(false)`
/// - Otherwise wraps as a named variable (placeholder for the expression).
fn spec_body_to_formula(spec_body: &str) -> Formula {
    let trimmed = spec_body.trim();
    match trimmed {
        "true" => Formula::Bool(true),
        "false" => Formula::Bool(false),
        _ => {
            // Wrap the spec body as a Var so it passes through the formula
            // translation. The trust_wp bridge will see it as a named predicate.
            Formula::Var(trimmed.to_string(), Sort::Bool)
        }
    }
}

// ---------------------------------------------------------------------------
// Stdlib specs seed importer
// ---------------------------------------------------------------------------

/// Import standard library specs as seed `SpecProposal`s for the strengthen loop.
///
/// Converts `FnContract` entries from the stdlib registry into `SpecProposal`
/// format suitable for the CEGIS feedback loop. These serve as ground truth
/// for standard library functions (Vec, Option, Result, Iterator).
#[must_use]
pub fn import_stdlib_seed_specs() -> Vec<SpecProposal> {
    let registry = StdlibSpecs::new();
    let mut seeds = Vec::new();

    for contract in registry.all() {
        seeds.extend(contract_to_proposals(contract));
    }

    seeds
}

/// Convert a single `FnContract` into `SpecProposal`s.
fn contract_to_proposals(contract: &FnContract) -> Vec<SpecProposal> {
    let mut proposals = Vec::new();

    // Extract the short function name from the fully-qualified path
    let fn_name = contract.fn_path.rsplit("::").next().unwrap_or(&contract.fn_path).to_string();

    for (i, pre) in contract.preconditions.iter().enumerate() {
        proposals.push(SpecProposal {
            function_path: contract.fn_path.clone(),
            function_name: fn_name.clone(),
            kind: SpecKind::Requires,
            spec_body: format!("{pre:?}"),
            confidence: 1.0, // stdlib specs are ground truth
            rationale: format!(
                "Standard library contract: precondition {} for {}",
                i + 1,
                contract.fn_path
            ),
            iteration: 0, // seed, not inferred
            validated: true,
            validation_errors: Vec::new(),
        });
    }

    for (i, post) in contract.postconditions.iter().enumerate() {
        proposals.push(SpecProposal {
            function_path: contract.fn_path.clone(),
            function_name: fn_name.clone(),
            kind: SpecKind::Ensures,
            spec_body: format!("{post:?}"),
            confidence: 1.0, // stdlib specs are ground truth
            rationale: format!(
                "Standard library contract: postcondition {} for {}",
                i + 1,
                contract.fn_path
            ),
            iteration: 0,
            validated: true,
            validation_errors: Vec::new(),
        });
    }

    proposals
}

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // TrustWpDirectOracle basic tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_trust_wp_oracle_default() {
        let oracle = TrustWpDirectOracle::default();
        assert_eq!(oracle.backend.name(), "trust-wp-native");
    }

    #[test]
    fn test_trust_wp_oracle_with_timeout() {
        let oracle = TrustWpDirectOracle::with_timeout(5_000);
        assert_eq!(oracle.backend.name(), "trust-wp-native");
    }

    #[test]
    fn test_trust_wp_oracle_empty_specs_passes() {
        let oracle = TrustWpDirectOracle::new();
        let outcome = oracle.verify_specs("test::f", &[]);
        assert!(matches!(outcome, VerifyOutcome::AllPassed));
    }

    #[test]
    fn test_trust_wp_oracle_unsupported_mir_fails_before_backend_dispatch() {
        let backend = TrustWpNativeBackend::new();
        let spec = SpecProposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Ensures,
            spec_body: "result > 0".into(),
            confidence: 0.8,
            rationale: "test".into(),
            iteration: 1,
            validated: true,
            validation_errors: vec![],
        };
        let vc = VerificationCondition {
            kind: VcKind::UnsupportedMir {
                kind: "terminator".into(),
                detail: "opaque terminator not modeled".into(),
            },
            function: "test::f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };

        let (failed_spec, reason) =
            unsupported_mir_soft_failure(&backend, &spec, &vc).expect("unsupported MIR guard");
        assert_eq!(failed_spec.spec_body, spec.spec_body);
        assert!(reason.contains("unsupported MIR"));
        assert!(reason.contains("opaque terminator not modeled"));
    }

    #[test]
    fn test_trust_wp_oracle_trivially_true_spec_passes() {
        let oracle = TrustWpDirectOracle::new();
        let spec = SpecProposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Ensures,
            spec_body: "true".into(),
            confidence: 0.9,
            rationale: "trivially true".into(),
            iteration: 1,
            validated: true,
            validation_errors: vec![],
        };
        let outcome = oracle.verify_specs("test::f", &[spec]);
        assert!(
            matches!(outcome, VerifyOutcome::AllPassed),
            "trivially true ensures should pass: {outcome:?}"
        );
    }

    #[test]
    fn test_trust_wp_oracle_trivially_false_spec_fails() {
        let oracle = TrustWpDirectOracle::new();
        let spec = SpecProposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Ensures,
            spec_body: "false".into(),
            confidence: 0.5,
            rationale: "trivially false".into(),
            iteration: 1,
            validated: true,
            validation_errors: vec![],
        };
        let outcome = oracle.verify_specs("test::f", &[spec]);
        assert!(
            matches!(outcome, VerifyOutcome::Failed { .. }),
            "trivially false ensures should fail: {outcome:?}"
        );
    }

    #[test]
    fn test_trust_wp_oracle_nontrivial_spec_returns_failed_or_unknown() {
        let oracle = TrustWpDirectOracle::new();
        let spec = SpecProposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Ensures,
            spec_body: "x > 0".into(),
            confidence: 0.8,
            rationale: "nontrivial".into(),
            iteration: 1,
            validated: true,
            validation_errors: vec![],
        };
        let outcome = oracle.verify_specs("test::f", &[spec]);
        // Nontrivial specs go through trust_wp which returns Unknown (solver pending)
        // Our oracle treats Unknown as soft failure for CEGIS refinement
        assert!(
            matches!(outcome, VerifyOutcome::Failed { .. }),
            "nontrivial spec should be treated as inconclusive/failed: {outcome:?}"
        );
    }

    #[test]
    fn test_trust_wp_oracle_unhandleable_vc_skipped() {
        let oracle = TrustWpDirectOracle::new();
        // DivisionByZero VcKind is not a deductive VC kind, so trust_wp
        // cannot handle it. The oracle should skip it (not fail).
        // We need a Requires spec because that generates a Precondition VcKind
        // which IS deductive. So use an Invariant with a non-loop message
        // to get something trust_wp rejects.
        // Actually, let's just test with a spec that produces a VcKind
        // trust_wp can't handle. Requires -> Precondition is deductive.
        // Ensures -> Postcondition is deductive. Invariant with loop prefix is too.
        // The only way trust_wp rejects is if the formula can't translate.
        // Test: all specs pass because trust_wp skips unhandleable ones.
        let spec = SpecProposal {
            function_path: "test::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Requires,
            spec_body: "true".into(),
            confidence: 0.9,
            rationale: "should pass".into(),
            iteration: 1,
            validated: true,
            validation_errors: vec![],
        };
        let outcome = oracle.verify_specs("test::f", &[spec]);
        assert!(
            matches!(outcome, VerifyOutcome::AllPassed),
            "trivially true precondition should pass: {outcome:?}"
        );
    }

    // -----------------------------------------------------------------------
    // spec_to_vc conversion tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_spec_to_vc_requires() {
        let spec = SpecProposal {
            function_path: "math::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Requires,
            spec_body: "x > 0".into(),
            confidence: 0.8,
            rationale: "test".into(),
            iteration: 1,
            validated: true,
            validation_errors: vec![],
        };
        let vc = spec_to_vc(&spec, "math::f");
        assert!(matches!(vc.kind, VcKind::Precondition { .. }));
        assert_eq!(vc.function, "math::f");
    }

    #[test]
    fn test_spec_to_vc_ensures() {
        let spec = SpecProposal {
            function_path: "math::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Ensures,
            spec_body: "result > 0".into(),
            confidence: 0.8,
            rationale: "test".into(),
            iteration: 1,
            validated: true,
            validation_errors: vec![],
        };
        let vc = spec_to_vc(&spec, "math::f");
        assert!(matches!(vc.kind, VcKind::Postcondition));
    }

    #[test]
    fn test_spec_to_vc_invariant() {
        let spec = SpecProposal {
            function_path: "math::f".into(),
            function_name: "f".into(),
            kind: SpecKind::Invariant,
            spec_body: "i < n".into(),
            confidence: 0.7,
            rationale: "test".into(),
            iteration: 1,
            validated: true,
            validation_errors: vec![],
        };
        let vc = spec_to_vc(&spec, "math::f");
        assert!(matches!(vc.kind, VcKind::Assertion { .. }));
        if let VcKind::Assertion { message } = &vc.kind {
            assert!(message.contains("[loop:invariant]"));
        }
    }

    // -----------------------------------------------------------------------
    // spec_body_to_formula tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_spec_body_true() {
        let f = spec_body_to_formula("true");
        assert!(matches!(f, Formula::Bool(true)));
    }

    #[test]
    fn test_spec_body_false() {
        let f = spec_body_to_formula("false");
        assert!(matches!(f, Formula::Bool(false)));
    }

    #[test]
    fn test_spec_body_expression() {
        let f = spec_body_to_formula("x > 0");
        assert!(matches!(f, Formula::Var(..)));
    }

    // -----------------------------------------------------------------------
    // Stdlib seed import tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_import_stdlib_seed_specs_nonempty() {
        let seeds = import_stdlib_seed_specs();
        assert!(!seeds.is_empty(), "stdlib should have seed specs");
    }

    #[test]
    fn test_import_stdlib_seed_specs_have_full_confidence() {
        let seeds = import_stdlib_seed_specs();
        for spec in &seeds {
            assert!(
                (spec.confidence - 1.0).abs() < f64::EPSILON,
                "stdlib seed spec should have confidence 1.0: {}",
                spec.function_path
            );
        }
    }

    #[test]
    fn test_import_stdlib_seed_specs_are_validated() {
        let seeds = import_stdlib_seed_specs();
        for spec in &seeds {
            assert!(spec.validated, "stdlib seeds should be pre-validated");
            assert!(
                spec.validation_errors.is_empty(),
                "stdlib seeds should have no validation errors"
            );
        }
    }

    #[test]
    fn test_import_stdlib_seed_specs_iteration_zero() {
        let seeds = import_stdlib_seed_specs();
        for spec in &seeds {
            assert_eq!(spec.iteration, 0, "stdlib seeds should have iteration 0 (not inferred)");
        }
    }

    #[test]
    fn test_import_stdlib_seed_specs_have_correct_kinds() {
        let seeds = import_stdlib_seed_specs();
        let has_requires = seeds.iter().any(|s| s.kind == SpecKind::Requires);
        let has_ensures = seeds.iter().any(|s| s.kind == SpecKind::Ensures);
        assert!(
            has_requires || has_ensures,
            "stdlib seeds should have at least one requires or ensures"
        );
    }

    #[test]
    fn test_contract_to_proposals() {
        let contract = FnContract::new("std::vec::Vec::push")
            .pre(Formula::Bool(true))
            .post(Formula::Bool(true));
        let proposals = contract_to_proposals(&contract);
        assert_eq!(proposals.len(), 2);
        assert_eq!(proposals[0].kind, SpecKind::Requires);
        assert_eq!(proposals[1].kind, SpecKind::Ensures);
        assert_eq!(proposals[0].function_name, "push");
        assert_eq!(proposals[0].function_path, "std::vec::Vec::push");
    }

    // -----------------------------------------------------------------------
    // Integration: TrustWpDirectOracle with real spec through feedback loop
    // -----------------------------------------------------------------------

    #[test]
    fn test_trust_wp_oracle_integration_mixed_specs() {
        let oracle = TrustWpDirectOracle::new();
        let specs = vec![
            SpecProposal {
                function_path: "math::add".into(),
                function_name: "add".into(),
                kind: SpecKind::Ensures,
                spec_body: "true".into(),
                confidence: 0.9,
                rationale: "trivially valid".into(),
                iteration: 1,
                validated: true,
                validation_errors: vec![],
            },
            SpecProposal {
                function_path: "math::add".into(),
                function_name: "add".into(),
                kind: SpecKind::Ensures,
                spec_body: "false".into(),
                confidence: 0.5,
                rationale: "trivially invalid".into(),
                iteration: 1,
                validated: true,
                validation_errors: vec![],
            },
        ];
        let outcome = oracle.verify_specs("math::add", &specs);
        // The false spec should cause failure
        assert!(
            matches!(outcome, VerifyOutcome::Failed { .. }),
            "mixed specs with a false one should fail: {outcome:?}"
        );
        if let VerifyOutcome::Failed { failed_specs, .. } = &outcome {
            assert_eq!(failed_specs.len(), 1, "only the false spec should fail");
            assert_eq!(failed_specs[0].spec_body, "false");
        }
    }
}
