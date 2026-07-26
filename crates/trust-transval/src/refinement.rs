// trust-transval: Refinement checker
//
// Orchestrates per-function translation validation by:
// 1. Building a simulation relation (via SimulationRelationBuilder)
// 2. Generating equivalence VCs (via EquivalenceVcGenerator)
// 3. Analyzing results to produce a verdict
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::equivalence::{EquivalenceVcGenerator, VcClassification};
use crate::error::TransvalError;
use crate::simulation::SimulationRelationBuilder;

/// The verdict of a translation validation check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidationVerdict {
    /// All VCs were generated successfully and are ready for solver dispatch.
    /// The actual UNSAT/SAT check happens at the solver layer.
    Validated,

    /// A structural violation was detected without needing a solver.
    ///
    /// For example: target missing a return block that the source has.
    Refuted {
        /// Human-readable explanation of the structural violation.
        reason: String,
    },

    /// Validation could not determine refinement (e.g., unsupported constructs).
    Unknown {
        /// Why the check was inconclusive.
        reason: String,
    },
}

/// The result of a refinement check.
#[derive(Debug, Clone)]
pub struct ValidationResult {
    /// Overall verdict.
    pub verdict: ValidationVerdict,
    /// Total number of checks generated.
    pub checks_total: usize,
    /// Number of checks that are structurally valid (no trivial violations).
    pub checks_passed: usize,
    /// The VCs for solver dispatch.
    pub vcs: Vec<VerificationCondition>,
    /// VC classification breakdown.
    pub classification: VcClassification,
    /// Source function name.
    pub source_function: String,
    /// Target function name.
    pub target_function: String,
}

/// Orchestrates translation validation for a pair of functions.
///
/// Given a source (pre-optimization) and target (post-optimization) function,
/// the checker:
/// 1. Infers or uses a provided simulation relation
/// 2. Generates verification conditions
/// 3. Classifies the result as Validated, Refuted, or Unknown
///
/// Note: "Validated" means VCs were generated successfully and contain no
/// trivial violations (like `Formula::Bool(true)`). The actual proof requires
/// dispatching VCs to a solver (ay) and confirming all are UNSAT.
#[derive(Debug, Clone, Default)]
pub struct RefinementChecker {
    /// If set, skip termination checks.
    skip_termination: bool,
}

impl RefinementChecker {
    /// Create a new checker with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Skip termination checks (for known loop-safe optimizations).
    #[must_use]
    pub fn skip_termination(mut self) -> Self {
        self.skip_termination = true;
        self
    }

    /// Check that `target` refines `source`.
    ///
    /// Automatically infers a simulation relation from the function structure.
    pub fn check(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<ValidationResult, TransvalError> {
        let builder = SimulationRelationBuilder::new();
        // Name/type-aware relation: maps source locals to target locals by
        // (name, ty), falling back to positional identity for unnamed/unmatched
        // locals. A strict generalization of build_from_functions — identical when
        // layouts coincide (same-function translation validation), but correct for
        // the general case where a TS-image and a Rust-image share observable names
        // yet lay out locals differently (positional mapping would be vacuous).
        let relation = builder.build_by_name(source, target)?;
        self.check_with_relation(source, target, &relation)
    }

    /// Check that `target` refines `source` using a provided simulation relation.
    pub fn check_with_relation(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
        relation: &SimulationRelation,
    ) -> Result<ValidationResult, TransvalError> {
        let mut generator = EquivalenceVcGenerator::new();
        if self.skip_termination {
            generator = generator.skip_termination();
        }

        let vcs = generator.generate(source, target, relation)?;
        let classification = EquivalenceVcGenerator::classify_vcs(&vcs);
        let checks_total = vcs.len();

        // Count structural violations: VCs with `Formula::Bool(true)` are
        // trivially SAT under the refinement-violation VC convention.
        let trivial_violations =
            vcs.iter().filter(|vc| matches!(vc.formula, Formula::Bool(true))).count();

        let checks_passed = checks_total - trivial_violations;

        let verdict = if trivial_violations > 0 {
            ValidationVerdict::Refuted {
                reason: format!("{trivial_violations} structural violation(s) detected"),
            }
        } else if checks_total == 0 {
            ValidationVerdict::Unknown { reason: "no verification conditions generated".into() }
        } else {
            ValidationVerdict::Validated
        };

        Ok(ValidationResult {
            verdict,
            checks_total,
            checks_passed,
            vcs,
            classification,
            source_function: source.name.clone(),
            target_function: target.name.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn simple_add(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                    LocalDecl { index: 3, ty: Ty::i32(), name: None },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(1)),
                                Operand::Copy(Place::local(2)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                }],
                arg_count: 2,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_check_identical_functions_validates() {
        let source = simple_add("source");
        let target = simple_add("target");
        let checker = RefinementChecker::new();

        let result = checker.check(&source, &target).unwrap();
        assert_eq!(result.verdict, ValidationVerdict::Validated);
        assert!(result.checks_total > 0);
        assert_eq!(result.checks_passed, result.checks_total);
    }

    #[test]
    fn test_check_signature_mismatch() {
        let source = simple_add("source");
        let mut target = simple_add("target");
        target.body.arg_count = 5;

        let checker = RefinementChecker::new();
        let err = checker.check(&source, &target).unwrap_err();
        assert!(matches!(err, TransvalError::SignatureMismatch { .. }));
    }

    #[test]
    fn test_check_empty_source() {
        let mut source = simple_add("source");
        source.body.blocks.clear();
        let target = simple_add("target");

        let checker = RefinementChecker::new();
        let err = checker.check(&source, &target).unwrap_err();
        assert!(matches!(err, TransvalError::EmptyBody(_)));
    }

    #[test]
    fn test_check_with_relation_custom() {
        let source = simple_add("source");
        let target = simple_add("target");
        let relation = SimulationRelationBuilder::build_identity(&source);
        let checker = RefinementChecker::new();

        let result = checker.check_with_relation(&source, &target, &relation).unwrap();
        assert_eq!(result.verdict, ValidationVerdict::Validated);
        assert_eq!(result.source_function, "source");
        assert_eq!(result.target_function, "target");
    }

    #[test]
    fn test_check_with_modified_target_return() {
        let source = simple_add("source");
        let mut target = simple_add("target");
        // Change target's return block terminator to Unreachable.
        target.body.blocks[0].terminator = Terminator::Unreachable;

        let checker = RefinementChecker::new();
        let result = checker.check(&source, &target).unwrap();
        // Source returns but target doesn't => structural violation.
        assert!(
            matches!(result.verdict, ValidationVerdict::Refuted { .. }),
            "got: {:?}",
            result.verdict
        );
    }

    #[test]
    fn test_skip_termination_option() {
        let source = simple_add("source");
        let target = simple_add("target");

        let checker_full = RefinementChecker::new();
        let checker_skip = RefinementChecker::new().skip_termination();

        let result_full = checker_full.check(&source, &target).unwrap();
        let result_skip = checker_skip.check(&source, &target).unwrap();

        assert!(result_skip.checks_total <= result_full.checks_total);
    }

    #[test]
    fn test_classification_in_result() {
        let source = simple_add("source");
        let target = simple_add("target");
        let checker = RefinementChecker::new();

        let result = checker.check(&source, &target).unwrap();
        assert_eq!(result.classification.total(), result.checks_total);
    }
}
