// trust-transval: Equivalence VC generator
//
// Produces verification conditions proving that target code refines source
// code. Uses trust-transval's vc_core as the authoritative implementation.
//
// Each VC asserts: NOT(source_behavior == target_behavior).
// UNSAT => behaviors are equivalent (refinement holds).
// SAT => a concrete divergence exists (miscompilation).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use crate::error::TransvalError;
use crate::vc_core::generate_refinement_vcs;

/// Generates equivalence verification conditions between source and target.
///
/// Wraps `generate_refinement_vcs` (in `vc_core`) with additional analysis:
/// - Classifies VCs by check kind (control flow, data flow, return, termination)
/// - Provides per-block-pair generation for focused validation
/// - Converts `RefinementVc` to standard `VerificationCondition` for solver dispatch
#[derive(Debug, Clone, Default)]
pub struct EquivalenceVcGenerator {
    /// If true, skip termination checks (useful for known-safe loop transforms).
    pub(crate) skip_termination: bool,
}

impl EquivalenceVcGenerator {
    /// Create a new generator with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a generator that skips termination checks.
    #[must_use]
    pub fn skip_termination(mut self) -> Self {
        self.skip_termination = true;
        self
    }

    /// Generate all refinement VCs between source and target.
    ///
    /// Returns standard `VerificationCondition`s ready for solver dispatch.
    pub fn generate(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
        relation: &SimulationRelation,
    ) -> Result<Vec<VerificationCondition>, TransvalError> {
        let refinement_vcs = generate_refinement_vcs(source, target, relation)?;

        let vcs: Vec<VerificationCondition> = refinement_vcs
            .iter()
            .filter(|rvc| {
                if self.skip_termination { rvc.check.kind != CheckKind::Termination } else { true }
            })
            .map(|rvc| rvc.to_vc())
            .collect();

        Ok(vcs)
    }

    /// Generate VCs for a specific source/target block pair.
    ///
    /// Useful for focused validation of a single optimization site.
    pub fn generate_for_block_pair(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
        relation: &SimulationRelation,
        source_block_id: BlockId,
        target_block_id: BlockId,
    ) -> Result<Vec<VerificationCondition>, TransvalError> {
        let all_vcs = self.generate(source, target, relation)?;

        let filtered: Vec<VerificationCondition> = all_vcs
            .into_iter()
            .filter(|vc| {
                // Filter by the block pair encoded in the VC description.
                let desc = vc.kind.description();
                desc.contains(&format!("{source_block_id:?}"))
                    && desc.contains(&format!("{target_block_id:?}"))
            })
            .collect();

        Ok(filtered)
    }

    /// Count VCs by check kind category.
    #[must_use]
    pub fn classify_vcs(vcs: &[VerificationCondition]) -> VcClassification {
        let mut classification = VcClassification::default();
        for vc in vcs {
            let desc = vc.kind.description();
            if desc.contains("ControlFlow") {
                classification.control_flow += 1;
            } else if desc.contains("DataFlow") {
                classification.data_flow += 1;
            } else if desc.contains("ReturnValue") {
                classification.return_value += 1;
            } else if desc.contains("Termination") {
                classification.termination += 1;
            } else {
                classification.other += 1;
            }
        }
        classification
    }
}

/// Counts of VCs by category.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VcClassification {
    pub control_flow: usize,
    pub data_flow: usize,
    pub return_value: usize,
    pub termination: usize,
    pub other: usize,
}

impl VcClassification {
    /// Total number of VCs across all categories.
    #[must_use]
    pub fn total(&self) -> usize {
        self.control_flow + self.data_flow + self.return_value + self.termination + self.other
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn make_function(
        name: &str,
        blocks: Vec<BasicBlock>,
        locals: Vec<LocalDecl>,
        arg_count: usize,
    ) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody { locals, blocks, arg_count, return_ty: Ty::i32() },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn add_pair() -> (VerifiableFunction, VerifiableFunction) {
        let locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None },
            LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
            LocalDecl { index: 3, ty: Ty::i32(), name: None },
        ];
        let blocks = vec![BasicBlock {
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
        }];
        let source = make_function("source", blocks.clone(), locals.clone(), 2);
        let target = make_function("target", blocks, locals, 2);
        (source, target)
    }

    fn identity_relation(func: &VerifiableFunction) -> SimulationRelation {
        SimulationRelation::identity(func)
    }

    #[test]
    fn test_generate_identical_functions_produces_vcs() {
        let (source, target) = add_pair();
        let rel = identity_relation(&source);
        let generator = EquivalenceVcGenerator::new();

        let vcs = generator.generate(&source, &target, &rel).unwrap();
        assert!(!vcs.is_empty(), "identical functions should still produce VCs to check");
    }

    #[test]
    fn test_generate_signature_mismatch_errors() {
        let (source, mut target) = add_pair();
        target.body.arg_count = 5;
        let rel = identity_relation(&source);
        let generator = EquivalenceVcGenerator::new();

        let err = generator.generate(&source, &target, &rel).unwrap_err();
        assert!(matches!(err, TransvalError::SignatureMismatch { .. }));
    }

    #[test]
    fn test_classify_vcs_counts() {
        let (source, target) = add_pair();
        let rel = identity_relation(&source);
        let generator = EquivalenceVcGenerator::new();
        let vcs = generator.generate(&source, &target, &rel).unwrap();

        let classification = EquivalenceVcGenerator::classify_vcs(&vcs);
        assert_eq!(classification.total(), vcs.len());
    }

    #[test]
    fn test_skip_termination_filters_correctly() {
        let (source, target) = add_pair();
        let rel = identity_relation(&source);

        let gen_full = EquivalenceVcGenerator::new();
        let gen_skip = EquivalenceVcGenerator::new().skip_termination();

        let vcs_full = gen_full.generate(&source, &target, &rel).unwrap();
        let vcs_skip = gen_skip.generate(&source, &target, &rel).unwrap();

        assert!(vcs_skip.len() <= vcs_full.len());
    }

    #[test]
    fn test_generate_for_block_pair() {
        let (source, target) = add_pair();
        let rel = identity_relation(&source);
        let generator = EquivalenceVcGenerator::new();

        let vcs = generator
            .generate_for_block_pair(&source, &target, &rel, BlockId(0), BlockId(0))
            .unwrap();
        // All VCs should reference block 0 on both sides.
        for vc in &vcs {
            let desc = vc.kind.description();
            assert!(desc.contains("BlockId(0)"), "VC should reference BlockId(0): {desc}");
        }
    }

    #[test]
    fn test_vc_classification_default_is_zero() {
        let c = VcClassification::default();
        assert_eq!(c.total(), 0);
        assert_eq!(c.control_flow, 0);
        assert_eq!(c.data_flow, 0);
    }
}
