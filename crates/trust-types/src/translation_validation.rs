// trust-types: Translation validation shared types
//
// Core types for translation validation — proving that compiled code
// (post-optimization MIR or machine code) refines pre-optimization MIR semantics.
//
// These types live in trust-types so both trust_vcgen and trust-transval
// (the authoritative translation validation crate) can use them without
// circular dependencies.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use crate::fx::FxHashMap;

use crate::{
    BlockId, Formula, Sort, SortFromTy, SourceSpan, Ty, VcKind, VerifiableBody,
    VerifiableFunction, VerificationCondition,
};

// The translation-validation *data records* (CheckKind, TranslationCheck,
// RefinementVc) live in trust-ir-contract (shared cross-repo vocabulary).
// Re-exported so `trust_types::translation_validation::*` is unchanged. The
// machinery over them (SimulationRelation, the MIR-walking helpers, and
// `RefinementVc::to_vc` below) stays here — it needs the full MIR/VC layer and
// is not part of the cross-repo contract.
pub use trust_ir_contract::translation_validation::{CheckKind, RefinementVc, TranslationCheck};

/// Error type for translation validation operations.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum TranslationValidationError {
    /// Source and target functions have incompatible signatures.
    #[error("signature mismatch: source has {source_args} args, target has {target_args}")]
    SignatureMismatch { source_args: usize, target_args: usize },

    /// A source block has no corresponding target block in the simulation relation.
    #[error("unmapped source block {0:?} has no target correspondence")]
    UnmappedBlock(BlockId),

    /// The simulation relation is invalid (e.g., maps to nonexistent blocks).
    #[error("invalid simulation relation: {0}")]
    InvalidRelation(String),

    /// Source or target function body is empty.
    #[error("empty function body: {0}")]
    EmptyBody(String),

    /// Target block does not exist (typed variant replaces InvalidRelation format string).
    #[error("target block {block:?} does not exist in target function")]
    InvalidTargetBlock { block: BlockId },

    /// Target local index out of range (typed variant replaces InvalidRelation format string).
    #[error("target local index {index} out of range (target has {num_locals} locals)")]
    InvalidTargetLocal { index: usize, num_locals: usize },
}

// `TranslationCheck` and `CheckKind` are defined in trust-ir-contract and
// re-exported above.

/// A simulation relation mapping source program points and variables to target ones.
///
/// This is the "glue" between source (pre-optimization MIR) and target
/// (post-optimization MIR or machine code). A valid simulation relation must:
///   1. Map every reachable source block to at least one target block.
///   2. Map source locals to target locals (or expressions over target locals).
///   3. Preserve the entry and return points.
#[derive(Debug, Clone)]
pub struct SimulationRelation {
    /// Maps source block IDs to target block IDs.
    pub block_map: FxHashMap<BlockId, BlockId>,
    /// Maps source local variable indices to target local variable indices.
    pub variable_map: FxHashMap<usize, usize>,
    /// Optional: maps source locals to target formula expressions (for
    /// optimizations that restructure variables, e.g., constant folding).
    pub expression_map: FxHashMap<usize, Formula>,
}

impl SimulationRelation {
    /// Create a new empty simulation relation.
    #[must_use]
    pub fn new() -> Self {
        Self {
            block_map: FxHashMap::default(),
            variable_map: FxHashMap::default(),
            expression_map: FxHashMap::default(),
        }
    }

    /// Create an identity simulation relation for a function.
    ///
    /// Maps each block and variable to itself. Used as a starting point
    /// or for validating trivial transformations.
    #[must_use]
    pub fn identity(func: &VerifiableFunction) -> Self {
        let block_map: FxHashMap<BlockId, BlockId> =
            func.body.blocks.iter().map(|bb| (bb.id, bb.id)).collect();

        let variable_map: FxHashMap<usize, usize> =
            func.body.locals.iter().map(|local| (local.index, local.index)).collect();

        Self { block_map, variable_map, expression_map: FxHashMap::default() }
    }

    /// Validate that the simulation relation is well-formed with respect to
    /// source and target functions.
    pub fn validate(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<(), TranslationValidationError> {
        // Check that all source blocks have a mapping.
        for block in &source.body.blocks {
            if !self.block_map.contains_key(&block.id) {
                return Err(TranslationValidationError::UnmappedBlock(block.id));
            }
        }

        // Check that all mapped target blocks actually exist.
        let target_block_ids: Vec<BlockId> = target.body.blocks.iter().map(|bb| bb.id).collect();
        for target_id in self.block_map.values() {
            if !target_block_ids.contains(target_id) {
                return Err(TranslationValidationError::InvalidTargetBlock { block: *target_id });
            }
        }

        // Check that mapped variables exist in the target.
        for target_idx in self.variable_map.values() {
            if *target_idx >= target.body.locals.len() {
                return Err(TranslationValidationError::InvalidTargetLocal {
                    index: *target_idx,
                    num_locals: target.body.locals.len(),
                });
            }
        }

        Ok(())
    }

    /// Look up the target expression for a source local.
    ///
    /// Prefers `expression_map` (for optimized representations), falls back
    /// to `variable_map` (direct local-to-local mapping).
    #[must_use]
    pub fn resolve_variable(
        &self,
        source_local: usize,
        target: &VerifiableFunction,
    ) -> Option<Formula> {
        // Check expression map first (handles constant folding, etc.)
        if let Some(expr) = self.expression_map.get(&source_local) {
            return Some(expr.clone());
        }

        // Fall back to direct variable mapping.
        if let Some(&target_local) = self.variable_map.get(&source_local) {
            let decl = target.body.locals.get(target_local)?;
            let fallback = format!("_{}", target_local);
            let name = decl.name.as_deref().unwrap_or(&fallback);
            let sort = match &decl.ty {
                Ty::Bool => Sort::Bool,
                Ty::Int { .. } => Sort::Int,
                other => Sort::from_ty(other),
            };
            return Some(Formula::Var(name.to_string(), sort));
        }

        None
    }
}

impl Default for SimulationRelation {
    fn default() -> Self {
        Self::new()
    }
}

// `RefinementVc` is defined in trust-ir-contract and re-exported above. Its
// `to_vc` lowering lives here (not in the contract crate) because it constructs
// a `VerificationCondition`, which belongs to the full VC layer.

/// Extension trait providing `RefinementVc::to_vc()` — lowering a refinement
/// check to a standard `VerificationCondition` for solver dispatch. Bring into
/// scope (`use trust_types::RefinementVcToVc;`) to call `rvc.to_vc()`.
pub trait RefinementVcToVc {
    /// Convert to a standard `VerificationCondition` for solver dispatch.
    fn to_vc(&self) -> VerificationCondition;
}

impl RefinementVcToVc for RefinementVc {
    fn to_vc(&self) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::RefinementViolation {
                spec_file: self.source_function.clone(),
                action: format!(
                    "{:?} check at source {:?} -> target {:?}",
                    self.check.kind, self.check.source_point, self.check.target_point
                ),
            },
            function: crate::Symbol::intern(&self.target_function),
            location: SourceSpan::default(),
            formula: self.check.formula.clone(),
            contract_metadata: None,
        }
    }
}

/// Infer an identity simulation relation between two functions with the same structure.
///
/// This is a convenience for when source and target have the same block count
/// and local count — common for minor optimizations like constant folding
/// within blocks.
#[must_use]
pub fn infer_identity_relation(
    source: &VerifiableFunction,
    target: &VerifiableFunction,
) -> Option<SimulationRelation> {
    if source.body.blocks.len() != target.body.blocks.len() {
        return None;
    }

    let block_map: FxHashMap<BlockId, BlockId> = source
        .body
        .blocks
        .iter()
        .zip(target.body.blocks.iter())
        .map(|(s, t)| (s.id, t.id))
        .collect();

    let local_count = source.body.locals.len().min(target.body.locals.len());
    let variable_map: FxHashMap<usize, usize> = (0..local_count).map(|i| (i, i)).collect();

    Some(SimulationRelation { block_map, variable_map, expression_map: FxHashMap::default() })
}

/// Detect back-edges in the CFG (header, latch) pairs.
pub fn detect_back_edges(body: &VerifiableBody) -> Vec<(BlockId, BlockId)> {
    let mut edges = Vec::new();
    for block in &body.blocks {
        for succ in block_successors_list(&block.terminator) {
            if succ.0 <= block.id.0 && block.id.0 > 0 {
                edges.push((succ, block.id));
            }
        }
    }
    edges
}

/// Get all successor block IDs from a terminator.
pub fn block_successors_list(term: &crate::Terminator) -> Vec<BlockId> {
    #[allow(unreachable_patterns)] // wildcard kept for #[non_exhaustive] forward compat
    match term {
        crate::Terminator::Goto(target) => vec![*target],
        crate::Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut succs: Vec<BlockId> = targets.iter().map(|(_, b)| *b).collect();
            succs.push(*otherwise);
            succs
        }
        crate::Terminator::Return | crate::Terminator::Unreachable => vec![],
        crate::Terminator::Call { target, .. } => target.iter().copied().collect(),
        crate::Terminator::Assert { target, .. } => vec![*target],
        crate::Terminator::Drop { target, .. } => vec![*target],
        crate::Terminator::Opaque { targets, .. } => targets.clone(),
        _ => vec![],
    }
}
