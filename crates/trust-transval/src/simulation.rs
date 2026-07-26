// trust-transval: Simulation relation builder
//
// Constructs simulation relations between source (pre-optimization MIR) and
// target (post-optimization MIR) programs. A simulation relation maps:
//   - Source blocks -> target blocks
//   - Source locals -> target locals (or target expressions)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;

use trust_types::*;

use crate::error::TransvalError;

/// Builds simulation relations between source and target functions.
///
/// The builder analyzes structural similarities between MIR functions and
/// constructs a `SimulationRelation` mapping source program points to target
/// program points.
#[derive(Debug, Clone, Default)]
pub struct SimulationRelationBuilder {
    /// Optional expression overrides for specific source locals.
    expression_overrides: FxHashMap<usize, Formula>,
}

impl SimulationRelationBuilder {
    /// Create a new builder with no overrides.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add an expression override: source local `idx` maps to `expr` in the target.
    ///
    /// Used for constant folding and other value-transforming optimizations.
    #[must_use]
    pub fn with_expression(mut self, source_local: usize, expr: Formula) -> Self {
        self.expression_overrides.insert(source_local, expr);
        self
    }

    /// Build a simulation relation by analyzing source and target functions.
    ///
    /// Strategy:
    /// 1. Same block count -> identity block mapping (positional).
    /// 2. Target has fewer blocks -> match by terminator type and successors.
    /// 3. Otherwise -> partial mapping for what can be matched.
    pub fn build_from_functions(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<SimulationRelation, TransvalError> {
        if source.body.blocks.is_empty() {
            return Err(TransvalError::EmptyBody("source".into()));
        }
        if target.body.blocks.is_empty() {
            return Err(TransvalError::EmptyBody("target".into()));
        }

        let block_map = if source.body.blocks.len() == target.body.blocks.len() {
            // Same block count: positional identity mapping.
            source
                .body
                .blocks
                .iter()
                .zip(target.body.blocks.iter())
                .map(|(s, t)| (s.id, t.id))
                .collect()
        } else {
            // Different block count: match by terminator type.
            self.match_blocks_by_terminator(source, target)
        };

        let local_count = source.body.locals.len().min(target.body.locals.len());
        let variable_map: FxHashMap<usize, usize> = (0..local_count).map(|i| (i, i)).collect();

        Ok(SimulationRelation {
            block_map,
            variable_map,
            expression_map: self.expression_overrides.clone(),
        })
    }

    /// Build a simulation relation mapping source locals to target locals by
    /// **(name, type)**, not by position.
    ///
    /// `build_from_functions` maps locals positionally (`i -> i`), which is correct
    /// only when the two programs are byte-isomorphic in their local layout (e.g. a
    /// function and its hand-authored bug-variant). It is WRONG whenever the two
    /// sides were authored independently — a frontend-derived image (say the one
    /// `trust-ts-embed` lowers) and a Rust MIR image share observable *names*
    /// (the ObservationMap α aligns them) but lay out their locals differently,
    /// so positional mapping compares unrelated variables and yields a vacuous
    /// or spurious verdict.
    ///
    /// This builder maps each *named* source local to the first target local with
    /// the same name AND type. Unnamed locals (the return slot, anonymous
    /// temporaries) and unmatched named locals fall back to positional identity
    /// (clamped to the target's local count). Block mapping uses the same
    /// positional/terminator strategy as [`Self::build_from_functions`]. When local
    /// layouts already coincide (names and positions agree, as in translation
    /// validation of a function against its optimized self) this is identical to
    /// `build_from_functions`.
    pub fn build_by_name(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> Result<SimulationRelation, TransvalError> {
        if source.body.blocks.is_empty() {
            return Err(TransvalError::EmptyBody("source".into()));
        }
        if target.body.blocks.is_empty() {
            return Err(TransvalError::EmptyBody("target".into()));
        }

        let block_map = if source.body.blocks.len() == target.body.blocks.len() {
            source
                .body
                .blocks
                .iter()
                .zip(target.body.blocks.iter())
                .map(|(s, t)| (s.id, t.id))
                .collect()
        } else {
            self.match_blocks_by_terminator(source, target)
        };

        let target_locals = &target.body.locals;
        let fallback_cap = target_locals.len().saturating_sub(1);
        let variable_map: FxHashMap<usize, usize> = source
            .body
            .locals
            .iter()
            .enumerate()
            .map(|(i, sl)| {
                let by_name = sl.name.as_ref().and_then(|name| {
                    target_locals
                        .iter()
                        .position(|tl| tl.name.as_ref() == Some(name) && tl.ty == sl.ty)
                });
                (i, by_name.unwrap_or_else(|| i.min(fallback_cap)))
            })
            .collect();

        Ok(SimulationRelation {
            block_map,
            variable_map,
            expression_map: self.expression_overrides.clone(),
        })
    }

    /// Build an identity simulation relation for a function.
    ///
    /// Maps each block and variable to itself. Used for validating trivial
    /// transformations or as a baseline.
    #[must_use]
    pub fn build_identity(func: &VerifiableFunction) -> SimulationRelation {
        SimulationRelation::identity(func)
    }

    /// Match source blocks to target blocks by terminator type.
    ///
    /// For each source block, find the first unmatched target block with a
    /// compatible terminator. Entry (block 0) and return blocks are anchored.
    fn match_blocks_by_terminator(
        &self,
        source: &VerifiableFunction,
        target: &VerifiableFunction,
    ) -> FxHashMap<BlockId, BlockId> {
        let mut block_map = FxHashMap::default();
        let mut used_targets: Vec<bool> = vec![false; target.body.blocks.len()];

        // Anchor: entry blocks always map.
        if let (Some(sb), Some(tb)) = (source.body.blocks.first(), target.body.blocks.first()) {
            block_map.insert(sb.id, tb.id);
            used_targets[0] = true;
        }

        // Anchor: return blocks.
        for sb in &source.body.blocks {
            if matches!(sb.terminator, Terminator::Return) {
                for (ti, tb) in target.body.blocks.iter().enumerate() {
                    if !used_targets[ti] && matches!(tb.terminator, Terminator::Return) {
                        block_map.insert(sb.id, tb.id);
                        used_targets[ti] = true;
                        break;
                    }
                }
            }
        }

        // Match remaining by terminator discriminant.
        for sb in &source.body.blocks {
            if block_map.contains_key(&sb.id) {
                continue;
            }
            let source_disc = terminator_discriminant(&sb.terminator);
            for (ti, tb) in target.body.blocks.iter().enumerate() {
                if !used_targets[ti] && terminator_discriminant(&tb.terminator) == source_disc {
                    block_map.insert(sb.id, tb.id);
                    used_targets[ti] = true;
                    break;
                }
            }
        }

        block_map
    }
}

/// Classify a terminator into a discriminant for matching.
///
/// Terminator is #[non_exhaustive], so unknown variants get a
/// fallback discriminant (255) instead of panicking.
fn terminator_discriminant(term: &Terminator) -> u8 {
    match term {
        Terminator::Goto(_) => 0,
        Terminator::SwitchInt { .. } => 1,
        Terminator::Return => 2,
        Terminator::Unreachable => 3,
        Terminator::Call { .. } => 4,
        Terminator::Assert { .. } => 5,
        Terminator::Drop { .. } => 6,
        Terminator::Opaque { .. } => 7,
        _ => 255, // Unknown terminator variant — safe fallback.
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn simple_function(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("a".into()) },
                    LocalDecl { index: 2, ty: Ty::i32(), name: Some("b".into()) },
                ],
                blocks: vec![BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
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
    fn build_by_name_maps_locals_by_name_not_position() {
        // source: locals [0:ret, 1:"a", 2:"b"].
        let source = simple_function("source");
        // target: same observable names, but "a"/"b" live at SHIFTED indices behind
        // an anonymous temp — exactly the TS-image-vs-Rust-image layout divergence.
        let mut target = simple_function("target");
        target.body.locals = vec![
            LocalDecl { index: 0, ty: Ty::i32(), name: None }, // ret
            LocalDecl { index: 1, ty: Ty::i32(), name: None }, // anonymous temp (shifts a/b down)
            LocalDecl { index: 2, ty: Ty::i32(), name: Some("a".into()) },
            LocalDecl { index: 3, ty: Ty::i32(), name: Some("b".into()) },
        ];

        let builder = SimulationRelationBuilder::new();
        let by_name = builder.build_by_name(&source, &target).unwrap();
        // Named locals map by (name, ty): a@1 -> 2, b@2 -> 3.
        assert_eq!(by_name.variable_map.get(&1), Some(&2), "named local `a` maps by name");
        assert_eq!(by_name.variable_map.get(&2), Some(&3), "named local `b` maps by name");
        // The unnamed return slot falls back to positional identity.
        assert_eq!(by_name.variable_map.get(&0), Some(&0));

        // Positional mapping gets `a`/`b` WRONG (1->1, 2->2): this is precisely the
        // generalization the name-aware builder provides.
        let positional = builder.build_from_functions(&source, &target).unwrap();
        assert_eq!(positional.variable_map.get(&1), Some(&1));
        assert_ne!(
            positional.variable_map.get(&1),
            by_name.variable_map.get(&1),
            "name-aware and positional must disagree on the shifted layout"
        );
    }

    fn two_block_function(name: &str) -> VerifiableFunction {
        VerifiableFunction {
            name: name.to_string(),
            def_path: format!("test::{name}"),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::i32(), name: None },
                    LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                ],
                blocks: vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                            span: SourceSpan::default(),
                        }],
                        terminator: Terminator::Goto(BlockId(1)),
                    },
                    BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                ],
                arg_count: 1,
                return_ty: Ty::i32(),
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    #[test]
    fn test_build_identity_maps_all_blocks_and_locals() {
        let func = simple_function("f");
        let rel = SimulationRelationBuilder::build_identity(&func);

        assert_eq!(rel.block_map.len(), 1);
        assert_eq!(rel.block_map[&BlockId(0)], BlockId(0));
        assert_eq!(rel.variable_map.len(), 3);
    }

    #[test]
    fn test_build_from_functions_same_structure() {
        let source = simple_function("source");
        let target = simple_function("target");
        let builder = SimulationRelationBuilder::new();

        let rel = builder.build_from_functions(&source, &target).unwrap();
        assert_eq!(rel.block_map.len(), 1);
        assert_eq!(rel.variable_map.len(), 3);
    }

    #[test]
    fn test_build_from_functions_different_block_count() {
        let source = two_block_function("source");
        let target = simple_function("target");
        let builder = SimulationRelationBuilder::new();

        let rel = builder.build_from_functions(&source, &target).unwrap();
        // Should map at least entry and return blocks.
        assert!(!rel.block_map.is_empty());
        // Entry block mapped.
        assert!(rel.block_map.contains_key(&BlockId(0)));
    }

    #[test]
    fn test_build_from_functions_empty_source_errors() {
        let mut source = simple_function("source");
        source.body.blocks.clear();
        let target = simple_function("target");
        let builder = SimulationRelationBuilder::new();

        let err = builder.build_from_functions(&source, &target).unwrap_err();
        assert!(matches!(err, TransvalError::EmptyBody(_)));
    }

    #[test]
    fn test_with_expression_override() {
        let source = simple_function("source");
        let target = simple_function("target");
        let builder = SimulationRelationBuilder::new().with_expression(1, Formula::Int(42));

        let rel = builder.build_from_functions(&source, &target).unwrap();
        assert_eq!(rel.expression_map.get(&1), Some(&Formula::Int(42)));
    }

    #[test]
    fn test_terminator_discriminant_distinct() {
        assert_ne!(
            terminator_discriminant(&Terminator::Return),
            terminator_discriminant(&Terminator::Goto(BlockId(0)))
        );
        assert_ne!(
            terminator_discriminant(&Terminator::Return),
            terminator_discriminant(&Terminator::Unreachable)
        );
    }
}
