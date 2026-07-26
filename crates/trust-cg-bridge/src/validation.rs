//! Validation of lowered trust_cg LIR for common structural errors.
//!
//! Checks that the LIR function produced by the bridge is internally consistent
//! before it is handed off to trust_cg codegen. This catches bugs early rather than
//! producing confusing failures downstream.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

// Validator constructors take many parameters by design — each captures
// the structural slot it checks (function, block, instruction position,
// operand kind, expected type, span, severity, label). Collapsing them
// behind a struct would just rename the same data without simplifying
// callers.
#![allow(clippy::too_many_arguments)]

use trust_cg_lower::function::Function as LirFunction;
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_types::fx::FxHashSet;

/// Errors detected during LIR validation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ValidationError {
    /// A jump/branch references a block that does not exist in the function.
    MissingJumpTarget { source: Block, target: Block },

    /// A block contains duplicate result Values (instruction IDs).
    DuplicateInstructionId { block: Block, value: Value },

    /// An instruction uses a Value as an argument that was never defined.
    UndefinedValue { block: Block, value: Value },

    /// The number of return values in a Return instruction does not match
    /// the function signature's declared return types.
    ReturnArityMismatch { block: Block, expected: usize, actual: usize },
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingJumpTarget { source, target } => {
                write!(f, "block {} references nonexistent target block {}", source.0, target.0)
            }
            Self::DuplicateInstructionId { block, value } => {
                write!(f, "block {} has duplicate result value {}", block.0, value.0)
            }
            Self::UndefinedValue { block, value } => {
                write!(f, "block {} uses undefined value {}", block.0, value.0)
            }
            Self::ReturnArityMismatch { block, expected, actual } => {
                write!(
                    f,
                    "return arity mismatch: signature declares {} returns, \
                     but block {} returns {} values",
                    expected, block.0, actual
                )
            }
        }
    }
}

impl std::error::Error for ValidationError {}

/// Validate a lowered LIR function for structural consistency.
///
/// Returns `Ok(())` if the function passes all checks, or a list of all
/// errors found (never short-circuits on the first error).
pub fn validate_lir(func: &LirFunction) -> Result<(), Vec<ValidationError>> {
    let mut errors = Vec::new();

    let block_order = sorted_lir_blocks(func);
    let block_ids: FxHashSet<Block> = block_order.iter().map(|(block_id, _)| *block_id).collect();

    // Signature-implied argument values: Value(0)..Value(params.len()-1).
    let mut function_params: FxHashSet<Value> = FxHashSet::default();
    for i in 0..func.signature.params.len() as u32 {
        function_params.insert(Value(i));
    }

    for (block_id, bb) in block_order {
        let mut block_defined = function_params.clone();
        for (val, _ty) in &bb.params {
            block_defined.insert(*val);
        }
        let mut seen_results: FxHashSet<Value> = FxHashSet::default();

        // --- Check 1: All jump targets exist ---
        for instr in &bb.instructions {
            match &instr.opcode {
                Opcode::Jump { dest } if !block_ids.contains(dest) => {
                    errors.push(ValidationError::MissingJumpTarget {
                        source: block_id,
                        target: *dest,
                    });
                }
                Opcode::Jump { .. } => {}
                Opcode::Brif { cond: _, then_dest, else_dest } => {
                    if !block_ids.contains(then_dest) {
                        errors.push(ValidationError::MissingJumpTarget {
                            source: block_id,
                            target: *then_dest,
                        });
                    }
                    if !block_ids.contains(else_dest) {
                        errors.push(ValidationError::MissingJumpTarget {
                            source: block_id,
                            target: *else_dest,
                        });
                    }
                }
                _ => {}
            }
        }

        // --- Check 2/3: No duplicate result Values within a block, and all
        // operand Values are defined before use in this block's scope.
        for instr in &bb.instructions {
            validate_instruction_operands(block_id, instr, &block_defined, &mut errors);
            for r in &instr.results {
                if !seen_results.insert(*r) {
                    errors.push(ValidationError::DuplicateInstructionId {
                        block: block_id,
                        value: *r,
                    });
                }
                block_defined.insert(*r);
            }
        }

        // --- Check 4: Return arity consistency ---
        let expected_returns = func.signature.returns.len();
        for instr in &bb.instructions {
            if matches!(instr.opcode, Opcode::Return) {
                let actual = instr.args.len();
                if actual != expected_returns {
                    errors.push(ValidationError::ReturnArityMismatch {
                        block: block_id,
                        expected: expected_returns,
                        actual,
                    });
                }
            }
        }
    }

    if errors.is_empty() { Ok(()) } else { Err(errors) }
}

fn validate_instruction_operands(
    block_id: Block,
    instr: &Instruction,
    block_defined: &FxHashSet<Value>,
    errors: &mut Vec<ValidationError>,
) {
    for arg in &instr.args {
        if !block_defined.contains(arg) {
            errors.push(ValidationError::UndefinedValue { block: block_id, value: *arg });
        }
    }
    if let Opcode::Brif { cond, .. } = &instr.opcode {
        if !block_defined.contains(cond) {
            errors.push(ValidationError::UndefinedValue { block: block_id, value: *cond });
        }
    }
}

fn sorted_lir_blocks(func: &LirFunction) -> Vec<(Block, &trust_cg_lower::function::BasicBlock)> {
    // trust_cg stores LIR blocks in a std HashMap as part of its public serde
    // contract. Sort by stable numeric block id before validation so diagnostics
    // do not depend on hash-map iteration order.
    #[allow(rustc::potential_query_instability)]
    let mut blocks: Vec<_> = func.blocks.iter().map(|(block, bb)| (*block, bb)).collect();
    blocks.sort_by_key(|(block, _)| block.0);
    blocks
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use trust_cg_lower::function::{BasicBlock as LirBlock, Signature};
    use trust_cg_lower::instructions::Instruction;
    use trust_cg_lower::types::Type as LirType;

    use super::*;

    /// Helper: build a minimal valid function with one block containing a Return.
    fn make_valid_function() -> LirFunction {
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        LirFunction {
            param_pointee_types: Vec::new(),
            name: "test_fn".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        }
    }

    #[test]
    fn test_validate_valid_function_passes() {
        let func = make_valid_function();
        assert!(validate_lir(&func).is_ok());
    }

    #[test]
    fn test_validate_jump_to_existing_block_passes() {
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Jump { dest: Block(1) },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        blocks.insert(
            Block(1),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "jump_ok".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        assert!(validate_lir(&func).is_ok());
    }

    #[test]
    fn test_validate_missing_jump_target() {
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Jump { dest: Block(99) },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "bad_jump".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(matches!(
            &errors[0],
            ValidationError::MissingJumpTarget { source: Block(0), target: Block(99) }
        ));
    }

    #[test]
    fn test_validate_missing_brif_targets() {
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Brif {
                        cond: Value(0),
                        then_dest: Block(10),
                        else_dest: Block(20),
                    },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "bad_brif".to_string(),
            signature: Signature {
                params: vec![LirType::I32], // Value(0) is a param
                returns: vec![],
            },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        assert_eq!(errors.len(), 2);
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ValidationError::MissingJumpTarget { target: Block(10), .. }))
        );
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ValidationError::MissingJumpTarget { target: Block(20), .. }))
        );
    }

    #[test]
    fn test_validate_duplicate_instruction_ids() {
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 1 },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 2 },
                        args: vec![],
                        results: vec![Value(0)], // duplicate!
                    },
                    Instruction { opcode: Opcode::Return, args: vec![], results: vec![] },
                ],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "dup_id".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::DuplicateInstructionId { value: Value(0), .. }
            ))
        );
    }

    #[test]
    fn test_validate_undefined_value() {
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![Value(100), Value(200)], // never defined
                        results: vec![Value(0)],
                    },
                    Instruction { opcode: Opcode::Return, args: vec![], results: vec![] },
                ],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "undef_val".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ValidationError::UndefinedValue { value: Value(100), .. }))
        );
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, ValidationError::UndefinedValue { value: Value(200), .. }))
        );
    }

    #[test]
    fn test_validate_rejects_forward_reference_in_block() {
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction { opcode: Opcode::Return, args: vec![Value(0)], results: vec![] },
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 42 },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                ],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "forward_ref".to_string(),
            signature: Signature { params: vec![], returns: vec![LirType::I32] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        assert!(errors.iter().any(|e| matches!(
            e,
            ValidationError::UndefinedValue { block: Block(0), value: Value(0) }
        )));
    }

    #[test]
    fn test_validate_return_arity_mismatch() {
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 42 },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![Value(0)], // returns 1 value
                        results: vec![],
                    },
                ],
                ..Default::default()
            },
        );
        // Signature says 0 returns but block returns 1
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "bad_ret".to_string(),
            signature: Signature {
                params: vec![],
                returns: vec![], // expects 0
            },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        assert!(errors.iter().any(|e| matches!(
            e,
            ValidationError::ReturnArityMismatch { expected: 0, actual: 1, .. }
        )));
    }

    #[test]
    fn test_validate_return_arity_correct() {
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 42 },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                    Instruction { opcode: Opcode::Return, args: vec![Value(0)], results: vec![] },
                ],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "good_ret".to_string(),
            signature: Signature { params: vec![], returns: vec![LirType::I32] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        assert!(validate_lir(&func).is_ok());
    }

    #[test]
    fn test_validate_params_count_as_defined() {
        // Function params create Value(0)..Value(n-1) — these should be usable.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![Value(0), Value(1)], // param values
                        results: vec![Value(2)],
                    },
                    Instruction { opcode: Opcode::Return, args: vec![Value(2)], results: vec![] },
                ],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "use_params".to_string(),
            signature: Signature {
                params: vec![LirType::I32, LirType::I32],
                returns: vec![LirType::I32],
            },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        assert!(validate_lir(&func).is_ok());
    }

    #[test]
    fn test_validate_collects_all_errors() {
        // Multiple errors in one function — validator reports all of them.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 1 },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 2 },
                        args: vec![],
                        results: vec![Value(0)], // duplicate
                    },
                    Instruction {
                        opcode: Opcode::Jump { dest: Block(99) }, // missing target
                        args: vec![Value(50)],                    // undefined value
                        results: vec![],
                    },
                ],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "many_errors".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        // Should have at least 3 distinct error kinds
        assert!(errors.len() >= 3, "expected >=3 errors, got {}", errors.len());
    }

    #[test]
    fn test_validate_multiblock_function() {
        // A valid multi-block function with branching.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::B1, imm: 1 },
                        args: vec![],
                        results: vec![Value(1)],
                    },
                    Instruction {
                        opcode: Opcode::Brif {
                            cond: Value(1),
                            then_dest: Block(1),
                            else_dest: Block(2),
                        },
                        args: vec![],
                        results: vec![],
                    },
                ],
                ..Default::default()
            },
        );
        blocks.insert(
            Block(1),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(0)],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        blocks.insert(
            Block(2),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(0)],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "multi_block".to_string(),
            signature: Signature {
                params: vec![LirType::I32], // Value(0) is param
                returns: vec![LirType::I32],
            },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        assert!(validate_lir(&func).is_ok());
    }

    // =========================================================================
    // Additional validation coverage: complex scenarios
    // =========================================================================

    #[test]
    fn test_validate_many_blocks_all_valid_jumps() {
        // 10-block chain: each jumps to the next, last returns.
        let mut blocks = HashMap::new();
        for i in 0..9u32 {
            blocks.insert(
                Block(i),
                LirBlock {
                    params: vec![],
                    instructions: vec![Instruction {
                        opcode: Opcode::Jump { dest: Block(i + 1) },
                        args: vec![],
                        results: vec![],
                    }],
                    ..Default::default()
                },
            );
        }
        blocks.insert(
            Block(9),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "chain".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        assert!(validate_lir(&func).is_ok());
    }

    #[test]
    fn test_validate_diamond_cfg_valid() {
        // Diamond: block0 -> block1, block2; both -> block3.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::B1, imm: 1 },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                    Instruction {
                        opcode: Opcode::Brif {
                            cond: Value(0),
                            then_dest: Block(1),
                            else_dest: Block(2),
                        },
                        args: vec![],
                        results: vec![],
                    },
                ],
                ..Default::default()
            },
        );
        blocks.insert(
            Block(1),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Jump { dest: Block(3) },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        blocks.insert(
            Block(2),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Jump { dest: Block(3) },
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        blocks.insert(
            Block(3),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "diamond".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        assert!(validate_lir(&func).is_ok());
    }

    #[test]
    fn test_validate_undefined_value_across_blocks() {
        // Value defined in block0 is NOT visible to block1 through args.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 42 },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                    Instruction {
                        opcode: Opcode::Jump { dest: Block(1) },
                        args: vec![],
                        results: vec![],
                    },
                ],
                ..Default::default()
            },
        );
        blocks.insert(
            Block(1),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(0)], // Uses Value(0) defined in block0
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "cross_block_val".to_string(),
            signature: Signature { params: vec![], returns: vec![LirType::I32] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        assert!(errors.iter().any(|e| matches!(
            e,
            ValidationError::UndefinedValue { block: Block(1), value: Value(0) }
        )));
    }

    #[test]
    fn test_validate_block_params_define_values() {
        // Block params should count as defined values.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![(Value(10), LirType::I32)],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![Value(10)], // Defined by block param
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "block_param".to_string(),
            signature: Signature { params: vec![], returns: vec![LirType::I32] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        assert!(validate_lir(&func).is_ok());
    }

    #[test]
    fn test_validate_multiple_missing_targets() {
        // Brif where BOTH targets are missing should report 2 errors.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::B1, imm: 1 },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                    Instruction {
                        opcode: Opcode::Brif {
                            cond: Value(0),
                            then_dest: Block(50),
                            else_dest: Block(60),
                        },
                        args: vec![],
                        results: vec![],
                    },
                ],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "both_missing".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        let missing_target_count = errors
            .iter()
            .filter(|e| matches!(e, ValidationError::MissingJumpTarget { .. }))
            .count();
        assert_eq!(missing_target_count, 2);
    }

    #[test]
    fn test_validate_return_arity_multiple_blocks() {
        // Multiple blocks with return — some correct, some wrong.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 1 },
                        args: vec![],
                        results: vec![Value(0)],
                    },
                    Instruction {
                        opcode: Opcode::Return,
                        args: vec![Value(0)], // correct: 1 return
                        results: vec![],
                    },
                ],
                ..Default::default()
            },
        );
        blocks.insert(
            Block(1),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![], // wrong: 0 returns, expected 1
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "mixed_ret".to_string(),
            signature: Signature {
                params: vec![],
                returns: vec![LirType::I32], // expects 1 return value
            },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        assert!(errors.iter().any(|e| matches!(
            e,
            ValidationError::ReturnArityMismatch { expected: 1, actual: 0, .. }
        )));
    }

    #[test]
    fn test_validate_duplicate_results_across_blocks() {
        // Same Value(5) result in different blocks — currently NOT an error
        // because our validator checks duplicates within a single block only.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 1 },
                        args: vec![],
                        results: vec![Value(5)],
                    },
                    Instruction {
                        opcode: Opcode::Jump { dest: Block(1) },
                        args: vec![],
                        results: vec![],
                    },
                ],
                ..Default::default()
            },
        );
        blocks.insert(
            Block(1),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iconst { ty: LirType::I32, imm: 2 },
                        args: vec![],
                        results: vec![Value(5)], // Same value ID, different block
                    },
                    Instruction { opcode: Opcode::Return, args: vec![Value(5)], results: vec![] },
                ],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "cross_block_dup".to_string(),
            signature: Signature { params: vec![], returns: vec![LirType::I32] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        // This is a valid scenario by current validator rules (dup check is per-block).
        assert!(validate_lir(&func).is_ok());
    }

    #[test]
    fn test_validate_error_display_formatting() {
        // Verify that error Display impl produces readable messages.
        let e1 = ValidationError::MissingJumpTarget { source: Block(0), target: Block(99) };
        assert_eq!(e1.to_string(), "block 0 references nonexistent target block 99");

        let e2 = ValidationError::DuplicateInstructionId { block: Block(3), value: Value(7) };
        assert_eq!(e2.to_string(), "block 3 has duplicate result value 7");

        let e3 = ValidationError::UndefinedValue { block: Block(1), value: Value(42) };
        assert_eq!(e3.to_string(), "block 1 uses undefined value 42");

        let e4 = ValidationError::ReturnArityMismatch { block: Block(2), expected: 1, actual: 3 };
        assert_eq!(
            e4.to_string(),
            "return arity mismatch: signature declares 1 returns, but block 2 returns 3 values"
        );
    }

    #[test]
    fn test_validate_large_function_stress() {
        // 50 blocks in a chain — all valid. Tests scalability.
        let mut blocks = HashMap::new();
        for i in 0..49u32 {
            blocks.insert(
                Block(i),
                LirBlock {
                    params: vec![],
                    instructions: vec![Instruction {
                        opcode: Opcode::Jump { dest: Block(i + 1) },
                        args: vec![],
                        results: vec![],
                    }],
                    ..Default::default()
                },
            );
        }
        blocks.insert(
            Block(49),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "long_chain".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        assert!(validate_lir(&func).is_ok());
    }

    #[test]
    fn test_validate_many_undefined_values_reported() {
        // Block using 5 undefined values — all should be reported.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![Value(10), Value(11)],
                        results: vec![Value(0)],
                    },
                    Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![Value(12), Value(13)],
                        results: vec![Value(1)],
                    },
                    Instruction {
                        opcode: Opcode::Iadd,
                        args: vec![Value(14), Value(0)],
                        results: vec![Value(2)],
                    },
                    Instruction { opcode: Opcode::Return, args: vec![], results: vec![] },
                ],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "many_undef".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        let errors = validate_lir(&func).unwrap_err();
        let undef_count =
            errors.iter().filter(|e| matches!(e, ValidationError::UndefinedValue { .. })).count();
        // Value(10), Value(11), Value(12), Value(13), Value(14) are undefined = 5
        assert_eq!(undef_count, 5);
    }

    #[test]
    fn test_validate_empty_function_valid() {
        // A function with one block containing only Return is valid.
        let mut blocks = HashMap::new();
        blocks.insert(
            Block(0),
            LirBlock {
                params: vec![],
                instructions: vec![Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                }],
                ..Default::default()
            },
        );
        let func = LirFunction {
            param_pointee_types: Vec::new(),
            name: "empty".to_string(),
            signature: Signature { params: vec![], returns: vec![] },
            blocks,
            block_order: vec![],
            trust_ir_origins: HashMap::new(),
            entry_block: Block(0),
            stack_slots: vec![],
            value_types: HashMap::new(),
            pure_callees: Default::default(),
            // trust-cg's LirFunction carries the libm callees ISel may treat as
            // pure; the bridge asserts no libm purity, and empty is that claim.
            libm_pure_callees: Default::default(),
            debug_meta: Default::default(),
            debug_value_bindings: vec![],
            stack_protector: Default::default(),
            eh_info: Default::default(),
        };
        assert!(validate_lir(&func).is_ok());
    }
}
