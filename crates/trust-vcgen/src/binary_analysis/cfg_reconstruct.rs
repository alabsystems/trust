// trust_vcgen/binary_analysis/cfg_reconstruct.rs: CFG reconstruction for binaries
//
// Reconstructs basic blocks from a linear instruction stream and emits a
// control-flow graph suitable for MIR lowering or security analysis.
//
// Part of #148: Binary analysis pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use trust_types::*;

use super::lifter::{AbstractInsn, AbstractOp};
#[cfg(test)]
use super::lowering::{build_lowering_context, lower_cfg_to_blocks, synthetic_registers};

/// One reconstructed basic block in the binary CFG.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CfgNode {
    /// Start address of the block.
    pub(crate) address: u64,
    /// Assigned block identifier in reconstructed order.
    pub(crate) block_id: BlockId,
    /// Instructions belonging to this block.
    pub(crate) instructions: Vec<AbstractInsn>,
}

/// One edge in the reconstructed CFG.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct CfgEdge {
    /// Source block start address.
    pub(crate) from: u64,
    /// Target block start address.
    pub(crate) to: u64,
    /// Edge classification.
    pub(crate) kind: EdgeKind,
}

/// Kinds of control-flow transfer observed during reconstruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[non_exhaustive]
pub(crate) enum EdgeKind {
    /// Straight-line flow into the next block.
    Fallthrough,
    /// Unconditional branch.
    Branch,
    /// Conditional branch when the guard holds.
    ConditionalTrue,
    /// Conditional branch when the guard does not hold.
    ConditionalFalse,
    /// A call continuation edge.
    Call,
    /// A modeled return edge.
    Return,
}

/// Reconstructed control-flow graph for a lifted binary function.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ReconstructedCfg {
    /// CFG nodes in block order.
    pub(crate) nodes: Vec<CfgNode>,
    /// CFG edges between node start addresses.
    pub(crate) edges: Vec<CfgEdge>,
    /// Entry block address.
    pub(crate) entry: u64,
}

/// Reconstruct a CFG from a linear instruction stream.
#[must_use]
pub(crate) fn reconstruct_cfg(instructions: &[AbstractInsn]) -> ReconstructedCfg {
    if instructions.is_empty() {
        return ReconstructedCfg { nodes: vec![], edges: vec![], entry: 0 };
    }

    let mut ordered = instructions.to_vec();
    ordered.sort_by_key(|insn| insn.address);

    let instruction_addresses: BTreeSet<u64> = ordered.iter().map(|insn| insn.address).collect();
    let mut boundaries = BTreeSet::from([ordered[0].address]);

    for (index, insn) in ordered.iter().enumerate() {
        let next_address = ordered.get(index + 1).map(|next| next.address);

        match &insn.op {
            AbstractOp::Branch { target } => {
                insert_boundary_if_present(&mut boundaries, *target, &instruction_addresses);
                if let Some(next_address) = next_address {
                    boundaries.insert(next_address);
                }
            }
            AbstractOp::CondBranch { true_target, false_target, .. } => {
                insert_boundary_if_present(&mut boundaries, *true_target, &instruction_addresses);
                insert_boundary_if_present(&mut boundaries, *false_target, &instruction_addresses);
                if let Some(next_address) = next_address {
                    boundaries.insert(next_address);
                }
            }
            AbstractOp::Call { next, .. } => {
                if let Some(target) = next.or(next_address) {
                    insert_boundary_if_present(&mut boundaries, target, &instruction_addresses);
                }
                if let Some(next_address) = next_address {
                    boundaries.insert(next_address);
                }
            }
            AbstractOp::Return { .. } | AbstractOp::IndirectBranch { .. } => {
                if let Some(next_address) = next_address {
                    boundaries.insert(next_address);
                }
            }
            AbstractOp::Load { .. }
            | AbstractOp::Store { .. }
            | AbstractOp::BinArith { .. }
            | AbstractOp::UnaryOp { .. }
            | AbstractOp::Assign { .. }
            | AbstractOp::Compare { .. }
            | AbstractOp::Nop => {}
        }
    }

    let boundaries: Vec<u64> = boundaries.into_iter().collect();
    let boundary_positions: Vec<usize> = boundaries
        .iter()
        .filter_map(|boundary| ordered.iter().position(|insn| insn.address == *boundary))
        .collect();

    let mut nodes = Vec::new();
    for (block_index, start_position) in boundary_positions.iter().enumerate() {
        let end_position =
            boundary_positions.get(block_index + 1).copied().unwrap_or(ordered.len());

        if *start_position >= end_position {
            continue;
        }

        let instructions = ordered[*start_position..end_position].to_vec();
        nodes.push(CfgNode {
            address: instructions[0].address,
            block_id: BlockId(block_index),
            instructions,
        });
    }

    let edges = reconstruct_edges(&nodes);

    ReconstructedCfg { entry: ordered[0].address, nodes, edges }
}

/// Convert reconstructed CFG nodes into trust-types basic blocks.
#[cfg(test)]
#[must_use]
fn cfg_to_blocks(cfg: &ReconstructedCfg) -> Vec<BasicBlock> {
    let registers = synthetic_registers(cfg);
    let context = build_lowering_context(cfg, &registers);
    lower_cfg_to_blocks(cfg, &context)
}

fn insert_boundary_if_present(
    boundaries: &mut BTreeSet<u64>,
    target: u64,
    instruction_addresses: &BTreeSet<u64>,
) {
    if instruction_addresses.contains(&target) {
        boundaries.insert(target);
    }
}

fn reconstruct_edges(nodes: &[CfgNode]) -> Vec<CfgEdge> {
    let mut edges = BTreeSet::new();
    let address_to_node: BTreeMap<u64, &CfgNode> =
        nodes.iter().map(|node| (node.address, node)).collect();

    for (index, node) in nodes.iter().enumerate() {
        let next_node_address = nodes.get(index + 1).map(|next| next.address);
        let Some(last_instruction) = node.instructions.last() else {
            continue;
        };

        match &last_instruction.op {
            AbstractOp::Branch { target } => {
                if address_to_node.contains_key(target) {
                    edges.insert(CfgEdge {
                        from: node.address,
                        to: *target,
                        kind: EdgeKind::Branch,
                    });
                }
            }
            AbstractOp::CondBranch { true_target, false_target, .. } => {
                if address_to_node.contains_key(true_target) {
                    edges.insert(CfgEdge {
                        from: node.address,
                        to: *true_target,
                        kind: EdgeKind::ConditionalTrue,
                    });
                }
                if address_to_node.contains_key(false_target) {
                    edges.insert(CfgEdge {
                        from: node.address,
                        to: *false_target,
                        kind: EdgeKind::ConditionalFalse,
                    });
                }
            }
            AbstractOp::Call { next, .. } => {
                if let Some(target) = next.or(next_node_address)
                    && address_to_node.contains_key(&target)
                {
                    edges.insert(CfgEdge { from: node.address, to: target, kind: EdgeKind::Call });
                }
            }
            AbstractOp::Return { .. } | AbstractOp::IndirectBranch { .. } => {}
            AbstractOp::Load { .. }
            | AbstractOp::Store { .. }
            | AbstractOp::BinArith { .. }
            | AbstractOp::UnaryOp { .. }
            | AbstractOp::Assign { .. }
            | AbstractOp::Compare { .. }
            | AbstractOp::Nop => {
                if let Some(target) = next_node_address {
                    edges.insert(CfgEdge {
                        from: node.address,
                        to: target,
                        kind: EdgeKind::Fallthrough,
                    });
                }
            }
        }
    }

    edges.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary_analysis::{AbstractValue, MemoryAccess};

    fn insn(address: u64, op: AbstractOp) -> AbstractInsn {
        AbstractInsn { address, op, size: 4 }
    }

    #[test]
    fn test_reconstruct_cfg_empty_input() {
        let cfg = reconstruct_cfg(&[]);
        assert!(cfg.nodes.is_empty());
        assert!(cfg.edges.is_empty());
        assert_eq!(cfg.entry, 0);
        assert!(cfg_to_blocks(&cfg).is_empty());
    }

    #[test]
    fn test_reconstruct_cfg_linear_sequence() {
        let cfg = reconstruct_cfg(&[
            insn(
                0x100,
                AbstractOp::BinArith {
                    dst: 1,
                    op: BinOp::Add,
                    lhs: AbstractValue::Register(0),
                    rhs: AbstractValue::Formula(Formula::Int(1)),
                },
            ),
            insn(0x104, AbstractOp::Return { value: Some(AbstractValue::Register(1)) }),
        ]);

        assert_eq!(cfg.nodes.len(), 1);
        assert!(cfg.edges.is_empty());

        let blocks = cfg_to_blocks(&cfg);
        assert_eq!(blocks.len(), 1);
        assert!(matches!(blocks[0].terminator, Terminator::Return));
    }

    #[test]
    fn test_reconstruct_cfg_simple_branch() {
        let cfg = reconstruct_cfg(&[
            insn(
                0x100,
                AbstractOp::CondBranch {
                    cond: AbstractValue::Register(0),
                    true_target: 0x110,
                    false_target: 0x120,
                },
            ),
            insn(0x110, AbstractOp::Return { value: None }),
            insn(0x120, AbstractOp::Return { value: None }),
        ]);

        assert_eq!(cfg.nodes.len(), 3);
        assert_eq!(cfg.edges.len(), 2);
        assert!(cfg.edges.iter().any(|edge| edge.kind == EdgeKind::ConditionalTrue));
        assert!(cfg.edges.iter().any(|edge| edge.kind == EdgeKind::ConditionalFalse));
    }

    #[test]
    fn test_reconstruct_cfg_diamond_pattern() {
        let cfg = reconstruct_cfg(&[
            insn(
                0x100,
                AbstractOp::CondBranch {
                    cond: AbstractValue::Register(0),
                    true_target: 0x110,
                    false_target: 0x120,
                },
            ),
            insn(0x110, AbstractOp::Branch { target: 0x130 }),
            insn(0x120, AbstractOp::Branch { target: 0x130 }),
            insn(0x130, AbstractOp::Return { value: None }),
        ]);

        assert_eq!(cfg.nodes.len(), 4);
        assert_eq!(cfg.edges.len(), 4);
        assert!(cfg.edges.iter().filter(|edge| edge.kind == EdgeKind::Branch).count() == 2);

        let blocks = cfg_to_blocks(&cfg);
        assert!(matches!(blocks[0].terminator, Terminator::SwitchInt { .. }));
        assert!(matches!(blocks[1].terminator, Terminator::Goto(BlockId(3))));
        assert!(matches!(blocks[2].terminator, Terminator::Goto(BlockId(3))));
    }

    #[test]
    fn test_reconstruct_cfg_loop() {
        let cfg = reconstruct_cfg(&[
            insn(
                0x100,
                AbstractOp::CondBranch {
                    cond: AbstractValue::Register(0),
                    true_target: 0x110,
                    false_target: 0x120,
                },
            ),
            insn(0x110, AbstractOp::Branch { target: 0x100 }),
            insn(0x120, AbstractOp::Return { value: None }),
        ]);

        assert_eq!(cfg.nodes.len(), 3);
        assert!(
            cfg.edges.iter().any(|edge| edge.from == 0x110
                && edge.to == 0x100
                && edge.kind == EdgeKind::Branch)
        );
    }

    #[test]
    fn test_reconstruct_cfg_unreachable_code() {
        let cfg = reconstruct_cfg(&[
            insn(0x100, AbstractOp::Return { value: None }),
            insn(
                0x104,
                AbstractOp::Load {
                    dst: 0,
                    access: MemoryAccess::Read {
                        addr: Formula::Var("ptr".into(), Sort::Int),
                        size: 4,
                    },
                },
            ),
            insn(0x108, AbstractOp::Return { value: None }),
        ]);

        assert_eq!(cfg.nodes.len(), 2);
        assert!(cfg.edges.is_empty());

        let blocks = cfg_to_blocks(&cfg);
        assert_eq!(blocks.len(), 2);
        assert!(matches!(blocks[0].terminator, Terminator::Return));
        assert!(matches!(blocks[1].terminator, Terminator::Return));
    }
}
