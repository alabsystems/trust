// trust-lift: Control flow graph types for lifted binary code
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{MemoryAccessFact, TrustLevel, UnsupportedLedger};

use trust_disasm::{ControlFlow, Instruction};

/// Role of a recovered CFG edge.
///
/// The target class lives in [`CfgEdgeTarget`], so a conditional edge can still
/// record whether it targets an in-function block, an external address, or an
/// unresolved indirect destination.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CfgEdgeKind {
    /// Ordinary fallthrough to the next block.
    Fallthrough,
    /// Direct unconditional branch.
    DirectBranch,
    /// Conditional branch taken edge.
    ConditionalTrue,
    /// Conditional branch not-taken/fallthrough edge.
    ConditionalFalse,
    /// Call target edge. This is metadata and is not a local CFG successor.
    Call,
    /// Post-call continuation edge.
    CallFallthrough,
    /// Function return.
    Return,
    /// Trap/exception/architectural halt.
    Trap,
}

impl CfgEdgeKind {
    /// Whether this edge contributes an in-function successor in the local CFG.
    #[must_use]
    pub fn is_cfg_successor(self) -> bool {
        matches!(
            self,
            Self::Fallthrough
                | Self::DirectBranch
                | Self::ConditionalTrue
                | Self::ConditionalFalse
                | Self::CallFallthrough
        )
    }

    /// Whether an unresolved target for this edge must fail closed in proof mode.
    #[must_use]
    pub fn is_strict_control_flow(self) -> bool {
        matches!(
            self,
            Self::DirectBranch | Self::ConditionalTrue | Self::ConditionalFalse | Self::Call
        )
    }
}

/// Target class for a CFG edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CfgEdgeTarget {
    /// Target is another recovered block in the current function.
    Internal(u64),
    /// Target is a concrete address outside the recovered function CFG.
    External(u64),
    /// Target is indirect or otherwise not recoverable as a concrete address.
    Unresolved,
    /// Terminal edge with no address.
    None,
}

impl CfgEdgeTarget {
    /// Classify an address relative to a function's address range.
    #[must_use]
    pub fn for_function_addr(addr: u64, entry: u64, func_end: u64) -> Self {
        if addr >= entry && addr < func_end { Self::Internal(addr) } else { Self::External(addr) }
    }

    /// Address carried by an internal or external target.
    #[must_use]
    pub fn address(self) -> Option<u64> {
        match self {
            Self::Internal(addr) | Self::External(addr) => Some(addr),
            Self::Unresolved | Self::None => None,
        }
    }

    /// In-function successor address, if any.
    #[must_use]
    pub fn internal_addr(self) -> Option<u64> {
        match self {
            Self::Internal(addr) => Some(addr),
            Self::External(_) | Self::Unresolved | Self::None => None,
        }
    }
}

/// First-class metadata for one recovered control-flow edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CfgEdge {
    /// Source block start address.
    pub source: u64,
    /// Edge role.
    pub kind: CfgEdgeKind,
    /// Edge target class.
    pub target: CfgEdgeTarget,
}

impl CfgEdge {
    /// Construct a CFG edge.
    #[must_use]
    pub fn new(source: u64, kind: CfgEdgeKind, target: CfgEdgeTarget) -> Self {
        Self { source, kind, target }
    }

    /// In-function CFG successor address carried by this edge, if any.
    #[must_use]
    pub fn internal_successor(self) -> Option<u64> {
        self.kind.is_cfg_successor().then_some(())?;
        self.target.internal_addr()
    }
}

/// A basic block in the lifted CFG, prior to TrustIr conversion.
///
/// Each block contains the decoded instructions from the binary and tracks
/// its successor edges for CFG construction.
#[derive(Debug, Clone)]
pub struct LiftedBlock {
    /// Block index (corresponds to its position in the CFG block list).
    pub id: usize,
    /// Start address of the block.
    pub start_addr: u64,
    /// Decoded instructions in this block.
    pub instructions: Vec<Instruction>,
    /// Successor block addresses (for CFG edge construction).
    pub successors: Vec<u64>,
    /// Whether this block ends with a return.
    pub is_return: bool,
}

/// A control flow graph built from recovered basic blocks.
#[derive(Debug, Clone, Default)]
pub struct Cfg {
    /// Basic blocks, indexed by their block ID.
    pub blocks: Vec<LiftedBlock>,
    /// Map from start address to block index.
    // Made pub for downstream crate construction.
    pub addr_to_block: FxHashMap<u64, usize>,
    /// Entry block index.
    pub entry: usize,
}

impl Cfg {
    /// Create a new empty CFG.
    // Made pub so trust_vcgen tests can construct fixtures.
    pub fn new() -> Self {
        Self { blocks: Vec::new(), addr_to_block: FxHashMap::default(), entry: 0 }
    }

    /// Add a block and register its address mapping.
    // Made pub so trust_vcgen tests can construct fixtures.
    pub fn add_block(&mut self, block: LiftedBlock) -> usize {
        let idx = self.blocks.len();
        self.addr_to_block.insert(block.start_addr, idx);
        self.blocks.push(block);
        idx
    }

    /// Look up a block index by start address.
    #[must_use]
    pub fn block_index(&self, addr: u64) -> Option<usize> {
        self.addr_to_block.get(&addr).copied()
    }

    /// Number of blocks.
    #[must_use]
    pub fn block_count(&self) -> usize {
        self.blocks.len()
    }

    /// Recover typed edge metadata for a block while preserving the legacy
    /// `LiftedBlock::successors` representation for local in-function edges.
    #[must_use]
    pub fn edges_for_block(&self, block: &LiftedBlock) -> Vec<CfgEdge> {
        let Some(last) = block.instructions.last() else {
            if block.is_return {
                return vec![CfgEdge::new(
                    block.start_addr,
                    CfgEdgeKind::Return,
                    CfgEdgeTarget::None,
                )];
            }
            return self.legacy_successor_edges(block, CfgEdgeKind::Fallthrough);
        };

        let mut edges = Vec::new();
        for insn in &block.instructions {
            if matches!(insn.flow, ControlFlow::Call) {
                let target = insn
                    .branch_target()
                    .map_or(CfgEdgeTarget::Unresolved, |addr| self.edge_target_for_addr(addr));
                edges.push(CfgEdge::new(block.start_addr, CfgEdgeKind::Call, target));
            }
        }

        match last.flow {
            ControlFlow::Return => {
                edges.push(CfgEdge::new(
                    block.start_addr,
                    CfgEdgeKind::Return,
                    CfgEdgeTarget::None,
                ));
            }
            ControlFlow::Exception => {
                edges.push(CfgEdge::new(block.start_addr, CfgEdgeKind::Trap, CfgEdgeTarget::None));
            }
            ControlFlow::Branch => {
                let target = last
                    .branch_target()
                    .map_or(CfgEdgeTarget::Unresolved, |addr| self.edge_target_for_addr(addr));
                edges.push(CfgEdge::new(block.start_addr, CfgEdgeKind::DirectBranch, target));
            }
            ControlFlow::ConditionalBranch => {
                let fallthrough = last.address + u64::from(last.size);
                edges.push(CfgEdge::new(
                    block.start_addr,
                    CfgEdgeKind::ConditionalFalse,
                    self.edge_target_for_addr(fallthrough),
                ));
                let target = last
                    .branch_target()
                    .map_or(CfgEdgeTarget::Unresolved, |addr| self.edge_target_for_addr(addr));
                edges.push(CfgEdge::new(block.start_addr, CfgEdgeKind::ConditionalTrue, target));
            }
            ControlFlow::Call => {
                let fallthrough = last.address + u64::from(last.size);
                edges.push(CfgEdge::new(
                    block.start_addr,
                    CfgEdgeKind::CallFallthrough,
                    self.edge_target_for_addr(fallthrough),
                ));
            }
            ControlFlow::Fallthrough => {
                edges.extend(self.legacy_successor_edges(block, CfgEdgeKind::Fallthrough));
            }
            _ => {
                edges.extend(self.legacy_successor_edges(block, CfgEdgeKind::Fallthrough));
            }
        }

        edges
    }

    fn edge_target_for_addr(&self, addr: u64) -> CfgEdgeTarget {
        if self.block_index(addr).is_some() {
            CfgEdgeTarget::Internal(addr)
        } else {
            CfgEdgeTarget::External(addr)
        }
    }

    fn legacy_successor_edges(&self, block: &LiftedBlock, kind: CfgEdgeKind) -> Vec<CfgEdge> {
        block
            .successors
            .iter()
            .map(|&addr| CfgEdge::new(block.start_addr, kind, self.edge_target_for_addr(addr)))
            .collect()
    }
}

/// A fully lifted function ready for verification.
#[derive(Debug, Clone)]
pub struct LiftedFunction {
    /// Function name (from symbol table).
    pub name: String,
    /// Entry point address.
    pub entry_point: u64,
    /// The recovered control flow graph.
    pub cfg: Cfg,
    /// The TrustIr representation of the function body.
    pub trust_ir_body: trust_types::VerifiableBody,
    /// SSA form computed from the CFG (None if SSA construction was skipped).
    pub ssa: Option<crate::ssa::SsaForm>,
    /// Proof annotations linking TrustIr statements to binary offsets.
    pub annotations: Vec<ProofAnnotation>,
    /// Memory accesses recovered from machine semantics.
    pub memory_accesses: Vec<MemoryAccessFact>,
    /// Conservative trust level for this lifted artifact.
    pub trust_level: TrustLevel,
    /// Unsupported features encountered while producing this artifact.
    pub unsupported: UnsupportedLedger,
}

/// Proof annotation linking a TrustIr statement back to its binary source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofAnnotation {
    /// TrustIr block index.
    pub block_id: usize,
    /// Statement index within the block.
    pub stmt_index: usize,
    /// Original binary offset.
    pub binary_offset: u64,
    /// Legacy compact instruction encoding.
    pub encoding: u32,
    /// Original instruction size in bytes.
    pub instruction_size: u8,
    /// Original instruction bytes as decoded from the input stream.
    pub instruction_bytes: Vec<u8>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cfg_add_and_lookup() {
        let mut cfg = Cfg::new();
        let block = LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        };
        let idx = cfg.add_block(block);
        assert_eq!(idx, 0);
        assert_eq!(cfg.block_index(0x1000), Some(0));
        assert_eq!(cfg.block_index(0x2000), None);
        assert_eq!(cfg.block_count(), 1);
    }

    #[test]
    fn test_edges_for_conditional_external_arm() {
        let mut cfg = Cfg::new();
        cfg.add_block(LiftedBlock {
            id: 0,
            start_addr: 0x1000,
            instructions: vec![
                trust_disasm::decode_aarch64(&0xB4000080u32.to_le_bytes(), 0x1000)
                    .expect("decode CBZ"),
            ],
            successors: vec![0x1004],
            is_return: false,
        });
        cfg.add_block(LiftedBlock {
            id: 1,
            start_addr: 0x1004,
            instructions: vec![],
            successors: vec![],
            is_return: true,
        });

        let edges = cfg.edges_for_block(&cfg.blocks[0]);
        assert!(edges.contains(&CfgEdge::new(
            0x1000,
            CfgEdgeKind::ConditionalFalse,
            CfgEdgeTarget::Internal(0x1004),
        )));
        assert!(edges.contains(&CfgEdge::new(
            0x1000,
            CfgEdgeKind::ConditionalTrue,
            CfgEdgeTarget::External(0x1010),
        )));
    }
}
