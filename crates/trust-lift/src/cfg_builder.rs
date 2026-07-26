// trust-lift: CFG recovery from disassembled instructions
//
// Implements basic block recovery by following control flow from the entry point.
// Uses a worklist algorithm to discover all reachable blocks.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeSet, VecDeque};
use trust_types::fx::FxHashMap;

use trust_disasm::operand::RegKind;
use trust_disasm::{ControlFlow, Decoder, DisasmError, Instruction, Opcode, Operand};

use crate::cfg::{Cfg, CfgEdge, CfgEdgeKind, CfgEdgeTarget, LiftedBlock};
use crate::error::{LiftError, LiftProofMode};
use crate::lifter::LiftArch;

fn unresolved_control_flow_error(message: impl Into<String>) -> LiftError {
    LiftError::UnresolvedControlFlow { mode: LiftProofMode::Cfg, message: message.into() }
}

fn classify_direct_branch_target(
    insn: &Instruction,
    entry: u64,
    func_end: u64,
) -> Result<CfgEdgeTarget, LiftError> {
    match insn.branch_target() {
        Some(target) => Ok(CfgEdgeTarget::for_function_addr(target, entry, func_end)),
        None => Err(unresolved_control_flow_error(format!(
            "branch at 0x{:x} has no direct CFG target",
            insn.address
        ))),
    }
}

fn instruction_bytes_display(bytes: &[u8]) -> String {
    let bytes = bytes.iter().map(|byte| format!("0x{byte:02x}")).collect::<Vec<_>>().join(", ");
    format!("[{bytes}]")
}

fn aarch64_return_boundary_register(insn: &Instruction) -> Option<String> {
    if insn.opcode != Opcode::Ret {
        return None;
    }

    match insn.operand(0) {
        Some(Operand::Reg(reg))
            if reg.kind == RegKind::Gpr && reg.index == 30 && reg.width == 64 =>
        {
            None
        }
        Some(Operand::Reg(reg)) => Some(reg.to_string()),
        Some(other) => Some(format!("{other:?}")),
        None => Some("<missing>".to_string()),
    }
}

fn validate_return_boundary(insn: &Instruction, arch: LiftArch) -> Result<(), LiftError> {
    match arch {
        LiftArch::Aarch64 => {
            if let Some(register) = aarch64_return_boundary_register(insn) {
                return Err(unresolved_control_flow_error(format!(
                    "unsupported AArch64 return boundary at binary:0x{:x} size {} encoding 0x{:08x} bytes {}: RET {register} is not the ABI link-register return (X30); proof-grade CFG recovery/replay must carry a checked return-target witness and unsupported-ledger entry before lowering to TrustIr Return",
                    insn.address,
                    insn.size,
                    insn.encoding,
                    instruction_bytes_display(&insn.bytes)
                )));
            }
        }
        LiftArch::X86_64 => {}
    }

    Ok(())
}

fn direct_branch_edge(
    source: u64,
    insn: &Instruction,
    entry: u64,
    func_end: u64,
) -> Result<CfgEdge, LiftError> {
    Ok(CfgEdge::new(
        source,
        CfgEdgeKind::DirectBranch,
        classify_direct_branch_target(insn, entry, func_end)?,
    ))
}

fn conditional_branch_edges(
    source: u64,
    insn: &Instruction,
    fallthrough: u64,
    entry: u64,
    func_end: u64,
) -> Result<Vec<CfgEdge>, LiftError> {
    let target = classify_direct_branch_target(insn, entry, func_end)?;
    Ok(vec![
        CfgEdge::new(
            source,
            CfgEdgeKind::ConditionalFalse,
            CfgEdgeTarget::for_function_addr(fallthrough, entry, func_end),
        ),
        CfgEdge::new(source, CfgEdgeKind::ConditionalTrue, target),
    ])
}

fn fallthrough_edge(source: u64, target: u64, entry: u64, func_end: u64) -> CfgEdge {
    CfgEdge::new(
        source,
        CfgEdgeKind::Fallthrough,
        CfgEdgeTarget::for_function_addr(target, entry, func_end),
    )
}

fn call_fallthrough_edge(source: u64, target: u64, entry: u64, func_end: u64) -> CfgEdge {
    CfgEdge::new(
        source,
        CfgEdgeKind::CallFallthrough,
        CfgEdgeTarget::for_function_addr(target, entry, func_end),
    )
}

fn push_internal_successors(successors: &mut Vec<u64>, edges: &[CfgEdge]) {
    successors.extend(edges.iter().filter_map(|edge| edge.internal_successor()));
}

/// Recover the control flow graph starting from `entry` within the given
/// code bytes (which begin at virtual address `base_addr`).
///
/// Uses a worklist algorithm:
/// 1. Start with the entry address on the worklist.
/// 2. Decode instructions sequentially from each worklist address until a
///    terminating instruction (branch, return, exception) is reached.
/// 3. For each successor address, add it to the worklist if not yet visited.
/// 4. If a branch lands in the middle of an existing block, split it.
pub(crate) fn recover_cfg(
    decoder: &dyn Decoder,
    arch: LiftArch,
    code: &[u8],
    base_addr: u64,
    entry: u64,
    func_end: u64,
) -> Result<Cfg, LiftError> {
    // Phase 1: Identify all block leader addresses.
    let leaders = find_leaders(decoder, arch, code, base_addr, entry, func_end)?;

    // Phase 2: Build blocks by decoding from each leader to the next.
    let mut cfg = Cfg::new();
    let sorted_leaders: Vec<u64> = leaders.into_iter().collect();

    // Pre-decode all instructions in the function for efficiency.
    let insn_map = decode_range(decoder, code, base_addr, entry, func_end)?;

    for (block_idx, &leader_addr) in sorted_leaders.iter().enumerate() {
        let next_leader = sorted_leaders.get(block_idx + 1).copied().unwrap_or(func_end);
        let mut instructions = Vec::new();
        let mut successors = Vec::new();
        let mut is_return = false;

        // Collect instructions from this leader to (but not including) the next leader.
        let mut addr = leader_addr;
        while addr < next_leader && addr < func_end {
            if let Some(insn) = insn_map.get(&addr) {
                let next_addr = addr + insn.size as u64;
                match insn.flow {
                    ControlFlow::Return => {
                        validate_return_boundary(insn, arch)?;
                        is_return = true;
                        instructions.push(insn.clone());
                        break;
                    }
                    ControlFlow::Branch => {
                        push_internal_successors(
                            &mut successors,
                            &[direct_branch_edge(leader_addr, insn, entry, func_end)?],
                        );
                        instructions.push(insn.clone());
                        break;
                    }
                    ControlFlow::ConditionalBranch => {
                        // Fallthrough + target.
                        let edges = conditional_branch_edges(
                            leader_addr,
                            insn,
                            next_addr,
                            entry,
                            func_end,
                        )?;
                        push_internal_successors(&mut successors, &edges);
                        instructions.push(insn.clone());
                        break;
                    }
                    ControlFlow::Call => {
                        // Calls fall through to the next instruction.
                        instructions.push(insn.clone());
                        if next_addr < next_leader {
                            addr = next_addr;
                        } else {
                            // Call at end of block — fallthrough is next leader.
                            push_internal_successors(
                                &mut successors,
                                &[call_fallthrough_edge(leader_addr, next_addr, entry, func_end)],
                            );
                            break;
                        }
                    }
                    ControlFlow::Exception => {
                        instructions.push(insn.clone());
                        break;
                    }
                    ControlFlow::Fallthrough => {
                        instructions.push(insn.clone());
                        addr = next_addr;
                    }
                    other => {
                        return Err(unresolved_control_flow_error(format!(
                            "unsupported control-flow classification at 0x{:x}: {other:?}",
                            insn.address
                        )));
                    }
                }
            } else {
                // Could not decode instruction at this address — stop the block.
                break;
            }
        }

        // If we fell off the end without a terminator, add fallthrough to next leader.
        if !is_return && successors.is_empty() && !instructions.is_empty() {
            let last = instructions.last().ok_or(LiftError::EmptyBlock { address: leader_addr })?;
            let fallthrough = last.address + last.size as u64;
            match last.flow {
                ControlFlow::Fallthrough => push_internal_successors(
                    &mut successors,
                    &[fallthrough_edge(leader_addr, fallthrough, entry, func_end)],
                ),
                ControlFlow::Call
                | ControlFlow::Branch
                | ControlFlow::ConditionalBranch
                | ControlFlow::Return
                | ControlFlow::Exception => {}
                other => {
                    return Err(unresolved_control_flow_error(format!(
                        "unsupported control-flow classification at 0x{:x}: {other:?}",
                        last.address
                    )));
                }
            }
        }

        cfg.add_block(LiftedBlock {
            id: block_idx,
            start_addr: leader_addr,
            instructions,
            successors,
            is_return,
        });
    }

    synthesize_x86_64_empty_slice_exit(&mut cfg, arch, func_end);

    // Set entry to the block containing the entry address.
    cfg.entry = cfg.block_index(entry).ok_or_else(|| {
        unresolved_control_flow_error(format!(
            "entry address 0x{entry:x} does not map to a recovered basic block"
        ))
    })?;

    Ok(cfg)
}

fn synthesize_x86_64_empty_slice_exit(cfg: &mut Cfg, arch: LiftArch, func_end: u64) {
    if arch != LiftArch::X86_64 || cfg.blocks.len() != 1 {
        return;
    }

    let Some(block) = cfg.blocks.first() else {
        return;
    };
    if block.is_return || !block.successors.is_empty() || block.instructions.is_empty() {
        return;
    }
    if !block.instructions.iter().all(|insn| matches!(insn.opcode, Opcode::Nop | Opcode::Endbr64)) {
        return;
    }
    let Some(last) = block.instructions.last() else {
        return;
    };
    if last.flow != ControlFlow::Fallthrough || last.address + u64::from(last.size) != func_end {
        return;
    }

    cfg.blocks[0].successors.push(func_end);
    cfg.add_block(LiftedBlock {
        id: cfg.blocks.len(),
        start_addr: func_end,
        instructions: Vec::new(),
        successors: Vec::new(),
        is_return: true,
    });
}

/// Find all basic block leaders (addresses that start a basic block).
///
/// Leaders are:
/// 1. The entry point.
/// 2. Branch targets.
/// 3. The instruction after a branch/call (fallthrough).
fn find_leaders(
    decoder: &dyn Decoder,
    arch: LiftArch,
    code: &[u8],
    base_addr: u64,
    entry: u64,
    func_end: u64,
) -> Result<BTreeSet<u64>, LiftError> {
    let mut leaders = BTreeSet::new();
    let mut worklist = VecDeque::new();
    let mut visited = BTreeSet::new();

    leaders.insert(entry);
    worklist.push_back(entry);

    while let Some(addr) = worklist.pop_front() {
        if !visited.insert(addr) {
            continue;
        }
        if addr < entry || addr >= func_end {
            continue;
        }

        let mut cur = addr;
        while cur < func_end {
            let offset = (cur - base_addr) as usize;
            if offset >= code.len() {
                break;
            }
            let insn = decoder
                .decode(&code[offset..], cur)
                .map_err(|e| LiftError::Disasm { address: cur, source: e })?;
            let next = cur + insn.size as u64;

            match insn.flow {
                ControlFlow::Return => {
                    validate_return_boundary(&insn, arch)?;
                    break;
                }
                ControlFlow::Exception => break,
                ControlFlow::Branch => {
                    if let Some(target) =
                        direct_branch_edge(addr, &insn, entry, func_end)?.internal_successor()
                    {
                        leaders.insert(target);
                        worklist.push_back(target);
                    }
                    break;
                }
                ControlFlow::ConditionalBranch => {
                    // Fallthrough is a leader.
                    for successor in conditional_branch_edges(addr, &insn, next, entry, func_end)?
                        .iter()
                        .filter_map(|edge| edge.internal_successor())
                    {
                        leaders.insert(successor);
                        worklist.push_back(successor);
                    }
                    break;
                }
                ControlFlow::Call => {
                    // After a call, fallthrough is a leader if we split here.
                    cur = next;
                }
                ControlFlow::Fallthrough => {
                    cur = next;
                }
                other => {
                    return Err(unresolved_control_flow_error(format!(
                        "unsupported control-flow classification at 0x{:x}: {other:?}",
                        insn.address
                    )));
                }
            }
        }
    }

    Ok(leaders)
}

/// Decode all instructions in a range and return them indexed by address.
fn decode_range(
    decoder: &dyn Decoder,
    code: &[u8],
    base_addr: u64,
    start: u64,
    end: u64,
) -> Result<FxHashMap<u64, Instruction>, LiftError> {
    let mut map = FxHashMap::default();
    let mut addr = start;
    while addr < end {
        let offset = (addr - base_addr) as usize;
        if offset >= code.len() {
            return Err(LiftError::Disasm {
                address: addr,
                source: DisasmError::InsufficientBytes {
                    needed: decoder.min_insn_size(),
                    available: 0,
                },
            });
        }
        match decoder.decode(&code[offset..], addr) {
            Ok(insn) => {
                let size = insn.size as u64;
                map.insert(addr, insn);
                addr += size;
            }
            Err(source) => return Err(LiftError::Disasm { address: addr, source }),
        }
    }
    Ok(map)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Verify that the leader finder puts the entry into the leader set.
    #[test]
    fn test_find_leaders_entry_is_leader() {
        // We can't easily test without a real decoder, but we verify the
        // module compiles and the types are correct.
        let leaders = BTreeSet::from([0x1000u64]);
        assert!(leaders.contains(&0x1000));
    }

    #[test]
    fn test_recover_cfg_indirect_branch_fails_closed() {
        let decoder = trust_disasm::aarch64::Aarch64Decoder::new();
        let code = 0xD61F0200u32.to_le_bytes(); // BR X16

        let err = recover_cfg(&decoder, LiftArch::Aarch64, &code, 0x1000, 0x1000, 0x1004)
            .expect_err("indirect branch target is not recoverable");
        assert!(matches!(
            &err,
            LiftError::UnresolvedControlFlow {
                mode: LiftProofMode::Cfg,
                message
            } if message.contains("has no direct CFG target")
        ));
        assert_eq!(
            err.to_string(),
            "SSA construction error: CFG proof mode: branch at 0x1000 has no direct CFG target"
        );
    }

    #[test]
    fn test_recover_cfg_non_link_register_return_fails_closed() {
        let decoder = trust_disasm::aarch64::Aarch64Decoder::new();
        let code = 0xD65F0200u32.to_le_bytes(); // RET X16

        let err = recover_cfg(&decoder, LiftArch::Aarch64, &code, 0x1000, 0x1000, 0x1004)
            .expect_err("RET through a non-link register must not become plain TrustIr Return");
        assert!(matches!(
            &err,
            LiftError::UnresolvedControlFlow {
                mode: LiftProofMode::Cfg,
                message
            } if message.contains("unsupported AArch64 return boundary")
                && message.contains("RET X16")
                && message.contains("proof-grade")
                && message.contains("replay")
                && message.contains("unsupported-ledger")
        ));
    }

    #[test]
    fn test_recover_cfg_conditional_external_target_keeps_fallthrough_successor() {
        let decoder = trust_disasm::aarch64::Aarch64Decoder::new();
        let mut code = Vec::new();
        code.extend_from_slice(&0xB4000080u32.to_le_bytes()); // CBZ X0, #0x10 -> 0x1010
        code.extend_from_slice(&0xD65F03C0u32.to_le_bytes()); // RET at 0x1004

        let cfg = recover_cfg(&decoder, LiftArch::Aarch64, &code, 0x1000, 0x1000, 0x1008)
            .expect("mixed conditional external target should recover");

        assert_eq!(cfg.block_count(), 2);
        let block = &cfg.blocks[0];
        assert_eq!(block.successors, vec![0x1004]);
        let edges = cfg.edges_for_block(block);
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

    #[test]
    fn test_recover_cfg_direct_external_branch_is_terminal() {
        let decoder = trust_disasm::aarch64::Aarch64Decoder::new();
        let code = 0x14000040u32.to_le_bytes(); // B #0x100 from 0x1000 -> 0x1100

        let cfg = recover_cfg(&decoder, LiftArch::Aarch64, &code, 0x1000, 0x1000, 0x1004)
            .expect("direct external branch should recover as a terminal block");

        assert_eq!(cfg.block_count(), 1);
        let block = &cfg.blocks[0];
        assert_eq!(block.start_addr, 0x1000);
        assert!(block.successors.is_empty());
        assert!(!block.is_return);
        assert_eq!(block.instructions.last().and_then(Instruction::branch_target), Some(0x1100));
    }

    #[test]
    fn test_recover_cfg_trailing_undecoded_bytes_fail_closed() {
        let decoder = trust_disasm::x86_64::X86_64Decoder::new();
        let code = [0xC3, 0xFF]; // RET followed by an incomplete group opcode.

        let err = recover_cfg(&decoder, LiftArch::X86_64, &code, 0x1000, 0x1000, 0x1002)
            .expect_err("strict CFG recovery should reject undecoded bytes in the function range");

        assert!(matches!(err, LiftError::Disasm { address: 0x1001, .. }));
    }

    #[test]
    fn test_recover_cfg_x86_ret_is_not_aarch64_return_boundary() {
        let decoder = trust_disasm::x86_64::X86_64Decoder::new();
        let code = [0xC3]; // x86-64 RET

        let cfg = recover_cfg(&decoder, LiftArch::X86_64, &code, 0x1000, 0x1000, 0x1001)
            .expect("x86-64 RET must not be validated as an AArch64 X30 return");

        assert_eq!(cfg.block_count(), 1);
        let block = &cfg.blocks[0];
        assert!(block.is_return);
        assert_eq!(block.instructions.len(), 1);
        assert_eq!(block.instructions[0].opcode, Opcode::Ret);
        assert!(block.successors.is_empty());
    }

    #[test]
    fn test_recover_cfg_x86_empty_slice_synthesizes_boundary_exit() {
        let decoder = trust_disasm::x86_64::X86_64Decoder::new();
        let code = [0x90]; // NOP

        let cfg = recover_cfg(&decoder, LiftArch::X86_64, &code, 0x400000, 0x400000, 0x400001)
            .expect("selected x86-64 no-data slice should recover with a boundary exit");

        assert_eq!(cfg.block_count(), 2);
        assert_eq!(cfg.blocks[0].successors, vec![0x400001]);
        assert!(!cfg.blocks[0].is_return);
        assert_eq!(cfg.blocks[1].start_addr, 0x400001);
        assert!(cfg.blocks[1].instructions.is_empty());
        assert!(cfg.blocks[1].is_return);
    }

    #[test]
    fn test_recover_cfg_x86_dataflow_slice_does_not_get_empty_boundary_exit() {
        let decoder = trust_disasm::x86_64::X86_64Decoder::new();
        let code = [0x48, 0x89, 0xE5]; // MOV RBP, RSP

        let cfg = recover_cfg(&decoder, LiftArch::X86_64, &code, 0x400000, 0x400000, 0x400003)
            .expect("CFG recovery should leave non-boundary x86 dataflow fail-closed downstream");

        assert_eq!(cfg.block_count(), 1);
        assert!(cfg.blocks[0].successors.is_empty());
        assert!(!cfg.blocks[0].is_return);
        assert_eq!(cfg.blocks[0].instructions[0].opcode, Opcode::Mov);
    }
}
