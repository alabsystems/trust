//! A bounded, non-authorizing recovery of a retained scalar equality proof.
//! This checks a closed source/machine fragment, not general frame/ABI or
//! linked-executable refinement. The existing gate and its grades are unchanged.

use std::collections::BTreeMap;

use trust_disasm::operand::{Operand, RegKind};
use trust_disasm::{Opcode, decode_aarch64};
use trust_ir::inst::{BinOp, Inst};
use trust_ir::{Constant, FuncAttrs, Ty};
use trust_machine_sem::{Aarch64Semantics, Effect, MachineState, Semantics};

use super::*;

const MAX_SOURCE_INSTRUCTIONS: usize = 128;
const MAX_MACHINE_INSTRUCTIONS: usize = 256;
const MAX_EXPANDED_VALUE: usize = 512;
const MAX_EXPANDED_TOTAL: usize = 4096;

fn scalar_width(ty: &Ty) -> Result<u32, String> {
    match ty {
        Ty::U8 => Ok(8),
        Ty::U16 => Ok(16),
        Ty::U32 => Ok(32),
        Ty::U64 => Ok(64),
        _ => Err("scalar certificate: unsupported source type".into()),
    }
}

pub(super) fn qualify_source(source: &TrustIrGateSource) -> Result<(), String> {
    require_unique_source_ids(&source.module)?;
    let function = source
        .module
        .function_by_id(source.func_id)
        .ok_or("scalar certificate: missing function")?;
    if function.name != source.symbol
        || function.blocks.len() != 1
        || function.summary.is_some()
        || !function.proofs.is_empty()
        || function.attrs != FuncAttrs::default()
        || function.source_provenance.is_some()
    {
        return Err("scalar certificate: unsupported source context/claims/blocks".into());
    }
    let signature = source
        .module
        .func_types
        .get(function.ty.index() as usize)
        .ok_or("scalar certificate: missing signature")?;
    let block = &function.blocks[0];
    if block.id != function.entry
        || signature.is_vararg
        || signature.params.len() > 8
        || signature.returns.len() != 1
        || block.params.len() != signature.params.len()
        || block.body.is_empty()
        || block.body.len() > MAX_SOURCE_INSTRUCTIONS
    {
        return Err("scalar certificate: unsupported entry/signature/population".into());
    }
    scalar_width(&signature.returns[0])?;
    let mut values = BTreeMap::new();
    for ((id, ty), expected) in block.params.iter().zip(&signature.params) {
        scalar_width(ty)?;
        if ty != expected || values.insert(*id, (ty.clone(), 1usize)).is_some() {
            return Err("scalar certificate: parameter type/identity mismatch".into());
        }
    }
    let mut total = 0usize;
    for (index, node) in block.body.iter().enumerate() {
        if node.proof_context.is_some() || !node.proofs.is_empty() {
            return Err("scalar certificate: source proof/assumption carrier".into());
        }
        let result = match &node.inst {
            Inst::Const { ty, value: Constant::Int(value) } => {
                let width = scalar_width(ty)?;
                if *value < 0 || (*value as u128) >= (1u128 << width) {
                    return Err("scalar certificate: unsigned literal outside type".into());
                }
                Some((ty.clone(), 1))
            }
            Inst::BinOp {
                op: BinOp::Add | BinOp::Sub | BinOp::And | BinOp::Or | BinOp::Xor,
                ty,
                lhs,
                rhs,
            } => {
                scalar_width(ty)?;
                let left = values.get(lhs).ok_or("scalar certificate: undefined left SSA")?;
                let right = values.get(rhs).ok_or("scalar certificate: undefined right SSA")?;
                if &left.0 != ty || &right.0 != ty {
                    return Err("scalar certificate: binary operand type mismatch".into());
                }
                let size = left
                    .1
                    .checked_add(right.1)
                    .and_then(|n| n.checked_add(1))
                    .ok_or("scalar certificate: expression size overflow")?;
                Some((ty.clone(), size))
            }
            Inst::Return { values: returned } if index + 1 == block.body.len() => {
                if !node.results.is_empty()
                    || returned.len() != 1
                    || values.get(&returned[0]).map(|value| &value.0) != Some(&signature.returns[0])
                {
                    return Err("scalar certificate: final return type/identity mismatch".into());
                }
                None
            }
            _ => {
                return Err(
                    "scalar certificate: unsupported source instruction, including unused effect"
                        .into(),
                );
            }
        };
        if let Some((ty, cost)) = result {
            total =
                total.checked_add(cost).ok_or("scalar certificate: source expression budget")?;
            if index + 1 == block.body.len()
                || node.results.len() != 1
                || cost > MAX_EXPANDED_VALUE
                || total > MAX_EXPANDED_TOTAL
                || values.insert(node.results[0], (ty, cost)).is_some()
            {
                return Err("scalar certificate: source SSA/result/expression budget".into());
            }
        }
    }
    Ok(())
}

fn u16_at(bytes: &[u8], at: usize) -> Result<u16, String> {
    let end = at.checked_add(2).ok_or("scalar certificate: offset overflow")?;
    Ok(u16::from_le_bytes(
        bytes.get(at..end).ok_or("scalar certificate: truncated u16")?.try_into().unwrap(),
    ))
}
fn u32_at(bytes: &[u8], at: usize) -> Result<u32, String> {
    let end = at.checked_add(4).ok_or("scalar certificate: offset overflow")?;
    Ok(u32::from_le_bytes(
        bytes.get(at..end).ok_or("scalar certificate: truncated u32")?.try_into().unwrap(),
    ))
}
fn u64_at(bytes: &[u8], at: usize) -> Result<u64, String> {
    let end = at.checked_add(8).ok_or("scalar certificate: offset overflow")?;
    Ok(u64::from_le_bytes(
        bytes.get(at..end).ok_or("scalar certificate: truncated u64")?.try_into().unwrap(),
    ))
}
fn extent(bytes: &[u8], at: usize, count: usize, width: usize) -> Result<usize, String> {
    let end = count
        .checked_mul(width)
        .and_then(|n| at.checked_add(n))
        .ok_or("scalar certificate: extent overflow")?;
    bytes.get(at..end).ok_or("scalar certificate: truncated extent")?;
    Ok(end)
}

// Initial proof production refuses every relocation. Text equality cannot
// attest the machine code after a linker modifies it. This is an extra refusal
// on the diagnostic fallback only, not a change to the existing emitter.
fn no_relocations(object: &[u8]) -> Result<(), String> {
    bounded_part(object)?;
    if object.starts_with(&[0xcf, 0xfa, 0xed, 0xfe]) {
        extent(object, 0, 1, 32)?;
        if u32_at(object, 4)? != 0x0100_000c || u32_at(object, 12)? != 1 {
            return Err("scalar certificate: not an AArch64 relocatable Mach-O".into());
        }
        let count = u32_at(object, 16)? as usize;
        let size = u32_at(object, 20)? as usize;
        let end = extent(object, 32, size, 1)?;
        let mut at = 32usize;
        let mut seen = BTreeSet::new();
        let mut text_sections = 0usize;
        for _ in 0..count {
            if at.checked_add(8).is_none_or(|n| n > end) {
                return Err("scalar certificate: truncated command".into());
            }
            let tag = u32_at(object, at)?;
            if !seen.insert(tag) {
                return Err("scalar certificate: duplicate Mach-O command".into());
            }
            let size = u32_at(object, at + 4)? as usize;
            if size < 8 || size % 8 != 0 {
                return Err("scalar certificate: invalid command size".into());
            }
            let next = extent(object, at, size, 1)?;
            if next > end {
                return Err("scalar certificate: command outside table".into());
            }
            match tag {
                0x19 => {
                    if size < 72 {
                        return Err("scalar certificate: truncated segment".into());
                    }
                    let sections = u32_at(object, at + 64)? as usize;
                    if sections != 1 {
                        return Err("scalar certificate: requires one complete text section".into());
                    }
                    if extent(object, at + 72, sections, 80)? != next {
                        return Err("scalar certificate: segment section extent".into());
                    }
                    for section in 0..sections {
                        let header = at + 72 + section * 80;
                        if &object[header..header + 16] != b"__text\0\0\0\0\0\0\0\0\0\0" {
                            return Err("scalar certificate: unsupported non-text section".into());
                        }
                        text_sections += 1;
                        if u32_at(object, at + 72 + section * 80 + 60)? != 0 {
                            return Err(
                                "scalar certificate: relocation-bearing object is not modeled"
                                    .into(),
                            );
                        }
                    }
                }
                2 if size == 24 => {} // LC_SYMTAB; names independently checked below.
                0x0b if size == 80 => {
                    // LC_DYSYMTAB auxiliary tables/indirections and relocations
                    // are all outside this closed scalar fragment.
                    for field in [36, 44, 52, 60, 68, 76] {
                        if u32_at(object, at + field)? != 0 {
                            return Err(
                                "scalar certificate: dynamic/relocation table is not modeled"
                                    .into(),
                            );
                        }
                    }
                }
                0x32 if size >= 24 => {
                    if extent(object, at + 24, u32_at(object, at + 20)? as usize, 8)? != next {
                        return Err("scalar certificate: build-version table extent".into());
                    }
                }
                _ => return Err("scalar certificate: unsupported Mach-O command".into()),
            }
            at = next;
        }
        if at != end || text_sections != 1 || !seen.contains(&2) {
            return Err("scalar certificate: unconsumed/missing command or text bytes".into());
        }
    } else if object.starts_with(b"\x7fELF\x02\x01\x01") {
        extent(object, 0, 1, 64)?;
        if u16_at(object, 16)? != 1
            || u16_at(object, 18)? != 183
            || u16_at(object, 52)? != 64
            || u16_at(object, 56)? != 0
        {
            return Err("scalar certificate: not a simple AArch64 relocatable ELF".into());
        }
        let table =
            usize::try_from(u64_at(object, 40)?).map_err(|_| "scalar certificate: table offset")?;
        let size = u16_at(object, 58)? as usize;
        let count = u16_at(object, 60)? as usize;
        if size != 64 || count == 0 {
            return Err("scalar certificate: unsupported ELF sections".into());
        }
        extent(object, table, count, size)?;
        let mut text_sections = 0usize;
        for index in 0..count {
            let at = table + index * size;
            let kind = u32_at(object, at + 4)?;
            let flags = u64_at(object, at + 8)?;
            if flags & 4 != 0 {
                if kind != 1 {
                    return Err("scalar certificate: executable non-PROGBITS section".into());
                }
                text_sections += 1;
            } else if flags & 2 != 0 {
                return Err("scalar certificate: non-text allocated section".into());
            }
            if matches!(kind, 4 | 9) && u64_at(object, at + 32)? != 0 {
                return Err("scalar certificate: relocation-bearing object is not modeled".into());
            }
            if !matches!(kind, 0..=4 | 8 | 9) {
                return Err("scalar certificate: unsupported ELF section kind".into());
            }
        }
        if text_sections != 1 {
            return Err("scalar certificate: complete ELF text population".into());
        }
    } else {
        return Err("scalar certificate: unsupported object format".into());
    }
    Ok(())
}

pub(super) fn qualify_machine(
    source: &TrustIrGateSource,
    object: &[u8],
    arch: TrustCgTargetArch,
) -> Result<(), String> {
    if arch != TrustCgTargetArch::AArch64 {
        return Err("scalar certificate: unsupported architecture".into());
    }
    no_relocations(object)?;
    let symbols = raw_symbols(object)?;
    if symbols.len() != 1 || symbols[0].name != source.symbol || symbols[0].offset != 0 {
        return Err("scalar certificate: exact entry/symbol population mismatch".into());
    }
    let (text, base) = extract_text_from_object(object)?;
    if text.is_empty() || text.len() % 4 != 0 || text.len() / 4 > MAX_MACHINE_INSTRUCTIONS {
        return Err("scalar certificate: complete text instruction extent".into());
    }
    let state = MachineState::symbolic();
    let mut costs = [1usize; 31];
    let mut total = 0usize;
    for (index, bytes) in text.chunks_exact(4).enumerate() {
        let pc = base.checked_add((index * 4) as u64).ok_or("scalar certificate: PC overflow")?;
        let decoded =
            decode_aarch64(bytes, pc).map_err(|e| format!("scalar certificate: decode {e}"))?;
        let last = index + 1 == text.len() / 4;
        if last {
            if decoded.opcode != Opcode::Ret
                || u32::from_le_bytes(bytes.try_into().unwrap()) != 0xd65f_03c0
            {
                return Err("scalar certificate: final instruction must be RET X30".into());
            }
            let effects = Aarch64Semantics.effects(&state, &decoded).map_err(|e| e.to_string())?;
            if effects
                != vec![
                    Effect::Return { target: state.gpr[30].clone() },
                    Effect::PcUpdate { value: state.gpr[30].clone() },
                ]
            {
                return Err("scalar certificate: return effects differ from original X30".into());
            }
            continue;
        }
        if !matches!(
            decoded.opcode,
            Opcode::Orr
                | Opcode::Movz
                | Opcode::Movn
                | Opcode::Movk
                | Opcode::Add
                | Opcode::Sub
                | Opcode::And
                | Opcode::Eor
                | Opcode::Ubfm
                | Opcode::Sbfm
                | Opcode::Nop
        ) {
            return Err(format!(
                "scalar certificate: unsupported decoded opcode {:?}",
                decoded.opcode
            ));
        }
        let mut cost = 1usize;
        for operand in decoded.operands() {
            match operand {
                Operand::Reg(reg)
                | Operand::ShiftedReg { reg, .. }
                | Operand::ExtendedReg { reg, .. } => {
                    if !matches!(reg.width, 32 | 64) {
                        return Err("scalar certificate: register width".into());
                    }
                    match reg.kind {
                        RegKind::Gpr if reg.index <= 17 => {
                            cost = cost
                                .checked_add(costs[reg.index as usize])
                                .ok_or("scalar certificate: machine expression budget")?
                        }
                        RegKind::Zr if reg.index == 31 => {}
                        _ => {
                            return Err(
                                "scalar certificate: reserved/callee-saved/SP/LR operand".into()
                            );
                        }
                    }
                }
                Operand::Imm(_) | Operand::SignedImm(_) => {}
                _ => return Err("scalar certificate: unsupported decoded operand".into()),
            }
        }
        total = total.checked_add(cost).ok_or("scalar certificate: machine expression budget")?;
        if cost > MAX_EXPANDED_VALUE || total > MAX_EXPANDED_TOTAL {
            return Err("scalar certificate: machine expression budget".into());
        }
        // Fresh symbolic registers suffice to inspect this instruction's full
        // effects. The gate independently composes the actual execution below.
        for effect in Aarch64Semantics.effects(&state, &decoded).map_err(|e| e.to_string())? {
            match effect {
                Effect::RegWrite { index, width: 32 | 64, .. } if index <= 17 => {
                    costs[index as usize] = cost
                }
                Effect::RegWrite { index: 31, width: 32 | 64, .. } => {}
                Effect::PcUpdate { value }
                    if value
                        == Formula::BvAdd(
                            Box::new(state.pc.clone()),
                            Box::new(Formula::BitVec { value: 4, width: 64 }),
                            64,
                        ) => {}
                _ => {
                    return Err(
                        "scalar certificate: unsupported machine effect, including unused effect"
                            .into(),
                    );
                }
            }
        }
    }
    Ok(())
}

pub(super) fn capture_scalar_certificate(
    source: &TrustIrGateSource,
    object: &[u8],
    arch: TrustCgTargetArch,
    budget: &ay_proof::BvExprProofBudget,
) -> Result<ay_proof::BvBlastProof, String> {
    encode(&source.module, MAX_PART_BYTES)?;
    qualify_source(source)?;
    qualify_machine(source, object, arch)?;
    let obligation = trust_ir_gate_obligation(source, object, arch)?;
    if obligation.spec_reach != Formula::Bool(true)
        || obligation.machine_reach != Formula::Bool(true)
        || !obligation.ambient_pre.is_empty()
        || !obligation.spec_side_conditions.is_empty()
        || !obligation.abi_residue.is_empty()
    {
        return Err("scalar certificate: conditional/effect/modeling obligations".into());
    }
    let proof = ay_proof::export_bv_blast_proof_expr_bounded(
        &formula_to_bvexpr(&obligation.machine_value)?,
        &formula_to_bvexpr(&obligation.spec_value)?,
        budget,
    )
    .map_err(|e| format!("scalar certificate: bounded export refused: {e}"))?;
    encode(&proof, MAX_PART_BYTES)?;
    // Reconstruct the graph again and replay THIS retained refutation in the
    // kernel before it becomes a production diagnostic payload. No grade flip.
    replay_bitblast(&obligation.machine_value, &obligation.spec_value, &proof)?;
    Ok(proof)
}

#[cfg(test)]
mod tests;
