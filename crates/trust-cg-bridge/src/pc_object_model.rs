//! Admission to execution over relocatable-object instruction offsets.
//!
//! A section offset identifies a CFG location; it is not a loaded address.
//! Address-producing instructions need a placed-image witness that CER does
//! not currently have. This boundary is independent of relocation presence.

use trust_disasm::Instruction;
use trust_disasm::instruction::ControlFlow;
use trust_disasm::opcode::Opcode;
use trust_disasm::operand::{MemoryOperand, Operand};

/// Whether evaluating this instruction's address/control effects requires an actual
/// runtime placement. Relative CFG transfers retain their existing structural
/// target/site checks in CER; this function grants them no separate authority.
pub(crate) fn requires_runtime_placement(instruction: &Instruction) -> bool {
    if matches!(
        instruction.opcode,
        Opcode::Adr | Opcode::Adrp | Opcode::LdrLiteral | Opcode::Br | Opcode::Blr
    ) {
        return true;
    }
    let relative_control = matches!(
        (instruction.opcode, instruction.flow),
        (Opcode::B, ControlFlow::Branch)
            | (Opcode::Bl, ControlFlow::Call)
            | (
                Opcode::BCond | Opcode::Cbz | Opcode::Cbnz | Opcode::Tbz | Opcode::Tbnz,
                ControlFlow::ConditionalBranch
            )
    );
    // A register target is an absolute runtime address even when symbolic
    // evaluation reduces it to a literal that numerically equals an object
    // offset. Only the authenticated relative-control families below may
    // produce object-coordinate targets. RET has its separate ABI/LR check.
    if matches!(
        instruction.flow,
        ControlFlow::Branch | ControlFlow::Call | ControlFlow::ConditionalBranch
    ) && !relative_control
    {
        return true;
    }
    instruction.operands().any(|operand| match operand {
        Operand::PcRelAddr(_) => !relative_control,
        Operand::Mem(MemoryOperand::PcRelative { .. } | MemoryOperand::RipRelative { .. }) => true,
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    use trust_disasm::decode_aarch64;

    use super::*;

    fn decode(word: u32) -> Instruction {
        decode_aarch64(&word.to_le_bytes(), 0x1234_5678).unwrap()
    }

    #[test]
    fn address_data_and_all_literal_memory_operands_require_placement() {
        // LDRSW literal has Opcode::Ldrsw, not LdrLiteral. PRFM is conservatively
        // outside this object-only model whenever its address is PC-relative.
        for (word, opcode) in [
            (0x1000_0000, Opcode::Adr),
            (0x9000_0000, Opcode::Adrp),
            (0x1800_0000, Opcode::LdrLiteral),
            (0x5800_0000, Opcode::LdrLiteral),
            (0x9800_0000, Opcode::Ldrsw),
            (0xd800_0000, Opcode::Prfm),
        ] {
            let instruction = decode(word);
            assert_eq!(instruction.opcode, opcode);
            assert!(requires_runtime_placement(&instruction), "{instruction:?}");
        }
    }

    #[test]
    fn relative_control_and_register_based_data_retain_their_existing_checks() {
        for word in [
            0x1400_0001, // B
            0x9400_0001, // BL
            0x5400_0020, // B.EQ
            0xb400_0020, // CBZ X0
            0xb500_0020, // CBNZ X0
            0x3600_0020, // TBZ W0
            0x3700_0020, // TBNZ W0
            0xd65f_03c0, // RET X30
            0xd280_0000, // MOV X0,#0
            0x9100_0420, // ADD X0,X1,#1
            0xf940_0020, // LDR X0,[X1]
            0xb980_0020, // LDRSW X0,[X1], register-based counterpart
            0xf900_0020, // STR X0,[X1]
        ] {
            let instruction = decode(word);
            assert!(!requires_runtime_placement(&instruction), "{instruction:?}");
        }
    }

    #[test]
    fn indirect_control_requires_placement_independently_of_a_constant_target() {
        for word in [0xd61f_0120, 0xd63f_0120] {
            let mut instruction = decode(word);
            assert!(requires_runtime_placement(&instruction), "{instruction:?}");
            instruction.flow = ControlFlow::Fallthrough;
            assert!(requires_runtime_placement(&instruction), "{instruction:?}");
        }
        let mut future_control = decode(0xd503_201f); // NOP
        for flow in [ControlFlow::Branch, ControlFlow::Call, ControlFlow::ConditionalBranch] {
            future_control.flow = flow;
            assert!(requires_runtime_placement(&future_control), "{future_control:?}");
        }
    }

    #[test]
    fn pc_relative_address_permission_requires_matching_opcode_and_control_flow() {
        let mut branch = decode(0x1400_0001);
        branch.flow = ControlFlow::Fallthrough;
        assert!(requires_runtime_placement(&branch));
        let mut call = decode(0x9400_0001);
        call.opcode = Opcode::Nop;
        assert!(requires_runtime_placement(&call));
        let mut address = decode(0x1000_0000);
        address.flow = ControlFlow::Branch;
        assert!(requires_runtime_placement(&address));
    }
}
