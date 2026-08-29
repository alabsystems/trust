// x86-64 ModR/M and SIB byte decoding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Reference: Intel SDM Vol 2A, Table 2-2 (ModR/M) and Table 2-3 (SIB).
//
// ModR/M byte layout: [mod:2][reg:3][rm:3]
// SIB byte layout:    [scale:2][index:3][base:3]

use super::prefix::Prefixes;
use crate::error::DisasmError;
use crate::operand::{MemoryOperand, Operand, Register};

/// Decoded ModR/M byte.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ModRM {
    /// Addressing mode (0-3). 3 = register direct.
    pub(crate) mode: u8,
    /// Register field (3 bits, extended by REX.R to 4 bits).
    pub(crate) reg: u8,
    /// R/M field (3 bits, extended by REX.B to 4 bits).
    pub(crate) rm: u8,
}

impl ModRM {
    /// Parse a ModR/M byte, applying REX extensions.
    #[must_use]
    pub(crate) fn decode(byte: u8, prefixes: &Prefixes) -> Self {
        let mode = (byte >> 6) & 0x03;
        let mut reg = (byte >> 3) & 0x07;
        let mut rm = byte & 0x07;

        if prefixes.rex.r {
            reg |= 0x08;
        }
        if prefixes.rex.b {
            rm |= 0x08;
        }

        Self { mode, reg, rm }
    }
}

/// Decoded SIB byte.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Sib {
    /// Scale factor: 1, 2, 4, or 8.
    pub(crate) scale: u8,
    /// Index register (3 bits, extended by REX.X to 4 bits). 4 = no index.
    pub(crate) index: u8,
    /// Base register (3 bits, extended by REX.B to 4 bits).
    pub(crate) base: u8,
}

impl Sib {
    /// Parse a SIB byte, applying REX extensions.
    #[must_use]
    pub(crate) fn decode(byte: u8, prefixes: &Prefixes) -> Self {
        let scale_bits = (byte >> 6) & 0x03;
        let mut index = (byte >> 3) & 0x07;
        let mut base = byte & 0x07;

        if prefixes.rex.x {
            index |= 0x08;
        }
        if prefixes.rex.b {
            base |= 0x08;
        }

        let scale = 1u8 << scale_bits;

        Self { scale, index, base }
    }
}

/// Result of decoding a ModR/M-based operand.
#[derive(Debug)]
pub(crate) struct ModRMOperand {
    /// The decoded operand (register or memory).
    pub(crate) operand: Operand,
    /// Number of bytes consumed after the ModR/M byte (SIB + displacement).
    pub(crate) extra_bytes: usize,
}

/// Decode the R/M operand from a ModR/M byte + optional SIB + displacement.
///
/// `bytes` starts AFTER the ModR/M byte (at potential SIB position).
/// `op_width` is the operand width in bits for register operands.
pub(crate) fn decode_rm_operand(
    modrm: &ModRM,
    bytes: &[u8],
    prefixes: &Prefixes,
    op_width: u16,
    address: u64,
) -> Result<ModRMOperand, DisasmError> {
    // Mode 3: register direct
    if modrm.mode == 3 {
        // Trust: an 8-bit r/m needs the AH-vs-SPL resolution; see `gpr8`.
        let reg = if op_width == 8 {
            gpr8(modrm.rm, prefixes.rex.present)
        } else {
            gpr(modrm.rm, op_width)
        };
        return Ok(ModRMOperand { operand: Operand::Reg(reg), extra_bytes: 0 });
    }

    // rm=4 (without REX.B) means SIB byte follows (unless mode=3).
    let rm_base = modrm.rm & 0x07; // strip REX.B for SIB check
    let needs_sib = rm_base == 4;

    if needs_sib {
        decode_sib_operand(modrm, bytes, prefixes, address)
    } else {
        decode_simple_rm(modrm, bytes, prefixes, address)
    }
}

/// Decode memory operand without SIB (rm != 4).
fn decode_simple_rm(
    modrm: &ModRM,
    bytes: &[u8],
    _prefixes: &Prefixes,
    // Trust: unused since RIP-relative resolution moved to the decoder's choke
    // point, which is the only place the final instruction length is known.
    _address: u64,
) -> Result<ModRMOperand, DisasmError> {
    let rm_base = modrm.rm & 0x07;

    match modrm.mode {
        0b00 => {
            if rm_base == 5 {
                // RIP-relative addressing: [RIP + disp32]
                if bytes.len() < 4 {
                    return Err(DisasmError::InsufficientBytes {
                        needed: 4,
                        available: bytes.len(),
                    });
                }
                let disp = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as i64;
                // Trust: RIP-relative is measured from the FIRST BYTE OF THE NEXT
                // instruction, which is not knowable here — a trailing immediate
                // can still extend this one (`48 C7 05 <disp32> <imm32>` is 11
                // bytes, so resolving at the end of the displacement is off by
                // 4). Emit the unresolved marker; `decode_instruction` rewrites
                // it once `size` is final. Previously this stored the raw
                // displacement as `PcRelative` and left a comment saying the
                // caller would adjust — no caller ever did, so every x86-64
                // RIP-relative address was short by `insn.size`.
                Ok(ModRMOperand {
                    operand: Operand::Mem(MemoryOperand::RipRelative { displacement: disp }),
                    extra_bytes: 4,
                })
            } else {
                // [reg] — indirect, no displacement
                let base = gpr(modrm.rm, 64);
                Ok(ModRMOperand {
                    operand: Operand::Mem(MemoryOperand::Base { base }),
                    extra_bytes: 0,
                })
            }
        }
        0b01 => {
            // [reg + disp8]
            if bytes.is_empty() {
                return Err(DisasmError::InsufficientBytes { needed: 1, available: 0 });
            }
            let disp = bytes[0] as i8 as i64;
            let base = gpr(modrm.rm, 64);
            Ok(ModRMOperand {
                operand: Operand::Mem(MemoryOperand::BaseOffset { base, offset: disp }),
                extra_bytes: 1,
            })
        }
        0b10 => {
            // [reg + disp32]
            if bytes.len() < 4 {
                return Err(DisasmError::InsufficientBytes { needed: 4, available: bytes.len() });
            }
            let disp = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as i64;
            let base = gpr(modrm.rm, 64);
            Ok(ModRMOperand {
                operand: Operand::Mem(MemoryOperand::BaseOffset { base, offset: disp }),
                extra_bytes: 4,
            })
        }
        _ => unreachable!("mode 3 handled above"),
    }
}

/// Decode memory operand with SIB byte.
fn decode_sib_operand(
    modrm: &ModRM,
    bytes: &[u8],
    prefixes: &Prefixes,
    _address: u64,
) -> Result<ModRMOperand, DisasmError> {
    if bytes.is_empty() {
        return Err(DisasmError::InsufficientBytes { needed: 1, available: 0 });
    }

    let sib = Sib::decode(bytes[0], prefixes);
    let after_sib = &bytes[1..];
    let sib_base_low = sib.base & 0x07;

    // Determine displacement size
    let (disp, disp_len) = match modrm.mode {
        0b00 => {
            if sib_base_low == 5 {
                // [disp32 + index*scale] or [disp32] (no base)
                if after_sib.len() < 4 {
                    return Err(DisasmError::InsufficientBytes {
                        needed: 4,
                        available: after_sib.len(),
                    });
                }
                let d = i32::from_le_bytes([after_sib[0], after_sib[1], after_sib[2], after_sib[3]])
                    as i64;
                (d, 4usize)
            } else {
                (0i64, 0usize)
            }
        }
        0b01 => {
            if after_sib.is_empty() {
                return Err(DisasmError::InsufficientBytes { needed: 1, available: 0 });
            }
            (after_sib[0] as i8 as i64, 1)
        }
        0b10 => {
            if after_sib.len() < 4 {
                return Err(DisasmError::InsufficientBytes {
                    needed: 4,
                    available: after_sib.len(),
                });
            }
            let d =
                i32::from_le_bytes([after_sib[0], after_sib[1], after_sib[2], after_sib[3]]) as i64;
            (d, 4)
        }
        _ => unreachable!("decode_sib_operand is only called for memory addressing modes"),
    };

    let has_base = !(modrm.mode == 0 && sib_base_low == 5);
    // Trust: "no index" is index == 0b100 AND REX.X == 0. `Sib::decode` has
    // already folded REX.X in, so R12 (index 12) is a REAL index register.
    // Testing the low three bits made `12 & 7 == 4` and silently dropped R12
    // from the address: `movq (%rbx,%r12),%rax` decoded as `[rbx]`.
    let has_index = sib.index != 4;

    // Trust: every x86-64 SIB form now has ONE faithful spelling. Until
    // 2026-08-18 this block produced a wrong address for THREE of its four
    // arms — the shared `MemoryOperand` enum is AArch64-shaped and had no
    // variant for an absolute address or for base+index+displacement, so the
    // decoder spelled them as `PcRelative` or discarded information outright.
    let mem = match (has_base, has_index) {
        // base + index*scale + disp. The displacement used to be DROPPED here
        // and mislabelled "an over-approximation downstream consumers must
        // handle": an over-approximation is a WIDER address set, whereas a
        // dropped displacement is a DIFFERENT, SPECIFIC, WRONG address.
        // `movq 0x20(%rbx,%rcx,2),%rdx` yielded `rbx + rcx*2`.
        (true, true) => MemoryOperand::BaseIndexOffset {
            base: Some(gpr(sib.base, 64)),
            index: gpr(sib.index, 64),
            scale_shift: scale_to_shift(sib.scale),
            displacement: disp,
        },
        (true, false) => {
            if disp == 0 {
                MemoryOperand::Base { base: gpr(sib.base, 64) }
            } else {
                MemoryOperand::BaseOffset { base: gpr(sib.base, 64), offset: disp }
            }
        }
        // index*scale + disp32, with NO base register. This used to emit
        // `BaseRegister { base: gpr(sib.base) }` — where `sib.base` is the 101
        // "no base" encoding — under a comment claiming "Won't be used". It WAS
        // used, so `movq 0x10(,%rax,4),%rcx` read RBP and dropped the 0x10,
        // yielding `rbp + rax*4`. `base: None` contributes zero, as the
        // encoding requires.
        (false, true) => MemoryOperand::BaseIndexOffset {
            base: None,
            index: gpr(sib.index, 64),
            scale_shift: scale_to_shift(sib.scale),
            displacement: disp,
        },
        // [disp32] — an ABSOLUTE address. Spelling it `PcRelative` made it
        // resolve to `PC + disp`.
        (false, false) => MemoryOperand::Absolute { address: disp as u64 },
    };

    Ok(ModRMOperand {
        operand: Operand::Mem(mem),
        extra_bytes: 1 + disp_len, // SIB byte + displacement
    })
}

/// Convert SIB scale factor (1,2,4,8) to shift amount (0,1,2,3).
fn scale_to_shift(scale: u8) -> u8 {
    match scale {
        1 => 0,
        2 => 1,
        4 => 2,
        8 => 3,
        _ => 0,
    }
}

/// Create a general-purpose register operand for x86-64.
/// index: 0-15 (RAX, RCX, RDX, RBX, RSP, RBP, RSI, RDI, R8-R15).
/// width: 8, 16, 32, or 64 bits.
#[must_use]
/// An 8-bit register operand, resolving the AH/CH/DH/BH vs SPL/BPL/SIL/DIL
/// ambiguity.
///
/// x86-64: 8-bit register numbers 4..7 denote the legacy HIGH-BYTE registers
/// `AH/CH/DH/BH` when NO REX prefix is present, and the low bytes
/// `SPL/BPL/SIL/DIL` when one is. Encoding both as `RegKind::Gpr` index 4..7
/// made `mov ah, imm8` indistinguishable from a write to `SPL`, and machine-sem
/// then modelled it as a STACK POINTER write.
pub(crate) fn gpr8(index: u8, rex_present: bool) -> Register {
    use crate::operand::RegKind;
    if !rex_present && (4..=7).contains(&index) {
        // AH/CH/DH/BH are bits 15:8 of RAX/RCX/RDX/RBX respectively.
        return Register { kind: RegKind::GprHighByte, index: index - 4, width: 8 };
    }
    Register { kind: RegKind::Gpr, index, width: 8 }
}

/// A general-purpose register operand of any width, resolving the 8-bit
/// AH/CH/DH/BH vs SPL/BPL/SIL/DIL ambiguity when the width is 8.
///
/// Use this wherever the width is a VARIABLE. Calling `gpr` with a width that
/// can be 8 reintroduces the defect: `decode_modrm_rm_reg` did exactly that and
/// rendered `mov r/m8, r8` reg 5 as `bpl` instead of `ch` — found by the
/// x86-64 decode differential on its first random run, after three other sites
/// had been fixed by hand.
pub(crate) fn gpr_sized(index: u8, width: u16, rex_present: bool) -> Register {
    if width == 8 { gpr8(index, rex_present) } else { gpr(index, width) }
}

pub(crate) fn gpr(index: u8, width: u16) -> Register {
    use crate::operand::RegKind;
    // RSP (index 4) is also the stack pointer, but in x86-64 context
    // we treat all as GPR for consistency with the Register type.
    Register { kind: RegKind::Gpr, index, width }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_modrm_decode_reg_direct() {
        let prefixes = Prefixes::default();
        // MOV RAX, RCX: ModR/M = 0xC1 = 11_000_001
        let m = ModRM::decode(0xC1, &prefixes);
        assert_eq!(m.mode, 3);
        assert_eq!(m.reg, 0); // RAX
        assert_eq!(m.rm, 1); // RCX
    }

    #[test]
    fn test_modrm_rex_extension() {
        let mut prefixes = Prefixes::default();
        prefixes.rex.r = true;
        prefixes.rex.b = true;
        // ModR/M = 0xC1 = 11_000_001 -> reg=8, rm=9
        let m = ModRM::decode(0xC1, &prefixes);
        assert_eq!(m.reg, 8); // R8
        assert_eq!(m.rm, 9); // R9
    }

    #[test]
    fn test_modrm_indirect_no_disp() {
        let prefixes = Prefixes::default();
        // [RCX]: mode=00, rm=001
        let m = ModRM::decode(0x01, &prefixes);
        assert_eq!(m.mode, 0);
        assert_eq!(m.rm, 1);
        let result = decode_rm_operand(&m, &[], &prefixes, 64, 0).unwrap();
        assert_eq!(result.extra_bytes, 0);
        assert!(matches!(result.operand, Operand::Mem(MemoryOperand::Base { .. })));
    }

    #[test]
    fn test_modrm_disp8() {
        let prefixes = Prefixes::default();
        // [RCX + 0x10]: mode=01, rm=001
        let m = ModRM::decode(0x41, &prefixes);
        assert_eq!(m.mode, 1);
        let result = decode_rm_operand(&m, &[0x10], &prefixes, 64, 0).unwrap();
        assert_eq!(result.extra_bytes, 1);
        match result.operand {
            Operand::Mem(MemoryOperand::BaseOffset { base, offset }) => {
                assert_eq!(base.index, 1); // RCX
                assert_eq!(offset, 0x10);
            }
            _ => panic!("expected BaseOffset"),
        }
    }

    #[test]
    fn test_modrm_rip_relative() {
        let prefixes = Prefixes::default();
        // [RIP + disp32]: mode=00, rm=5
        let m = ModRM::decode(0x05, &prefixes);
        assert_eq!(m.mode, 0);
        assert_eq!(m.rm, 5);
        let disp_bytes = 0x100i32.to_le_bytes();
        let result = decode_rm_operand(&m, &disp_bytes, &prefixes, 64, 0x1000).unwrap();
        assert_eq!(result.extra_bytes, 4);
        // The ModRM layer emits the UNRESOLVED marker and nothing more: the
        // effective address is relative to the next instruction, whose start is
        // not knowable here because a trailing immediate can still extend this
        // one. `decode_instruction` resolves it once `size` is final.
        //
        // This asserted `PcRelative { offset: 0x100 }` until 2026-08-18 — it
        // pinned the shape that let the address stay unadjusted all the way
        // into the lifted memory facts.
        assert!(matches!(
            result.operand,
            Operand::Mem(MemoryOperand::RipRelative { displacement: 0x100 })
        ));
    }

    /// The unresolved marker must NEVER survive a full decode — that is the
    /// invariant which makes a missed resolution fail closed rather than
    /// silently produce an AArch64-correct/x86-wrong address.
    #[test]
    fn the_unresolved_rip_marker_never_escapes_a_full_decode() {
        use crate::arch::{Arch, Decoder};
        let decoder = crate::x86_64::X86_64Decoder::new();
        // mov rax,[rip+0x10] at 0x1000 -> 0x1000 + 7 + 0x10
        let insn = decoder
            .decode(&[0x48, 0x8B, 0x05, 0x10, 0x00, 0x00, 0x00], 0x1000)
            .expect("decode should succeed");
        assert_eq!(
            insn.operand(1),
            Some(&Operand::Mem(MemoryOperand::Absolute { address: 0x1017 })),
            "0x1000 + 7 + 0x10 = 0x1017"
        );
    }

    #[test]
    fn test_sib_decode() {
        let prefixes = Prefixes::default();
        // SIB: scale=2 (01), index=RCX (001), base=RAX (000) => 0x48
        let sib = Sib::decode(0x48, &prefixes);
        assert_eq!(sib.scale, 2);
        assert_eq!(sib.index, 1); // RCX
        assert_eq!(sib.base, 0); // RAX
    }

    #[test]
    fn test_gpr_creation() {
        let r = gpr(0, 64);
        assert_eq!(r.index, 0);
        assert_eq!(r.width, 64);
    }
}
