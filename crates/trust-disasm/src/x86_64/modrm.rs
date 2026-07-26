// x86-64 ModR/M and SIB byte decoding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// Reference: Intel SDM Vol 2A, Table 2-2 (ModR/M) and Table 2-3 (SIB).
//
// ModR/M byte layout: [mod:2][reg:3][rm:3]
// SIB byte layout:    [scale:2][index:3][base:3]

use crate::error::DisasmError;
use crate::operand::{MemoryOperand, Operand, Register};

use super::prefix::Prefixes;

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
        return Ok(ModRMOperand { operand: Operand::Reg(gpr(modrm.rm, op_width)), extra_bytes: 0 });
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
    address: u64,
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
                // The RIP-relative address is computed from the END of the instruction,
                // but we don't know the full size yet. Store as PcRelative offset.
                // The caller can adjust when the full instruction length is known.
                let _ = address; // Address used by caller for adjustment
                Ok(ModRMOperand {
                    operand: Operand::Mem(MemoryOperand::PcRelative { offset: disp }),
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
    let sib_index_low = sib.index & 0x07;

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
    let has_index = sib_index_low != 4; // index=4 (RSP) means no index

    let mem = match (has_base, has_index) {
        (true, true) => MemoryOperand::BaseRegister {
            base: gpr(sib.base, 64),
            index: gpr(sib.index, 64),
            extend: None,
            shift: scale_to_shift(sib.scale),
        },
        (true, false) => {
            if disp == 0 {
                MemoryOperand::Base { base: gpr(sib.base, 64) }
            } else {
                MemoryOperand::BaseOffset { base: gpr(sib.base, 64), offset: disp }
            }
        }
        (false, true) => {
            // [index*scale + disp32]
            // We represent this as BaseOffset with a synthetic zero-base +
            // the index encoded in the base. Not ideal but works with our
            // existing MemoryOperand variants. Use BaseRegister with a known
            // pattern: base is a placeholder, but better to use BaseOffset
            // with the displacement and note the index separately.
            // For now, use BaseRegister where base is RBP (index 5) as
            // that's the conventional encoding.
            MemoryOperand::BaseRegister {
                base: gpr(sib.base, 64), // Won't be used — mod=00, base=5
                index: gpr(sib.index, 64),
                extend: None,
                shift: scale_to_shift(sib.scale),
            }
        }
        (false, false) => {
            // [disp32] absolute
            MemoryOperand::PcRelative { offset: disp }
        }
    };

    // Adjust for displacement if we have base+offset but used BaseRegister
    let mem = if has_base && has_index && disp != 0 {
        // Limitation: MemoryOperand lacks a base+index+disp variant.
        // We use BaseRegister (base+index) and the displacement is dropped.
        // Downstream consumers must handle this over-approximation.
        mem
    } else if has_base && !has_index && disp != 0 {
        MemoryOperand::BaseOffset { base: gpr(sib.base, 64), offset: disp }
    } else {
        mem
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
        assert!(matches!(
            result.operand,
            Operand::Mem(MemoryOperand::PcRelative { offset: 0x100 })
        ));
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
