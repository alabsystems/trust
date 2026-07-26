// trust-disasm operand types
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use core::fmt;

/// A register reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Register {
    /// Register class.
    pub kind: RegKind,
    /// Register index (0-30 for GPR, 0-31 for SIMD/FP).
    pub index: u8,
    /// Width in bits (32 for W, 64 for X, 8/16/32/64/128 for SIMD).
    pub width: u16,
}

impl Register {
    /// Create a general-purpose register (X0-X30 or W0-W30).
    #[must_use]
    pub fn gpr(index: u8, is_64bit: bool) -> Self {
        Self { kind: RegKind::Gpr, index, width: if is_64bit { 64 } else { 32 } }
    }

    /// Create the stack pointer register (SP / WSP).
    #[must_use]
    pub fn sp(is_64bit: bool) -> Self {
        Self { kind: RegKind::Sp, index: 31, width: if is_64bit { 64 } else { 32 } }
    }

    /// Create the zero register (XZR / WZR).
    #[must_use]
    pub fn zr(is_64bit: bool) -> Self {
        Self { kind: RegKind::Zr, index: 31, width: if is_64bit { 64 } else { 32 } }
    }

    /// Create a SIMD/FP register.
    #[must_use]
    pub fn simd(index: u8, width: u16) -> Self {
        Self { kind: RegKind::Simd, index, width }
    }

    /// True if this is the zero register.
    #[must_use]
    pub fn is_zero_register(&self) -> bool {
        self.kind == RegKind::Zr
    }

    /// True if this is the stack pointer.
    #[must_use]
    pub fn is_stack_pointer(&self) -> bool {
        self.kind == RegKind::Sp
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            RegKind::Gpr => {
                let prefix = if self.width == 64 { 'X' } else { 'W' };
                write!(f, "{prefix}{}", self.index)
            }
            RegKind::Sp => {
                if self.width == 64 {
                    write!(f, "SP")
                } else {
                    write!(f, "WSP")
                }
            }
            RegKind::Zr => {
                if self.width == 64 {
                    write!(f, "XZR")
                } else {
                    write!(f, "WZR")
                }
            }
            RegKind::Simd => {
                let prefix = match self.width {
                    8 => 'B',
                    16 => 'H',
                    32 => 'S',
                    64 => 'D',
                    128 => 'Q',
                    _ => 'V',
                };
                write!(f, "{prefix}{}", self.index)
            }
            RegKind::System => write!(f, "SYS{}", self.index),
        }
    }
}

/// Register class/kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RegKind {
    /// General-purpose register (X0-X30 / W0-W30).
    Gpr,
    /// Stack pointer (SP / WSP). Encoded as register 31 in SP contexts.
    Sp,
    /// Zero register (XZR / WZR). Encoded as register 31 in ZR contexts.
    Zr,
    /// SIMD / floating-point register (V0-V31 / Q/D/S/H/B).
    Simd,
    /// System register (for MSR/MRS).
    System,
}

/// Shift type for shifted-register operands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ShiftType {
    Lsl,
    Lsr,
    Asr,
    Ror,
}

impl fmt::Display for ShiftType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lsl => write!(f, "LSL"),
            Self::Lsr => write!(f, "LSR"),
            Self::Asr => write!(f, "ASR"),
            Self::Ror => write!(f, "ROR"),
        }
    }
}

/// Extend type for extended-register operands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum ExtendType {
    Uxtb,
    Uxth,
    Uxtw,
    Uxtx,
    Sxtb,
    Sxth,
    Sxtw,
    Sxtx,
}

impl fmt::Display for ExtendType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Uxtb => write!(f, "UXTB"),
            Self::Uxth => write!(f, "UXTH"),
            Self::Uxtw => write!(f, "UXTW"),
            Self::Uxtx => write!(f, "UXTX"),
            Self::Sxtb => write!(f, "SXTB"),
            Self::Sxth => write!(f, "SXTH"),
            Self::Sxtw => write!(f, "SXTW"),
            Self::Sxtx => write!(f, "SXTX"),
        }
    }
}

/// AArch64 condition codes (4-bit encoding).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Condition {
    Eq = 0b0000,
    Ne = 0b0001,
    Cs = 0b0010, // aka HS
    Cc = 0b0011, // aka LO
    Mi = 0b0100,
    Pl = 0b0101,
    Vs = 0b0110,
    Vc = 0b0111,
    Hi = 0b1000,
    Ls = 0b1001,
    Ge = 0b1010,
    Lt = 0b1011,
    Gt = 0b1100,
    Le = 0b1101,
    Al = 0b1110,
    Nv = 0b1111,
}

impl Condition {
    /// Decode a 4-bit condition code.
    #[must_use]
    pub fn from_u8(val: u8) -> Self {
        match val & 0xF {
            0b0000 => Self::Eq,
            0b0001 => Self::Ne,
            0b0010 => Self::Cs,
            0b0011 => Self::Cc,
            0b0100 => Self::Mi,
            0b0101 => Self::Pl,
            0b0110 => Self::Vs,
            0b0111 => Self::Vc,
            0b1000 => Self::Hi,
            0b1001 => Self::Ls,
            0b1010 => Self::Ge,
            0b1011 => Self::Lt,
            0b1100 => Self::Gt,
            0b1101 => Self::Le,
            0b1110 => Self::Al,
            _ => Self::Nv,
        }
    }

    /// Invert the condition.
    #[must_use]
    pub fn invert(self) -> Self {
        Self::from_u8((self as u8) ^ 1)
    }
}

impl fmt::Display for Condition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Eq => write!(f, "EQ"),
            Self::Ne => write!(f, "NE"),
            Self::Cs => write!(f, "CS"),
            Self::Cc => write!(f, "CC"),
            Self::Mi => write!(f, "MI"),
            Self::Pl => write!(f, "PL"),
            Self::Vs => write!(f, "VS"),
            Self::Vc => write!(f, "VC"),
            Self::Hi => write!(f, "HI"),
            Self::Ls => write!(f, "LS"),
            Self::Ge => write!(f, "GE"),
            Self::Lt => write!(f, "LT"),
            Self::Gt => write!(f, "GT"),
            Self::Le => write!(f, "LE"),
            Self::Al => write!(f, "AL"),
            Self::Nv => write!(f, "NV"),
        }
    }
}

/// Barrier type for DMB/DSB/ISB.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BarrierDomain {
    Osh, // Outer shareable
    Nsh, // Non-shareable
    Ish, // Inner shareable
    Sy,  // Full system
}

/// Barrier type qualifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum BarrierType {
    Ld,   // Load
    St,   // Store
    Full, // Load + Store
}

/// Memory addressing mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MemoryOperand {
    /// `[base]` — base register only.
    Base { base: Register },
    /// `[base, #imm]` — base + signed immediate offset.
    BaseOffset { base: Register, offset: i64 },
    /// `[base, Xm]` or `[base, Xm, shift]` — base + register offset.
    BaseRegister { base: Register, index: Register, extend: Option<ExtendType>, shift: u8 },
    /// `[base, #imm]!` — pre-indexed.
    PreIndex { base: Register, offset: i64 },
    /// `[base], #imm` — post-indexed.
    PostIndex { base: Register, offset: i64 },
    /// PC-relative literal (LDR literal).
    PcRelative { offset: i64 },
}

/// An instruction operand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Operand {
    /// A register.
    Reg(Register),
    /// A shifted register: Rm, shift #amount.
    ShiftedReg { reg: Register, shift: ShiftType, amount: u8 },
    /// An extended register: Rm, extend #amount.
    ExtendedReg { reg: Register, extend: ExtendType, shift: u8 },
    /// An immediate value.
    Imm(u64),
    /// A signed immediate value (for offsets, etc.).
    SignedImm(i64),
    /// A PC-relative address (branch target, ADR/ADRP).
    PcRelAddr(u64),
    /// A memory operand (for loads/stores).
    Mem(MemoryOperand),
    /// A condition code.
    Cond(Condition),
    /// A barrier option (for DMB/DSB).
    Barrier { domain: BarrierDomain, kind: BarrierType },
    /// A system register (encoded as op0:op1:CRn:CRm:op2).
    SysReg(u16),
    /// Bit position (for TBZ/TBNZ).
    BitPos(u8),
}
