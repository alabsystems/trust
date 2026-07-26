// trust-disasm opcode definitions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use core::fmt;

/// Instruction opcode / mnemonic.
///
/// This enum is a shared mnemonic set, not an architectural completeness
/// claim. For AArch64 it covers the current scalar decode/lift subset plus
/// selected fail-closed classes. Additional ISAs reuse opcodes where the
/// mnemonic matches (e.g., ADD, SUB are common) and add ISA-specific variants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Opcode {
    // === Data Processing (Immediate) ===
    Add,
    Adds,
    Sub,
    Subs,
    Adr,
    Adrp,
    And,
    Ands,
    Orr,
    Eor,
    Movn,
    Movz,
    Movk,
    /// Bitfield move.
    Sbfm,
    Ubfm,
    Bfm,
    /// Extract.
    Extr,

    // === Data Processing (Register) ===
    /// Logical shifted register.
    Bic,
    Bics,
    Orn,
    Eon,
    /// Arithmetic shifted register (ADD/SUB reuse the immediate variants).
    /// Add/subtract with carry.
    Adc,
    Adcs,
    Sbc,
    Sbcs,
    /// Conditional compare (immediate).
    Ccmn,
    Ccmp,
    /// Conditional select.
    Csel,
    Csinc,
    Csinv,
    Csneg,
    /// Data processing (2 source).
    Udiv,
    Sdiv,
    Lslv,
    Lsrv,
    Asrv,
    Rorv,
    /// Data processing (3 source).
    Madd,
    Msub,
    Smaddl,
    Smsubl,
    Smulh,
    Umaddl,
    Umsubl,
    Umulh,
    /// Reverse bits/bytes.
    Rbit,
    Rev16,
    Rev32,
    Rev,
    Clz,
    Cls,

    // === Loads and Stores ===
    Ldr,
    Ldrb,
    Ldrh,
    Ldrsb,
    Ldrsh,
    Ldrsw,
    Str,
    Strb,
    Strh,
    /// Load pair.
    Ldp,
    /// Store pair.
    Stp,
    /// Load exclusive.
    Ldxr,
    /// Store exclusive.
    Stxr,
    /// Load-acquire.
    Ldar,
    /// Store-release.
    Stlr,
    /// Load-acquire exclusive.
    Ldaxr,
    /// Store-release exclusive.
    Stlxr,
    /// Load literal (PC-relative).
    LdrLiteral,
    /// Prefetch.
    Prfm,

    // === Branches ===
    B,
    Bl,
    Br,
    Blr,
    Ret,
    /// Conditional branch (B.cond).
    BCond,
    Cbz,
    Cbnz,
    Tbz,
    Tbnz,

    // === System ===
    Nop,
    Svc,
    Hvc,
    Smc,
    Brk,
    Hlt,
    Msr,
    Mrs,
    Dmb,
    Dsb,
    Isb,
    Clrex,
    /// Yield, WFE, WFI, SEV, SEVL (hint instructions).
    Yield,
    Wfe,
    Wfi,
    Sev,
    Sevl,

    // === SIMD / FP basics ===
    FmovImm,
    FmovReg,
    Fadd,
    Fsub,
    Fmul,
    Fdiv,
    Fcmp,
    Fcsel,
    Fabs,
    Fneg,
    Fsqrt,
    Scvtf,
    Ucvtf,
    Fcvtzs,
    Fcvtzu,
    Fcvt,
    /// SIMD move.
    SimdMov,

    // === x86-64 Specific ===
    /// x86-64 MOV (register/memory/immediate).
    Mov,
    /// x86-64 PUSH.
    Push,
    /// x86-64 POP.
    Pop,
    /// x86-64 LEA (load effective address).
    Lea,
    /// x86-64 CALL (near).
    Call,
    /// x86-64 JMP (near unconditional).
    Jmp,
    /// x86-64 Jcc (conditional jump).
    Jcc,
    /// x86-64 CMP.
    Cmp,
    /// x86-64 TEST.
    Test,
    /// x86-64 XOR.
    Xor,
    /// x86-64 OR.
    Or,
    /// x86-64 INC.
    Inc,
    /// x86-64 DEC.
    Dec,
    /// x86-64 NEG.
    Neg,
    /// x86-64 NOT.
    Not,
    /// x86-64 SHL/SAL.
    Shl,
    /// x86-64 SHR.
    Shr,
    /// x86-64 SAR.
    Sar,
    /// x86-64 IMUL.
    Imul,
    /// x86-64 IDIV.
    Idiv,
    /// x86-64 DIV (unsigned).
    Div,
    /// x86-64 MUL (unsigned).
    Mul,
    /// x86-64 MOVZX (zero-extend).
    Movzx,
    /// x86-64 MOVSX / MOVSXD (sign-extend).
    Movsx,
    /// x86-64 CDQ / CQO (sign-extend accumulator).
    Cdq,
    /// x86-64 XCHG.
    Xchg,
    /// x86-64 LEAVE.
    Leave,
    /// x86-64 INT3 (breakpoint).
    Int3,
    /// x86-64 SYSCALL.
    Syscall,
    /// x86-64 ENDBR64 (CET).
    Endbr64,
    /// x86-64 CMOVcc (conditional move).
    Cmovcc,
    /// x86-64 SETcc (set byte on condition).
    Setcc,
    /// x86-64 MOVSXD (sign-extend DWORD to QWORD, opcode 0x63 with REX.W).
    Movsxd,
    /// x86-64 CMPXCHG (compare and exchange).
    Cmpxchg,
    /// x86-64 BSF (bit scan forward).
    Bsf,
    /// x86-64 BSR (bit scan reverse).
    Bsr,
    /// x86-64 CQO (sign-extend RAX into RDX:RAX).
    Cqo,

    /// Unknown or unimplemented instruction (stores raw encoding).
    Unknown,
}

impl fmt::Display for Opcode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::Add => "ADD",
            Self::Adds => "ADDS",
            Self::Sub => "SUB",
            Self::Subs => "SUBS",
            Self::Adr => "ADR",
            Self::Adrp => "ADRP",
            Self::And => "AND",
            Self::Ands => "ANDS",
            Self::Orr => "ORR",
            Self::Eor => "EOR",
            Self::Movn => "MOVN",
            Self::Movz => "MOVZ",
            Self::Movk => "MOVK",
            Self::Sbfm => "SBFM",
            Self::Ubfm => "UBFM",
            Self::Bfm => "BFM",
            Self::Extr => "EXTR",
            Self::Bic => "BIC",
            Self::Bics => "BICS",
            Self::Orn => "ORN",
            Self::Eon => "EON",
            Self::Adc => "ADC",
            Self::Adcs => "ADCS",
            Self::Sbc => "SBC",
            Self::Sbcs => "SBCS",
            Self::Ccmn => "CCMN",
            Self::Ccmp => "CCMP",
            Self::Csel => "CSEL",
            Self::Csinc => "CSINC",
            Self::Csinv => "CSINV",
            Self::Csneg => "CSNEG",
            Self::Udiv => "UDIV",
            Self::Sdiv => "SDIV",
            Self::Lslv => "LSLV",
            Self::Lsrv => "LSRV",
            Self::Asrv => "ASRV",
            Self::Rorv => "RORV",
            Self::Madd => "MADD",
            Self::Msub => "MSUB",
            Self::Smaddl => "SMADDL",
            Self::Smsubl => "SMSUBL",
            Self::Smulh => "SMULH",
            Self::Umaddl => "UMADDL",
            Self::Umsubl => "UMSUBL",
            Self::Umulh => "UMULH",
            Self::Rbit => "RBIT",
            Self::Rev16 => "REV16",
            Self::Rev32 => "REV32",
            Self::Rev => "REV",
            Self::Clz => "CLZ",
            Self::Cls => "CLS",
            Self::Ldr => "LDR",
            Self::Ldrb => "LDRB",
            Self::Ldrh => "LDRH",
            Self::Ldrsb => "LDRSB",
            Self::Ldrsh => "LDRSH",
            Self::Ldrsw => "LDRSW",
            Self::Str => "STR",
            Self::Strb => "STRB",
            Self::Strh => "STRH",
            Self::Ldp => "LDP",
            Self::Stp => "STP",
            Self::Ldxr => "LDXR",
            Self::Stxr => "STXR",
            Self::Ldar => "LDAR",
            Self::Stlr => "STLR",
            Self::Ldaxr => "LDAXR",
            Self::Stlxr => "STLXR",
            Self::LdrLiteral => "LDR",
            Self::Prfm => "PRFM",
            Self::B => "B",
            Self::Bl => "BL",
            Self::Br => "BR",
            Self::Blr => "BLR",
            Self::Ret => "RET",
            Self::BCond => "B",
            Self::Cbz => "CBZ",
            Self::Cbnz => "CBNZ",
            Self::Tbz => "TBZ",
            Self::Tbnz => "TBNZ",
            Self::Nop => "NOP",
            Self::Svc => "SVC",
            Self::Hvc => "HVC",
            Self::Smc => "SMC",
            Self::Brk => "BRK",
            Self::Hlt => "HLT",
            Self::Msr => "MSR",
            Self::Mrs => "MRS",
            Self::Dmb => "DMB",
            Self::Dsb => "DSB",
            Self::Isb => "ISB",
            Self::Clrex => "CLREX",
            Self::Yield => "YIELD",
            Self::Wfe => "WFE",
            Self::Wfi => "WFI",
            Self::Sev => "SEV",
            Self::Sevl => "SEVL",
            Self::FmovImm => "FMOV",
            Self::FmovReg => "FMOV",
            Self::Fadd => "FADD",
            Self::Fsub => "FSUB",
            Self::Fmul => "FMUL",
            Self::Fdiv => "FDIV",
            Self::Fcmp => "FCMP",
            Self::Fcsel => "FCSEL",
            Self::Fabs => "FABS",
            Self::Fneg => "FNEG",
            Self::Fsqrt => "FSQRT",
            Self::Scvtf => "SCVTF",
            Self::Ucvtf => "UCVTF",
            Self::Fcvtzs => "FCVTZS",
            Self::Fcvtzu => "FCVTZU",
            Self::Fcvt => "FCVT",
            Self::SimdMov => "MOV",
            Self::Mov => "MOV",
            Self::Push => "PUSH",
            Self::Pop => "POP",
            Self::Lea => "LEA",
            Self::Call => "CALL",
            Self::Jmp => "JMP",
            Self::Jcc => "Jcc",
            Self::Cmp => "CMP",
            Self::Test => "TEST",
            Self::Xor => "XOR",
            Self::Or => "OR",
            Self::Inc => "INC",
            Self::Dec => "DEC",
            Self::Neg => "NEG",
            Self::Not => "NOT",
            Self::Shl => "SHL",
            Self::Shr => "SHR",
            Self::Sar => "SAR",
            Self::Imul => "IMUL",
            Self::Idiv => "IDIV",
            Self::Div => "DIV",
            Self::Mul => "MUL",
            Self::Movzx => "MOVZX",
            Self::Movsx => "MOVSX",
            Self::Cdq => "CDQ",
            Self::Xchg => "XCHG",
            Self::Leave => "LEAVE",
            Self::Int3 => "INT3",
            Self::Syscall => "SYSCALL",
            Self::Endbr64 => "ENDBR64",
            Self::Cmovcc => "CMOVcc",
            Self::Setcc => "SETcc",
            Self::Movsxd => "MOVSXD",
            Self::Cmpxchg => "CMPXCHG",
            Self::Bsf => "BSF",
            Self::Bsr => "BSR",
            Self::Cqo => "CQO",
            Self::Unknown => "???",
        };
        write!(f, "{s}")
    }
}
